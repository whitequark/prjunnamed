use std::collections::{hash_map, HashMap, HashSet};

use prjunnamed_netlist::{
    CellRepr, Const, ControlNet, Design, FlipFlop, Instance, IoBuffer, IoNet, IoValue, Net, ParamValue, Trit, Value,
};

use crate::yosys;

#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Json(json::Error),
    Syntax(yosys::SyntaxError),
    MetaDataType(yosys::MetadataTypeError),
    Semantic,
}

impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<json::Error> for Error {
    fn from(error: json::Error) -> Self {
        Self::Json(error)
    }
}

impl From<yosys::SyntaxError> for Error {
    fn from(error: yosys::SyntaxError) -> Self {
        Self::Syntax(error)
    }
}

impl From<yosys::MetadataTypeError> for Error {
    fn from(error: yosys::MetadataTypeError) -> Self {
        Self::MetaDataType(error)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Io(error) => write!(f, "I/O error: {}", error),
            Error::Json(error) => write!(f, "JSON parse error: {}", error),
            Error::Syntax(error) => write!(f, "{}", error),
            Error::MetaDataType(error) => write!(f, "{}", error),
            Error::Semantic => write!(f, "semantic error"),
        }
    }
}

impl std::error::Error for Error {}

struct ModuleImporter<'a> {
    module: &'a yosys::Module,
    design_io_ports: &'a HashSet<(&'a str, &'a str)>,
    io_nets: HashMap<usize, IoNet>,
    driven_nets: HashSet<usize>,
    nets: HashMap<usize, Net>,
    init: HashMap<usize, Trit>,
    design: Design,
}

impl ModuleImporter<'_> {
    fn drive(&mut self, bits: &yosys::BitVector, value: Value) {
        assert_eq!(bits.len(), value.len());
        for (&bit, net) in bits.iter().zip(value.into_iter()) {
            let yosys::Bit::Net(ynet) = bit else { unreachable!() };
            assert!(!self.driven_nets.contains(&ynet));
            match self.nets.entry(ynet) {
                hash_map::Entry::Occupied(e) => {
                    let cell = self.design.find_cell(*e.get()).unwrap().0;
                    self.design.replace_cell(cell.index(), CellRepr::Buf(Value::from(net)));
                }
                hash_map::Entry::Vacant(e) => {
                    e.insert(net);
                }
            }
            if let Some(&io_net) = self.io_nets.get(&ynet) {
                self.design.add_cell(CellRepr::Iob(IoBuffer {
                    enable: ControlNet::Pos(Net::ONE),
                    output: Value::from(net),
                    io: IoValue::from(io_net),
                }));
            }
            self.driven_nets.insert(ynet);
        }
    }

    fn port_drive(&mut self, cell: &yosys::CellDetails, port: &str, value: Value) {
        self.drive(cell.connections.get(port).unwrap(), value);
    }

    fn value(&mut self, bits: &yosys::BitVector) -> Value {
        let mut nets = vec![];
        for &bit in bits.iter() {
            let net = match bit {
                yosys::Bit::HiZ | yosys::Bit::Undef => Net::UNDEF,
                yosys::Bit::Zero => Net::ZERO,
                yosys::Bit::One => Net::ONE,
                yosys::Bit::Net(ynet) => *self
                    .nets
                    .entry(ynet)
                    .or_insert_with(|| self.design.add_cell(CellRepr::Buf(Value::undef(1))).output()[0]),
            };
            nets.push(net);
        }
        Value::from_iter(nets)
    }

    fn io_value(&self, bits: &yosys::BitVector) -> IoValue {
        let mut io = vec![];
        for &bit in bits.iter() {
            let yosys::Bit::Net(ynet) = bit else { unreachable!() };
            let io_net = *self.io_nets.get(&ynet).unwrap();
            io.push(io_net);
        }
        IoValue::from_iter(io)
    }

    fn port_value(&mut self, cell: &yosys::CellDetails, port: &str) -> Value {
        self.value(cell.connections.get(port).unwrap())
    }

    fn port_control_net(&mut self, cell: &yosys::CellDetails, port: &str) -> ControlNet {
        let value = self.port_value(cell, port);
        assert_eq!(value.len(), 1);
        let net = value[0];
        let polarity = cell.parameters.get(&format!("{port}_POLARITY")).unwrap().as_bool().unwrap();
        if polarity {
            ControlNet::Pos(net)
        } else {
            ControlNet::Neg(net)
        }
    }

    fn init_value(&self, cell: &yosys::CellDetails, port: &str) -> Const {
        let bits = cell.connections.get(port).unwrap();
        let mut res = vec![];
        for &bit in bits.iter() {
            let yosys::Bit::Net(ynet) = bit else { unreachable!() };
            res.push(match self.init.get(&ynet) {
                None => Trit::Undef,
                Some(&val) => val,
            });
        }
        Const::from_iter(res)
    }

    fn value_ext(&mut self, cell: &yosys::CellDetails, port: &str, width: usize, signed: bool) -> Value {
        if signed {
            self.port_value(cell, port).sext(width)
        } else {
            self.port_value(cell, port).zext(width)
        }
    }

    fn handle_init(&mut self) -> Result<(), Error> {
        for net_details in self.module.netnames.0.values() {
            let Some(init) = net_details.attributes.get("init") else { continue };
            let init = init.as_const()?;
            if init.len() != net_details.bits.len() {
                Err(yosys::MetadataTypeError)?;
            }
            for (&bit, binit) in net_details.bits.iter().zip(init.into_iter()) {
                if binit == Trit::Undef {
                    continue;
                }
                let yosys::Bit::Net(ynet) = bit else { Err(yosys::MetadataTypeError)? };
                match self.init.entry(ynet) {
                    hash_map::Entry::Occupied(e) => {
                        assert_eq!(*e.get(), binit);
                    }
                    hash_map::Entry::Vacant(e) => {
                        e.insert(binit);
                    }
                }
            }
        }
        Ok(())
    }

    fn handle_ports(&mut self) -> Result<(), Error> {
        // determine set of nets that need to be IOs from cell port connections.
        let mut io_net_conns = HashSet::new();
        for cell in self.module.cells.0.values() {
            for (port_name, bits) in cell.connections.iter() {
                if self.design_io_ports.contains(&(&cell.type_, port_name)) {
                    for &bit in bits.iter() {
                        let yosys::Bit::Net(net) = bit else { return Err(Error::Semantic) };
                        io_net_conns.insert(net);
                    }
                }
            }
        }

        // now create all IoValues we're going to need.
        let mut io_ports = HashSet::new();
        for (port_name, port) in self.module.ports.iter() {
            let mut is_inout = port.direction == yosys::PortDirection::Inout;
            for &bit in port.bits.iter() {
                if let yosys::Bit::Net(net) = bit {
                    if io_net_conns.contains(&net) {
                        is_inout = true;
                    }
                }
            }
            if is_inout {
                let ioval = self.design.add_io(port_name.clone(), port.bits.0.len());
                for (index, &bit) in port.bits.iter().enumerate() {
                    let yosys::Bit::Net(net) = bit else { return Err(Error::Semantic) };
                    match self.io_nets.entry(net) {
                        hash_map::Entry::Occupied(_) => {
                            return Err(Error::Semantic);
                        }
                        hash_map::Entry::Vacant(e) => {
                            e.insert(ioval[index]);
                        }
                    }
                }
                io_ports.insert(port_name);
            }
        }
        // handle all other ports
        for (port_name, port) in self.module.ports.iter() {
            if io_ports.contains(port_name) {
                continue;
            }
            match port.direction {
                yosys::PortDirection::Input => {
                    let value =
                        self.design.add_cell(CellRepr::TopInput(port_name.clone(), port.bits.len() as u32)).output();
                    self.drive(&port.bits, value);
                }
                yosys::PortDirection::Output => {
                    let value = self.value(&port.bits);
                    self.design.add_cell(CellRepr::TopOutput(port_name.clone(), value));
                }
                yosys::PortDirection::Inout => unreachable!(),
            }
        }
        Ok(())
    }

    fn handle_cell(&mut self, cell: &yosys::CellDetails) -> Result<(), Error> {
        match &cell.type_[..] {
            "$not" | "$pos" | "$neg" => {
                let width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a_signed = cell.parameters.get("A_SIGNED").unwrap().as_bool()?;
                let a = self.value_ext(cell, "A", width, a_signed);
                let value = match &cell.type_[..] {
                    "$not" => self.design.add_cell(CellRepr::Not(a)).output(),
                    "$pos" => a,
                    "$neg" => self.design.add_cell(CellRepr::Sub(Value::zero(width), a)).output(),
                    _ => unreachable!(),
                };
                self.port_drive(cell, "Y", value);
            }
            "$reduce_and" | "$reduce_or" | "$reduce_xor" | "$reduce_xnor" | "$reduce_bool" | "$logic_not" => {
                let width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a = self.port_value(cell, "A");
                let mut value = match &cell.type_[..] {
                    "$reduce_and" => self.design.add_cell(CellRepr::Eq(Value::ones(width), a)).output(),
                    "$reduce_or" | "$reduce_bool" => {
                        let val = self.design.add_cell(CellRepr::Eq(Value::zero(width), a)).output();
                        self.design.add_cell(CellRepr::Not(val)).output()
                    }
                    "$reduce_xor" => {
                        let mut val = Value::zero(1);
                        for bit in &a {
                            val = self.design.add_cell(CellRepr::Xor(val, bit.into())).output();
                        }
                        val
                    }
                    "$reduce_xnor" => {
                        let mut val = Value::ones(1);
                        for bit in &a {
                            val = self.design.add_cell(CellRepr::Xor(val, bit.into())).output();
                        }
                        val
                    }
                    "$logic_not" => self.design.add_cell(CellRepr::Eq(Value::zero(width), a)).output(),
                    _ => unreachable!(),
                };
                if width == 0 {
                    value = Value::from_iter([]);
                } else if width > 1 {
                    value = value.zext(width);
                }
                self.port_drive(cell, "Y", value);
            }
            "$and" | "$or" | "$xor" | "$xnor" | "$add" | "$sub" | "$mul" | "$div" | "$mod" | "$divfloor"
            | "$modfloor" => {
                let width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a_signed = cell.parameters.get("A_SIGNED").unwrap().as_bool()?;
                let b_signed = cell.parameters.get("B_SIGNED").unwrap().as_bool()?;
                assert_eq!(a_signed, b_signed);
                let a = self.value_ext(cell, "A", width, a_signed);
                let b = self.value_ext(cell, "B", width, b_signed);
                let value = match &cell.type_[..] {
                    "$and" => self.design.add_cell(CellRepr::And(a, b)).output(),
                    "$or" => self.design.add_cell(CellRepr::Or(a, b)).output(),
                    "$xor" => self.design.add_cell(CellRepr::Xor(a, b)).output(),
                    "$xnor" => {
                        let val = self.design.add_cell(CellRepr::Xor(a, b)).output();
                        self.design.add_cell(CellRepr::Not(val)).output()
                    }
                    "$add" => self.design.add_cell(CellRepr::Add(a, b)).output(),
                    "$sub" => self.design.add_cell(CellRepr::Sub(a, b)).output(),
                    "$mul" => self.design.add_cell(CellRepr::Mul(a, b)).output(),
                    "$div" | "$divfloor" if !a_signed => self.design.add_cell(CellRepr::UDiv(a, b)).output(),
                    "$mod" | "$modfloor" if !a_signed => self.design.add_cell(CellRepr::UMod(a, b)).output(),
                    "$div" => self.design.add_cell(CellRepr::SDivTrunc(a, b)).output(),
                    "$mod" => self.design.add_cell(CellRepr::SModTrunc(a, b)).output(),
                    "$divfloor" => self.design.add_cell(CellRepr::SDivFloor(a, b)).output(),
                    "$modfloor" => self.design.add_cell(CellRepr::SModFloor(a, b)).output(),
                    _ => unreachable!(),
                };
                self.port_drive(cell, "Y", value);
            }
            "$shl" | "$sshl" | "$shr" | "$sshr" | "$shiftx" => {
                todo!()
            }
            "$lt" | "$le" | "$gt" | "$ge" | "$eq" | "$ne" => {
                let y_width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a_width = cell.parameters.get("A_WIDTH").unwrap().as_i32()? as usize;
                let b_width = cell.parameters.get("B_WIDTH").unwrap().as_i32()? as usize;
                let a_signed = cell.parameters.get("A_SIGNED").unwrap().as_bool()?;
                let b_signed = cell.parameters.get("B_SIGNED").unwrap().as_bool()?;
                let width = std::cmp::max(a_width, b_width);
                assert_eq!(a_signed, b_signed);
                let a = self.value_ext(cell, "A", width, a_signed);
                let b = self.value_ext(cell, "B", width, b_signed);
                let (mut value, inv) = match &cell.type_[..] {
                    "$lt" if !a_signed => (self.design.add_cell(CellRepr::ULt(a, b)).output(), false),
                    "$gt" if !a_signed => (self.design.add_cell(CellRepr::ULt(b, a)).output(), false),
                    "$le" if !a_signed => (self.design.add_cell(CellRepr::ULt(b, a)).output(), true),
                    "$ge" if !a_signed => (self.design.add_cell(CellRepr::ULt(a, b)).output(), true),
                    "$lt" if a_signed => (self.design.add_cell(CellRepr::SLt(a, b)).output(), false),
                    "$gt" if a_signed => (self.design.add_cell(CellRepr::SLt(b, a)).output(), false),
                    "$le" if a_signed => (self.design.add_cell(CellRepr::SLt(b, a)).output(), true),
                    "$ge" if a_signed => (self.design.add_cell(CellRepr::SLt(a, b)).output(), true),
                    "$eq" => (self.design.add_cell(CellRepr::Eq(a, b)).output(), false),
                    "$ne" => (self.design.add_cell(CellRepr::Eq(a, b)).output(), true),
                    _ => unreachable!(),
                };
                if inv {
                    value = self.design.add_cell(CellRepr::Not(value)).output();
                }
                if y_width == 0 {
                    value = Value::from_iter([]);
                } else if width > 1 {
                    value = value.zext(width);
                }
                self.port_drive(cell, "Y", value);
            }
            "$logic_and" | "$logic_or" => {
                let y_width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a = self.port_value(cell, "A");
                let a = self.design.add_cell(CellRepr::Eq(Value::zero(a.len()), a)).output();
                let a = self.design.add_cell(CellRepr::Not(a)).output();
                let b = self.port_value(cell, "B");
                let b = self.design.add_cell(CellRepr::Eq(Value::zero(b.len()), b)).output();
                let b = self.design.add_cell(CellRepr::Not(b)).output();
                let mut value = match &cell.type_[..] {
                    "$logic_and" => self.design.add_cell(CellRepr::And(a, b)).output(),
                    "$logic_or" => self.design.add_cell(CellRepr::Or(a, b)).output(),
                    _ => unreachable!(),
                };
                if y_width == 0 {
                    value = Value::from_iter([]);
                } else if y_width > 1 {
                    value = value.zext(y_width);
                }
                self.port_drive(cell, "Y", value);
            }
            "$mux" => {
                let a = self.port_value(cell, "A");
                let b = self.port_value(cell, "B");
                let s = self.port_value(cell, "S");
                assert_eq!(a.len(), b.len());
                assert_eq!(s.len(), 1);
                let y = self.design.add_cell(CellRepr::Mux(s[0], b, a)).output();
                self.port_drive(cell, "Y", y);
            }
            "$bmux" => {
                let mut value = self.port_value(cell, "A");
                let sel = self.port_value(cell, "S");
                for s in sel.into_iter().rev() {
                    assert_eq!(value.len() % 2, 0);
                    let lo = Value::from(&value[..(value.len() / 2)]);
                    let hi = Value::from(&value[(value.len() / 2)..]);
                    value = self.design.add_cell(CellRepr::Mux(s, hi, lo)).output();
                }
                self.port_drive(cell, "Y", value);
            }
            "$pmux" => {
                let mut value = self.port_value(cell, "A");
                let b = self.port_value(cell, "B");
                let sel = self.port_value(cell, "S");
                assert_eq!(b.len(), value.len() * sel.len());
                for (i, s) in sel.into_iter().enumerate() {
                    value = self
                        .design
                        .add_cell(CellRepr::Mux(s, Value::from(&b[(i * value.len())..((i + 1) * value.len())]), value))
                        .output();
                }
                self.port_drive(cell, "Y", value);
            }
            "$tribuf" => {
                let output = self.port_value(cell, "A");
                let enable = self.port_value(cell, "EN");
                assert_eq!(enable.len(), 1);
                let enable = ControlNet::Pos(enable[0]);
                let bits = cell.connections.get("Y").unwrap();
                let io = self.io_value(bits);
                let value = self.design.add_cell(CellRepr::Iob(IoBuffer { output, enable, io })).output();
                for (&bit, net) in bits.iter().zip(value.into_iter()) {
                    let yosys::Bit::Net(ynet) = bit else { unreachable!() };
                    assert!(!self.driven_nets.contains(&ynet));
                    match self.nets.entry(ynet) {
                        hash_map::Entry::Occupied(e) => {
                            let cell = self.design.find_cell(*e.get()).unwrap().0;
                            self.design.replace_cell(cell.index(), CellRepr::Buf(Value::from(net)));
                        }
                        hash_map::Entry::Vacant(e) => {
                            e.insert(net);
                        }
                    }
                    self.driven_nets.insert(ynet);
                }
            }
            "$dff" | "$dffe" | "$adff" | "$adffe" | "$sdff" | "$sdffe" | "$sdffce" => {
                let data = self.port_value(cell, "D");
                let enable = if cell.connections.contains_key("EN") {
                    self.port_control_net(cell, "EN")
                } else {
                    ControlNet::Pos(Net::ONE)
                };
                let (clear, clear_value) = if cell.connections.contains_key("ARST") {
                    (self.port_control_net(cell, "ARST"), cell.parameters.get("ARST_VALUE").unwrap().as_const()?)
                } else {
                    (ControlNet::Pos(Net::ZERO), Const::undef(data.len()))
                };
                let (reset, reset_value) = if cell.connections.contains_key("SRST") {
                    (self.port_control_net(cell, "SRST"), cell.parameters.get("SRST_VALUE").unwrap().as_const()?)
                } else {
                    (ControlNet::Pos(Net::ZERO), Const::undef(data.len()))
                };
                let clock = self.port_control_net(cell, "CLK");
                let init_value = self.init_value(cell, "Q");
                let q = self
                    .design
                    .add_cell(CellRepr::Dff(FlipFlop {
                        data,
                        clock,
                        enable,
                        reset,
                        reset_over_enable: cell.type_ != "$sdffce",
                        clear,
                        init_value,
                        reset_value,
                        clear_value,
                    }))
                    .output();
                self.port_drive(cell, "Q", q);
            }
            _ => {
                if cell.type_.starts_with('$') {
                    panic!("unrecognized cell type {}", cell.type_);
                }
                // instance
                let mut out_bits = vec![];
                let mut next_out = 0;
                let mut inputs = HashMap::new();
                let mut outputs = HashMap::new();
                let mut ios = HashMap::new();
                for (name, bits) in cell.connections.iter() {
                    let direction = *cell.port_directions.get(name).unwrap();
                    if self.design_io_ports.contains(&(&cell.type_, name)) || direction == yosys::PortDirection::Inout {
                        ios.insert(name.clone(), self.io_value(bits));
                    } else if direction == yosys::PortDirection::Output {
                        let range = next_out..(next_out + bits.len());
                        next_out += bits.len();
                        out_bits.push((bits, range.clone()));
                        outputs.insert(name.clone(), range);
                    } else {
                        inputs.insert(name.clone(), self.value(bits));
                    }
                }
                let mut parameters = HashMap::new();
                for (name, val) in cell.parameters.iter() {
                    let val = match val {
                        yosys::MetadataValue::Const(val) => ParamValue::Const(val.clone()),
                        yosys::MetadataValue::String(val) => ParamValue::String(val.clone()),
                    };
                    parameters.insert(name.clone(), val);
                }
                let output = self
                    .design
                    .add_cell(CellRepr::Other(Instance {
                        reference: cell.type_.strip_prefix('\\').unwrap().to_string(),
                        parameters,
                        inputs,
                        outputs,
                        ios,
                    }))
                    .output();
                for (bits, range) in out_bits {
                    self.drive(bits, Value::from(&output[range]));
                }
            }
        }
        Ok(())
    }

    fn handle_undriven_io_nets(&mut self) {
        for (&ynet, &io_net) in &self.io_nets {
            if self.driven_nets.contains(&ynet) {
                continue;
            }
            let Some(&net) = self.nets.get(&ynet) else { continue };
            let index = self.design.find_cell(net).unwrap().0.index();
            self.design.replace_cell(
                index,
                CellRepr::Iob(IoBuffer {
                    output: Value::undef(1),
                    enable: ControlNet::Pos(Net::ZERO),
                    io: IoValue::from(io_net),
                }),
            );
        }
    }
}

fn import_module(module: &yosys::Module, design_io_ports: &HashSet<(&str, &str)>) -> Result<Option<Design>, Error> {
    if let Some(val) = module.attributes.get("blackbox") {
        if val.as_bool()? {
            return Ok(None);
        }
    }

    let mut importer = ModuleImporter {
        module,
        design_io_ports,
        io_nets: HashMap::new(),
        driven_nets: HashSet::new(),
        nets: HashMap::new(),
        init: HashMap::new(),
        design: Design::new(),
    };

    importer.handle_init()?;
    importer.handle_ports()?;
    for cell in module.cells.0.values() {
        importer.handle_cell(cell)?;
    }
    importer.handle_undriven_io_nets();

    Ok(Some(importer.design))
}

fn index_io_ports(design: &yosys::Design) -> Result<HashSet<(&str, &str)>, Error> {
    let mut io_ports: HashSet<(&str, &str)> = HashSet::new();
    io_ports.insert(("$tribuf", "Y"));
    for (mod_name, module) in design.modules.iter() {
        for (port_name, port) in module.ports.iter() {
            if port.direction == yosys::PortDirection::Inout {
                io_ports.insert((mod_name, port_name));
                continue;
            }
            let Some(net_details) = module.netnames.get(port_name) else { continue };
            if let Some(val) = net_details.attributes.get("iopad_external_pin") {
                if val.as_bool()? == true {
                    io_ports.insert((mod_name, port_name));
                }
            }
        }
    }
    Ok(io_ports)
}

pub fn import(reader: &mut impl std::io::Read) -> Result<HashMap<String, Design>, Error> {
    let mut text = String::new();
    reader.read_to_string(&mut text)?;
    let json = json::parse(text.as_str())?;
    let yosys_design = yosys::Design::try_from(json)?;

    let io_ports = index_io_ports(&yosys_design)?;
    let mut designs = HashMap::new();
    for (name, module) in yosys_design.modules.iter() {
        if let Some(design) = import_module(module, &io_ports)? {
            designs.insert(name.clone(), design);
        }
    }
    Ok(designs)
}
