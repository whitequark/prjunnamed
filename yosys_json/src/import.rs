use std::collections::{btree_map, BTreeMap, BTreeSet};

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
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
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
    design_io_ports: &'a BTreeSet<(&'a str, &'a str)>,
    io_nets: BTreeMap<usize, IoNet>,
    driven_nets: BTreeSet<usize>,
    nets: BTreeMap<usize, Net>,
    init: BTreeMap<usize, Trit>,
    design: Design,
}

impl ModuleImporter<'_> {
    fn drive(&mut self, bits: &yosys::BitVector, value: impl Into<Value>) {
        self.design.apply();
        let value = value.into();
        assert_eq!(bits.len(), value.len());
        for (&bit, net) in bits.iter().zip(value.iter()) {
            let yosys::Bit::Net(ynet) = bit else { unreachable!() };
            assert!(!self.driven_nets.contains(&ynet));
            match self.nets.entry(ynet) {
                btree_map::Entry::Occupied(e) => {
                    self.design.find_cell(*e.get()).unwrap().0.replace(CellRepr::Buf(Value::from(net)));
                }
                btree_map::Entry::Vacant(e) => {
                    e.insert(net);
                }
            }
            if let Some(&io_net) = self.io_nets.get(&ynet) {
                self.design.add_iob(IoBuffer {
                    enable: ControlNet::Pos(Net::ONE),
                    output: Value::from(net),
                    io: IoValue::from(io_net),
                });
            }
            self.driven_nets.insert(ynet);
        }
    }

    fn port_drive(&mut self, cell: &yosys::CellDetails, port: &str, value: impl Into<Value>) {
        self.drive(cell.connections.get(port).unwrap(), value);
    }

    fn value(&mut self, bits: &yosys::BitVector) -> Value {
        let mut nets = vec![];
        for &bit in bits.iter() {
            let net = match bit {
                yosys::Bit::HiZ | yosys::Bit::Undef => Net::UNDEF,
                yosys::Bit::Zero => Net::ZERO,
                yosys::Bit::One => Net::ONE,
                yosys::Bit::Net(ynet) => {
                    *self.nets.entry(ynet).or_insert_with(|| self.design.add_buf(Value::undef(1)).unwrap_net())
                }
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
        let net = self.port_value(cell, port).unwrap_net();
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
            for (&bit, binit) in net_details.bits.iter().zip(init.iter()) {
                if binit == Trit::Undef {
                    continue;
                }
                let yosys::Bit::Net(ynet) = bit else { Err(yosys::MetadataTypeError)? };
                match self.init.entry(ynet) {
                    btree_map::Entry::Occupied(e) => {
                        assert_eq!(*e.get(), binit);
                    }
                    btree_map::Entry::Vacant(e) => {
                        e.insert(binit);
                    }
                }
            }
        }
        Ok(())
    }

    fn handle_ports(&mut self) -> Result<(), Error> {
        // determine set of nets that need to be IOs from cell port connections.
        let mut io_net_conns = BTreeSet::new();
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
        let mut io_ports = BTreeSet::new();
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
                        btree_map::Entry::Occupied(_) => {
                            return Err(Error::Semantic);
                        }
                        btree_map::Entry::Vacant(e) => {
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
                    let value = self.design.add_input(port_name, port.bits.len());
                    self.drive(&port.bits, value);
                }
                yosys::PortDirection::Output => {
                    let value = self.value(&port.bits);
                    self.design.add_output(port_name, value);
                }
                yosys::PortDirection::Inout => unreachable!(),
            }
        }
        Ok(())
    }

    fn handle_names(&mut self) -> Result<(), Error> {
        for (name, details) in self.module.netnames.iter() {
            if details.hide_name {
                continue;
            }
            let value = self.value(&details.bits);
            self.design.add_name(name, value);
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
                    "$not" => self.design.add_not(a),
                    "$pos" => a,
                    "$neg" => {
                        let value = self.design.add_not(a);
                        self.design.add_adc(value, Value::zero(width), Net::ONE)[..width].into()
                    }
                    _ => unreachable!(),
                };
                self.port_drive(cell, "Y", value);
            }
            "$reduce_and" | "$reduce_or" | "$reduce_xor" | "$reduce_xnor" | "$reduce_bool" | "$logic_not" => {
                let width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a = self.port_value(cell, "A");
                let mut value = match &cell.type_[..] {
                    "$reduce_and" => self.design.add_eq(Value::ones(a.len()), a),
                    "$reduce_or" | "$reduce_bool" => self.design.add_ne(Value::zero(a.len()), a),
                    "$reduce_xor" => {
                        let mut val = Value::zero(1);
                        for bit in &a {
                            val = self.design.add_xor(val, bit);
                        }
                        val
                    }
                    "$reduce_xnor" => {
                        let mut val = Value::ones(1);
                        for bit in &a {
                            val = self.design.add_xor(val, bit);
                        }
                        val
                    }
                    "$logic_not" => self.design.add_eq(Value::zero(a.len()), a),
                    _ => unreachable!(),
                };
                if width == 0 {
                    value = Value::EMPTY;
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
                    "$and" => self.design.add_and(a, b),
                    "$or" => self.design.add_or(a, b),
                    "$xor" => self.design.add_xor(a, b),
                    "$xnor" => {
                        let val = self.design.add_xor(a, b);
                        self.design.add_not(val)
                    }
                    "$add" => self.design.add_adc(a, b, Net::ZERO)[..width].into(),
                    "$sub" => {
                        let inv_b = self.design.add_not(b);
                        self.design.add_adc(a, inv_b, Net::ONE)[..width].into()
                    }
                    "$mul" => self.design.add_mul(a, b),
                    "$div" | "$divfloor" if !a_signed => self.design.add_udiv(a, b),
                    "$mod" | "$modfloor" if !a_signed => self.design.add_umod(a, b),
                    "$div" => self.design.add_sdiv_trunc(a, b),
                    "$mod" => self.design.add_smod_trunc(a, b),
                    "$divfloor" => self.design.add_sdiv_floor(a, b),
                    "$modfloor" => self.design.add_smod_floor(a, b),
                    _ => unreachable!(),
                };
                self.port_drive(cell, "Y", value);
            }
            "$alu" => {
                let width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let bi = self.port_value(cell, "BI").unwrap_net();
                let ci = self.port_value(cell, "CI").unwrap_net();
                let a_signed = cell.parameters.get("A_SIGNED").unwrap().as_bool()?;
                let b_signed = cell.parameters.get("B_SIGNED").unwrap().as_bool()?;
                let a = self.value_ext(cell, "A", width, a_signed);
                let b = self.value_ext(cell, "B", width, b_signed);
                let b_inv = self.design.add_not(&b);
                let b = self.design.add_mux(bi, b_inv, &b);
                let x = self.design.add_xor(&a, &b);
                self.port_drive(cell, "X", x);
                let y = self.design.add_adc(&a, &b, ci);
                self.port_drive(cell, "Y", &y[..width]);
                let xor = self.design.add_xor(&a[1..], &b[1..]);
                let co = self.design.add_xor(xor, &y[1..]).concat(y[width]);
                self.port_drive(cell, "CO", co);
            }
            "$shl" | "$sshl" | "$shr" | "$sshr" | "$shift" | "$shiftx" => {
                let width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a_signed = cell.parameters.get("A_SIGNED").unwrap().as_bool()?;
                let b_signed = cell.parameters.get("B_SIGNED").unwrap().as_bool()?;
                let mut a = self.port_value(cell, "A");
                if a.len() < width {
                    if cell.type_ == "$shiftx" {
                        let a_width = a.len();
                        a = a.concat(Value::undef(width - a_width))
                    } else {
                        if a_signed {
                            a = a.sext(width);
                        } else {
                            a = a.zext(width);
                        }
                    }
                }
                let b = self.port_value(cell, "B");
                let value = match &cell.type_[..] {
                    "$shl" | "$sshl" => self.design.add_shl(a, b, 1),
                    "$shr" => self.design.add_ushr(a, b, 1),
                    "$sshr" => {
                        if a_signed {
                            self.design.add_sshr(a, b, 1)
                        } else {
                            self.design.add_ushr(a, b, 1)
                        }
                    }
                    "$shift" | "$shiftx" => {
                        let val_shr = if cell.type_ == "$shiftx" {
                            self.design.add_xshr(&a, &b, 1)
                        } else if a_signed {
                            self.design.add_sshr(&a, &b, 1)
                        } else {
                            self.design.add_ushr(&a, &b, 1)
                        };
                        if b_signed {
                            let b_inv = self.design.add_not(&b);
                            let b_neg =
                                Value::from(&self.design.add_adc(Value::zero(b.len()), &b_inv, Net::ONE)[..b.len()]);
                            let val_shl = self.design.add_shl(&a, b_neg, 1);
                            self.design.add_mux(b[b.len() - 1], val_shl, val_shr)
                        } else {
                            val_shr
                        }
                    }
                    _ => unreachable!(),
                };
                self.port_drive(cell, "Y", &value[..width]);
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
                    "$lt" if !a_signed => (self.design.add_ult(a, b), false),
                    "$gt" if !a_signed => (self.design.add_ult(b, a), false),
                    "$le" if !a_signed => (self.design.add_ult(b, a), true),
                    "$ge" if !a_signed => (self.design.add_ult(a, b), true),
                    "$lt" if a_signed => (self.design.add_slt(a, b), false),
                    "$gt" if a_signed => (self.design.add_slt(b, a), false),
                    "$le" if a_signed => (self.design.add_slt(b, a), true),
                    "$ge" if a_signed => (self.design.add_slt(a, b), true),
                    "$eq" => (self.design.add_eq(a, b), false),
                    "$ne" => (self.design.add_eq(a, b), true),
                    _ => unreachable!(),
                };
                if inv {
                    value = self.design.add_not(value);
                }
                if y_width == 0 {
                    value = Value::EMPTY;
                } else if y_width > 1 {
                    value = value.zext(width);
                }
                self.port_drive(cell, "Y", value);
            }
            "$logic_and" | "$logic_or" => {
                let y_width = cell.parameters.get("Y_WIDTH").unwrap().as_i32()? as usize;
                let a = self.port_value(cell, "A");
                let a = self.design.add_eq(Value::zero(a.len()), a);
                let a = self.design.add_not(a);
                let b = self.port_value(cell, "B");
                let b = self.design.add_eq(Value::zero(b.len()), b);
                let b = self.design.add_not(b);
                let mut value = match &cell.type_[..] {
                    "$logic_and" => self.design.add_and(a, b),
                    "$logic_or" => self.design.add_or(a, b),
                    _ => unreachable!(),
                };
                if y_width == 0 {
                    value = Value::EMPTY;
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
                let y = self.design.add_mux(s.unwrap_net(), b, a);
                self.port_drive(cell, "Y", y);
            }
            "$bmux" => {
                let mut value = self.port_value(cell, "A");
                let sel = self.port_value(cell, "S");
                for s in sel.iter().rev() {
                    assert_eq!(value.len() % 2, 0);
                    let lo = Value::from(&value[..(value.len() / 2)]);
                    let hi = Value::from(&value[(value.len() / 2)..]);
                    value = self.design.add_mux(s, hi, lo);
                }
                self.port_drive(cell, "Y", value);
            }
            "$pmux" => {
                let mut value = self.port_value(cell, "A");
                let b = self.port_value(cell, "B");
                let sel = self.port_value(cell, "S");
                assert_eq!(b.len(), value.len() * sel.len());
                for (i, s) in sel.iter().enumerate() {
                    value = self.design.add_mux(s, &b[(i * value.len())..((i + 1) * value.len())], value);
                }
                self.port_drive(cell, "Y", value);
            }
            "$tribuf" => {
                let output = self.port_value(cell, "A");
                let enable = self.port_value(cell, "EN");
                let enable = ControlNet::Pos(enable.unwrap_net());
                let bits = cell.connections.get("Y").unwrap();
                let io = self.io_value(bits);
                let value = self.design.add_iob(IoBuffer { output, enable, io });
                self.design.apply();
                for (&bit, net) in bits.iter().zip(value.iter()) {
                    let yosys::Bit::Net(ynet) = bit else { unreachable!() };
                    assert!(!self.driven_nets.contains(&ynet));
                    match self.nets.entry(ynet) {
                        btree_map::Entry::Occupied(e) => {
                            self.design.find_cell(*e.get()).unwrap().0.replace(CellRepr::Buf(Value::from(net)));
                        }
                        btree_map::Entry::Vacant(e) => {
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
                let q = self.design.add_dff(FlipFlop {
                    data,
                    clock,
                    enable,
                    reset,
                    reset_over_enable: cell.type_ != "$sdffce",
                    clear,
                    init_value,
                    reset_value,
                    clear_value,
                });
                self.port_drive(cell, "Q", q);
            }
            _ => {
                if cell.type_.starts_with('$') {
                    panic!("unrecognized cell type {}", cell.type_);
                }
                // instance
                let mut out_bits = vec![];
                let mut next_out = 0;
                let mut inputs = BTreeMap::new();
                let mut outputs = BTreeMap::new();
                let mut ios = BTreeMap::new();
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
                let mut parameters = BTreeMap::new();
                for (name, val) in cell.parameters.iter() {
                    let val = match val {
                        yosys::MetadataValue::Const(val) => ParamValue::Const(val.clone()),
                        yosys::MetadataValue::String(val) => ParamValue::String(val.clone()),
                    };
                    parameters.insert(name.clone(), val);
                }
                let output = self.design.add_other(Instance {
                    kind: cell.type_.strip_prefix('\\').unwrap_or(cell.type_.as_str()).to_string(),
                    params: parameters,
                    inputs,
                    outputs,
                    ios,
                });
                for (bits, range) in out_bits {
                    self.drive(bits, &output[range]);
                }
            }
        }
        Ok(())
    }

    fn handle_undriven_io_nets(&mut self) {
        self.design.apply();
        for (&ynet, &io_net) in &self.io_nets {
            if self.driven_nets.contains(&ynet) {
                continue;
            }
            let Some(&net) = self.nets.get(&ynet) else { continue };
            self.design.find_cell(net).unwrap().0.replace(CellRepr::Iob(IoBuffer {
                output: Value::undef(1),
                enable: ControlNet::Pos(Net::ZERO),
                io: io_net.into(),
            }));
        }
    }

    fn finalize(&mut self) {
        self.design.replace_bufs();
        self.design.compact();
    }
}

fn import_module(module: &yosys::Module, design_io_ports: &BTreeSet<(&str, &str)>) -> Result<Option<Design>, Error> {
    if let Some(val) = module.attributes.get("blackbox") {
        if val.as_bool()? {
            return Ok(None);
        }
    }

    let mut importer = ModuleImporter {
        module,
        design_io_ports,
        io_nets: BTreeMap::new(),
        driven_nets: BTreeSet::new(),
        nets: BTreeMap::new(),
        init: BTreeMap::new(),
        design: Design::new(),
    };

    importer.handle_init()?;
    importer.handle_ports()?;
    importer.handle_names()?;
    for cell in module.cells.0.values() {
        importer.handle_cell(cell)?;
    }
    importer.handle_undriven_io_nets();
    importer.finalize();

    Ok(Some(importer.design))
}

fn index_io_ports(design: &yosys::Design) -> Result<BTreeSet<(&str, &str)>, Error> {
    let mut io_ports: BTreeSet<(&str, &str)> = BTreeSet::new();
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

pub fn import(reader: &mut impl std::io::Read) -> Result<BTreeMap<String, Design>, Error> {
    let mut text = String::new();
    reader.read_to_string(&mut text)?;
    let json = json::parse(text.as_str())?;
    let yosys_design = yosys::Design::try_from(json)?;

    let io_ports = index_io_ports(&yosys_design)?;
    let mut designs = BTreeMap::new();
    for (name, module) in yosys_design.modules.iter() {
        if let Some(design) = import_module(module, &io_ports)? {
            designs.insert(name.clone(), design);
        }
    }
    Ok(designs)
}
