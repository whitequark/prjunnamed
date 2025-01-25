use std::ops::Range;
use std::cell::RefCell;
use std::borrow::Cow;
use std::collections::{btree_map, BTreeMap, BTreeSet};
use std::fmt::Display;

use crate::cell::{Cell, CellRepr};
use crate::{ControlNet, FlipFlop, Instance, IoBuffer, IoNet, IoValue, Net, Trit, Value};

#[derive(Debug)]
pub struct Design {
    ios: BTreeMap<String, Range<u32>>,
    cells: Vec<Cell>,
    changes: RefCell<ChangeQueue>,
}

#[derive(Debug)]
struct ChangeQueue {
    next_io: u32,
    added_ios: BTreeMap<String, Range<u32>>,
    added_cells: Vec<Cell>,
    replaced_cells: BTreeMap<usize, CellRepr>,
    replaced_nets: BTreeMap<Net, Net>,
}

impl Design {
    pub fn new() -> Design {
        Design {
            ios: BTreeMap::new(),
            cells: vec![],
            changes: RefCell::new(ChangeQueue {
                next_io: 0,
                added_ios: BTreeMap::new(),
                added_cells: vec![],
                replaced_cells: BTreeMap::new(),
                replaced_nets: BTreeMap::new(),
            }),
        }
    }

    pub fn add_io(&self, name: impl Into<String>, width: usize) -> IoValue {
        let mut changes = self.changes.borrow_mut();
        let name = name.into();
        let width = width as u32;
        let range = changes.next_io..(changes.next_io + width);
        changes.next_io += width;
        if self.ios.contains_key(&name) {
            panic!("duplicate IO port {name}");
        }
        match changes.added_ios.entry(name) {
            btree_map::Entry::Occupied(entry) => {
                panic!("duplicate IO port {}", entry.key());
            }
            btree_map::Entry::Vacant(entry) => {
                entry.insert(range.clone());
            }
        }
        IoValue::from_range(range)
    }

    pub fn find_io(&self, io_net: IoNet) -> Option<(&str, usize)> {
        for (name, range) in self.ios.iter() {
            if range.contains(&io_net.0) {
                return Some((name.as_str(), (io_net.0 - range.start) as usize));
            }
        }
        None
    }
    pub fn add_cell(&self, cell: CellRepr) -> Value {
        cell.validate();
        let mut changes = self.changes.borrow_mut();
        let index = self.cells.len() + changes.added_cells.len();
        let output_len = cell.output_len();
        changes.added_cells.push(cell.into());
        if output_len > 1 {
            for _ in 0..(output_len - 1) {
                changes.added_cells.push(Cell::Skip(index.try_into().expect("cell index too large")))
            }
        }
        Value::cell(index, output_len)
    }

    fn locate_cell(&self, net: Net) -> Result<(usize, usize), Trit> {
        if let Some(trit) = net.as_const() {
            return Err(trit);
        }
        let index = net.as_cell().unwrap();
        let (cell_index, bit_index) = match self.cells[index] {
            Cell::Skip(start) => (start as usize, index - start as usize),
            _ => (index, 0),
        };
        Ok((cell_index, bit_index))
    }

    pub fn find_cell(&self, net: Net) -> Result<(CellRef, usize), Trit> {
        self.locate_cell(net).map(|(cell_index, bit_index)| (CellRef { design: self, index: cell_index }, bit_index))
    }

    pub fn iter_cells(&self) -> CellIter {
        CellIter { design: self, index: 0 }
    }

    pub fn replace_net(&self, from_net: impl Into<Net>, to_net: impl Into<Net>) {
        let (from_net, to_net) = (from_net.into(), to_net.into());
        if from_net != to_net {
            let mut changes = self.changes.borrow_mut();
            assert_eq!(changes.replaced_nets.insert(from_net, to_net), None);
        }
    }

    pub fn replace_value<'a, 'b>(&self, from_value: impl Into<Cow<'a, Value>>, to_value: impl Into<Cow<'b, Value>>) {
        let (from_value, to_value) = (from_value.into(), to_value.into());
        assert_eq!(from_value.len(), to_value.len());
        for (from_net, to_net) in from_value.into_iter().zip(to_value.into_iter()) {
            self.replace_net(from_net, to_net);
        }
    }

    pub fn map_net(&self, net: impl Into<Net>) -> Net {
        let changes = self.changes.borrow();
        let net = net.into();
        let mapped_net = *changes.replaced_nets.get(&net).unwrap_or(&net);
        // Assume the caller might want to locate the cell behind the net.
        match mapped_net.as_cell() {
            Some(index) if index >= self.cells.len() => return net,
            _ => return mapped_net
        }
    }

    pub fn map_value(&self, value: impl Into<Value>) -> Value {
        value.into().into_iter().map(|net| self.map_net(net)).collect::<Vec<_>>().into()
    }

    pub fn apply(&mut self) -> bool {
        let changes = self.changes.get_mut();
        let mut did_change = !changes.added_ios.is_empty() || !changes.added_cells.is_empty();
        for (index, new_cell) in std::mem::take(&mut changes.replaced_cells) {
            assert_eq!(self.cells[index].output_len(), new_cell.output_len());
            if *self.cells[index].repr() != new_cell {
                self.cells[index] = new_cell.into();
                did_change = true;
            }
        }
        self.ios.extend(std::mem::take(&mut changes.added_ios));
        self.cells.extend(std::mem::take(&mut changes.added_cells));
        if !changes.replaced_nets.is_empty() {
            for cell in self.cells.iter_mut().filter(|cell| !matches!(cell, Cell::Skip(_))) {
                cell.visit_mut(|net| {
                    while let Some(new_net) = changes.replaced_nets.get(net) {
                        if *net != *new_net {
                            *net = *new_net;
                            did_change = true;
                        }
                    }
                });
            }
            changes.replaced_nets.clear();
        }
        did_change
    }
}

#[derive(Clone, Copy)]
pub struct CellRef<'a> {
    design: &'a Design,
    index: usize,
}

impl PartialEq<CellRef<'_>> for CellRef<'_> {
    fn eq(&self, other: &CellRef<'_>) -> bool {
        std::ptr::eq(self.design, other.design) && self.index == other.index
    }
}

impl Eq for CellRef<'_> {}

impl<'a> CellRef<'a> {
    pub fn repr(&self) -> Cow<'a, CellRepr> {
        self.design.cells[self.index].repr()
    }

    pub fn output_len(&self) -> usize {
        self.design.cells[self.index].output_len()
    }

    pub fn output(&self) -> Value {
        Value::cell(self.index, self.output_len())
    }

    pub fn visit(&self, f: impl FnMut(Net)) {
        self.design.cells[self.index].visit(f)
    }

    pub fn replace(&self, to_cell: CellRepr) {
        to_cell.validate();
        let mut changes = self.design.changes.borrow_mut();
        assert!(changes.replaced_cells.insert(self.index, to_cell).is_none());
    }

    pub fn unalive(&self) {
        self.replace(CellRepr::Buf(Value::undef(self.output_len())));
    }

    // Returns the same index as the one used by `Display` implementation.`
    pub fn debug_index(&self) -> usize {
        self.index
    }
}

pub struct CellIter<'a> {
    design: &'a Design,
    index: usize,
}

impl<'a> Iterator for CellIter<'a> {
    type Item = CellRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.design.cells.len() {
            let cell_ref = CellRef { design: self.design, index: self.index };
            self.index += self.design.cells[self.index].output_len().max(1);
            Some(cell_ref)
        } else {
            None
        }
    }
}

macro_rules! builder_fn {
    () => {};

    ($func:ident( $($arg:ident : $ty:ty),+ ) -> $repr:ident $body:tt; $($rest:tt)*) => {
        pub fn $func(&self, $( $arg: $ty ),+) -> Value {
            self.add_cell(CellRepr::$repr $body)
        }

        builder_fn!{ $($rest)* }
    };

    // For cells with no output value.
    ($func:ident( $($arg:ident : $ty:ty),+ ) : $repr:ident $body:tt; $($rest:tt)*) => {
        pub fn $func(&self, $( $arg: $ty ),+) {
            self.add_cell(CellRepr::$repr $body);
        }

        builder_fn!{ $($rest)* }
    };
}

impl Design {
    builder_fn! {
        add_buf(arg: impl Into<Value>) ->
            Buf(arg.into());
        add_not(arg: impl Into<Value>) ->
            Not(arg.into());
        add_and(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            And(arg1.into(), arg2.into());
        add_or(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            Or(arg1.into(), arg2.into());
        add_xor(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            Xor(arg1.into(), arg2.into());
        add_mux(arg1: impl Into<Net>, arg2: impl Into<Value>, arg3: impl Into<Value>) ->
            Mux(arg1.into(), arg2.into(), arg3.into());
        add_adc(arg1: impl Into<Value>, arg2: impl Into<Value>, arg3: impl Into<Net>) ->
            Adc(arg1.into(), arg2.into(), arg3.into());

        add_eq(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            Eq(arg1.into(), arg2.into());
        add_ult(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            ULt(arg1.into(), arg2.into());
        add_slt(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            SLt(arg1.into(), arg2.into());

        add_shl(arg1: impl Into<Value>, arg2: impl Into<Value>, stride: u32) ->
            Shl(arg1.into(), arg2.into(), stride);
        add_ushr(arg1: impl Into<Value>, arg2: impl Into<Value>, stride: u32) ->
            UShr(arg1.into(), arg2.into(), stride);
        add_sshr(arg1: impl Into<Value>, arg2: impl Into<Value>, stride: u32) ->
            SShr(arg1.into(), arg2.into(), stride);
        add_xshr(arg1: impl Into<Value>, arg2: impl Into<Value>, stride: u32) ->
            XShr(arg1.into(), arg2.into(), stride);

        add_mul(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            Mul(arg1.into(), arg2.into());
        add_udiv(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            UDiv(arg1.into(), arg2.into());
        add_umod(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            UMod(arg1.into(), arg2.into());
        add_sdiv_trunc(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            SDivTrunc(arg1.into(), arg2.into());
        add_sdiv_floor(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            SDivFloor(arg1.into(), arg2.into());
        add_smod_trunc(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            SModTrunc(arg1.into(), arg2.into());
        add_smod_floor(arg1: impl Into<Value>, arg2: impl Into<Value>) ->
            SModFloor(arg1.into(), arg2.into());

        add_dff(arg: impl Into<FlipFlop>) ->
            Dff(arg.into());
        add_iob(arg: impl Into<IoBuffer>) ->
            Iob(arg.into());
        add_other(arg: impl Into<Instance>) ->
            Other(arg.into());

        add_input(name: impl Into<String>, width: usize) ->
            Input(name.into(), width);
        add_output(name: impl Into<String>, value: impl Into<Value>) :
            Output(name.into(), value.into());
        add_name(name: impl Into<String>, value: impl Into<Value>) :
            Name(name.into(), value.into());
    }

    pub fn add_ne(&mut self, arg1: impl Into<Value>, arg2: impl Into<Value>) -> Value {
        let eq = self.add_eq(arg1, arg2);
        self.add_not(eq)
    }
}

impl Design {
    pub fn iter_cells_topo<'a>(&'a self) -> impl Iterator<Item = CellRef<'a>> {
        let mut outgoing = BTreeMap::<usize, BTreeSet<usize>>::new();
        let mut incoming = BTreeMap::<usize, BTreeSet<usize>>::new();
        let mut queue = BTreeSet::new();
        for (index, cell) in self.cells.iter().enumerate() {
            if let Cell::Skip(_) = cell {
                continue;
            }
            cell.visit(|net| {
                if let Ok((cell_ref, _offset)) = self.find_cell(net) {
                    incoming.entry(index).or_default().insert(cell_ref.index);
                    outgoing.entry(cell_ref.index).or_default().insert(index);
                }
            });
            match &*cell.repr() {
                CellRepr::Dff(_) | CellRepr::Iob(_) | CellRepr::Other(_) | CellRepr::Input(_, _) => {
                    queue.insert(index);
                }
                _ => (),
            }
        }

        let mut order = vec![];
        while let Some(from_index) = queue.pop_first() {
            order.push(from_index);
            for to_index in std::mem::take(outgoing.entry(from_index).or_default()) {
                let incoming = incoming.entry(to_index).or_default();
                incoming.remove(&from_index);
                if incoming.is_empty() {
                    queue.insert(to_index);
                }
            }
        }

        order.into_iter().map(|index| CellRef { design: self, index })
    }

    pub fn compact(&mut self) {
        self.apply();

        let mut queue = BTreeSet::new();
        for (index, cell) in self.cells.iter().enumerate() {
            if let Cell::Skip(_) = cell {
                continue;
            }
            match &*cell.repr() {
                CellRepr::Dff(_)
                | CellRepr::Iob(_)
                | CellRepr::Other(_)
                | CellRepr::Input(_, _)
                | CellRepr::Output(_, _)
                | CellRepr::Name(_, _) => {
                    queue.insert(index);
                }
                _ => (),
            }
        }

        let mut keep = BTreeSet::new();
        while let Some(index) = queue.pop_first() {
            keep.insert(index);
            let cell = &self.cells[index];
            cell.visit(|net| {
                if let Ok((cell_ref, _offset)) = self.find_cell(net) {
                    if !keep.contains(&cell_ref.index) {
                        queue.insert(cell_ref.index);
                    }
                }
            });
        }

        let mut net_map = BTreeMap::new();
        for (old_index, cell) in std::mem::take(&mut self.cells).into_iter().enumerate() {
            if keep.contains(&old_index) {
                let new_index = self.cells.len();
                for offset in 0..cell.output_len() {
                    net_map.insert(Net::from_cell(old_index + offset), Net::from_cell(new_index + offset));
                }
                let skip_count = cell.output_len().checked_sub(1).unwrap_or(0);
                self.cells.push(cell);
                for _ in 0..skip_count {
                    self.cells.push(Cell::Skip(new_index as u32));
                }
            }
        }

        for cell in self.cells.iter_mut().filter(|cell| !matches!(cell, Cell::Skip(_))) {
            cell.visit_mut(|net| {
                if ![Net::UNDEF, Net::ZERO, Net::ONE].contains(net) {
                    *net = net_map[net];
                }
            });
        }
    }
}

impl Display for Design {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let write_net = |f: &mut std::fmt::Formatter, net: Net| -> std::fmt::Result {
            match self.find_cell(net) {
                Ok((cell_ref, offset)) => {
                    if cell_ref.output().len() == 1 {
                        write!(f, "%{}", cell_ref.index)
                    } else {
                        write!(f, "%{}+{}", cell_ref.index, offset)
                    }
                }
                Err(trit) => write!(f, "{}", trit),
            }
        };

        let write_value = |f: &mut std::fmt::Formatter, value: &Value| -> std::fmt::Result {
            if value.len() == 0 {
                return write!(f, "{{}}");
            }
            if let Ok((cell_ref, _offset)) = self.find_cell(value[0]) {
                if *value == cell_ref.output() {
                    return write!(f, "%{}", cell_ref.index);
                }
            }
            if let Some(value) = value.as_const() {
                return write!(f, "{}", value);
            }
            if value.len() == 1 {
                return write_net(f, value[0]);
            }
            write!(f, "{{")?;
            for net in value {
                write!(f, " ")?;
                write_net(f, net)?;
            }
            write!(f, " }}")?;
            Ok(())
        };

        let write_control = |f: &mut std::fmt::Formatter, name: &str, control_net: &ControlNet| -> std::fmt::Result {
            if control_net.is_positive() {
                write!(f, "{}=", name)?;
            } else {
                write!(f, "!{}=", name)?;
            }
            write_net(f, control_net.net())
        };

        let write_cell = |f: &mut std::fmt::Formatter, name: &str, args: &[&Value]| -> std::fmt::Result {
            write!(f, "{}", name)?;
            for arg in args {
                write!(f, " ")?;
                write_value(f, arg)?;
            }
            Ok(())
        };

        let write_io_net = |f: &mut std::fmt::Formatter, io_net: IoNet| -> std::fmt::Result {
            write!(f, "#")?;
            match self.find_io(io_net) {
                Some((name, offset)) => {
                    if self.ios[name].len() == 1 {
                        write!(f, "{:?}", name)
                    } else {
                        write!(f, "{:?}+{}", name, offset)
                    }
                }
                None => write!(f, "<invalid>"),
            }
        };

        let write_io_value = |f: &mut std::fmt::Formatter, io_value: &IoValue| -> std::fmt::Result {
            if io_value.len() == 1 {
                write_io_net(f, io_value[0])
            } else {
                write!(f, "{{")?;
                for io_net in io_value {
                    write!(f, " ")?;
                    write_io_net(f, io_net)?;
                }
                write!(f, " }}")?;
                Ok(())
            }
        };

        let write_shift =
            |f: &mut std::fmt::Formatter, name: &str, arg1: &Value, arg2: &Value, stride: u32| -> std::fmt::Result {
                write!(f, "{} ", name)?;
                write_value(f, arg1)?;
                write!(f, " ")?;
                write_value(f, arg2)?;
                write!(f, " {stride}")?;
                Ok(())
            };

        for (name, range) in self.ios.iter() {
            write!(f, "#{:?}:{}\n", name, range.len())?;
        }

        for cell_ref in self.iter_cells() {
            write!(f, "%{}:{} = ", cell_ref.index, cell_ref.output_len())?;
            match &*cell_ref.repr() {
                CellRepr::Buf(arg) => write_cell(f, "buf", &[arg])?,
                CellRepr::Not(arg) => write_cell(f, "not", &[arg])?,
                CellRepr::And(arg1, arg2) => write_cell(f, "and", &[arg1, arg2])?,
                CellRepr::Or(arg1, arg2) => write_cell(f, "or", &[arg1, arg2])?,
                CellRepr::Xor(arg1, arg2) => write_cell(f, "xor", &[arg1, arg2])?,
                CellRepr::Mux(arg1, arg2, arg3) => {
                    write!(f, "mux ")?;
                    write_net(f, *arg1)?;
                    write!(f, " ")?;
                    write_value(f, arg2)?;
                    write!(f, " ")?;
                    write_value(f, arg3)?;
                }
                CellRepr::Adc(arg1, arg2, arg3) => {
                    write!(f, "adc ")?;
                    write_value(f, arg1)?;
                    write!(f, " ")?;
                    write_value(f, arg2)?;
                    write!(f, " ")?;
                    write_net(f, *arg3)?;
                }

                CellRepr::Eq(arg1, arg2) => write_cell(f, "eq", &[arg1, arg2])?,
                CellRepr::ULt(arg1, arg2) => write_cell(f, "ult", &[arg1, arg2])?,
                CellRepr::SLt(arg1, arg2) => write_cell(f, "slt", &[arg1, arg2])?,

                CellRepr::Shl(arg1, arg2, stride) => write_shift(f, "shl", arg1, arg2, *stride)?,
                CellRepr::UShr(arg1, arg2, stride) => write_shift(f, "ushr", arg1, arg2, *stride)?,
                CellRepr::SShr(arg1, arg2, stride) => write_shift(f, "sshr", arg1, arg2, *stride)?,
                CellRepr::XShr(arg1, arg2, stride) => write_shift(f, "xshr", arg1, arg2, *stride)?,

                CellRepr::Mul(arg1, arg2) => write_cell(f, "mul", &[arg1, arg2])?,
                CellRepr::UDiv(arg1, arg2) => write_cell(f, "udiv", &[arg1, arg2])?,
                CellRepr::UMod(arg1, arg2) => write_cell(f, "umod", &[arg1, arg2])?,
                CellRepr::SDivTrunc(arg1, arg2) => write_cell(f, "sdiv_trunc", &[arg1, arg2])?,
                CellRepr::SDivFloor(arg1, arg2) => write_cell(f, "sdiv_floor", &[arg1, arg2])?,
                CellRepr::SModTrunc(arg1, arg2) => write_cell(f, "smod_trunc", &[arg1, arg2])?,
                CellRepr::SModFloor(arg1, arg2) => write_cell(f, "smod_floor", &[arg1, arg2])?,

                CellRepr::Dff(flip_flop) => {
                    write_cell(f, "dff", &[&flip_flop.data])?;
                    write_control(f, " clk", &flip_flop.clock)?;
                    if flip_flop.has_clear() {
                        write_control(f, " clr", &flip_flop.clear)?;
                        if flip_flop.clear_value != flip_flop.init_value {
                            write!(f, ",{}", flip_flop.clear_value)?;
                        }
                    }
                    if flip_flop.has_reset() {
                        write_control(f, " rst", &flip_flop.reset)?;
                        if flip_flop.reset_value != flip_flop.init_value {
                            write!(f, ",{}", flip_flop.reset_value)?;
                        }
                    }
                    if flip_flop.has_enable() {
                        write_control(f, " en", &flip_flop.enable)?;
                    }
                    if flip_flop.has_reset() && flip_flop.has_enable() {
                        if flip_flop.reset_over_enable {
                            write!(f, " rst>en")?;
                        } else {
                            write!(f, " en>rst")?;
                        }
                    }
                    if flip_flop.has_init_value() {
                        write!(f, " init={}", flip_flop.init_value)?;
                    }
                }
                CellRepr::Iob(io_buffer) => {
                    write_cell(f, "iob", &[&io_buffer.output])?;
                    write_control(f, " en", &io_buffer.enable)?;
                    write!(f, " io=")?;
                    write_io_value(f, &io_buffer.io)?;
                }
                CellRepr::Other(instance) => {
                    write!(f, "{:?} {{\n", instance.reference)?;
                    for (name, value) in instance.parameters.iter() {
                        write!(f, "  p@{:?}={:?}", name, value)?;
                    }
                    for (name, value) in instance.inputs.iter() {
                        write!(f, "  i@{:?}={:?}", name, value)?;
                    }
                    for (name, value) in instance.outputs.iter() {
                        write!(f, "  o@{:?}={:?}", name, value)?;
                    }
                    for (name, value) in instance.ios.iter() {
                        write!(f, "  io@{:?}=", name)?;
                        write_io_value(f, value)?;
                    }
                    write!(f, "}}")?;
                }

                CellRepr::Input(name, _size) => write!(f, "input {:?}", name)?,
                CellRepr::Output(name, value) => {
                    write!(f, "output {:?} ", name)?;
                    write_value(f, value)?;
                }
                CellRepr::Name(name, value) => {
                    write!(f, "name {:?} ", name)?;
                    write_value(f, value)?;
                }
            }

            write!(f, "\n")?;
        }

        write!(f, "\n")
    }
}
