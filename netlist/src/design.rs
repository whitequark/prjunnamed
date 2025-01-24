use std::borrow::Cow;
use std::collections::{btree_map, BTreeMap, BTreeSet};
use std::fmt::Display;
use std::ops::Range;

use crate::cell::{Cell, CellRepr};
use crate::{ControlNet, FlipFlop, Instance, IoBuffer, IoNet, IoValue, Net, Trit, Value};

#[derive(Debug)]
pub struct Design {
    cells: Vec<Cell>,
    ios: BTreeMap<String, Range<u32>>,
    next_io: u32,
}

impl Design {
    pub fn new() -> Design {
        Design { cells: vec![], ios: BTreeMap::new(), next_io: 0 }
    }

    pub fn add_cell(&mut self, cell: CellRepr) -> CellRef {
        let index = self.cells.len();
        let output_len = cell.output_len();
        self.cells.push(cell.into());
        if output_len > 1 {
            for _ in 0..(output_len - 1) {
                self.cells.push(Cell::Skip(index.try_into().expect("cell index too large")))
            }
        }
        CellRef { design: self, index }
    }

    pub fn replace_cell(&mut self, index: CellIndex, cell: CellRepr) {
        assert_eq!(self.cells[index.0].output_len(), cell.output_len());
        self.cells[index.0] = cell.into();
    }

    pub fn visit_cell_mut(&mut self, index: CellIndex, f: impl FnMut(&mut Net)) {
        self.cells[index.0].visit_mut(f);
    }

    pub fn find_cell(&self, net: Net) -> Result<(CellRef, usize), Trit> {
        if let Some(trit) = net.as_const() {
            return Err(trit);
        }
        let index = net.as_cell().unwrap();
        let (cell_index, bit_index) = match self.cells[index] {
            Cell::Skip(start) => (start as usize, index - start as usize),
            _ => (index, 0),
        };
        Ok((CellRef { design: self, index: cell_index }, bit_index))
    }

    pub fn iter_cells(&self) -> CellIter {
        CellIter { design: self, index: 0 }
    }

    pub fn add_io(&mut self, name: String, width: usize) -> IoValue {
        let width = width as u32;
        let range = self.next_io..(self.next_io + width);
        match self.ios.entry(name) {
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

    // Invalidates all existing `CellIndex`es.
    pub fn compact(&mut self) {
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
                | CellRepr::Output(_, _) => {
                    queue.insert(index);
                }
                _ => (),
            }
        }

        let mut keep = BTreeSet::new();
        while let Some(index) = queue.pop_first() {
            keep.insert(index);
            let cell = &self.cells[index];
            cell.visit(|net| match self.find_cell(net) {
                Ok((cell_ref, _offset)) => {
                    if !keep.contains(&cell_ref.index) {
                        queue.insert(cell_ref.index);
                    }
                }
                Err(_trit) => (),
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

        for cell in self.cells.iter_mut() {
            if let Cell::Skip(_) = cell {
                continue;
            }
            cell.visit_mut(|net| {
                if ![Net::UNDEF, Net::ZERO, Net::ONE].contains(net) {
                    *net = net_map[net];
                }
            });
        }
    }
}

macro_rules! builder_fn {
    () => {};

    ($func:ident( $($arg:ident : $ty:ty),+ ) -> $repr:ident $body:tt; $($rest:tt)*) => {
        pub fn $func(&mut self, $( $arg: $ty ),+) -> Value {
            self.add_cell(CellRepr::$repr $body).output()
        }

        builder_fn!{ $($rest)* }
    };

    // For cells with no output value.
    ($func:ident( $($arg:ident : $ty:ty),+ ) : $repr:ident $body:tt; $($rest:tt)*) => {
        pub fn $func(&mut self, $( $arg: $ty ),+) {
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
    }
}

impl Design {
    pub fn add_ne(&mut self, arg1: impl Into<Value>, arg2: impl Into<Value>) -> Value {
        let eq = self.add_eq(arg1, arg2);
        self.add_not(eq)
    }
}

// Only used for replacing a cell; otherwise a `CellRef` is a better choice.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct CellIndex(usize);

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
    fn deref(&self) -> &Cell {
        &self.design.cells[self.index]
    }

    pub fn repr(&self) -> Cow<'a, CellRepr> {
        self.design.cells[self.index].repr()
    }

    pub fn output(&self) -> Value {
        Value::cell(self.index, self.deref().output_len())
    }

    pub fn index(&self) -> CellIndex {
        CellIndex(self.index)
    }

    pub fn visit(&self, f: impl FnMut(Net)) {
        self.design.cells[self.index].visit(f)
    }
}

#[derive(Debug)]
pub struct CellIter<'a> {
    design: &'a Design,
    index: usize,
}

impl<'a> Iterator for CellIter<'a> {
    type Item = CellRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.design.cells.len() {
            let cell_ref = CellRef { design: self.design, index: self.index };
            self.index += cell_ref.deref().output_len().max(1);
            Some(cell_ref)
        } else {
            None
        }
    }
}

impl Display for Design {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut cell_index_map = BTreeMap::new();
        for (index, cell) in self.cells.iter().enumerate() {
            match cell {
                Cell::Skip(_) => (),
                _ => {
                    cell_index_map.insert(index, cell_index_map.len());
                }
            }
        }

        let cell_ident = |cell_ref: CellRef| cell_index_map.get(&cell_ref.index).unwrap();

        let write_net = |f: &mut std::fmt::Formatter, net: Net| -> std::fmt::Result {
            match self.find_cell(net) {
                Ok((cell_ref, offset)) => {
                    if cell_ref.output().len() == 1 {
                        write!(f, "%{}", cell_ident(cell_ref))
                    } else {
                        write!(f, "%{}.{}", cell_ident(cell_ref), offset)
                    }
                }
                Err(trit) => write!(f, "{}", trit),
            }
        };

        let write_value = |f: &mut std::fmt::Formatter, value: &Value| -> std::fmt::Result {
            match self.find_cell(value[0]) {
                Ok((cell_ref, _offset)) if *value == cell_ref.output() => {
                    write!(f, "%{}", cell_ident(cell_ref))
                }
                _ => {
                    write!(f, "{{")?;
                    for net in value {
                        write!(f, " ")?;
                        write_net(f, net)?;
                    }
                    write!(f, " }}")?;
                    Ok(())
                }
            }
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

        let write_io_value = |f: &mut std::fmt::Formatter, io_value: &IoValue| -> std::fmt::Result {
            write!(f, "{{")?;
            for io_net in io_value {
                write!(f, " #")?;
                match self.find_io(io_net) {
                    Some((name, offset)) => write!(f, "{:?}.{}", name, offset)?,
                    None => write!(f, "<invalid>")?,
                }
            }
            write!(f, " }}")?;
            Ok(())
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

        for (index, cell) in self.cells.iter().enumerate() {
            if let Cell::Skip(_) = cell {
                continue;
            }

            write!(f, "%{}:{} = ", cell_index_map.get(&index).unwrap(), cell.output_len())?;
            match &*cell.repr() {
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
            }

            write!(f, "\n")?;
        }

        write!(f, "\n")
    }
}
