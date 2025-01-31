use std::ops::Range;
use std::cell::RefCell;
use std::borrow::Cow;
use std::collections::{btree_map, BTreeMap, BTreeSet};
use std::fmt::Display;
use std::str::FromStr;
use std::sync::Arc;

use crate::cell::{Cell, CellRepr};
use crate::{
    ControlNet, FlipFlop, Instance, IoBuffer, IoNet, IoValue, Net, ParamValue, Target, Trit, Value, TargetCellPurity,
    TargetCell, TargetPrototype,
};

#[derive(Debug, Clone)]
pub struct Design {
    ios: BTreeMap<String, Range<u32>>,
    cells: Vec<Cell>,
    changes: RefCell<ChangeQueue>,
    target: Option<Arc<dyn Target>>,
}

#[derive(Debug, Clone)]
struct ChangeQueue {
    next_io: u32,
    added_ios: BTreeMap<String, Range<u32>>,
    added_cells: Vec<Cell>,
    replaced_cells: BTreeMap<usize, CellRepr>,
    unalived_cells: BTreeSet<usize>,
    replaced_nets: BTreeMap<Net, Net>,
}

impl Design {
    pub fn new() -> Design {
        Self::with_target(None)
    }

    pub fn with_target(target: Option<Arc<dyn Target>>) -> Design {
        Design {
            ios: BTreeMap::new(),
            cells: vec![],
            changes: RefCell::new(ChangeQueue {
                next_io: 0,
                added_ios: BTreeMap::new(),
                added_cells: vec![],
                replaced_cells: BTreeMap::new(),
                unalived_cells: BTreeSet::new(),
                replaced_nets: BTreeMap::new(),
            }),
            target,
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

    pub fn get_io(&self, name: impl AsRef<str>) -> Option<IoValue> {
        self.ios.get(name.as_ref()).map(|range| IoValue::from_range(range.clone()))
    }

    pub fn find_io(&self, io_net: IoNet) -> Option<(&str, usize)> {
        for (name, range) in self.ios.iter() {
            if range.contains(&io_net.index) {
                return Some((name.as_str(), (io_net.index - range.start) as usize));
            }
        }
        None
    }

    pub fn iter_ios(&self) -> impl Iterator<Item = (&str, IoValue)> {
        self.ios.iter().map(|(name, range)| (name.as_str(), IoValue::from_range(range.clone())))
    }

    pub fn add_cell(&self, cell: CellRepr) -> Value {
        cell.validate(self);
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

    pub fn add_void(&self, width: usize) -> Value {
        let mut changes = self.changes.borrow_mut();
        let index = self.cells.len() + changes.added_cells.len();
        for _ in 0..width {
            changes.added_cells.push(Cell::Void);
        }
        Value::cell(index, width)
    }

    fn locate_cell(&self, net: Net) -> Result<(usize, usize), Trit> {
        if let Some(trit) = net.as_const() {
            return Err(trit);
        }
        let index = net.as_cell().unwrap();
        let (cell_index, bit_index) = match self.cells[index] {
            Cell::Void => unreachable!(),
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
        for (from_net, to_net) in from_value.iter().zip(to_value.iter()) {
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
            _ => return mapped_net,
        }
    }

    pub fn map_value(&self, value: impl Into<Value>) -> Value {
        value.into().iter().map(|net| self.map_net(net)).collect::<Vec<_>>().into()
    }

    pub fn apply(&mut self) -> bool {
        let changes = self.changes.get_mut();
        let mut did_change = !changes.added_ios.is_empty() || !changes.added_cells.is_empty();
        for cell_index in std::mem::take(&mut changes.unalived_cells) {
            let output_len = self.cells[cell_index].output_len().max(1);
            for index in cell_index..cell_index + output_len {
                self.cells[index] = Cell::Void;
            }
            did_change = true;
        }
        for (index, new_cell) in std::mem::take(&mut changes.replaced_cells) {
            assert_eq!(self.cells[index].output_len(), new_cell.output_len());
            // CellRef::replace() ensures the new repr is different.
            self.cells[index] = new_cell.into();
            did_change = true;
        }
        self.ios.extend(std::mem::take(&mut changes.added_ios));
        self.cells.extend(std::mem::take(&mut changes.added_cells));
        if !changes.replaced_nets.is_empty() {
            for cell in self.cells.iter_mut().filter(|cell| !matches!(cell, Cell::Skip(_) | Cell::Void)) {
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

    pub fn target(&self) -> Option<Arc<dyn Target>> {
        self.target.as_ref().map(|target| target.clone())
    }

    pub fn target_prototype(&self, target_cell: &TargetCell) -> &TargetPrototype {
        self.target.as_ref().unwrap().prototype(&target_cell.kind).unwrap()
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
        if *self.design.cells[self.index].repr() != to_cell {
            to_cell.validate(&self.design);
            let mut changes = self.design.changes.borrow_mut();
            assert!(changes.replaced_cells.insert(self.index, to_cell).is_none());
        }
    }

    pub fn unalive(&self) {
        let mut changes = self.design.changes.borrow_mut();
        changes.unalived_cells.insert(self.index);
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
        while matches!(self.design.cells.get(self.index), Some(Cell::Void)) {
            self.index += 1;
        }
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
        add_target(arg: impl Into<TargetCell>) ->
            Target(arg.into());

        add_input(name: impl Into<String>, width: usize) ->
            Input(name.into(), width);
        add_output(name: impl Into<String>, value: impl Into<Value>) :
            Output(name.into(), value.into());
        add_name(name: impl Into<String>, value: impl Into<Value>) :
            Name(name.into(), value.into());
    }

    pub fn add_ne(&self, arg1: impl Into<Value>, arg2: impl Into<Value>) -> Value {
        let eq = self.add_eq(arg1, arg2);
        self.add_not(eq)
    }

    pub fn add_input_net(&self, name: impl Into<String>) -> Net {
        self.add_input(name, 1)[0]
    }
}

impl Design {
    pub fn iter_cells_topo<'a>(&'a self) -> impl Iterator<Item = CellRef<'a>> {
        let mut outgoing = BTreeMap::<usize, BTreeSet<usize>>::new();
        let mut incoming = BTreeMap::<usize, BTreeSet<usize>>::new();
        let mut queue = BTreeSet::new();
        for (index, cell) in self.cells.iter().enumerate() {
            if matches!(cell, Cell::Skip(_) | Cell::Void) {
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
                CellRepr::Target(target_cell) => {
                    if self.target_prototype(target_cell).purity != TargetCellPurity::Pure {
                        queue.insert(index);
                    }
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

    pub fn compact(&mut self) -> bool {
        let did_change = self.apply();

        let mut queue = BTreeSet::new();
        for (index, cell) in self.cells.iter().enumerate() {
            if matches!(cell, Cell::Skip(_) | Cell::Void) {
                continue;
            }
            match &*cell.repr() {
                CellRepr::Iob(_)
                | CellRepr::Other(_)
                | CellRepr::Input(_, _)
                | CellRepr::Output(_, _)
                | CellRepr::Name(_, _) => {
                    queue.insert(index);
                }
                CellRepr::Target(target_cell) => {
                    if self.target_prototype(target_cell).purity == TargetCellPurity::HasEffects {
                        queue.insert(index);
                    }
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

        did_change
    }

    pub fn replace_bufs(&mut self) {
        self.apply();

        for cell_ref in self.iter_cells() {
            match &*cell_ref.repr() {
                CellRepr::Buf(arg) => self.replace_value(cell_ref.output(), arg),
                _ => (),
            }
        }
    }
}

#[derive(Debug)]
pub enum NotIsomorphic {
    NoOutputLeft(String),
    NoOutputRight(String),
    OutputSizeMismatch(String),
    IoSizeMismatch(String),
    NameSizeMismatch(String),
    ValueSizeMismatch(Value, Value),
    NetMismatch(Net, Net),
    IoNetMismatch(IoNet, IoNet),
}

impl Display for NotIsomorphic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NotIsomorphic::NoOutputLeft(name) => write!(f, "output {:?} is missing in the left design", name),
            NotIsomorphic::NoOutputRight(name) => write!(f, "output {:?} is missing in the right design", name),
            NotIsomorphic::OutputSizeMismatch(name) => write!(f, "size of output {:?} does not match", name),
            NotIsomorphic::IoSizeMismatch(name) => write!(f, "size of IO {:?} does not match", name),
            NotIsomorphic::NameSizeMismatch(name) => write!(f, "size of name cell {:?} does not match", name),
            NotIsomorphic::ValueSizeMismatch(value_l, value_r) => {
                write!(f, "size of values {} and {} do not match", value_l, value_r)
            }
            NotIsomorphic::NetMismatch(net_l, net_r) => write!(f, "nets {} and {} are not isomorphic", net_l, net_r),
            NotIsomorphic::IoNetMismatch(io_net_l, io_net_r) => {
                write!(f, "IO nets {} and {} are not isomorphic", io_net_l, io_net_r)
            }
        }
    }
}

// Beware: this function will ignore instances that have no output bits.
pub fn isomorphic(lft: &Design, rgt: &Design) -> Result<(), NotIsomorphic> {
    let mut queue: BTreeSet<(Net, Net)> = BTreeSet::new();
    fn queue_vals(queue: &mut BTreeSet<(Net, Net)>, val_l: &Value, val_r: &Value) -> Result<(), NotIsomorphic> {
        if val_l.len() != val_r.len() {
            return Err(NotIsomorphic::ValueSizeMismatch(val_l.clone(), val_r.clone()));
        }
        for (net_l, net_r) in val_l.iter().zip(val_r) {
            queue.insert((net_l, net_r));
        }
        Ok(())
    }

    let mut visited: BTreeSet<(Net, Net)> = BTreeSet::new();
    visited.insert((Net::UNDEF, Net::UNDEF));
    visited.insert((Net::ZERO, Net::ZERO));
    visited.insert((Net::ONE, Net::ONE));
    let mut outputs_l = BTreeMap::new();
    let mut names_l = BTreeMap::new();
    for cell in lft.iter_cells() {
        match &*cell.repr() {
            CellRepr::Output(name, value) => {
                outputs_l.insert(name.clone(), value.clone());
            }
            CellRepr::Name(name, value) => {
                names_l.insert(name.clone(), value.clone());
            }
            _ => (),
        }
    }
    let mut outputs_r = BTreeMap::new();
    let mut names_r = BTreeMap::new();
    for cell in rgt.iter_cells() {
        match &*cell.repr() {
            CellRepr::Output(name, value) => {
                outputs_r.insert(name.clone(), value.clone());
            }
            CellRepr::Name(name, value) => {
                names_r.insert(name.clone(), value.clone());
            }
            _ => (),
        }
    }
    for (name, value_l) in &outputs_l {
        if let Some(value_r) = outputs_r.get(name) {
            if value_l.len() != value_r.len() {
                return Err(NotIsomorphic::OutputSizeMismatch(name.clone()));
            }
            for (net_l, net_r) in value_l.iter().zip(value_r) {
                queue.insert((net_l, net_r));
            }
        } else {
            return Err(NotIsomorphic::NoOutputRight(name.clone()));
        }
    }
    for name in outputs_r.keys() {
        if !outputs_l.contains_key(name) {
            return Err(NotIsomorphic::NoOutputLeft(name.clone()));
        }
    }
    for (name, value_l) in &names_l {
        if let Some(value_r) = names_r.get(name) {
            if value_l.len() != value_r.len() {
                return Err(NotIsomorphic::NameSizeMismatch(name.clone()));
            }
            for (net_l, net_r) in value_l.iter().zip(value_r) {
                queue.insert((net_l, net_r));
            }
        }
    }
    let mut ios = BTreeSet::new();
    ios.insert((IoNet::FLOATING, IoNet::FLOATING));
    for name in lft.ios.keys() {
        if let (Some(io_l), Some(io_r)) = (lft.get_io(name), rgt.get_io(name)) {
            if io_l.len() != io_r.len() {
                return Err(NotIsomorphic::IoSizeMismatch(name.clone()));
            }
            for (ionet_l, ionet_r) in io_l.iter().zip(io_r.iter()) {
                ios.insert((ionet_l, ionet_r));
            }
        }
    }
    while let Some((net_l, net_r)) = queue.pop_first() {
        if visited.contains(&(net_l, net_r)) {
            continue;
        }
        if net_l.as_const().is_some() || net_r.as_const().is_some() {
            // (const, const) pairs already added to visitted at the beginning
            return Err(NotIsomorphic::NetMismatch(net_l, net_r));
        }
        let (cell_l, bit_l) = lft.find_cell(net_l).unwrap();
        let (cell_r, bit_r) = rgt.find_cell(net_r).unwrap();
        let out_l = cell_l.output();
        let out_r = cell_r.output();
        if bit_l != bit_r || out_l.len() != out_r.len() {
            return Err(NotIsomorphic::NetMismatch(net_l, net_r));
        }
        for (net_l, net_r) in out_l.iter().zip(out_r) {
            visited.insert((net_l, net_r));
        }
        match (&*cell_l.repr(), &*cell_r.repr()) {
            (CellRepr::Buf(val_l), CellRepr::Buf(val_r)) | (CellRepr::Not(val_l), CellRepr::Not(val_r)) => {
                queue_vals(&mut queue, val_l, val_r)?
            }
            (CellRepr::And(arg1_l, arg2_l), CellRepr::And(arg1_r, arg2_r))
            | (CellRepr::Or(arg1_l, arg2_l), CellRepr::Or(arg1_r, arg2_r))
            | (CellRepr::Xor(arg1_l, arg2_l), CellRepr::Xor(arg1_r, arg2_r))
            | (CellRepr::Eq(arg1_l, arg2_l), CellRepr::Eq(arg1_r, arg2_r))
            | (CellRepr::ULt(arg1_l, arg2_l), CellRepr::ULt(arg1_r, arg2_r))
            | (CellRepr::SLt(arg1_l, arg2_l), CellRepr::SLt(arg1_r, arg2_r))
            | (CellRepr::Mul(arg1_l, arg2_l), CellRepr::Mul(arg1_r, arg2_r))
            | (CellRepr::UDiv(arg1_l, arg2_l), CellRepr::UDiv(arg1_r, arg2_r))
            | (CellRepr::UMod(arg1_l, arg2_l), CellRepr::UMod(arg1_r, arg2_r))
            | (CellRepr::SDivTrunc(arg1_l, arg2_l), CellRepr::SDivTrunc(arg1_r, arg2_r))
            | (CellRepr::SDivFloor(arg1_l, arg2_l), CellRepr::SDivFloor(arg1_r, arg2_r))
            | (CellRepr::SModTrunc(arg1_l, arg2_l), CellRepr::SModTrunc(arg1_r, arg2_r))
            | (CellRepr::SModFloor(arg1_l, arg2_l), CellRepr::SModFloor(arg1_r, arg2_r)) => {
                queue_vals(&mut queue, arg1_l, arg1_r)?;
                queue_vals(&mut queue, arg2_l, arg2_r)?;
            }
            (CellRepr::Mux(arg1_l, arg2_l, arg3_l), CellRepr::Mux(sel_r, arg2_r, arg3_r)) => {
                queue.insert((*arg1_l, *sel_r));
                queue_vals(&mut queue, arg2_l, arg2_r)?;
                queue_vals(&mut queue, arg3_l, arg3_r)?;
            }
            (CellRepr::Adc(arg1_l, arg2_l, arg3_l), CellRepr::Adc(arg1_r, arg2_r, arg3_r)) => {
                queue_vals(&mut queue, arg1_l, arg1_r)?;
                queue_vals(&mut queue, arg2_l, arg2_r)?;
                queue.insert((*arg3_l, *arg3_r));
            }
            (CellRepr::Shl(arg1_l, arg2_l, stride_l), CellRepr::Shl(arg1_r, arg2_r, stride_r))
            | (CellRepr::UShr(arg1_l, arg2_l, stride_l), CellRepr::UShr(arg1_r, arg2_r, stride_r))
            | (CellRepr::SShr(arg1_l, arg2_l, stride_l), CellRepr::SShr(arg1_r, arg2_r, stride_r))
            | (CellRepr::XShr(arg1_l, arg2_l, stride_l), CellRepr::XShr(arg1_r, arg2_r, stride_r)) => {
                queue_vals(&mut queue, arg1_l, arg1_r)?;
                queue_vals(&mut queue, arg2_l, arg2_r)?;
                if stride_l != stride_r {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            (CellRepr::Dff(ff_l), CellRepr::Dff(ff_r)) => {
                queue_vals(&mut queue, &ff_l.data, &ff_r.data)?;
                queue.insert((ff_l.clock.net(), ff_r.clock.net()));
                queue.insert((ff_l.clear.net(), ff_r.clear.net()));
                queue.insert((ff_l.reset.net(), ff_r.reset.net()));
                queue.insert((ff_l.enable.net(), ff_r.enable.net()));
                if ff_l.clock.is_positive() != ff_r.clock.is_positive()
                    || ff_l.clear.is_positive() != ff_r.clear.is_positive()
                    || ff_l.reset.is_positive() != ff_r.reset.is_positive()
                    || ff_l.enable.is_positive() != ff_r.enable.is_positive()
                    || (ff_l.reset_over_enable != ff_r.reset_over_enable
                        && !ff_l.reset.is_always(false)
                        && !ff_l.enable.is_always(true))
                    || ff_l.clear_value != ff_r.clear_value
                    || ff_l.reset_value != ff_r.reset_value
                    || ff_l.init_value != ff_r.init_value
                {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            (CellRepr::Iob(iob_l), CellRepr::Iob(iob_r)) => {
                for (io_net_l, io_net_r) in iob_l.io.iter().zip(iob_r.io.iter()) {
                    if !ios.contains(&(io_net_l, io_net_r)) {
                        return Err(NotIsomorphic::IoNetMismatch(io_net_l, io_net_r));
                    }
                }
                queue_vals(&mut queue, &iob_l.output, &iob_r.output)?;
                queue.insert((iob_l.enable.net(), iob_r.enable.net()));
                if iob_l.enable.is_positive() != iob_r.enable.is_positive() {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            (CellRepr::Target(target_cell_l), CellRepr::Target(target_cell_r)) => {
                for (io_net_l, io_net_r) in target_cell_l.ios.iter().zip(target_cell_r.ios.iter()) {
                    if !ios.contains(&(io_net_l, io_net_r)) {
                        return Err(NotIsomorphic::IoNetMismatch(io_net_l, io_net_r));
                    }
                }
                if target_cell_l.kind != target_cell_r.kind || target_cell_l.params != target_cell_r.params {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
                queue_vals(&mut queue, &target_cell_l.inputs, &target_cell_r.inputs)?;
            }
            (CellRepr::Other(inst_l), CellRepr::Other(inst_r)) => {
                if inst_l.kind != inst_r.kind || inst_l.params != inst_r.params || inst_l.outputs != inst_r.outputs {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
                for (name, value_l) in &inst_l.inputs {
                    let Some(value_r) = inst_r.inputs.get(name) else {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    };
                    queue_vals(&mut queue, value_l, value_r)?;
                }
                for name in inst_r.inputs.keys() {
                    if !inst_l.inputs.contains_key(name) {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    }
                }
                for (name, io_value_l) in &inst_l.ios {
                    let Some(io_value_r) = inst_r.ios.get(name) else {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    };
                    for (io_net_l, io_net_r) in io_value_l.iter().zip(io_value_r.iter()) {
                        if !ios.contains(&(io_net_l, io_net_r)) {
                            return Err(NotIsomorphic::IoNetMismatch(io_net_l, io_net_r));
                        }
                    }
                }
                for name in inst_r.ios.keys() {
                    if !inst_l.ios.contains_key(name) {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    }
                }
            }
            (CellRepr::Input(name_l, _), CellRepr::Input(name_r, _)) => {
                if name_l != name_r {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            _ => return Err(NotIsomorphic::NetMismatch(net_l, net_r)),
        }
    }
    Ok(())
}

#[macro_export]
macro_rules! assert_isomorphic {
    ( $lft:ident, $rgt:ident ) => {
        $lft.apply();
        $rgt.apply();
        let result = prjunnamed_netlist::isomorphic(&$lft, &$rgt);
        if let Err(error) = result {
            panic!("{}\nleft design:\n{}\nright design:\n{}", error, $lft, $rgt);
        }
    };
}

struct DisplayFn<'a, F: for<'b> Fn(&Design, &mut std::fmt::Formatter<'b>) -> std::fmt::Result>(&'a Design, F);

impl<F: Fn(&Design, &mut std::fmt::Formatter) -> std::fmt::Result> Display for DisplayFn<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.1(self.0, f)
    }
}

impl Design {
    fn write_string(&self, f: &mut std::fmt::Formatter, str: &str) -> std::fmt::Result {
        write!(f, "\"")?;
        for byte in str.as_bytes() {
            if (byte.is_ascii_graphic() || matches!(byte, b' ' | b'\t')) && *byte != b'"' {
                write!(f, "{}", *byte as char)?;
            } else {
                assert!(byte.is_ascii());
                write!(f, "\\{:02x}", byte)?;
            }
        }
        write!(f, "\"")?;
        Ok(())
    }

    fn write_net(&self, f: &mut std::fmt::Formatter, net: Net) -> std::fmt::Result {
        if let Some(index) = net.as_cell() {
            if index >= self.cells.len() {
                return write!(f, "%_{}", index);
            }
        }
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
    }

    fn write_value(&self, f: &mut std::fmt::Formatter, value: &Value) -> std::fmt::Result {
        if value.len() == 0 {
            return write!(f, "{{}}");
        } else if value.len() == 1 {
            return self.write_net(f, value[0]);
        } else if let Some(value) = value.as_const() {
            return write!(f, "{}", value);
        } else if value.iter().any(|net| net.as_cell().map(|index| index >= self.cells.len()).unwrap_or(false)) {
            // Value contains newly added cells that we can't look up. Don't try to make
            // the display nicer, just make sure it doesn't panic.
            write!(f, "{{")?;
            for net in value {
                write!(f, " ")?;
                self.write_net(f, net)?;
            }
            write!(f, " }}")?;
            return Ok(());
        } else if let Ok((cell_ref, _offset)) = self.find_cell(value[0]) {
            if *value == cell_ref.output() {
                if value.len() == 1 {
                    return write!(f, "%{}", cell_ref.index);
                } else {
                    return write!(f, "%{}:{}", cell_ref.index, value.len());
                }
            }
        }

        write!(f, "{{")?;
        let mut index = 0;
        while index < value.len() {
            write!(f, " ")?;
            if let Ok((cell_ref_a, 0)) = self.find_cell(value[index]) {
                let count = value[index..]
                    .iter()
                    .enumerate()
                    .take_while(|(addend, net)| {
                        if let Ok((cell_ref_b, offset_b)) = self.find_cell(**net) {
                            cell_ref_a == cell_ref_b && *addend == offset_b
                        } else {
                            false
                        }
                    })
                    .count();
                if count > 0 {
                    write!(f, "%{}:{}", cell_ref_a.index, count)?;
                    index += count;
                    continue;
                }
            }
            self.write_net(f, value[index])?;
            index += 1;
        }
        write!(f, " }}")
    }

    fn write_io_net(&self, f: &mut std::fmt::Formatter, io_net: IoNet) -> std::fmt::Result {
        if io_net.is_floating() {
            write!(f, "#_")
        } else {
            write!(f, "#")?;
            match self.find_io(io_net) {
                Some((name, offset)) => {
                    self.write_string(f, name)?;
                    if self.ios[name].len() > 1 {
                        write!(f, "+{}", offset)?;
                    }
                    Ok(())
                }
                None => write!(f, "??"),
            }
        }
    }

    fn write_io_value(&self, f: &mut std::fmt::Formatter, io_value: &IoValue) -> std::fmt::Result {
        if io_value.len() == 0 {
            write!(f, "{{}}")
        } else if io_value.len() == 1 {
            self.write_io_net(f, io_value[0])
        } else if io_value.iter().all(IoNet::is_floating) {
            write!(f, "#_:{}", io_value.len())
        } else {
            if let Some((name, _offset)) = self.find_io(io_value[0]) {
                if self.get_io(name).unwrap() == *io_value {
                    write!(f, "#")?;
                    self.write_string(f, name)?;
                    write!(f, ":{}", io_value.len())?;
                    return Ok(());
                }
            }
            write!(f, "{{")?;
            for io_net in io_value {
                write!(f, " ")?;
                self.write_io_net(f, io_net)?;
            }
            write!(f, " }}")
        }
    }

    fn write_cell(&self, f: &mut std::fmt::Formatter, cell_ref: CellRef) -> std::fmt::Result {
        let write_control_net = |f: &mut std::fmt::Formatter, control_net: ControlNet| -> std::fmt::Result {
            if control_net.is_negative() {
                write!(f, "!")?;
            };
            self.write_net(f, control_net.net())
        };

        let write_control = |f: &mut std::fmt::Formatter, name: &str, control_net: ControlNet| -> std::fmt::Result {
            write!(f, "{}=", name)?;
            write_control_net(f, control_net)
        };

        let write_common = |f: &mut std::fmt::Formatter, name: &str, args: &[&Value]| -> std::fmt::Result {
            write!(f, "{}", name)?;
            for arg in args {
                write!(f, " ")?;
                self.write_value(f, arg)?;
            }
            Ok(())
        };

        let write_shift =
            |f: &mut std::fmt::Formatter, name: &str, arg1: &Value, arg2: &Value, stride: u32| -> std::fmt::Result {
                write!(f, "{} ", name)?;
                self.write_value(f, arg1)?;
                write!(f, " ")?;
                self.write_value(f, arg2)?;
                write!(f, " {stride:b}")?;
                Ok(())
            };

        let write_param_value = |f: &mut std::fmt::Formatter, value: &ParamValue| -> std::fmt::Result {
            match value {
                ParamValue::Const(value) => write!(f, "const({})", value)?,
                ParamValue::Int(value) => write!(f, "int({})", value)?,
                ParamValue::Float(value) => write!(f, "float({})", value)?,
                ParamValue::String(value) => {
                    write!(f, "string(")?;
                    self.write_string(f, value)?;
                    write!(f, ")")?;
                }
            }
            Ok(())
        };

        let write_cell_argument = |f: &mut std::fmt::Formatter, sigil: &str, name: &str| -> std::fmt::Result {
            write!(f, "  {sigil}@")?;
            self.write_string(f, &name)?;
            write!(f, "=")?;
            Ok(())
        };

        write!(f, "%{}:{} = ", cell_ref.index, cell_ref.output_len())?;
        match &*cell_ref.repr() {
            CellRepr::Buf(arg) => write_common(f, "buf", &[arg])?,
            CellRepr::Not(arg) => write_common(f, "not", &[arg])?,
            CellRepr::And(arg1, arg2) => write_common(f, "and", &[arg1, arg2])?,
            CellRepr::Or(arg1, arg2) => write_common(f, "or", &[arg1, arg2])?,
            CellRepr::Xor(arg1, arg2) => write_common(f, "xor", &[arg1, arg2])?,
            CellRepr::Mux(arg1, arg2, arg3) => {
                write!(f, "mux ")?;
                self.write_net(f, *arg1)?;
                write!(f, " ")?;
                self.write_value(f, arg2)?;
                write!(f, " ")?;
                self.write_value(f, arg3)?;
            }
            CellRepr::Adc(arg1, arg2, arg3) => {
                write!(f, "adc ")?;
                self.write_value(f, arg1)?;
                write!(f, " ")?;
                self.write_value(f, arg2)?;
                write!(f, " ")?;
                self.write_net(f, *arg3)?;
            }

            CellRepr::Eq(arg1, arg2) => write_common(f, "eq", &[arg1, arg2])?,
            CellRepr::ULt(arg1, arg2) => write_common(f, "ult", &[arg1, arg2])?,
            CellRepr::SLt(arg1, arg2) => write_common(f, "slt", &[arg1, arg2])?,

            CellRepr::Shl(arg1, arg2, stride) => write_shift(f, "shl", arg1, arg2, *stride)?,
            CellRepr::UShr(arg1, arg2, stride) => write_shift(f, "ushr", arg1, arg2, *stride)?,
            CellRepr::SShr(arg1, arg2, stride) => write_shift(f, "sshr", arg1, arg2, *stride)?,
            CellRepr::XShr(arg1, arg2, stride) => write_shift(f, "xshr", arg1, arg2, *stride)?,

            CellRepr::Mul(arg1, arg2) => write_common(f, "mul", &[arg1, arg2])?,
            CellRepr::UDiv(arg1, arg2) => write_common(f, "udiv", &[arg1, arg2])?,
            CellRepr::UMod(arg1, arg2) => write_common(f, "umod", &[arg1, arg2])?,
            CellRepr::SDivTrunc(arg1, arg2) => write_common(f, "sdiv_trunc", &[arg1, arg2])?,
            CellRepr::SDivFloor(arg1, arg2) => write_common(f, "sdiv_floor", &[arg1, arg2])?,
            CellRepr::SModTrunc(arg1, arg2) => write_common(f, "smod_trunc", &[arg1, arg2])?,
            CellRepr::SModFloor(arg1, arg2) => write_common(f, "smod_floor", &[arg1, arg2])?,

            CellRepr::Dff(flip_flop) => {
                write_common(f, "dff", &[&flip_flop.data])?;
                write_control(f, " clk", flip_flop.clock)?;
                if flip_flop.has_clear() {
                    write_control(f, " clr", flip_flop.clear)?;
                    if flip_flop.clear_value != flip_flop.init_value {
                        write!(f, ",{}", flip_flop.clear_value)?;
                    }
                }
                if flip_flop.has_reset() {
                    write_control(f, " rst", flip_flop.reset)?;
                    if flip_flop.reset_value != flip_flop.init_value {
                        write!(f, ",{}", flip_flop.reset_value)?;
                    }
                }
                if flip_flop.has_enable() {
                    write_control(f, " en", flip_flop.enable)?;
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
                write!(f, "iob ")?;
                self.write_io_value(f, &io_buffer.io)?;
                write!(f, " o=")?;
                self.write_value(f, &io_buffer.output)?;
                write_control(f, " en", io_buffer.enable)?;
            }
            CellRepr::Other(instance) => {
                self.write_string(f, instance.kind.as_str())?;
                write!(f, " {{\n")?;
                for (name, value) in instance.params.iter() {
                    write_cell_argument(f, "p", name)?;
                    write_param_value(f, value)?;
                    write!(f, "\n")?;
                }
                for (name, value) in instance.inputs.iter() {
                    write_cell_argument(f, "i", name)?;
                    self.write_value(f, value)?;
                    write!(f, "\n")?;
                }
                for (name, range) in instance.outputs.iter() {
                    write_cell_argument(f, "o", name)?;
                    write!(f, "{}:{}\n", range.start, range.len())?;
                }
                for (name, value) in instance.ios.iter() {
                    write_cell_argument(f, "io", name)?;
                    self.write_io_value(f, value)?;
                    write!(f, "\n")?;
                }
                write!(f, "}}")?;
            }
            CellRepr::Target(target_cell) => {
                write!(f, "target ")?;
                let prototype = self.target_prototype(target_cell);
                self.write_string(f, &target_cell.kind)?;
                write!(f, " {{\n")?;
                for (param, value) in prototype.params.iter().zip(target_cell.params.iter()) {
                    write_cell_argument(f, "p", &param.name)?;
                    write_param_value(f, value)?;
                    write!(f, "\n")?;
                }
                for input in &prototype.inputs {
                    write_cell_argument(f, "i", &input.name)?;
                    self.write_value(f, &target_cell.inputs.slice(input.range.clone()))?;
                    write!(f, "\n")?;
                }
                for io in &prototype.ios {
                    write_cell_argument(f, "io", &io.name)?;
                    self.write_io_value(f, &target_cell.ios.slice(io.range.clone()))?;
                    write!(f, "\n")?;
                }
                write!(f, "}}")?;
            }

            CellRepr::Input(name, _size) => {
                write!(f, "input ")?;
                self.write_string(f, name)?;
            }
            CellRepr::Output(name, value) => {
                write!(f, "output ")?;
                self.write_string(f, name)?;
                write!(f, " ")?;
                self.write_value(f, value)?;
            }
            CellRepr::Name(name, value) => {
                write!(f, "name ")?;
                self.write_string(f, name)?;
                write!(f, " ")?;
                self.write_value(f, value)?;
            }
        }
        Ok(())
    }

    pub fn display_net<'a>(&'a self, net: impl Into<Net>) -> impl Display + 'a {
        let net = net.into();
        DisplayFn(self, move |design: &Design, f| design.write_net(f, net))
    }

    pub fn display_value<'a, 'b: 'a>(&'a self, value: impl Into<Cow<'b, Value>>) -> impl Display + 'a {
        let value = value.into().to_owned();
        DisplayFn(self, move |design: &Design, f| design.write_value(f, &value))
    }

    pub fn display_cell<'a>(&'a self, value: CellRef<'a>) -> impl Display + 'a {
        DisplayFn(self, move |design: &Design, f| design.write_cell(f, value))
    }
}

impl Display for Design {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(target) = self.target() {
            write!(f, "target ")?;
            self.write_string(f, target.name())?;
            for (name, value) in target.options() {
                write!(f, " ")?;
                self.write_string(f, &name)?;
                write!(f, "=")?;
                self.write_string(f, &value)?;
            }
            write!(f, "\n")?;
        }

        for (name, range) in self.ios.iter() {
            write!(f, "#")?;
            self.write_string(f, name)?;
            write!(f, ":{}\n", range.len())?;
        }

        for cell_ref in self.iter_cells() {
            self.write_cell(f, cell_ref)?;
            write!(f, "\n")?;
        }

        if cfg!(feature = "trace") {
            let (mut coarse_cells, mut skip_cells, mut fine_cells) = (0, 0, 0);
            for cell in self.cells.iter() {
                match cell {
                    Cell::Void => (),
                    Cell::Coarse(_) => {
                        coarse_cells += 1;
                    }
                    Cell::Skip(_) => {
                        skip_cells += 1;
                    }
                    _ => {
                        fine_cells += 1;
                    }
                }
            }
            writeln!(
                f,
                "; {} cells ({} coarse, {} fine) + {} skips",
                coarse_cells + fine_cells,
                coarse_cells,
                fine_cells,
                skip_cells
            )?;
        }

        Ok(())
    }
}

impl FromStr for Design {
    type Err = crate::ParseError;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        crate::parse(None, source)
    }
}
