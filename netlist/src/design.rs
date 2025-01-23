use std::borrow::Cow;
use std::collections::{hash_map, BTreeMap, HashMap};
use std::fmt::Display;
use std::ops::Range;

use crate::cell::{Cell, CellRepr};
use crate::{IoValue, Net, Trit, Value};

#[derive(Debug)]
pub struct Design {
    cells: Vec<Cell>,
    ios: HashMap<String, Range<u32>>,
    next_io: u32,
}

impl Design {
    pub fn new() -> Design {
        Design { cells: vec![], ios: HashMap::new(), next_io: 0 }
    }

    pub fn add_io(&mut self, name: String, width: usize) -> IoValue {
        let width = width as u32;
        let range = self.next_io..(self.next_io + width);
        match self.ios.entry(name) {
            hash_map::Entry::Occupied(entry) => {
                panic!("duplicate IO port {}", entry.key());
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(range.clone());
            }
        }
        IoValue::from_range(range)
    }

    pub fn add_cell(&mut self, cell: CellRepr) -> CellRef {
        let index = self.cells.len();
        let output_len = cell.output_len();
        self.cells.push(cell.into());
        if output_len > 1 {
            for _ in 0..(output_len - 1) {
                self.cells.push(Cell::Skip(index as u32))
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

    pub fn find_cell(&self, net: Net) -> Result<(CellRef, u32), Trit> {
        if let Some(trit) = net.as_const() {
            return Err(trit);
        }
        let index = net.as_cell().unwrap();
        let (cell_index, bit_index) = match self.cells[index] {
            Cell::Skip(start) => (start as usize, index - start as usize),
            _ => (index, 0),
        };
        Ok((CellRef { design: self, index: cell_index }, bit_index as u32))
    }

    pub fn iter_cells(&self) -> CellIter {
        CellIter { design: self, index: 0 }
    }
}

#[derive(Clone, Copy)]
pub struct CellRef<'a> {
    design: &'a Design,
    index: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct CellIndex(usize);

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

        let cell_ident = |cell_ref: CellRef| {
            cell_index_map.get(&cell_ref.index).unwrap()
        };

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
                    write!(f, "{{ ")?;
                    for net in value {
                        write_net(f, net)?;
                        write!(f, " ")?;
                    }
                    write!(f, "}}")?;
                    Ok(())
                }
            }
        };

        let write_cell = |f: &mut std::fmt::Formatter, name: &str, args: &[&Value]| -> std::fmt::Result {
            write!(f, "{}", name)?;
            for arg in args {
                write!(f, " ")?;
                write_value(f, arg)?;
            }
            Ok(())
        };

        // TODO: ios

        for (index, cell) in self.cells.iter().enumerate() {
            if let Cell::Skip(_) = cell { continue }

            write!(f, "%{}:{} = ", cell_index_map.get(&index).unwrap(), cell.output_len())?;
            match &*cell.repr() {
                CellRepr::Buf(arg) => write_cell(f, "buf", &[arg])?,
                CellRepr::Not(arg) => write_cell(f, "not", &[arg])?,
                CellRepr::And(arg1, arg2) => write_cell(f, "and", &[arg1, arg2])?,
                CellRepr::Or(arg1, arg2) => write_cell(f, "or", &[arg1, arg2])?,
                CellRepr::Xor(arg1, arg2) => write_cell(f, "xor", &[arg1, arg2])?,
                CellRepr::Mux(arg1, arg2, arg3) => write_cell(f, "mux", &[&arg1.into(), arg2, arg3])?,

                CellRepr::Add(arg1, arg2) => write_cell(f, "add", &[arg1, arg2])?,
                CellRepr::Sub(arg1, arg2) => write_cell(f, "sub", &[arg1, arg2])?,
                // CellRepr::Mul(arg1, arg2) => todo!(),
                // CellRepr::UDiv(arg1, arg2) => todo!(),
                // CellRepr::UMod(arg1, arg2) => todo!(),
                // CellRepr::SDivTrunc(arg1, arg2) => todo!(),
                // CellRepr::SDivFloor(arg1, arg2) => todo!(),
                // CellRepr::SModTrunc(arg1, arg2) => todo!(),
                // CellRepr::SModFloor(arg1, arg2) => todo!(),

                // CellRepr::Eq(arg1, arg2) => todo!(),
                // CellRepr::ULt(arg1, arg2) => todo!(),
                // CellRepr::SLt(arg1, arg2) => todo!(),

                // CellRepr::Shl(arg1, arg2, stride) => todo!(),
                // CellRepr::UShr(arg1, arg2, stride) => todo!(),
                // CellRepr::SShr(arg1, arg2, stride) => todo!(),
                // CellRepr::XShr(arg1, arg2, stride) => todo!(),

                // CellRepr::Dff(flip_flop) => todo!(),
                // CellRepr::Iob(io_buffer) => todo!(),
                // CellRepr::Other(instance) => todo!(),

                CellRepr::TopInput(name, _size) => write!(f, "top_input {:?}", name)?,
                CellRepr::TopOutput(name, value) => {
                    write!(f, "top_output {:?} ", name)?;
                    write_value(f, value)?;
                }

                _ => write!(f, "<unprintable>")?,
            }

            write!(f, "\n")?;
        }

        write!(f, "\n")
    }
}
