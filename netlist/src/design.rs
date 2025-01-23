use std::borrow::Cow;
use std::collections::{hash_map, HashMap};
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
