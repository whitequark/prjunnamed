use std::collections::{btree_set, BTreeMap, BTreeSet};

use prjunnamed_netlist::{CellIndex, Design, Net, Value};

pub struct Replacer {
    net_uses: BTreeMap<Net, BTreeSet<CellIndex>>,
    replace_cells: BTreeSet<CellIndex>,
    replace_nets: BTreeMap<Net, Net>,
}

impl Replacer {
    pub fn new(design: &Design) -> Replacer {
        let mut replacer = Replacer {
            net_uses: BTreeMap::new(),
            replace_cells: BTreeSet::new(),
            replace_nets: BTreeMap::new(),
        };
        for cell_ref in design.iter_cells() {
            cell_ref.visit(|net| {
                replacer.net_uses.entry(net).or_default().insert(cell_ref.index());
                ();
            });
        }
        replacer
    }

    #[allow(dead_code)]
    pub fn iter_uses(&self, net: Net) -> NetUseIter {
        NetUseIter(self.net_uses.get(&net).map(|entry| entry.iter()))
    }

    pub fn replace_net(&mut self, from_net: Net, to_net: Net) {
        if let Some(uses) = self.net_uses.get(&from_net) {
            self.replace_cells.extend(uses);
        }
        let already_replaced = self.replace_nets.insert(from_net, to_net).is_some();
        assert!(!already_replaced);
    }

    pub fn replace_value(&mut self, from_value: &Value, to_value: &Value) {
        assert_eq!(from_value.len(), to_value.len());
        for (from_net, to_net) in from_value.into_iter().zip(to_value.into_iter()) {
            self.replace_net(from_net, to_net);
        }
    }

    pub fn apply(&self, design: &mut Design) {
        for &cell_index in self.replace_cells.iter() {
            design.visit_cell_mut(cell_index, |net| {
                if let Some(new_net) = self.replace_nets.get(net) {
                    *net = *new_net;
                }
            });
        }
    }
}

#[derive(Debug)]
pub struct NetUseIter<'a>(Option<btree_set::Iter<'a, CellIndex>>);

impl<'a> Iterator for NetUseIter<'a> {
    type Item = CellIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().and_then(|iter| iter.next()).map(|item| *item)
    }
}
