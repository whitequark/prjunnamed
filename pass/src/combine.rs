use prjunnamed_netlist::{CellRepr, Design};

use crate::replacer::Replacer;

pub fn combine(design: &mut Design) {
    let mut design_index = Replacer::new(design);
    for cell_ref in design.iter_cells() {
        match &*cell_ref.repr() {
            CellRepr::Buf(arg) => design_index.replace_value(&cell_ref.output(), arg),
            _ => (),
        }
    }
    design_index.apply(design);
}
