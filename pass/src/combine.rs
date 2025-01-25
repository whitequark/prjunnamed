use prjunnamed_netlist::{CellRepr, Design};

pub fn combine(design: &mut Design) {
    for cell_ref in design.iter_cells() {
        match &*cell_ref.repr() {
            CellRepr::Buf(arg) => design.replace_value(&cell_ref.output(), arg),
            _ => (),
        }
    }
    design.apply();
}
