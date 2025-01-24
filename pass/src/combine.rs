use prjunnamed_netlist::{CellRepr, Design};

pub fn combine(design: &mut Design) {
    let mut replacer = design.replace_cells();
    for cell_ref in design.iter_cells() {
        match &*cell_ref.repr() {
            CellRepr::Buf(arg) => replacer.value(&cell_ref.output(), arg),
            _ => (),
        }
    }
    replacer.apply(design);
}
