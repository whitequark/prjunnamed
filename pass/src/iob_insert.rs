use prjunnamed_netlist::{Design, CellRepr, IoBuffer, Value, Net, ControlNet};

pub fn iob_insert(design: &mut Design) {
    for cell in design.iter_cells() {
        match &*cell.repr() {
            CellRepr::Input(name, width) => {
                cell.replace(CellRepr::Iob(IoBuffer {
                    io: design.add_io(name, *width),
                    output: Value::undef(*width),
                    enable: ControlNet::Pos(Net::ZERO),
                }));
            }
            CellRepr::Output(name, value) => {
                design.add_iob(IoBuffer {
                    io: design.add_io(name, value.len()),
                    output: value.clone(),
                    enable: ControlNet::Pos(Net::ONE)
                });
                cell.unalive();
            }
            _ => (),
        }
    }
    design.apply();
}
