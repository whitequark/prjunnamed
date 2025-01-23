use json::JsonValue;
use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
};

use crate::yosys::{self, CellDetails, NetDetails, PortDetails};
use prjunnamed_netlist::{CellRepr, ControlNet, Design, IoNet, IoValue, Net, Trit, Value};

struct Counter(usize);

impl Counter {
    fn advance(&mut self) -> usize {
        let index = self.0;
        self.0 += 1;
        index
    }
}

struct NetlistIndexerState {
    map: BTreeMap<Net, usize>,
    io_map: BTreeMap<IoNet, usize>,
    next: Counter,
}

struct NetlistIndexer(RefCell<NetlistIndexerState>);

impl NetlistIndexer {
    fn new() -> NetlistIndexer {
        NetlistIndexer(RefCell::new(NetlistIndexerState {
            map: BTreeMap::new(),
            io_map: BTreeMap::new(),
            next: Counter(2), // "to avoid confusion", as write_json claims
        }))
    }

    fn net(&self, net: Net) -> yosys::Bit {
        match net.as_const() {
            Some(Trit::Undef) => yosys::Bit::Undef,
            Some(Trit::Zero) => yosys::Bit::Zero,
            Some(Trit::One) => yosys::Bit::One,
            None => {
                let state = &mut *self.0.borrow_mut();
                yosys::Bit::Net(*state.map.entry(net).or_insert_with(|| state.next.advance()))
            }
        }
    }

    fn value(&self, value: &Value) -> yosys::BitVector {
        yosys::BitVector(value.into_iter().map(|n| self.net(n)).collect::<Vec<_>>())
    }

    fn io_net(&self, net: IoNet) -> yosys::Bit {
        let state = &mut *self.0.borrow_mut();
        yosys::Bit::Net(*state.io_map.entry(net).or_insert_with(|| state.next.advance()))
    }

    fn io_value(&self, value: &IoValue) -> yosys::BitVector {
        yosys::BitVector(value.into_iter().map(|n| self.io_net(n)).collect::<Vec<_>>())
    }

    fn synthetic(&self) -> yosys::Bit {
        yosys::Bit::Net(self.0.borrow_mut().next.advance())
    }
}

fn export_module(design: Design) -> yosys::Module {
    let indexer = NetlistIndexer::new();
    let mut ys_module = yosys::Module::new();

    for (cell_index, cell_ref) in design.iter_cells().enumerate() {
        let output = cell_ref.output();

        let ys_cell_name = format!("${}", cell_index);

        let ys_cell_unary = |module: &mut yosys::Module, ty: &str, a: &Value| {
            CellDetails::new(ty)
                .param("A_SIGNED", 0)
                .param("A_WIDTH", a.len())
                .param("Y_WIDTH", output.len())
                .input("A", indexer.value(a))
                .output("Y", indexer.value(&output))
                .add_to(&format!("${}", cell_index), module)
        };

        let ys_cell_binary = |module: &mut yosys::Module, ty: &str, a: &Value, b: &Value, signed: bool| {
            CellDetails::new(ty)
                .param("A_SIGNED", if signed { 1 } else { 0 })
                .param("A_WIDTH", a.len())
                .param("B_SIGNED", if signed { 1 } else { 0 })
                .param("B_WIDTH", b.len())
                .param("Y_WIDTH", output.len())
                .input("A", indexer.value(a))
                .input("B", indexer.value(b))
                .output("Y", indexer.value(&output))
                .add_to(&format!("${}", cell_index), module)
        };

        match cell_ref.repr().as_ref() {
            CellRepr::Buf(arg) => ys_cell_unary(&mut ys_module, "$pos", arg),
            CellRepr::Not(arg) => ys_cell_unary(&mut ys_module, "$not", arg),

            CellRepr::And(arg1, arg2) => ys_cell_binary(&mut ys_module, "$and", arg1, arg2, false),
            CellRepr::Or(arg1, arg2) => ys_cell_binary(&mut ys_module, "$or", arg1, arg2, false),
            CellRepr::Xor(arg1, arg2) => ys_cell_binary(&mut ys_module, "$xor", arg1, arg2, false),
            CellRepr::Mux(arg1, arg2, arg3) => CellDetails::new("$mux")
                .param("WIDTH", output.len())
                .input("A", indexer.value(arg3))
                .input("B", indexer.value(arg2))
                .input("S", indexer.net(*arg1))
                .output("Y", indexer.value(&output))
                .add_to(&format!("${}", cell_index), &mut ys_module),

            CellRepr::Add(arg1, arg2) => ys_cell_binary(&mut ys_module, "$add", arg1, arg2, false),
            CellRepr::Sub(arg1, arg2) => ys_cell_binary(&mut ys_module, "$sub", arg1, arg2, false),
            CellRepr::Mul(arg1, arg2) => ys_cell_binary(&mut ys_module, "$mul", arg1, arg2, false),
            CellRepr::UDiv(arg1, arg2) => ys_cell_binary(&mut ys_module, "$div", arg1, arg2, false),
            CellRepr::UMod(arg1, arg2) => ys_cell_binary(&mut ys_module, "$mod", arg1, arg2, false),
            CellRepr::SDivTrunc(arg1, arg2) => ys_cell_binary(&mut ys_module, "$div", arg1, arg2, true),
            CellRepr::SDivFloor(arg1, arg2) => ys_cell_binary(&mut ys_module, "$divfloor", arg1, arg2, true),
            CellRepr::SModTrunc(arg1, arg2) => ys_cell_binary(&mut ys_module, "$mod", arg1, arg2, true),
            CellRepr::SModFloor(arg1, arg2) => ys_cell_binary(&mut ys_module, "$modfloor", arg1, arg2, true),

            CellRepr::Eq(arg1, arg2) => ys_cell_binary(&mut ys_module, "$eq", arg1, arg2, false),
            CellRepr::ULt(arg1, arg2) => ys_cell_binary(&mut ys_module, "$lt", arg1, arg2, false),
            CellRepr::SLt(arg1, arg2) => ys_cell_binary(&mut ys_module, "$lt", arg1, arg2, true),

            CellRepr::Shl(_arg1, _arg2, _stride) => todo!(),
            CellRepr::UShr(_arg1, _arg2, _stride) => todo!(),
            CellRepr::SShr(_arg1, _arg2, _stride) => todo!(),
            CellRepr::XShr(_arg1, _arg2, _stride) => todo!(),

            CellRepr::Dff(flip_flop) => {
                // Support for this case requires emulating synchronous reset using a mux.
                assert!(
                    !(flip_flop.clear.is_used() && flip_flop.reset.is_used()),
                    "Flip-flops with both synchronous and asyncrhonous reset are not implemented for Yosys JSON export"
                );
                let ys_cell = if flip_flop.clear.is_used() {
                    CellDetails::new("$adffe")
                        .param("ARST_POLARITY", flip_flop.clear.is_positive())
                        .param("ARST_VALUE", flip_flop.clear_value.clone())
                        .input("ARST", indexer.net(flip_flop.clear.net()))
                } else {
                    CellDetails::new(if flip_flop.reset_over_enable { "$sdffe" } else { "$sdffce" })
                        .param("SRST_POLARITY", flip_flop.reset.is_positive())
                        .param("SRST_VALUE", flip_flop.reset_value.clone())
                        .input("SRST", indexer.net(flip_flop.reset.net()))
                };
                ys_cell
                    .param("EN_POLARITY", flip_flop.enable.is_positive())
                    .input("EN", indexer.net(flip_flop.enable.net()))
                    .param("CLK_POLARITY", flip_flop.clock.is_positive())
                    .input("CLK", indexer.net(flip_flop.clock.net()))
                    .param("WIDTH", output.len())
                    .input("D", indexer.value(&flip_flop.data))
                    .output("Q", indexer.value(&output))
                    .add_to(&ys_cell_name, &mut ys_module);
                NetDetails::new(indexer.value(&output))
                    .attr("init", flip_flop.init_value.clone())
                    .add_to(&format!("{}$out", ys_cell_name), &mut ys_module);
            }

            CellRepr::Iob(io_buffer) => {
                let ys_enable = match io_buffer.enable {
                    ControlNet::Pos(net) => indexer.net(net),
                    ControlNet::Neg(net) => {
                        let ys_enable_neg = indexer.synthetic();
                        CellDetails::new("$not")
                            .param("A_SIGNED", 0)
                            .param("A_WIDTH", 1)
                            .param("Y_WIDTH", output.len())
                            .input("A", indexer.value(&net.into()))
                            .output("Y", ys_enable_neg)
                            .add_to(&format!("${}$not", cell_index), &mut ys_module);
                        ys_enable_neg
                    }
                };
                CellDetails::new("$tribuf")
                    .param("WIDTH", output.len())
                    .input("A", indexer.value(&io_buffer.output))
                    .input("EN", ys_enable)
                    .output("Y", indexer.io_value(&io_buffer.io))
                    .add_to(&format!("${}", cell_index), &mut ys_module);
                CellDetails::new("$pos")
                    .param("A_SIGNED", 0)
                    .param("A_WIDTH", io_buffer.io.len())
                    .param("Y_WIDTH", output.len())
                    .input("A", indexer.io_value(&io_buffer.io))
                    .output("Y", indexer.value(&output))
                    .add_to(&format!("${}$pos", cell_index), &mut ys_module);
            }

            CellRepr::Other(instance) => {
                let mut ys_cell = CellDetails::new(&format!("\\{}", instance.reference));
                for (name, value) in instance.parameters.iter() {
                    ys_cell = ys_cell.param(&name, value);
                }
                for (name, value) in instance.inputs.iter() {
                    ys_cell = ys_cell.input(&name, indexer.value(&value));
                }
                for (name, value_range) in instance.outputs.iter() {
                    ys_cell = ys_cell.output(&name, indexer.value(&Value::from(&output[value_range.clone()])));
                }
                for (name, io_value) in instance.ios.iter() {
                    ys_cell = ys_cell.inout(&name, indexer.io_value(&io_value));
                }
                ys_cell.add_to(&ys_cell_name, &mut ys_module);
            }

            CellRepr::TopInput(port_name, _size) => {
                ys_module.ports.add(port_name, PortDetails::new(yosys::PortDirection::Input, indexer.value(&output)))
            }
            CellRepr::TopOutput(port_name, value) => {
                ys_module.ports.add(port_name, PortDetails::new(yosys::PortDirection::Output, indexer.value(value)))
            }
        };

        NetDetails::new(indexer.value(&output))
            .add_to(&format!("{}$out", ys_cell_name), &mut ys_module);
    }

    ys_module
}

pub fn export(writer: &mut impl std::io::Write, designs: HashMap<String, Design>) -> std::io::Result<()> {
    let mut ys_modules = HashMap::new();
    for (name, design) in designs {
        ys_modules.insert(name, export_module(design));
    }
    let ys_design = yosys::Design { creator: "prjunnamed".into(), modules: ys_modules.into() };

    let json = JsonValue::from(ys_design);
    json.write_pretty(writer, /*spaces=*/ 4)
}
