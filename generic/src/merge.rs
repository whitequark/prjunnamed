use std::{borrow::Cow, collections::HashMap};

use prjunnamed_netlist::{CellRef, CellRepr, Design, Value};

fn consider_for_merge(cell_ref: &CellRef) -> bool {
    match &*cell_ref.repr() {
        CellRepr::Other(_instance) => false,
        _ => true,
    }
}

struct Numberer(HashMap<CellRepr, Value>);

impl Numberer {
    fn new() -> Self {
        Numberer(HashMap::new())
    }

    fn find_or_insert<'a>(&mut self, cell_repr: CellRepr, value: impl Into<Cow<'a, Value>>) -> Value {
        self.0.entry(cell_repr).or_insert_with(|| value.into().into_owned()).clone()
    }

    fn bitwise_unary<F>(&mut self, rebuild: F, arg: Value, out: &Value) -> Value
    where
        F: Fn(Value) -> CellRepr,
    {
        let mut result = Value::EMPTY;
        for (out_net, arg_net) in out.into_iter().zip(arg.into_iter()) {
            let bit_cell_repr = rebuild(Value::from(arg_net));
            result = result.concat(self.find_or_insert(bit_cell_repr, Value::from(out_net)));
        }
        result
    }

    fn bitwise_binary<F>(&mut self, rebuild: F, arg1: Value, arg2: Value, out: &Value) -> Value
    where
        F: Fn(Value, Value) -> CellRepr,
    {
        let mut result = Value::EMPTY;
        for (out_net, (arg1_net, arg2_net)) in out.into_iter().zip(arg1.into_iter().zip(arg2.into_iter())) {
            let (arg1_net, arg2_net) = if arg1_net <= arg2_net { (arg1_net, arg2_net) } else { (arg2_net, arg1_net) };
            let bit_cell_repr = rebuild(Value::from(arg1_net), Value::from(arg2_net));
            result = result.concat(self.find_or_insert(bit_cell_repr, Value::from(out_net)));
        }
        result
    }

    fn commutative_binary<F>(&mut self, rebuild: F, arg1: Value, arg2: Value, out: &Value) -> Value
    where
        F: Fn(Value, Value) -> CellRepr,
    {
        let (arg1, arg2) = if arg1 <= arg2 { (arg1, arg2) } else { (arg2, arg1) };
        let cell_repr = rebuild(Value::from(arg1), Value::from(arg2));
        self.find_or_insert(cell_repr, out)
    }
}

pub fn merge(design: &mut Design) {
    let mut numberer = Numberer::new();
    for cell_ref in design.iter_cells_topo().filter(consider_for_merge) {
        let mut cell_repr = cell_ref.repr().into_owned();
        cell_repr.visit_mut(|net| *net = design.map_net(*net));
        let output = cell_ref.output();
        let canon = match cell_repr {
            CellRepr::Buf(arg) => numberer.bitwise_unary(CellRepr::Buf, arg, &output),
            CellRepr::Not(arg) => numberer.bitwise_unary(CellRepr::Not, arg, &output),
            CellRepr::And(arg1, arg2) => numberer.bitwise_binary(CellRepr::And, arg1, arg2, &output),
            CellRepr::Or(arg1, arg2) => numberer.bitwise_binary(CellRepr::Or, arg1, arg2, &output),
            CellRepr::Xor(arg1, arg2) => numberer.bitwise_binary(CellRepr::Xor, arg1, arg2, &output),
            CellRepr::Adc(arg1, arg2, arg3) => {
                numberer.commutative_binary(|arg1, arg2| CellRepr::Adc(arg1, arg2, arg3), arg1, arg2, &output)
            }
            CellRepr::Eq(arg1, arg2) => numberer.commutative_binary(CellRepr::Eq, arg1, arg2, &output),
            CellRepr::Mul(arg1, arg2) => numberer.commutative_binary(CellRepr::Mul, arg1, arg2, &output),
            _ => numberer.find_or_insert(cell_repr, output.clone()),
        };
        if cfg!(feature = "trace") {
            if output != canon {
                eprintln!(">merge {} => {}", design.display_value(&output), design.display_value(&canon));
            }
        }
        design.replace_value(output, canon);
    }
    design.compact();
}
