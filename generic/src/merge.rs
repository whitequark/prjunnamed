use std::{borrow::Cow, collections::HashMap};

use prjunnamed_netlist::{Cell, Design, Value};

struct Numberer(HashMap<Cell, Value>);

impl Numberer {
    fn new() -> Self {
        Numberer(HashMap::new())
    }

    fn find_or_insert<'a>(&mut self, cell: Cell, value: impl Into<Cow<'a, Value>>) -> Value {
        self.0.entry(cell).or_insert_with(|| value.into().into_owned()).clone()
    }

    fn bitwise_unary<F>(&mut self, rebuild: F, arg: Value, out: &Value) -> Value
    where
        F: Fn(Value) -> Cell,
    {
        let mut result = Value::EMPTY;
        for (out_net, arg_net) in out.iter().zip(arg.iter()) {
            let bit_cell = rebuild(Value::from(arg_net));
            result.extend(self.find_or_insert(bit_cell, out_net));
        }
        result
    }

    fn commutative_bitwise_binary<F>(&mut self, rebuild: F, arg1: Value, arg2: Value, out: &Value) -> Value
    where
        F: Fn(Value, Value) -> Cell,
    {
        let mut result = Value::EMPTY;
        for (out_net, (arg1_net, arg2_net)) in out.iter().zip(arg1.iter().zip(arg2.iter())) {
            let (arg1_net, arg2_net) = if arg1_net <= arg2_net { (arg1_net, arg2_net) } else { (arg2_net, arg1_net) };
            let bit_cell = rebuild(Value::from(arg1_net), Value::from(arg2_net));
            result.extend(self.find_or_insert(bit_cell, out_net));
        }
        result
    }

    fn bitwise_binary<F>(&mut self, rebuild: F, arg1: Value, arg2: Value, out: &Value) -> Value
    where
        F: Fn(Value, Value) -> Cell,
    {
        let mut result = Value::EMPTY;
        for (out_net, (arg1_net, arg2_net)) in out.iter().zip(arg1.iter().zip(arg2.iter())) {
            let bit_cell = rebuild(Value::from(arg1_net), Value::from(arg2_net));
            result.extend(self.find_or_insert(bit_cell, out_net));
        }
        result
    }

    fn commutative_binary<F>(&mut self, rebuild: F, arg1: Value, arg2: Value, out: &Value) -> Value
    where
        F: Fn(Value, Value) -> Cell,
    {
        let (arg1, arg2) = if arg1 <= arg2 { (arg1, arg2) } else { (arg2, arg1) };
        let cell = rebuild(arg1, arg2);
        self.find_or_insert(cell, out)
    }
}

pub fn merge(design: &mut Design) -> bool {
    let mut numberer = Numberer::new();
    for cell_ref in design.iter_cells_topo().filter(|cell_ref| cell_ref.get().has_effects(design)) {
        let mut cell = cell_ref.get().into_owned();
        cell.visit_mut(|net| *net = design.map_net(*net));
        let output = cell_ref.output();
        let canon = match cell {
            Cell::Buf(arg) => numberer.bitwise_unary(Cell::Buf, arg, &output),
            Cell::Not(arg) => numberer.bitwise_unary(Cell::Not, arg, &output),
            Cell::And(arg1, arg2) => numberer.commutative_bitwise_binary(Cell::And, arg1, arg2, &output),
            Cell::Or(arg1, arg2) => numberer.commutative_bitwise_binary(Cell::Or, arg1, arg2, &output),
            Cell::Xor(arg1, arg2) => numberer.commutative_bitwise_binary(Cell::Xor, arg1, arg2, &output),
            Cell::Mux(arg1, arg2, arg3) => {
                numberer.bitwise_binary(|arg2, arg3| Cell::Mux(arg1, arg2, arg3), arg2, arg3, &output)
            }
            Cell::Adc(arg1, arg2, arg3) => {
                numberer.commutative_binary(|arg1, arg2| Cell::Adc(arg1, arg2, arg3), arg1, arg2, &output)
            }
            Cell::Eq(arg1, arg2) => numberer.commutative_binary(Cell::Eq, arg1, arg2, &output),
            Cell::Mul(arg1, arg2) => numberer.commutative_binary(Cell::Mul, arg1, arg2, &output),
            _ => numberer.find_or_insert(cell, output.clone()),
        };
        if cfg!(feature = "trace") {
            if output != canon {
                eprintln!(">merge {} => {}", design.display_value(&output), design.display_value(&canon));
            }
        }
        design.replace_value(output, canon);
    }
    design.compact()
}
