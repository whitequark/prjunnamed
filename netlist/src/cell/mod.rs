use std::{borrow::Cow, hash::Hash};

use crate::{Const, Design, Net, Trit, Value};

mod flip_flop;
mod memory;
mod io_buffer;
mod target;
mod instance;

pub use flip_flop::FlipFlop;
pub use memory::{Memory, MemoryWritePort, MemoryReadPort, MemoryReadFlipFlop, MemoryPortRelation};
pub use io_buffer::IoBuffer;
pub use target::TargetCell;
pub use instance::Instance;

// Space-optimized representation of a cell, for compact AIGs.
#[derive(Debug, Clone)]
pub(crate) enum Cell {
    Void,
    Skip(u32),

    Buf(Net),
    Not(Net),
    And(Net, Net),
    Or(Net, Net),
    Xor(Net, Net),
    Mux(Net, Net, Net), // a ? b : c
    Adc(Net, Net, Net), // a + b + ci

    Coarse(Box<CellRepr>),
}

// General representation of a cell. Canonicalized to use a space-optimized representation
// wherever possible.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CellRepr {
    Buf(Value),
    Not(Value),
    And(Value, Value),
    Or(Value, Value),
    Xor(Value, Value),
    Mux(Net, Value, Value), // a ? b : c
    Adc(Value, Value, Net), // a + b + ci

    Eq(Value, Value),
    ULt(Value, Value),
    SLt(Value, Value),

    Shl(Value, Value, u32),
    UShr(Value, Value, u32),
    SShr(Value, Value, u32),
    XShr(Value, Value, u32),

    // future possibilities: popcnt, count leading/trailing zeros, powers
    Mul(Value, Value),
    UDiv(Value, Value),
    UMod(Value, Value),
    SDivTrunc(Value, Value),
    SDivFloor(Value, Value),
    SModTrunc(Value, Value),
    SModFloor(Value, Value),

    Dff(FlipFlop),
    Memory(Memory),
    Iob(IoBuffer),
    Target(TargetCell),
    Other(Instance),

    Input(String, usize),
    Output(String, Value),
    Name(String, Value),
}

impl CellRepr {
    pub fn validate(&self, design: &Design) {
        match self {
            CellRepr::Buf(_) => (),
            CellRepr::Not(_) => (),
            CellRepr::And(arg1, arg2)
            | CellRepr::Or(arg1, arg2)
            | CellRepr::Xor(arg1, arg2)
            | CellRepr::Mux(_, arg1, arg2)
            | CellRepr::Adc(arg1, arg2, _)
            | CellRepr::Eq(arg1, arg2)
            | CellRepr::ULt(arg1, arg2)
            | CellRepr::Mul(arg1, arg2)
            | CellRepr::UDiv(arg1, arg2)
            | CellRepr::UMod(arg1, arg2) => assert_eq!(arg1.len(), arg2.len()),
            CellRepr::SLt(arg1, arg2)
            | CellRepr::SDivTrunc(arg1, arg2)
            | CellRepr::SDivFloor(arg1, arg2)
            | CellRepr::SModTrunc(arg1, arg2)
            | CellRepr::SModFloor(arg1, arg2) => {
                assert_eq!(arg1.len(), arg2.len());
                assert!(arg1.len() > 0);
            }

            CellRepr::Shl(_, _, _) => (),
            CellRepr::UShr(_, _, _) => (),
            CellRepr::SShr(arg1, _, _) => assert!(arg1.len() > 0),
            CellRepr::XShr(_, _, _) => (),

            CellRepr::Dff(flip_flop) => {
                assert_eq!(flip_flop.data.len(), flip_flop.init_value.len());
                assert_eq!(flip_flop.data.len(), flip_flop.clear_value.len());
                assert_eq!(flip_flop.data.len(), flip_flop.reset_value.len());
            }
            CellRepr::Memory(memory) => {
                assert_eq!(memory.init_value.len(), memory.depth * memory.width);
                for port in &memory.write_ports {
                    assert_eq!(port.data.len(), port.mask.len());
                    if memory.width == 0 {
                        assert_eq!(port.data.len(), 0);
                    } else {
                        assert_eq!(port.data.len() % memory.width, 0);
                        let wide_factor = port.data.len() / memory.width;
                        assert!(wide_factor.is_power_of_two());
                        assert_eq!(memory.depth % wide_factor, 0);
                    }
                }
                for port in &memory.read_ports {
                    if memory.width == 0 {
                        assert_eq!(port.data_len, 0);
                    } else {
                        assert_eq!(port.data_len % memory.width, 0);
                        let wide_factor = port.data_len / memory.width;
                        assert!(wide_factor.is_power_of_two());
                        assert_eq!(memory.depth % wide_factor, 0);
                    }
                    if let Some(ref flip_flop) = port.flip_flop {
                        assert_eq!(flip_flop.clear_value.len(), port.data_len);
                        assert_eq!(flip_flop.reset_value.len(), port.data_len);
                        assert_eq!(flip_flop.init_value.len(), port.data_len);
                        assert_eq!(flip_flop.relations.len(), memory.write_ports.len());
                        for (write_port_index, &relation) in flip_flop.relations.iter().enumerate() {
                            if relation != MemoryPortRelation::Undefined {
                                assert_eq!(memory.write_ports[write_port_index].clock, flip_flop.clock);
                            }
                        }
                    }
                }
            }
            CellRepr::Iob(io_buffer) => {
                assert_eq!(io_buffer.output.len(), io_buffer.io.len());
            }
            CellRepr::Target(target_cell) => {
                let prototype = design.target_prototype(target_cell);
                assert_eq!(target_cell.params.len(), prototype.params.len());
                for (param, value) in prototype.params.iter().zip(target_cell.params.iter()) {
                    assert!(param.kind.is_valid(value));
                }
                assert_eq!(target_cell.inputs.len(), prototype.input_len);
                assert_eq!(target_cell.output_len, prototype.output_len);
                assert_eq!(target_cell.ios.len(), prototype.io_len);
                let target = design.target().unwrap();
                target.validate(design, target_cell);
            }
            CellRepr::Other(_instance) => {
                // TODO
            }
            CellRepr::Input(_, _) => (),
            CellRepr::Output(_, _) => (),
            CellRepr::Name(_, _) => (),
        }
    }

    pub fn slice(&self, range: impl std::ops::RangeBounds<usize> + Clone) -> Option<CellRepr> {
        match self {
            CellRepr::Buf(arg) => Some(CellRepr::Buf(arg.slice(range))),
            CellRepr::Not(arg) => Some(CellRepr::Not(arg.slice(range))),
            CellRepr::And(arg1, arg2) => Some(CellRepr::And(arg1.slice(range.clone()), arg2.slice(range))),
            CellRepr::Or(arg1, arg2) => Some(CellRepr::Or(arg1.slice(range.clone()), arg2.slice(range))),
            CellRepr::Xor(arg1, arg2) => Some(CellRepr::Xor(arg1.slice(range.clone()), arg2.slice(range))),
            CellRepr::Mux(arg1, arg2, arg3) => Some(CellRepr::Mux(*arg1, arg2.slice(range.clone()), arg3.slice(range))),
            CellRepr::Dff(flip_flop) => Some(CellRepr::Dff(flip_flop.slice(range))),
            CellRepr::Iob(io_buffer) => Some(CellRepr::Iob(io_buffer.slice(range))),
            _ => None,
        }
    }
}

impl<'a> From<&'a CellRepr> for Cow<'a, CellRepr> {
    fn from(value: &'a CellRepr) -> Self {
        Cow::Borrowed(value)
    }
}

impl From<CellRepr> for Cow<'_, CellRepr> {
    fn from(value: CellRepr) -> Self {
        Cow::Owned(value)
    }
}

impl Cell {
    pub fn repr<'a>(&'a self) -> Cow<'a, CellRepr> {
        match *self {
            Cell::Void | Cell::Skip(_) => unreachable!(),

            Cell::Buf(arg) => Cow::Owned(CellRepr::Buf(Value::from(arg))),
            Cell::Not(arg) => Cow::Owned(CellRepr::Not(Value::from(arg))),
            Cell::And(arg1, arg2) => Cow::Owned(CellRepr::And(Value::from(arg1), Value::from(arg2))),
            Cell::Or(arg1, arg2) => Cow::Owned(CellRepr::Or(Value::from(arg1), Value::from(arg2))),
            Cell::Xor(arg1, arg2) => Cow::Owned(CellRepr::Xor(Value::from(arg1), Value::from(arg2))),
            Cell::Mux(arg1, arg2, arg3) => Cow::Owned(CellRepr::Mux(arg1, Value::from(arg2), Value::from(arg3))),
            Cell::Adc(arg1, arg2, arg3) => Cow::Owned(CellRepr::Adc(Value::from(arg1), Value::from(arg2), arg3)),

            Cell::Coarse(ref coarse) => Cow::Borrowed(coarse),
        }
    }
}

impl From<CellRepr> for Cell {
    fn from(value: CellRepr) -> Self {
        match value {
            CellRepr::Buf(arg) if arg.len() == 1 => Cell::Buf(arg[0]),
            CellRepr::Not(arg) if arg.len() == 1 => Cell::Not(arg[0]),
            CellRepr::And(arg1, arg2) if arg1.len() == 1 && arg2.len() == 1 => Cell::And(arg1[0], arg2[0]),
            CellRepr::Or(arg1, arg2) if arg1.len() == 1 && arg2.len() == 1 => Cell::Or(arg1[0], arg2[0]),
            CellRepr::Xor(arg1, arg2) if arg1.len() == 1 && arg2.len() == 1 => Cell::Xor(arg1[0], arg2[0]),
            CellRepr::Mux(arg1, arg2, arg3) if arg2.len() == 1 && arg3.len() == 1 => Cell::Mux(arg1, arg2[0], arg3[0]),
            CellRepr::Adc(arg1, arg2, arg3) if arg1.len() == 1 && arg2.len() == 1 => Cell::Adc(arg1[0], arg2[0], arg3),

            coarse => Cell::Coarse(Box::new(coarse)),
        }
    }
}

impl Cell {
    pub fn output_len(&self) -> usize {
        match self {
            Cell::Void | Cell::Skip(_) => unreachable!(),

            Cell::Buf(_) | Cell::Not(_) | Cell::And(_, _) | Cell::Or(_, _) | Cell::Xor(_, _) | Cell::Mux(_, _, _) => 1,
            Cell::Adc(_, _, _) => 2,

            Cell::Coarse(coarse) => coarse.output_len(),
        }
    }

    pub(crate) fn visit(&self, mut f: impl FnMut(Net)) {
        match self {
            Cell::Void | Cell::Skip(_) => unreachable!(),
            Cell::Buf(arg) | Cell::Not(arg) => arg.visit(&mut f),
            Cell::And(arg1, arg2) | Cell::Or(arg1, arg2) | Cell::Xor(arg1, arg2) => {
                arg1.visit(&mut f);
                arg2.visit(&mut f);
            }
            Cell::Mux(arg1, arg2, arg3) | Cell::Adc(arg1, arg2, arg3) => {
                arg1.visit(&mut f);
                arg2.visit(&mut f);
                arg3.visit(&mut f);
            }
            Cell::Coarse(coarse) => coarse.visit(&mut f),
        }
    }

    pub(crate) fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        match self {
            Cell::Void | Cell::Skip(_) => unreachable!(),
            Cell::Buf(arg) | Cell::Not(arg) => arg.visit_mut(&mut f),
            Cell::And(arg1, arg2) | Cell::Or(arg1, arg2) | Cell::Xor(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            Cell::Mux(arg1, arg2, arg3) | Cell::Adc(arg1, arg2, arg3) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
                arg3.visit_mut(&mut f);
            }
            Cell::Coarse(coarse) => coarse.visit_mut(&mut f),
        }
    }
}

impl CellRepr {
    pub fn output_len(&self) -> usize {
        match self {
            CellRepr::Buf(arg) | CellRepr::Not(arg) => arg.len(),
            CellRepr::And(arg1, arg2)
            | CellRepr::Or(arg1, arg2)
            | CellRepr::Xor(arg1, arg2)
            | CellRepr::Mux(_, arg1, arg2) => {
                debug_assert_eq!(arg1.len(), arg2.len());
                arg1.len()
            }
            CellRepr::Adc(arg1, arg2, _) => {
                debug_assert_eq!(arg1.len(), arg2.len());
                arg1.len() + 1
            }

            CellRepr::Eq(_arg1, _arg2) => 1,
            CellRepr::ULt(_arg1, _arg2) => 1,
            CellRepr::SLt(_arg1, _arg2) => 1,

            CellRepr::Shl(arg1, _, _)
            | CellRepr::UShr(arg1, _, _)
            | CellRepr::SShr(arg1, _, _)
            | CellRepr::XShr(arg1, _, _) => arg1.len(),

            CellRepr::Mul(arg1, arg2)
            | CellRepr::UDiv(arg1, arg2)
            | CellRepr::UMod(arg1, arg2)
            | CellRepr::SDivTrunc(arg1, arg2)
            | CellRepr::SDivFloor(arg1, arg2)
            | CellRepr::SModTrunc(arg1, arg2)
            | CellRepr::SModFloor(arg1, arg2) => {
                debug_assert_eq!(arg1.len(), arg2.len());
                arg1.len()
            }

            CellRepr::Dff(flip_flop) => flip_flop.output_len(),
            CellRepr::Memory(memory) => memory.output_len(),
            CellRepr::Iob(io_buffer) => io_buffer.output_len(),
            CellRepr::Target(target_cell) => target_cell.output_len,
            CellRepr::Other(instance) => instance.output_len(),

            CellRepr::Input(_, width) => *width as usize,
            CellRepr::Output(_, _) => 0,
            CellRepr::Name(_, _) => 0,
        }
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        match self {
            CellRepr::Input(_, _) => (),
            CellRepr::Buf(arg) | CellRepr::Not(arg) | CellRepr::Output(_, arg) | CellRepr::Name(_, arg) => {
                arg.visit(&mut f)
            }
            CellRepr::And(arg1, arg2)
            | CellRepr::Or(arg1, arg2)
            | CellRepr::Xor(arg1, arg2)
            | CellRepr::Mul(arg1, arg2)
            | CellRepr::UDiv(arg1, arg2)
            | CellRepr::UMod(arg1, arg2)
            | CellRepr::SDivTrunc(arg1, arg2)
            | CellRepr::SDivFloor(arg1, arg2)
            | CellRepr::SModTrunc(arg1, arg2)
            | CellRepr::SModFloor(arg1, arg2)
            | CellRepr::Eq(arg1, arg2)
            | CellRepr::ULt(arg1, arg2)
            | CellRepr::SLt(arg1, arg2)
            | CellRepr::Shl(arg1, arg2, _)
            | CellRepr::UShr(arg1, arg2, _)
            | CellRepr::SShr(arg1, arg2, _)
            | CellRepr::XShr(arg1, arg2, _) => {
                arg1.visit(&mut f);
                arg2.visit(&mut f);
            }
            CellRepr::Mux(net, value1, value2) | CellRepr::Adc(value1, value2, net) => {
                value1.visit(&mut f);
                value2.visit(&mut f);
                net.visit(&mut f);
            }
            CellRepr::Dff(flip_flop) => flip_flop.visit(&mut f),
            CellRepr::Memory(memory) => memory.visit(&mut f),
            CellRepr::Iob(io_buffer) => io_buffer.visit(&mut f),
            CellRepr::Target(target_cell) => target_cell.visit(&mut f),
            CellRepr::Other(instance) => instance.visit(&mut f),
        }
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        match self {
            CellRepr::Input(_, _) => (),
            CellRepr::Buf(arg) | CellRepr::Not(arg) | CellRepr::Output(_, arg) | CellRepr::Name(_, arg) => {
                arg.visit_mut(&mut f)
            }
            CellRepr::And(arg1, arg2)
            | CellRepr::Or(arg1, arg2)
            | CellRepr::Xor(arg1, arg2)
            | CellRepr::Mul(arg1, arg2)
            | CellRepr::UDiv(arg1, arg2)
            | CellRepr::UMod(arg1, arg2)
            | CellRepr::SDivTrunc(arg1, arg2)
            | CellRepr::SDivFloor(arg1, arg2)
            | CellRepr::SModTrunc(arg1, arg2)
            | CellRepr::SModFloor(arg1, arg2)
            | CellRepr::Eq(arg1, arg2)
            | CellRepr::ULt(arg1, arg2)
            | CellRepr::SLt(arg1, arg2)
            | CellRepr::Shl(arg1, arg2, _)
            | CellRepr::UShr(arg1, arg2, _)
            | CellRepr::SShr(arg1, arg2, _)
            | CellRepr::XShr(arg1, arg2, _) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Mux(net, value1, value2) | CellRepr::Adc(value1, value2, net) => {
                value1.visit_mut(&mut f);
                value2.visit_mut(&mut f);
                net.visit_mut(&mut f);
            }
            CellRepr::Dff(flip_flop) => flip_flop.visit_mut(&mut f),
            CellRepr::Memory(memory) => memory.visit_mut(&mut f),
            CellRepr::Iob(io_buffer) => io_buffer.visit_mut(&mut f),
            CellRepr::Target(target_cell) => target_cell.visit_mut(&mut f),
            CellRepr::Other(instance) => instance.visit_mut(&mut f),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ParamValue {
    Const(Const),
    Int(i64),
    Float(f64),
    String(String),
}

impl From<Const> for ParamValue {
    fn from(value: Const) -> Self {
        Self::Const(value)
    }
}

impl From<&Const> for ParamValue {
    fn from(value: &Const) -> Self {
        Self::Const(value.clone())
    }
}

impl From<bool> for ParamValue {
    fn from(value: bool) -> Self {
        Self::Const(Trit::from(value).into())
    }
}

impl From<Trit> for ParamValue {
    fn from(value: Trit) -> Self {
        Self::Const(value.into())
    }
}

impl From<i64> for ParamValue {
    fn from(value: i64) -> Self {
        Self::Int(value)
    }
}

impl From<&str> for ParamValue {
    fn from(value: &str) -> Self {
        Self::String(value.into())
    }
}

impl From<String> for ParamValue {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl PartialEq for ParamValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(lft), Self::Const(rgt)) => lft == rgt,
            (Self::Int(lft), Self::Int(rgt)) => lft == rgt,
            (Self::Float(lft), Self::Float(rgt)) => lft.to_bits() == rgt.to_bits(),
            (Self::String(lft), Self::String(rgt)) => lft == rgt,
            _ => false,
        }
    }
}

impl Eq for ParamValue {}

impl Hash for ParamValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            ParamValue::Const(val) => val.hash(state),
            ParamValue::Int(val) => val.hash(state),
            ParamValue::Float(val) => val.to_bits().hash(state),
            ParamValue::String(val) => val.hash(state),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::cell::Cell;

    #[test]
    fn test_size() {
        assert!(size_of::<Cell>() == 16);
    }
}
