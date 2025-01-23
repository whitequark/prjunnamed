// on design:
// - number of iovalues and naming for that
//

use core::ops::Range;
use std::{borrow::Cow, collections::HashMap};

use crate::{Const, ControlNet, IoValue, Net, Value};

// Space-optimized representation of a cell, for compact AIGs.
#[derive(Debug)]
pub(crate) enum Cell {
    Skip(u32),

    Buf(Net),
    Not(Net),
    And(Net, Net),
    Xor(Net, Net),
    Mux(Net, Net, Net), // a ? b : c

    Coarse(Box<CellRepr>),
}

// General representation of a cell. Canonicalized to use a space-optimized representation
// wherever possible.
#[derive(Clone, Debug)]
pub enum CellRepr {
    Buf(Value),
    Not(Value),
    And(Value, Value),
    Or(Value, Value),
    Xor(Value, Value),
    Mux(Net, Value, Value),

    Add(Value, Value),
    Sub(Value, Value),
    Mul(Value, Value),
    UDiv(Value, Value),
    UMod(Value, Value),
    SDivTrunc(Value, Value),
    SDivFloor(Value, Value),
    SModTrunc(Value, Value),
    SModFloor(Value, Value),

    Eq(Value, Value),
    ULt(Value, Value),
    SLt(Value, Value),

    Shl(Value, Value, u32),
    UShr(Value, Value, u32),
    SShr(Value, Value, u32),
    XShr(Value, Value, u32),

    // future possibilities: popcnt, count leading/trailing zeros, powers

    Dff(FlipFlop),
    Iob(IoBuffer),
    Other(Instance),
    // TODO: memory

    TopInput(String, u32),
    TopOutput(String, Value),
}

impl Cell {
    pub fn repr<'a>(&'a self) -> Cow<'a, CellRepr> {
        match *self {
            Cell::Skip(_) => unreachable!(),

            Cell::Buf(arg) => Cow::Owned(CellRepr::Buf(Value::from(arg))),
            Cell::Not(arg) => Cow::Owned(CellRepr::Not(Value::from(arg))),
            Cell::And(arg1, arg2) => {
                Cow::Owned(CellRepr::And(Value::from(arg1), Value::from(arg2)))
            }
            Cell::Xor(arg1, arg2) => {
                Cow::Owned(CellRepr::Xor(Value::from(arg1), Value::from(arg2)))
            }
            Cell::Mux(arg1, arg2, arg3) => {
                Cow::Owned(CellRepr::Mux(arg1, Value::from(arg2), Value::from(arg3)))
            }

            Cell::Coarse(ref coarse) => Cow::Borrowed(coarse),
        }
    }
}

impl From<CellRepr> for Cell {
    fn from(value: CellRepr) -> Self {
        match value {
            CellRepr::Buf(arg) if arg.len() == 1 => Cell::Buf(arg[0]),
            CellRepr::Not(arg) if arg.len() == 1 => Cell::Not(arg[0]),
            CellRepr::And(arg1, arg2) if arg1.len() == 1 && arg2.len() == 1 => {
                Cell::And(arg1[0], arg2[0])
            }
            CellRepr::Xor(arg1, arg2) if arg1.len() == 1 && arg2.len() == 1 => {
                Cell::Xor(arg1[0], arg2[0])
            }
            CellRepr::Mux(arg1, arg2, arg3) if arg2.len() == 1 && arg3.len() == 1 => {
                Cell::Mux(arg1, arg2[0], arg3[0])
            }

            coarse => Cell::Coarse(Box::new(coarse)),
        }
    }
}

impl Cell {
    pub fn output_len(&self) -> usize {
        match self {
            Cell::Skip(_) => unreachable!(),

            Cell::Buf(_)
            | Cell::Not(_)
            | Cell::And(_, _)
            | Cell::Xor(_, _)
            | Cell::Mux(_, _, _) => 1,

            Cell::Coarse(coarse) => coarse.output_len(),
        }
    }

    pub(crate) fn visit<E>(&self, mut f: impl FnMut(Net) -> Result<(), E>) -> Result<(), E> {
        match self {
            Cell::Skip(_) => unreachable!(),

            Cell::Buf(arg) => arg.visit(&mut f)?,
            Cell::Not(arg) => arg.visit(&mut f)?,
            Cell::And(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            Cell::Xor(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            Cell::Mux(arg1, arg2, arg3) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
                arg3.visit(&mut f)?;
            }

            Cell::Coarse(coarse) => coarse.visit(&mut f)?,
        }
        Ok(())
    }

    pub(crate) fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        match self {
            Cell::Skip(_) => unreachable!(),

            Cell::Buf(arg) => arg.visit_mut(&mut f),
            Cell::Not(arg) => arg.visit_mut(&mut f),
            Cell::And(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            Cell::Xor(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            Cell::Mux(arg1, arg2, arg3) => {
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
            CellRepr::Buf(arg)
            | CellRepr::Not(arg) => arg.len(),
            CellRepr::And(arg1, arg2)
            | CellRepr::Or(arg1, arg2)
            | CellRepr::Xor(arg1, arg2)
            | CellRepr::Mux(_, arg1, arg2) => {
                debug_assert_eq!(arg1.len(), arg2.len());
                arg1.len()
            }

            CellRepr::Add(arg1, arg2)
            | CellRepr::Sub(arg1, arg2)
            | CellRepr::Mul(arg1, arg2)
            | CellRepr::UDiv(arg1, arg2)
            | CellRepr::UMod(arg1, arg2)
            | CellRepr::SDivTrunc(arg1, arg2)
            | CellRepr::SDivFloor(arg1, arg2)
            | CellRepr::SModTrunc(arg1, arg2)
            | CellRepr::SModFloor(arg1, arg2) => {
                debug_assert_eq!(arg1.len(), arg2.len());
                arg1.len()
            }

            CellRepr::Eq(_arg1, _arg2) => 1,
            CellRepr::ULt(_arg1, _arg2) => 1,
            CellRepr::SLt(_arg1, _arg2) => 1,

            CellRepr::Shl(arg1, _, _)
            | CellRepr::UShr(arg1, _, _)
            | CellRepr::SShr(arg1, _, _)
            | CellRepr::XShr(arg1, _, _) => arg1.len(),

            CellRepr::Dff(flip_flop) => flip_flop.output_len(),
            CellRepr::Iob(io_buffer) => io_buffer.output_len(),
            CellRepr::Other(instance) => instance.output_len(),

            CellRepr::TopInput(_, width) => *width as usize,
            CellRepr::TopOutput(_, _) => 0,
        }
    }

    pub(crate) fn visit<E>(&self, mut f: impl FnMut(Net) -> Result<(), E>) -> Result<(), E> {
        match self {
            CellRepr::Buf(arg)
            | CellRepr::Not(arg) => arg.visit(&mut f)?,
            CellRepr::And(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::Or(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::Xor(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::Mux(net, arg1, arg2) => {
                net.visit(&mut f)?;
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }

            CellRepr::Add(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::Sub(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::Mul(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::UDiv(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::UMod(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::SDivTrunc(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::SDivFloor(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::SModTrunc(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::SModFloor(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::Eq(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::ULt(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::SLt(arg1, arg2) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::Shl(arg1, arg2, _) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::UShr(arg1, arg2, _) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::SShr(arg1, arg2, _) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }
            CellRepr::XShr(arg1, arg2, _) => {
                arg1.visit(&mut f)?;
                arg2.visit(&mut f)?;
            }

            CellRepr::Dff(flip_flop) => flip_flop.visit(&mut f)?,
            CellRepr::Iob(io_buffer) => io_buffer.visit(&mut f)?,
            CellRepr::Other(instance) => instance.visit(&mut f)?,

            CellRepr::TopInput(_, _) => (),
            CellRepr::TopOutput(_, arg) => arg.visit(f)?,
        }
        Ok(())
    }

    pub(crate) fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        match self {
            CellRepr::Buf(arg) | CellRepr::Not(arg) => arg.visit_mut(&mut f),
            CellRepr::And(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Or(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Xor(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Mux(net, arg1, arg2) => {
                net.visit_mut(&mut f);
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }

            CellRepr::Add(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Sub(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Mul(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::UDiv(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::UMod(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::SDivTrunc(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::SDivFloor(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::SModTrunc(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::SModFloor(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Eq(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::ULt(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::SLt(arg1, arg2) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::Shl(arg1, arg2, _) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::UShr(arg1, arg2, _) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::SShr(arg1, arg2, _) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }
            CellRepr::XShr(arg1, arg2, _) => {
                arg1.visit_mut(&mut f);
                arg2.visit_mut(&mut f);
            }

            CellRepr::Dff(flip_flop) => flip_flop.visit_mut(&mut f),
            CellRepr::Iob(io_buffer) => io_buffer.visit_mut(&mut f),
            CellRepr::Other(instance) => instance.visit_mut(&mut f),

            CellRepr::TopInput(_, _) => (),
            CellRepr::TopOutput(_, arg) => arg.visit_mut(f),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FlipFlop {
    pub data: Value,
    pub clock: ControlNet,
    pub enable: ControlNet,
    pub reset: ControlNet, // sync reset
    pub reset_over_enable: bool,
    pub clear: ControlNet, // async reset

    pub init_value: Const,
    pub reset_value: Const,
    pub clear_value: Const,
}

impl FlipFlop {
    pub fn output_len(&self) -> usize {
        self.data.len()
    }

    pub fn visit<E>(&self, mut f: impl FnMut(Net) -> Result<(), E>) -> Result<(), E> {
        self.data.visit(&mut f)?;
        self.clock.visit(&mut f)?;
        self.enable.visit(&mut f)?;
        self.reset.visit(&mut f)?;
        self.clear.visit(&mut f)?;
        Ok(())
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        self.data.visit_mut(&mut f);
        self.clock.visit_mut(&mut f);
        self.enable.visit_mut(&mut f);
        self.reset.visit_mut(&mut f);
        self.clear.visit_mut(&mut f);
    }
}

#[derive(Debug, Clone)]
pub struct IoBuffer {
    pub io: IoValue,
    pub output: Value,
    pub enable: ControlNet,
}

impl IoBuffer {
    pub fn output_len(&self) -> usize {
        self.io.len()
    }

    pub fn visit<E>(&self, mut f: impl FnMut(Net) -> Result<(), E>) -> Result<(), E> {
        self.output.visit(&mut f)?;
        self.enable.visit(&mut f)?;
        Ok(())
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        self.output.visit_mut(&mut f);
        self.enable.visit_mut(&mut f);
    }
}

#[derive(Debug, Clone)]
pub enum ParamValue {
    Const(Const),
    Int(i64),
    String(String),
    Float(f64),
}

#[derive(Debug, Clone)]
pub struct Instance {
    pub reference: String,
    pub parameters: HashMap<String, ParamValue>,
    pub inputs: HashMap<String, Value>,
    pub outputs: HashMap<String, Range<usize>>,
    pub ios: HashMap<String, IoValue>,
}

impl Instance {
    pub fn output_len(&self) -> usize {
        self.outputs.values().map(|range| range.len()).sum()
    }

    pub fn visit<E>(&self, mut f: impl FnMut(Net) -> Result<(), E>) -> Result<(), E> {
        for val in self.inputs.values() {
            val.visit(&mut f)?;
        }
        Ok(())
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        for val in self.inputs.values_mut() {
            val.visit_mut(&mut f);
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
