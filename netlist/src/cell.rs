use core::ops::Range;
use std::{borrow::Cow, collections::BTreeMap, hash::Hash};

use crate::{Const, ControlNet, Design, IoValue, Net, TargetPrototype, Trit, Value};

// Space-optimized representation of a cell, for compact AIGs.
#[derive(Debug, Clone)]
pub(crate) enum Cell {
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

    // TODO: memory
    Dff(FlipFlop),
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
}

impl Cell {
    pub fn repr<'a>(&'a self) -> Cow<'a, CellRepr> {
        match *self {
            Cell::Skip(_) => unreachable!(),

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
            Cell::Skip(_) => unreachable!(),

            Cell::Buf(_) | Cell::Not(_) | Cell::And(_, _) | Cell::Or(_, _) | Cell::Xor(_, _) | Cell::Mux(_, _, _) => 1,
            Cell::Adc(_, _, _) => 2,

            Cell::Coarse(coarse) => coarse.output_len(),
        }
    }

    pub(crate) fn visit(&self, mut f: impl FnMut(Net)) {
        match self {
            Cell::Skip(_) => unreachable!(),
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
            Cell::Skip(_) => unreachable!(),
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
            CellRepr::Iob(io_buffer) => io_buffer.visit_mut(&mut f),
            CellRepr::Target(target_cell) => target_cell.visit_mut(&mut f),
            CellRepr::Other(instance) => instance.visit_mut(&mut f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FlipFlop {
    pub data: Value,
    pub clock: ControlNet,
    pub clear: ControlNet, // async reset
    pub reset: ControlNet, // sync reset
    pub enable: ControlNet,
    pub reset_over_enable: bool,

    pub clear_value: Const,
    pub reset_value: Const,
    pub init_value: Const,
}

impl FlipFlop {
    pub fn output_len(&self) -> usize {
        self.data.len()
    }

    pub fn has_clock(&self) -> bool {
        !self.clock.is_const()
    }

    pub fn has_enable(&self) -> bool {
        !self.enable.is_always(true)
    }

    pub fn has_reset(&self) -> bool {
        !self.reset.is_always(false)
    }

    pub fn has_reset_value(&self) -> bool {
        !self.reset_value.is_undef()
    }

    pub fn has_clear(&self) -> bool {
        !self.clear.is_always(false)
    }

    pub fn has_clear_value(&self) -> bool {
        !self.clear_value.is_undef()
    }

    pub fn has_init_value(&self) -> bool {
        !self.init_value.is_undef()
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        self.data.visit(&mut f);
        self.clock.visit(&mut f);
        self.enable.visit(&mut f);
        self.reset.visit(&mut f);
        self.clear.visit(&mut f);
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        self.data.visit_mut(&mut f);
        self.clock.visit_mut(&mut f);
        self.enable.visit_mut(&mut f);
        self.reset.visit_mut(&mut f);
        self.clear.visit_mut(&mut f);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IoBuffer {
    pub io: IoValue,
    pub output: Value,
    pub enable: ControlNet,
}

impl IoBuffer {
    pub fn output_len(&self) -> usize {
        self.io.len()
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        self.output.visit(&mut f);
        self.enable.visit(&mut f);
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
    Float(f64),
    String(String),
}

impl From<Const> for ParamValue {
    fn from(value: Const) -> Self {
        Self::Const(value)
    }
}

impl From<bool> for ParamValue {
    fn from(value: bool) -> Self {
        Self::Const(Trit::from(value).into())
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Instance {
    pub kind: String,
    pub params: BTreeMap<String, ParamValue>,
    pub inputs: BTreeMap<String, Value>,
    pub outputs: BTreeMap<String, Range<usize>>,
    pub ios: BTreeMap<String, IoValue>,
}

impl Instance {
    pub fn new(kind: String) -> Self {
        Instance {
            kind,
            params: Default::default(),
            inputs: Default::default(),
            outputs: Default::default(),
            ios: Default::default(),
        }
    }

    pub fn output_len(&self) -> usize {
        self.outputs.values().map(|range| range.len()).sum()
    }

    pub fn get_param_string(&self, name: &str) -> Option<&str> {
        let val = self.params.get(name)?;
        if let ParamValue::String(val) = val {
            Some(val)
        } else {
            None
        }
    }

    pub fn add_param(&mut self, name: impl Into<String>, value: impl Into<ParamValue>) {
        self.params.insert(name.into(), value.into());
    }

    pub fn rename_param(&mut self, name_from: impl AsRef<str>, name_to: impl Into<String>) {
        if let Some(param) = self.params.remove(name_from.as_ref()) {
            assert!(self.params.insert(name_to.into(), param).is_none());
        }
    }

    pub fn rename_input(&mut self, name_from: impl AsRef<str>, name_to: impl Into<String>) {
        if let Some(input) = self.inputs.remove(name_from.as_ref()) {
            assert!(self.inputs.insert(name_to.into(), input).is_none());
        }
    }

    pub fn rename_output(&mut self, name_from: impl AsRef<str>, name_to: impl Into<String>) {
        if let Some(output) = self.outputs.remove(name_from.as_ref()) {
            assert!(self.outputs.insert(name_to.into(), output).is_none());
        }
    }

    pub fn rename_io(&mut self, name_from: impl AsRef<str>, name_to: impl Into<String>) {
        if let Some(io) = self.ios.remove(name_from.as_ref()) {
            assert!(self.ios.insert(name_to.into(), io).is_none());
        }
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        for val in self.inputs.values() {
            val.visit(&mut f);
        }
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        for val in self.inputs.values_mut() {
            val.visit_mut(&mut f);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TargetCell {
    pub kind: String,
    pub params: Vec<ParamValue>,
    pub inputs: Value,
    pub output_len: usize,
    pub ios: IoValue,
}

impl TargetCell {
    pub fn new(kind: String, prototype: &TargetPrototype) -> Self {
        let mut result = Self {
            kind,
            params: vec![],
            inputs: Value::EMPTY,
            output_len: prototype.output_len,
            ios: IoValue::floating(prototype.io_len),
        };
        for param in &prototype.params {
            result.params.push(param.default.clone());
        }
        for input in &prototype.inputs {
            result.inputs.extend(Value::from(&input.default));
        }
        result
    }

    pub fn visit(&self, f: impl FnMut(Net)) {
        self.inputs.visit(f);
    }

    pub fn visit_mut(&mut self, f: impl FnMut(&mut Net)) {
        self.inputs.visit_mut(f);
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
