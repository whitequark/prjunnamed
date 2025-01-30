use std::fmt::{Debug, Display};

use prjunnamed_netlist::{Const, Net, Value};

pub trait NetOrValue: Sized + Clone + Debug + Display {
    fn len(&self) -> usize;
    fn iter(&self) -> impl Iterator<Item = Net>;
    fn as_value(&self) -> Value {
        Value::from_iter(self.iter())
    }
    fn as_const(&self) -> Option<Const>;
    fn try_from(other: impl NetOrValue) -> Option<Self>;

    #[must_use]
    fn accumulate(capture: &mut Option<Self>, net: Net) -> bool;
}

impl NetOrValue for Net {
    fn len(&self) -> usize {
        1
    }

    fn as_const(&self) -> Option<Const> {
        Net::as_const(*self).map(|trit| Const::from(trit))
    }

    fn iter(&self) -> impl Iterator<Item = Net> {
        std::iter::repeat_n(*self, 1)
    }

    fn try_from(other: impl NetOrValue) -> Option<Self> {
        if other.len() == 1 {
            other.iter().next()
        } else {
            None
        }
    }

    fn accumulate(capture: &mut Option<Self>, net: Net) -> bool {
        match capture {
            Some(captured_net) if *captured_net == net => return true,
            Some(_) => return false,
            None => *capture = Some(net),
        }
        true
    }
}

impl NetOrValue for Value {
    fn len(&self) -> usize {
        Value::len(self)
    }

    fn iter(&self) -> impl Iterator<Item = Net> {
        self.iter()
    }

    fn as_const(&self) -> Option<Const> {
        Value::as_const(&self)
    }

    fn try_from(other: impl NetOrValue) -> Option<Self> {
        Some(Value::from_iter(other.iter()))
    }

    fn accumulate(capture: &mut Option<Self>, net: Net) -> bool {
        match capture {
            Some(ref mut value) => *value = value.concat(net),
            None => *capture = Some(Value::from(net)),
        }
        true
    }
}
