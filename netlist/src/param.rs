use std::hash::Hash;

use crate::{Const, Trit};

#[derive(Debug, Clone)]
pub enum ParamValue {
    Const(Const),
    Int(i64),
    Float(f64),
    String(String),
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

impl From<i64> for ParamValue {
    fn from(value: i64) -> Self {
        Self::Int(value)
    }
}

impl From<String> for ParamValue {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<&str> for ParamValue {
    fn from(value: &str) -> Self {
        Self::String(value.into())
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
