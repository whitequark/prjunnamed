use std::{
    fmt::{Debug, Display},
    ops::{Index, IndexMut},
    slice::SliceIndex,
    borrow::Cow,
};

use crate::{Net, Trit};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Const {
    trits: Vec<Trit>,
}

impl Const {
    pub fn zero(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Trit::Zero, width))
    }

    pub fn ones(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Trit::One, width))
    }

    pub fn undef(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Trit::Undef, width))
    }

    pub fn len(&self) -> usize {
        self.trits.len()
    }

    pub fn is_zero(&self) -> bool {
        self.trits.iter().all(|&trit| trit == Trit::Zero)
    }

    pub fn is_ones(&self) -> bool {
        self.trits.iter().all(|&trit| trit == Trit::One)
    }

    pub fn is_undef(&self) -> bool {
        self.trits.iter().all(|&trit| trit == Trit::Undef)
    }

    pub fn has_undef(&self) -> bool {
        self.trits.iter().any(|&trit| trit == Trit::Undef)
    }

    pub fn as_power_of_two(&self) -> Option<u32> {
        let mut res = None;
        for (i, trit) in self.trits.iter().copied().enumerate() {
            if trit == Trit::Undef {
                return None;
            }
            if trit == Trit::One {
                if res.is_some() {
                    return None;
                }
                res = Some(i as u32);
            }
        }
        res
    }

    pub fn msb(&self) -> Trit {
        self.trits[self.len() - 1]
    }

    pub fn from_uint(val: u128, bits: usize) -> Self {
        let mut trits = vec![];
        if bits < 128 {
            assert!(val < (1 << bits));
        }
        for i in 0..bits {
            let trit = if i < u128::BITS as usize && ((val >> i) & 1) != 0 { Trit::One } else { Trit::Zero };
            trits.push(trit);
        }
        Self { trits }
    }

    pub fn not(&self) -> Const {
        Const::from_iter(self.into_iter().map(|x| !x))
    }

    pub fn and<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        Const::from_iter(self.into_iter().zip(other.into_iter()).map(|(x, y)| x & y))
    }

    pub fn or<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        Const::from_iter(self.into_iter().zip(other.into_iter()).map(|(x, y)| x | y))
    }

    pub fn xor<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        Const::from_iter(self.into_iter().zip(other.into_iter()).map(|(x, y)| x ^ y))
    }

    pub fn adc<'a>(&self, other: impl Into<Cow<'a, Const>>, ci: Trit) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        let mut sum = vec![];
        let mut carry = ci;
        for (x, y) in self.into_iter().zip(other.into_iter()) {
            let (s, co) = match (x, y, carry) {
                (Trit::Undef, _, _) => (Trit::Undef, Trit::Undef),
                (_, Trit::Undef, _) => (Trit::Undef, Trit::Undef),
                (_, _, Trit::Undef) => (Trit::Undef, Trit::Undef),
                (Trit::Zero, Trit::Zero, s) => (s, Trit::Zero),
                (Trit::Zero, s, Trit::Zero) => (s, Trit::Zero),
                (s, Trit::Zero, Trit::Zero) => (s, Trit::Zero),
                (Trit::One, Trit::One, s) => (s, Trit::One),
                (Trit::One, s, Trit::One) => (s, Trit::One),
                (s, Trit::One, Trit::One) => (s, Trit::One),
            };
            carry = co;
            sum.push(s);
        }
        sum.push(carry);
        Const::from_iter(sum)
    }

    pub fn eq<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Trit {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        let mut undef = false;
        for (x, y) in self.into_iter().zip(other.into_iter()) {
            if x == Trit::Undef || y == Trit::Undef {
                undef = true;
            } else if x != y {
                return Trit::Zero;
            }
        }
        if undef {
            Trit::Undef
        } else {
            Trit::One
        }
    }

    pub fn ult<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Trit {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        if self.has_undef() || other.has_undef() {
            Trit::Undef
        } else {
            for (x, y) in self.into_iter().zip(other.into_iter()).rev() {
                if x != y {
                    return Trit::from(x < y);
                }
            }
            Trit::Zero
        }
    }

    pub fn slt<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Trit {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        if self.has_undef() || other.has_undef() {
            Trit::Undef
        } else if self.msb() != other.msb() {
            Trit::from(self.msb() > other.msb())
        } else {
            for (x, y) in self.into_iter().zip(other.into_iter()).rev() {
                if x != y {
                    return Trit::from(x < y);
                }
            }
            Trit::Zero
        }
    }
}

impl From<Trit> for Const {
    fn from(trit: Trit) -> Self {
        Const { trits: vec![trit] }
    }
}

impl From<Vec<Trit>> for Const {
    fn from(trits: Vec<Trit>) -> Self {
        Const { trits }
    }
}

impl FromIterator<Trit> for Const {
    fn from_iter<T: IntoIterator<Item = Trit>>(iter: T) -> Self {
        Const { trits: iter.into_iter().collect() }
    }
}

impl IntoIterator for &Const {
    type Item = Trit;
    type IntoIter = std::vec::IntoIter<Trit>;

    fn into_iter(self) -> Self::IntoIter {
        self.trits.clone().into_iter()
    }
}

impl Debug for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Const(")?;
        for (index, trit) in self.trits.iter().enumerate() {
            if index != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", trit)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for trit in self.trits.iter().rev() {
            write!(f, "{}", trit)?;
        }
        Ok(())
    }
}

impl<'a> From<&'a Const> for Cow<'a, Const> {
    fn from(value: &'a Const) -> Self {
        Cow::Borrowed(value)
    }
}

impl<'a> From<Const> for Cow<'a, Const> {
    fn from(value: Const) -> Self {
        Cow::Owned(value)
    }
}

impl<'a> From<Trit> for Cow<'a, Const> {
    fn from(value: Trit) -> Self {
        Cow::Owned(Const::from(value))
    }
}

impl<I: SliceIndex<[Trit]>> Index<I> for Const {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.trits[index]
    }
}

impl<I: SliceIndex<[Trit]>> IndexMut<I> for Const {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.trits[index]
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Value {
    nets: Vec<Net>,
}

fn shift_count(val: &Const, stride: u32) -> usize {
    let stride = stride as usize;
    let mut res: usize = 0;
    for (i, trit) in val.into_iter().enumerate() {
        if trit == Trit::One {
            if i >= usize::BITS as usize {
                return usize::MAX;
            } else {
                res |= 1 << i;
            }
        }
    }
    res.checked_mul(stride).unwrap_or(usize::MAX)
}

impl Value {
    pub const EMPTY: Value = Value { nets: vec![] };

    pub fn zero(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Net::ZERO, width))
    }

    pub fn ones(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Net::ONE, width))
    }

    pub fn undef(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Net::UNDEF, width))
    }

    pub(crate) fn cell(cell_index: usize, count: usize) -> Value {
        let mut nets = vec![];
        for net_index in 0..count {
            nets.push(Net::from_cell(cell_index + net_index));
        }
        Value { nets }
    }

    pub fn len(&self) -> usize {
        self.nets.len()
    }

    pub fn lsb(&self) -> Net {
        self[0]
    }

    pub fn msb(&self) -> Net {
        self[self.len() - 1]
    }

    pub fn has_undef(&self) -> bool {
        self.nets.iter().any(|&net| net == Net::UNDEF)
    }

    pub fn as_const(&self) -> Option<Const> {
        if self.nets.iter().all(|net| net.as_const().is_some()) {
            let mut trits = vec![];
            for net in self.nets.iter() {
                trits.push(net.as_const().unwrap())
            }
            Some(Const { trits })
        } else {
            None
        }
    }

    pub fn as_net(&self) -> Option<Net> {
        if self.len() == 1 {
            Some(self[0])
        } else {
            None
        }
    }

    pub fn unwrap_net(&self) -> Net {
        self.as_net().unwrap()
    }

    pub fn concat<'a>(&self, other: impl Into<Cow<'a, Value>>) -> Self {
        Self::from_iter(self.into_iter().chain(other.into().into_iter()))
    }

    pub fn zext(&self, width: usize) -> Self {
        assert!(width >= self.len());
        self.concat(Value::zero(width - self.len()))
    }

    pub fn sext(&self, width: usize) -> Self {
        assert!(self.len() > 0);
        assert!(width >= self.len());
        Self::from_iter(self.into_iter().chain(std::iter::repeat_n(self[self.len() - 1], width - self.len())))
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        for &net in self.nets.iter() {
            f(net)
        }
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        for net in self.nets.iter_mut() {
            f(net)
        }
    }

    pub fn shl<'a>(&self, other: impl Into<Cow<'a, Const>>, stride: u32) -> Value {
        let other = other.into();
        if other.has_undef() {
            return Value::undef(self.len());
        }
        let shcnt = shift_count(&*other, stride);
        if shcnt >= self.len() {
            return Value::zero(self.len());
        }
        return Value::zero(shcnt).concat(Value::from(&self[..self.len() - shcnt]));
    }

    pub fn ushr<'a>(&self, other: impl Into<Cow<'a, Const>>, stride: u32) -> Value {
        let other = other.into();
        if other.has_undef() {
            return Value::undef(self.len());
        }
        let shcnt = shift_count(&*other, stride);
        if shcnt >= self.len() {
            return Value::zero(self.len());
        }
        return Value::from(&self[shcnt..]).zext(self.len());
    }

    pub fn sshr<'a>(&self, other: impl Into<Cow<'a, Const>>, stride: u32) -> Value {
        let other = other.into();
        if other.has_undef() {
            return Value::undef(self.len());
        }
        let shcnt = shift_count(&*other, stride);
        if shcnt >= self.len() {
            return Value::from(self.msb()).sext(self.len());
        }
        return Value::from(&self[shcnt..]).sext(self.len());
    }

    pub fn xshr<'a>(&self, other: impl Into<Cow<'a, Const>>, stride: u32) -> Value {
        let other = other.into();
        if other.has_undef() {
            return Value::undef(self.len());
        }
        let shcnt = shift_count(&*other, stride);
        if shcnt >= self.len() {
            return Value::undef(self.len());
        }
        return Value::from(&self[shcnt..]).concat(Value::undef(shcnt));
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Value(")?;
        for (index, net) in self.nets.iter().enumerate() {
            if index != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", net)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl<I: SliceIndex<[Net]>> Index<I> for Value {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.nets[index]
    }
}

impl<I: SliceIndex<[Net]>> IndexMut<I> for Value {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.nets[index]
    }
}

impl FromIterator<Net> for Value {
    fn from_iter<T: IntoIterator<Item = Net>>(iter: T) -> Self {
        Value { nets: iter.into_iter().collect() }
    }
}

impl IntoIterator for &Value {
    type Item = Net;
    type IntoIter = std::vec::IntoIter<Net>;

    fn into_iter(self) -> Self::IntoIter {
        self.nets.clone().into_iter()
    }
}

impl From<&Value> for Value {
    fn from(value: &Value) -> Self {
        value.clone()
    }
}

impl From<Net> for Value {
    fn from(net: Net) -> Self {
        Value { nets: vec![net] }
    }
}

impl From<&Net> for Value {
    fn from(net: &Net) -> Self {
        Value { nets: vec![*net] }
    }
}

impl From<Trit> for Value {
    fn from(trit: Trit) -> Self {
        Value { nets: vec![Net::from(trit)] }
    }
}

impl From<&[Net]> for Value {
    fn from(nets: &[Net]) -> Self {
        Value { nets: nets.to_vec() }
    }
}

impl From<Vec<Net>> for Value {
    fn from(nets: Vec<Net>) -> Self {
        Value { nets }
    }
}

impl From<&Const> for Value {
    fn from(value: &Const) -> Self {
        Value::from_iter(value.trits.iter().copied().map(Net::from))
    }
}

impl From<Const> for Value {
    fn from(value: Const) -> Self {
        Value::from(&value)
    }
}

impl From<Value> for Cow<'_, Value> {
    fn from(value: Value) -> Self {
        Cow::Owned(value)
    }
}

impl From<Net> for Cow<'_, Value> {
    fn from(value: Net) -> Self {
        Cow::Owned(Value::from(value))
    }
}

impl From<Trit> for Cow<'_, Value> {
    fn from(value: Trit) -> Self {
        Cow::Owned(Value::from(Net::from(value)))
    }
}

impl From<&Const> for Cow<'_, Value> {
    fn from(value: &Const) -> Self {
        Cow::Owned(Value::from(value))
    }
}

impl From<Const> for Cow<'_, Value> {
    fn from(value: Const) -> Self {
        Cow::Owned(Value::from(value))
    }
}

impl<'a> From<&'a Value> for Cow<'a, Value> {
    fn from(value: &'a Value) -> Self {
        Cow::Borrowed(value)
    }
}

#[cfg(test)]
mod test {
    use crate::{Net, Value};

    #[test]
    fn test_value() {
        let v01 = Value::from_iter([Net::ONE, Net::ZERO]);
        assert_eq!(v01.into_iter().collect::<Vec<_>>(), vec![Net::ONE, Net::ZERO]);
    }
}
