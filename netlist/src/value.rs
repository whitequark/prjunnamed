use std::{
    borrow::Cow,
    fmt::{Debug, Display},
    ops::{Index, IndexMut},
    slice::SliceIndex,
    str::FromStr,
};

use crate::{Net, Trit};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Const {
    trits: Vec<Trit>,
}

impl Const {
    pub const fn new() -> Self {
        Self { trits: vec![] }
    }

    pub fn zero(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Trit::Zero, width))
    }

    pub fn ones(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Trit::One, width))
    }

    pub fn undef(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Trit::Undef, width))
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

    pub fn as_uint(&self) -> Option<u64> {
        if self.has_undef() {
            return None;
        }
        let mut res = 0;
        for (pos, trit) in self.iter().enumerate() {
            if trit == Trit::One {
                if pos >= 64 {
                    return None;
                }
                res |= 1 << pos;
            }
        }
        Some(res)
    }

    pub fn as_int(&self) -> Option<i64> {
        if self.has_undef() {
            return None;
        }
        let mut width = self.len();
        while width > 1 && self[width - 1] == self[width - 2] {
            width -= 1;
        }
        if width > 64 {
            return None;
        }
        let mut res = 0;
        for (pos, trit) in self.iter().enumerate() {
            if trit == Trit::One {
                if pos == width - 1 {
                    res |= -1 << pos;
                } else {
                    res |= 1 << pos;
                }
            }
        }
        Some(res)
    }

    pub fn from_str(value: &str) -> Self {
        value.parse().expect("invalid constant")
    }

    pub fn len(&self) -> usize {
        self.trits.len()
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = Trit> + DoubleEndedIterator + ExactSizeIterator + 'a {
        self.trits.iter().copied()
    }

    pub fn lsb(&self) -> Trit {
        self.trits[0]
    }

    pub fn msb(&self) -> Trit {
        self.trits[self.len() - 1]
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
        let mut result = None;
        for (offset, trit) in self.trits.iter().copied().enumerate() {
            if trit == Trit::Undef {
                return None;
            }
            if trit == Trit::One {
                if result.is_some() {
                    return None;
                }
                result = Some(offset as u32);
            }
        }
        result
    }

    pub fn concat<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Self {
        Self::from_iter(self.iter().chain(other.into().iter()))
    }

    pub fn slice(&self, range: impl std::ops::RangeBounds<usize>) -> Const {
        Const::from_iter(self[(range.start_bound().cloned(), range.end_bound().cloned())].iter().copied())
    }

    pub fn combine<'a, 'b>(lft: impl Into<Cow<'a, Const>>, rgt: impl Into<Cow<'b, Const>>) -> Option<Const> {
        let (lft, rgt) = (lft.into(), rgt.into());
        assert_eq!(lft.len(), rgt.len());
        let mut trits = vec![];
        for (lft, rgt) in std::iter::zip(lft.iter(), rgt.iter()) {
            trits.push(Trit::combine(lft, rgt)?);
        }
        Some(Const { trits })
    }

    pub fn not(&self) -> Const {
        Const::from_iter(self.iter().map(|x| !x))
    }

    pub fn and<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        Const::from_iter(self.iter().zip(other.iter()).map(|(x, y)| x & y))
    }

    pub fn or<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        Const::from_iter(self.iter().zip(other.iter()).map(|(x, y)| x | y))
    }

    pub fn xor<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        Const::from_iter(self.iter().zip(other.iter()).map(|(x, y)| x ^ y))
    }

    pub fn adc<'a>(&self, other: impl Into<Cow<'a, Const>>, ci: Trit) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        let mut sum = vec![];
        let mut carry = ci;
        for (a, b) in self.iter().zip(other.iter()) {
            let (y, co) = match (a, b, carry) {
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
            sum.push(y);
        }
        sum.push(carry);
        Const::from_iter(sum)
    }

    pub fn eq<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Trit {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        let mut undef = false;
        for (x, y) in self.iter().zip(other.iter()) {
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
            for (x, y) in self.iter().zip(other.iter()).rev() {
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
            for (x, y) in self.iter().zip(other.iter()).rev() {
                if x != y {
                    return Trit::from(x < y);
                }
            }
            Trit::Zero
        }
    }

    pub fn mul<'a>(&self, other: impl Into<Cow<'a, Const>>) -> Const {
        let other = other.into();
        assert_eq!(self.len(), other.len());
        if self.has_undef() || other.has_undef() {
            Const::undef(self.len())
        } else {
            let mut res = Const::zero(self.len());
            for (i, bit) in other.iter().enumerate() {
                if bit == Trit::One {
                    res = res.adc(Const::zero(i).concat(self), Trit::Zero);
                } else {
                    res.trits.push(Trit::Zero);
                }
            }
            res.slice(..self.len())
        }
    }

    pub fn expand_undef(&self) -> Vec<Const> {
        let mut result = vec![self.clone()];
        for (index, trit) in self.iter().enumerate() {
            if trit == Trit::Undef {
                result = Vec::from_iter(
                    result
                        .iter()
                        .map(|value| {
                            let mut value = value.clone();
                            value[index] = Trit::Zero;
                            value
                        })
                        .chain(result.iter().map(|value| {
                            let mut value = value.clone();
                            value[index] = Trit::One;
                            value
                        })),
                );
            }
        }
        result
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

impl FromStr for Const {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut trits = vec![];
        let mut chars = s.chars();
        while let Some(char) = chars.next() {
            trits.push(Trit::from_str(&String::from(char))?)
        }
        trits.reverse();
        Ok(Const { trits })
    }
}

impl FromIterator<Trit> for Const {
    fn from_iter<T: IntoIterator<Item = Trit>>(iter: T) -> Self {
        Const { trits: iter.into_iter().collect() }
    }
}

impl Extend<Trit> for Const {
    fn extend<T: IntoIterator<Item = Trit>>(&mut self, iter: T) {
        for trit in iter {
            self.trits.push(trit);
        }
    }
}

impl IntoIterator for &Const {
    type Item = Trit;
    type IntoIter = std::vec::IntoIter<Trit>;

    fn into_iter(self) -> Self::IntoIter {
        self.trits.clone().into_iter()
    }
}

impl IntoIterator for Const {
    type Item = Trit;
    type IntoIter = std::vec::IntoIter<Trit>;

    fn into_iter(self) -> Self::IntoIter {
        self.trits.into_iter()
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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Value {
    nets: Vec<Net>,
}

fn shift_count(val: &Const, stride: u32) -> usize {
    let stride = stride as usize;
    let mut res: usize = 0;
    for (i, trit) in val.iter().enumerate() {
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

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = Net> + DoubleEndedIterator + ExactSizeIterator + 'a {
        self.nets.iter().copied()
    }

    pub fn is_undef(&self) -> bool {
        self.nets.iter().all(|&net| net == Net::UNDEF)
    }

    pub fn is_zero(&self) -> bool {
        self.nets.iter().all(|&net| net == Net::ZERO)
    }

    pub fn is_ones(&self) -> bool {
        self.nets.iter().all(|&net| net == Net::ONE)
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
        Self::from_iter(self.iter().chain(other.into().iter()))
    }

    pub fn slice(&self, range: impl std::ops::RangeBounds<usize>) -> Value {
        Value::from(&self[(range.start_bound().cloned(), range.end_bound().cloned())])
    }

    pub fn zext(&self, width: usize) -> Self {
        assert!(width >= self.len());
        self.concat(Value::zero(width - self.len()))
    }

    pub fn sext(&self, width: usize) -> Self {
        assert!(self.len() > 0);
        assert!(width >= self.len());
        Self::from_iter(self.iter().chain(std::iter::repeat_n(self[self.len() - 1], width - self.len())))
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

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.len() == 0 {
            write!(f, "{{}}")
        } else if self.len() == 1 {
            write!(f, "{}", self[0])
        } else {
            write!(f, "{{")?;
            for net in self.nets.iter() {
                write!(f, " {}", net)?;
            }
            write!(f, " }}")
        }
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

impl IntoIterator for Value {
    type Item = Net;
    type IntoIter = std::vec::IntoIter<Net>;

    fn into_iter(self) -> Self::IntoIter {
        self.nets.into_iter()
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

impl Extend<Net> for Value {
    fn extend<T: IntoIterator<Item = Net>>(&mut self, iter: T) {
        for net in iter {
            self.nets.push(net);
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Net, Value, Const, Trit};

    #[test]
    fn test_value() {
        let v01 = Value::from_iter([Net::ONE, Net::ZERO]);
        assert_eq!(v01.into_iter().collect::<Vec<_>>(), vec![Net::ONE, Net::ZERO]);
    }

    #[test]
    fn test_not() {
        for (a, y) in [("", ""), ("01", "10"), ("X10", "X01")] {
            assert_eq!(Const::from_str(a).not(), Const::from_str(y));
        }
    }

    #[test]
    fn test_and() {
        for (a, b, y) in [("", "", ""), ("1010", "1100", "1000"), ("X0X0", "XX00", "X000"), ("X1X1", "XX11", "XXX1")] {
            assert_eq!(Const::from_str(a).and(Const::from_str(b)), Const::from_str(y));
        }
    }

    #[test]
    fn test_or() {
        for (a, b, y) in [("", "", ""), ("1010", "1100", "1110"), ("X0X0", "XX00", "XXX0"), ("X1X1", "XX11", "X111")] {
            assert_eq!(Const::from_str(a).or(Const::from_str(b)), Const::from_str(y));
        }
    }

    #[test]
    fn test_xor() {
        for (a, b, y) in [("", "", ""), ("1010", "1100", "0110"), ("X0X0", "XX00", "XXX0"), ("X1X1", "XX11", "XXX0")] {
            assert_eq!(Const::from_str(a).xor(Const::from_str(b)), Const::from_str(y));
        }
    }

    #[test]
    fn test_mux() {
        for (s, a, b, y) in [
            ('0', "", "", ""),
            ('0', "XXX101010", "X10XX1100", "X10XX1100"),
            ('1', "XXX101010", "X10XX1100", "XXX101010"),
            ('X', "XXX101010", "X10XX1100", "XXXXX1XX0"),
        ] {
            assert_eq!(Trit::from_char(s).mux(Const::from_str(a), Const::from_str(b)), Const::from_str(y));
        }
    }

    #[test]
    fn test_adc() {
        for (a, b, c, y) in [
            ("", "", '0', "0"),
            ("", "", '1', "1"),
            ("10101010", "11001100", '0', "101110110"),
            ("1101", "1111", '1', "11101"),
            ("1010X010", "11001100", '0', "XXXXXX110"),
        ] {
            assert_eq!(Const::from_str(a).adc(Const::from_str(b), Trit::from_char(c)), Const::from_str(y));
        }
    }

    #[test]
    fn test_mul() {
        for (a, b, y) in [("", "", ""), ("0011", "0011", "1001"), ("0X11", "0011", "XXXX"), ("1101", "1101", "1001")] {
            assert_eq!(Const::from_str(a).mul(Const::from_str(b)), Const::from_str(y));
        }
    }

    #[test]
    fn test_expand_undef() {
        assert_eq!(Const::from_str("0101").expand_undef(), vec![Const::from_str("0101")]);
        assert_eq!(Const::from_str("0XX1").expand_undef(), vec![
            Const::from_str("0001"),
            Const::from_str("0011"),
            Const::from_str("0101"),
            Const::from_str("0111"),
        ]);
    }
}
