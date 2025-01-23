use std::{fmt::{Debug, Display}, ops::{Index, IndexMut}, slice::SliceIndex};

use crate::{Trit, Net};

#[derive(Clone)]
pub struct Const {
    trits: Vec<Trit>
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for trit in self.trits.iter().rev() {
            write!(f, "{}", trit)?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct Value {
    nets: Vec<Net>
}

impl Value {
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

    pub fn visit<E>(&self, mut f: impl FnMut(Net) -> Result<(), E>) -> Result<(), E> {
        for &net in self.nets.iter() {
            f(net)?;
        }
        Ok(())
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        for net in self.nets.iter_mut() {
            f(net)
        }
    }

    pub fn zero(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Net::ZERO, width))
    }

    pub fn ones(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Net::ONE, width))
    }

    pub fn undef(width: usize) -> Self {
        Self::from_iter(std::iter::repeat_n(Net::UNDEF, width))
    }

    pub fn zext(&self, width: usize) -> Self {
        assert!(width >= self.len());
        Self::from_iter(self.into_iter().chain(std::iter::repeat_n(Net::ZERO, width - self.len())))
    }

    pub fn sext(&self, width: usize) -> Self {
        assert!(self.len() > 0);
        assert!(width >= self.len());
        Self::from_iter(self.into_iter().chain(std::iter::repeat_n(self[self.len() - 1], width - self.len())))
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

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

#[cfg(test)]
mod test {
    use crate::{Net, Value};

    #[test]
    fn test_value() {
        let v01 = Value::from_iter([Net::ONE, Net::ZERO]);
        assert_eq!(v01.into_iter().collect::<Vec<_>>(), vec![Net::ONE, Net::ZERO]);
    }
}
