use std::ops::{Index, IndexMut, Range};
use std::slice::SliceIndex;

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct IoNet(pub u32);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct IoValue {
    nets: Vec<IoNet>,
}

impl IoValue {
    pub fn len(&self) -> usize {
        self.nets.len()
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = IoNet> + DoubleEndedIterator + ExactSizeIterator + 'a {
        self.nets.iter().copied()
    }

    pub fn from_range(range: Range<u32>) -> Self {
        Self { nets: range.map(|i| IoNet(i)).collect() }
    }
}

impl From<IoNet> for IoValue {
    fn from(value: IoNet) -> Self {
        Self { nets: vec![value] }
    }
}

impl FromIterator<IoNet> for IoValue {
    fn from_iter<T: IntoIterator<Item = IoNet>>(iter: T) -> Self {
        IoValue { nets: iter.into_iter().collect() }
    }
}

impl<I: SliceIndex<[IoNet]>> Index<I> for IoValue {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.nets[index]
    }
}

impl<I: SliceIndex<[IoNet]>> IndexMut<I> for IoValue {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.nets[index]
    }
}

impl IntoIterator for &IoValue {
    type Item = IoNet;
    type IntoIter = std::vec::IntoIter<IoNet>;

    fn into_iter(self) -> Self::IntoIter {
        self.nets.clone().into_iter()
    }
}
