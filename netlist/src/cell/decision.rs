use crate::{Const, Net, Value};

/// If `enable` is asserted, output is one-hot priority match of `value` against `patterns`.
/// Otherwise it is zero.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatchCell {
    pub value: Value,
    pub enable: Net,
    pub patterns: Vec<Vec<Const>>,
}

/// If `enable` is asserted, output is `value` where `value[offset..]` is replaced with `update`.
/// Otherwise it is `value`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssignCell {
    pub value: Value,
    pub enable: Net,
    pub update: Value,
    pub offset: usize,
}

impl MatchCell {
    pub fn output_len(&self) -> usize {
        self.patterns.len()
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        self.value.visit(&mut f);
        self.enable.visit(&mut f);
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        self.value.visit_mut(&mut f);
        self.enable.visit_mut(&mut f);
    }
}
impl AssignCell {
    pub fn output_len(&self) -> usize {
        self.value.len()
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        self.value.visit(&mut f);
        self.enable.visit(&mut f);
        self.update.visit(&mut f);
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        self.value.visit_mut(&mut f);
        self.enable.visit_mut(&mut f);
        self.update.visit_mut(&mut f);
    }
}
