use prjunnamed_netlist::{Const, Design, Net, Trit, Value};

use crate::{NetOrValue, Pattern};

pub struct PAny;

impl PAny {
    pub fn new() -> PAny {
        PAny
    }
}

impl<T: Clone> Pattern<T> for PAny {
    type Capture = (T,);

    fn execute(&self, _design: &Design, target: &T) -> Option<Self::Capture> {
        Some((target.clone(),))
    }
}

pub struct PConst;

impl PConst {
    pub fn new() -> PConst {
        PConst
    }
}

impl Pattern<Net> for PConst {
    type Capture = (Trit,);

    fn execute(&self, _design: &Design, target: &Net) -> Option<Self::Capture> {
        Net::as_const(*target).map(|value| (value,))
    }
}

impl Pattern<Value> for PConst {
    type Capture = (Const,);

    fn execute(&self, _design: &Design, target: &Value) -> Option<Self::Capture> {
        Value::as_const(&target).map(|value| (value,))
    }
}

pub struct PAllConst(Trit);

impl<T: NetOrValue> Pattern<T> for PAllConst {
    type Capture = ((),);

    fn execute(&self, _design: &Design, target: &T) -> Option<Self::Capture> {
        match target.as_const() {
            Some(value) if value.into_iter().all(|net| net == self.0) => Some(((),)),
            _ => None,
        }
    }
}

pub struct PZero;

impl PZero {
    pub fn new() -> PZero {
        PZero
    }
}

impl Pattern<u32> for PZero {
    type Capture = ((),);

    fn execute(&self, _design: &Design, target: &u32) -> Option<Self::Capture> {
        if *target == 0 {
            Some(((),))
        } else {
            None
        }
    }
}

impl<T: NetOrValue> Pattern<T> for PZero {
    type Capture = <PAllConst as Pattern<T>>::Capture;

    fn execute(&self, design: &Design, target: &T) -> Option<Self::Capture> {
        PAllConst(Trit::Zero).execute(design, target)
    }
}

pub struct POnes;

impl POnes {
    pub fn new() -> POnes {
        POnes
    }
}

impl<T: NetOrValue> Pattern<T> for POnes {
    type Capture = <PAllConst as Pattern<T>>::Capture;

    fn execute(&self, design: &Design, target: &T) -> Option<Self::Capture> {
        if target.len() == 0 {
            return None;
        }
        PAllConst(Trit::One).execute(design, target)
    }
}

pub struct PUndef;

impl PUndef {
    pub fn new() -> PUndef {
        PUndef
    }
}

impl<T: NetOrValue> Pattern<T> for PUndef {
    type Capture = <PAllConst as Pattern<T>>::Capture;

    fn execute(&self, design: &Design, target: &T) -> Option<Self::Capture> {
        if target.len() == 0 {
            return None;
        }
        PAllConst(Trit::Undef).execute(design, target)
    }
}

pub struct PHasX;

impl PHasX {
    pub fn new() -> PHasX {
        PHasX
    }
}

impl<T: NetOrValue> Pattern<T> for PHasX {
    type Capture = ((),);

    fn execute(&self, _design: &Design, target: &T) -> Option<Self::Capture> {
        match target.as_const() {
            Some(value) if value.has_undef() => Some(((),)),
            _ => None,
        }
    }
}

pub struct PPow2;

impl PPow2 {
    pub fn new() -> PPow2 {
        PPow2
    }
}

impl<T: NetOrValue> Pattern<T> for PPow2 {
    type Capture = (u32,);

    fn execute(&self, _design: &Design, target: &T) -> Option<Self::Capture> {
        target.as_const().and_then(|value| value.as_power_of_two().map(|exp| (exp,)))
    }
}

pub type POneHot = PPow2;
