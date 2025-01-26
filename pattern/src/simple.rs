use prjunnamed_netlist::{Const, Design, Net, Trit, Value};

use crate::{NetOrValue, Pattern};

pub struct PAny;

impl PAny {
    pub fn new() -> PAny {
        PAny
    }
}

impl<T: NetOrValue> Pattern<T> for PAny {
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
            Some(value) if value[0] == self.0 => Some(((),)),
            _ => None,
        }
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
        PAllConst(Trit::Undef).execute(design, target)
    }
}

pub struct PZero;

impl PZero {
    pub fn new() -> PZero {
        PZero
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
        PAllConst(Trit::One).execute(design, target)
    }
}
