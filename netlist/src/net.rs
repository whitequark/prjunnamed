use std::{fmt::Debug, borrow::Cow};
use crate::Const;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Trit {
    Undef,
    Zero,
    One,
}

impl Trit {
    pub fn mux<'a, 'b>(self, arg1: impl Into<Cow<'a, Const>>, arg2: impl Into<Cow<'b, Const>>) -> Const {
        let arg1 = arg1.into();
        let arg2 = arg2.into();
        match self {
            Trit::One => arg1.into_owned(),
            Trit::Zero => arg2.into_owned(),
            Trit::Undef => {
                Const::from_iter(
                    arg1.into_iter().zip(arg2.into_iter()).map(|(x, y)| if x == y { x } else { Trit::Undef }),
                )
            }
        }
    }
}

impl std::fmt::Display for Trit {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Trit::Undef => write!(f, "X"),
            Trit::Zero => write!(f, "0"),
            Trit::One => write!(f, "1"),
        }
    }
}

impl From<bool> for Trit {
    fn from(value: bool) -> Self {
        match value {
            false => Trit::Zero,
            true => Trit::One,
        }
    }
}

impl std::ops::Not for Trit {
    type Output = Trit;

    fn not(self) -> Self::Output {
        match self {
            Trit::One => Trit::Zero,
            Trit::Zero => Trit::One,
            Trit::Undef => Trit::Undef,
        }
    }
}

impl std::ops::BitAnd<Trit> for Trit {
    type Output = Trit;

    fn bitand(self, rhs: Trit) -> Self::Output {
        match (self, rhs) {
            (Trit::Zero, _) => Trit::Zero,
            (_, Trit::Zero) => Trit::Zero,
            (Trit::Undef, _) => Trit::Undef,
            (_, Trit::Undef) => Trit::Undef,
            (Trit::One, Trit::One) => Trit::One,
        }
    }
}

impl std::ops::BitOr<Trit> for Trit {
    type Output = Trit;

    fn bitor(self, rhs: Trit) -> Self::Output {
        match (self, rhs) {
            (Trit::One, _) => Trit::One,
            (_, Trit::One) => Trit::One,
            (Trit::Undef, _) => Trit::Undef,
            (_, Trit::Undef) => Trit::Undef,
            (Trit::Zero, Trit::Zero) => Trit::Zero,
        }
    }
}

impl std::ops::BitXor<Trit> for Trit {
    type Output = Trit;

    fn bitxor(self, rhs: Trit) -> Self::Output {
        match (self, rhs) {
            (Trit::Undef, _) => Trit::Undef,
            (_, Trit::Undef) => Trit::Undef,
            (Trit::One, Trit::One) => Trit::Zero,
            (Trit::One, Trit::Zero) => Trit::One,
            (Trit::Zero, Trit::One) => Trit::One,
            (Trit::Zero, Trit::Zero) => Trit::Zero,
        }
    }
}

impl TryFrom<Net> for Trit {
    type Error = ();

    fn try_from(value: Net) -> Result<Self, Self::Error> {
        if value == Net::UNDEF {
            Ok(Trit::Undef)
        } else if value == Net::ZERO {
            Ok(Trit::Zero)
        } else if value == Net::ONE {
            Ok(Trit::One)
        } else {
            Err(())
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Net {
    pub(crate) index: u32,
}

impl Net {
    pub const UNDEF: Net = Net { index: u32::MAX };
    pub const ZERO: Net = Net { index: 0 };
    pub const ONE: Net = Net { index: 1 };

    const FIRST_CELL: u32 = 2; // Zero, One, then cells

    pub(crate) fn from_cell(cell_index: usize) -> Net {
        assert!(cell_index <= u32::MAX as usize - 3);
        Net { index: cell_index as u32 + Net::FIRST_CELL }
    }

    pub(crate) fn as_cell(self) -> Option<usize> {
        if self.index >= Self::FIRST_CELL && self != Self::UNDEF {
            Some((self.index - Self::FIRST_CELL) as usize)
        } else {
            None
        }
    }

    pub fn as_const(self) -> Option<Trit> {
        if self == Self::UNDEF {
            Some(Trit::Undef)
        } else if self == Self::ZERO {
            Some(Trit::Zero)
        } else if self == Self::ONE {
            Some(Trit::One)
        } else {
            None
        }
    }

    pub fn visit(self, mut f: impl FnMut(Net)) {
        f(self)
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        f(self)
    }
}

impl From<bool> for Net {
    fn from(value: bool) -> Self {
        match value {
            false => Net::ZERO,
            true => Net::ONE,
        }
    }
}

impl From<Trit> for Net {
    fn from(value: Trit) -> Self {
        match value {
            Trit::Undef => Self::UNDEF,
            Trit::Zero => Self::ZERO,
            Trit::One => Self::ONE,
        }
    }
}

impl Debug for Net {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Net { index: 0 } => write!(f, "Net::ZERO"),
            Net { index: 1 } => write!(f, "Net::ONE"),
            Net { index: u32::MAX } => write!(f, "Net::UNDEF"),
            _ => {
                let cell_index = self.index.checked_sub(Net::FIRST_CELL).unwrap();
                write!(f, "Net::from_cell({cell_index})")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ControlNet {
    Pos(Net),
    Neg(Net),
}

impl ControlNet {
    pub fn net(self) -> Net {
        match self {
            Self::Pos(net) => net,
            Self::Neg(net) => net,
        }
    }

    pub fn is_positive(self) -> bool {
        matches!(self, Self::Pos(_))
    }

    pub fn is_negative(self) -> bool {
        matches!(self, Self::Neg(_))
    }

    pub fn is_active(self) -> Option<bool> {
        match self {
            Self::Pos(net) if net == Net::ZERO => Some(false),
            Self::Neg(net) if net == Net::ONE => Some(false),
            Self::Pos(net) if net == Net::ONE => Some(true),
            Self::Neg(net) if net == Net::ZERO => Some(true),
            _ => None,
        }
    }

    pub fn is_always(self, active: bool) -> bool {
        self.is_active() == Some(active)
    }

    pub fn is_const(self) -> bool {
        self.net().as_const().is_some()
    }

    pub fn visit(self, f: impl FnMut(Net)) {
        match self {
            ControlNet::Pos(net) => net.visit(f),
            ControlNet::Neg(net) => net.visit(f),
        }
    }

    pub fn visit_mut(&mut self, f: impl FnMut(&mut Net)) {
        match self {
            ControlNet::Pos(net) => net.visit_mut(f),
            ControlNet::Neg(net) => net.visit_mut(f),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Net, Trit};

    #[test]
    fn test_net() {
        assert_eq!(Net::from(Trit::Zero), Net::ZERO);
        assert_eq!(Net::from(Trit::One), Net::ONE);
        assert_eq!(Net::from(Trit::Undef), Net::UNDEF);
        assert_eq!(Net::from_cell(3), Net { index: 5 });
    }

    #[test]
    fn test_from_bool() {
        assert_eq!(Net::from(false), Net::ZERO);
        assert_eq!(Net::from(true), Net::ONE);
    }

    #[test]
    fn test_from_trit() {
        assert_eq!(Net::from(Trit::Zero), Net::ZERO);
        assert_eq!(Net::from(Trit::One), Net::ONE);
        assert_eq!(Net::from(Trit::Undef), Net::UNDEF);
    }

    #[test]
    fn test_net_debug() {
        assert_eq!(format!("{:?}", Net::ZERO), "Net::ZERO");
        assert_eq!(format!("{:?}", Net::ONE), "Net::ONE");
        assert_eq!(format!("{:?}", Net::UNDEF), "Net::UNDEF");
        assert_eq!(format!("{:?}", Net::from_cell(0)), "Net::from_cell(0)");
    }
}
