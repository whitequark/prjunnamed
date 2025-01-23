use std::fmt::Debug;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Net {
    pub(crate) index: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NetRepr {
    Zero,
    One,
    Undef,
    Cell(u32),
}

impl Net {
    pub const ZERO: Net = Net { index: 0 };
    pub const ONE: Net = Net { index: 1 };
    pub const UNDEF: Net = Net { index: 2 };

    const FIRST_CELL: u32 = 3; // Zero, One, Undef, Cell...

    pub fn cell(cell_index: u32) -> Net {
        Net { index: cell_index.checked_add(Net::FIRST_CELL).unwrap() }
    }

    pub fn repr(self) -> NetRepr {
        NetRepr::from(self)
    }
}

impl From<Net> for NetRepr {
    fn from(value: Net) -> Self {
        if value == Net::ZERO {
            Self::Zero
        } else if value == Net::ONE {
            Self::One
        } else if value == Net::UNDEF {
            Self::Undef
        } else {
            Self::Cell(value.index.checked_sub(Net::FIRST_CELL).unwrap())
        }
    }
}

impl From<NetRepr> for Net {
    fn from(value: NetRepr) -> Self {
        match value {
            NetRepr::Zero => Net::ZERO,
            NetRepr::One => Net::ONE,
            NetRepr::Undef => Net::UNDEF,
            NetRepr::Cell(cell_index) => Net::cell(cell_index),
        }
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

impl Debug for Net {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Net { index: 0 } => write!(f, "Net::ZERO"),
            Net { index: 1 } => write!(f, "Net::ONE"),
            Net { index: 2 } => write!(f, "Net::UNDEF"),
            _ => {
                let cell_index = self.index.checked_sub(Net::FIRST_CELL).unwrap();
                write!(f, "Net::cell({cell_index})")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Net, NetRepr};

    #[test]
    fn test_net() {
        assert_eq!(Net::ZERO.repr(), NetRepr::Zero);
        assert_eq!(Net::ONE.repr(), NetRepr::One);
        assert_eq!(Net::UNDEF.repr(), NetRepr::Undef);
        assert_eq!(Net { index: 7 }.repr(), NetRepr::Cell(4));

        assert_eq!(Net::from(NetRepr::Zero), Net::ZERO);
        assert_eq!(Net::from(NetRepr::One), Net::ONE);
        assert_eq!(Net::from(NetRepr::Undef), Net::UNDEF);
        assert_eq!(Net::from(NetRepr::Cell(3)), Net { index: 6 });
    }

    #[test]
    fn test_from_bool() {
        assert_eq!(Net::from(false), Net::ZERO);
        assert_eq!(Net::from(true), Net::ONE);
    }

    #[test]
    fn test_net_debug() {
        assert_eq!(format!("{:?}", Net::ZERO), "Net::ZERO");
        assert_eq!(format!("{:?}", Net::ONE), "Net::ONE");
        assert_eq!(format!("{:?}", Net::UNDEF), "Net::UNDEF");
        assert_eq!(format!("{:?}", Net::from(NetRepr::Cell(0))), "Net::cell(0)");
    }
}
