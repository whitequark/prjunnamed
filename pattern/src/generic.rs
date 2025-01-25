use prjunnamed_netlist::{CellRepr, Design, Value, Const};

use crate::Pattern;

macro_rules! pattern {
    {} => {};

    { generic $name:ident : $capture:ty => |$design:ident, $value:ident| $code:block; $($rest:tt)* } => {
        pub struct $name;

        impl $name {
            pub fn new() -> Self {
                $name
            }
        }

        impl Pattern for $name {
            type Capture = $capture;

            fn execute(&self, $design: &Design, $value: &Value) -> Option<Self::Capture> $code
        }

        pattern!{ $($rest)* }
    };

    {
        cell $patname:ident($( $cap:ident : $pty:ident ),+) => |$design:ident, $value:ident| $body:block;
        $($rest:tt)*
    } => {
        pub struct $patname<$( $pty: Pattern ),+> {
            $( $cap: $pty ),+
        }

        impl<$( $pty: Pattern ),+> $patname<$( $pty ),+> {
            pub fn new($( $cap: $pty ),+) -> Self {
                $patname { $( $cap ),+ }
            }
        }

        impl<$( $pty: Pattern ),+> Pattern for $patname<$( $pty ),+> {
            type Capture = (Value, $( $pty::Capture ),+);

            fn execute(&self, $design: &Design, $value: &Value) -> Option<Self::Capture> {
                $(
                    #[allow(unused_assignments)]
                    let mut $cap = vec![];
                )+
                $body
                $(
                    let $cap = match self.$cap.execute($design, &$design.map_value(Value::from_iter($cap))) {
                        Some(capture) => capture,
                        _ => return None
                    };
                )+
                Some(($value.clone(), $( $cap ),+))
            }
        }

        pattern! { $($rest)* }
    };

    { cell $patname:ident(_) => bitwise $cellname:ident; $($rest:tt)* } => {
        pattern! {
            cell $patname(cap: P1) => |design, value| {
                for net in value {
                    if let Ok((cell_ref, offset)) = design.find_cell(net) {
                        match &*cell_ref.repr() {
                            CellRepr::$cellname(value) => cap.push(value[offset]),
                            _ => return None
                        }
                    } else {
                        return None
                    }
                }
            };

            $($rest)*
        }
    };

    { cell $patname:ident(_, _) => bitwise $cellname:ident; $($rest:tt)* } => {
        pattern! {
            cell $patname(cap1: P1, cap2: P2) => |design, value| {
                for net in value {
                    if let Ok((cell_ref, offset)) = design.find_cell(net) {
                        match &*cell_ref.repr() {
                            CellRepr::$cellname(val1, val2) => {
                                cap1.push(val1[offset]);
                                cap2.push(val2[offset]);
                            }
                            _ => return None
                        }
                    } else {
                        return None
                    }
                }
            };

            $($rest)*
        }
    };

    { cell $patname:ident(_, _) => compare $cellname:ident; $($rest:tt)* } => {
        pattern! {
            cell $patname(cap1: P1, cap2: P2) => |design, value| {
                if value.len() != 1 { return None }
                if let Ok((cell_ref, _offset)) = design.find_cell(value[0]) {
                    match &*cell_ref.repr() {
                        CellRepr::$cellname(val1, val2) => {
                            cap1 = Vec::from_iter(val1);
                            cap2 = Vec::from_iter(val2);
                        }
                        _ => return None
                    }
                } else {
                    return None
                }
            };

            $($rest)*
        }
    };

    { cell $patname:ident(_, _) => arithmetic $cellname:ident; $($rest:tt)* } => {
        pattern! {
            cell $patname(cap1: P1, cap2: P2) => |design, value| {
                if value.len() == 0 { return None }
                if let Ok((cell_ref, 0)) = design.find_cell(value[0]) {
                    match &*cell_ref.repr() {
                        CellRepr::$cellname(val1, val2) if cell_ref.output() == *value => {
                            cap1 = Vec::from_iter(val1);
                            cap2 = Vec::from_iter(val2);
                        }
                        _ => return None
                    }
                } else {
                    return None
                }
            };

            $($rest)*
        }
    };
}

pattern! {
    generic PAny : (Value,) => |_design, value| {
        Some((value.clone(),))
    };

    generic PConst : (Const,) => |_design, value| {
        value.as_const().map(|x| (x,))
    };

    generic PZero : (usize,) => |_design, value| {
        value.as_const().and_then(|x| if x.is_zero() { Some((value.len(),)) } else { None })
    };

    generic POnes : (usize,) => |_design, value| {
        value.as_const().and_then(|x| if x.is_ones() { Some((value.len(),)) } else { None })
    };

    generic PUndef : (usize,) => |_design, value| {
        value.as_const().and_then(|x| if x.is_undef() { Some((value.len(),)) } else { None })
    };

    cell PBuf(_) => bitwise Buf;
    cell PNot(_) => bitwise Not;
    cell PAnd(_, _) => bitwise And;
    cell POr(_, _) => bitwise Or;
    cell PXor(_, _) => bitwise Xor;

    cell PMux(cap1: P1, cap2: P2, cap3: P3) => |design, value| {
        if value.len() == 0 { return None }
        for net in value {
            if let Ok((cell_ref, offset)) = design.find_cell(net) {
                match &*cell_ref.repr() {
                    CellRepr::Mux(val1, val2, val3) => {
                        if cap1.len() == 0 {
                            cap1.push(*val1);
                        } else if cap1[0] != *val1 {
                            return None
                        }
                        cap2.push(val2[offset]);
                        cap3.push(val3[offset]);
                    }
                    _ => return None,
                }
            } else {
                return None
            }
        }
    };

    cell PAdc(cap1: P1, cap2: P2, cap3: P3) => |design, value| {
        if value.len() == 0 { return None }
        if let Ok((cell_ref, 0)) = design.find_cell(value[0]) {
            match &*cell_ref.repr() {
                CellRepr::Adc(val1, val2, val3) if cell_ref.output() == *value => {
                    cap1 = Vec::from_iter(val1);
                    cap2 = Vec::from_iter(val2);
                    cap3 = vec![*val3];
                }
                _ => return None
            }
        } else {
            return None
        }
    };

    cell PEq(_, _) => compare Eq;
    cell PULt(_, _) => compare ULt;
    cell PSLt(_, _) => compare SLt;

    // Shl(Value, Value, u32),
    // UShr(Value, Value, u32),
    // SShr(Value, Value, u32),
    // XShr(Value, Value, u32),

    cell PMul(_, _) => arithmetic Mul;
    cell PUDiv(_, _) => arithmetic UDiv;
    cell PUMod(_, _) => arithmetic UMod;
    cell PSDivTrunc(_, _) => arithmetic SDivTrunc;
    cell PSDivFloor(_, _) => arithmetic SDivFloor;
    cell PSModTrunc(_, _) => arithmetic SModTrunc;
    cell PSModFloor(_, _) => arithmetic SModFloor;
}
