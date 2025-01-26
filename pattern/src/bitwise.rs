use prjunnamed_netlist::{CellRepr, Design, Net};

use crate::{NetOrValue, Pattern};

macro_rules! bitwise_patterns {
    {} => {};

    { $name:ident(_) => $repr:ident; $($rest:tt)* } => {
        pub struct $name<P>(P);

        impl<P> $name<P> {
            pub fn new(pat: P) -> $name<P> {
                $name(pat)
            }
        }

        impl<T: NetOrValue, P: Pattern<T>> Pattern<T> for $name<P> {
            type Capture = (T, P::Capture);

            fn execute(&self, design: &Design, target: &T) -> Option<Self::Capture> {
                let mut cap = None;
                for net in target.iter() {
                    if let Ok((cell_ref, offset)) = design.find_cell(net) {
                        if let CellRepr::$repr(arg) = &*cell_ref.repr() {
                            assert!(T::accumulate(&mut cap, arg[offset]));
                        } else {
                            return None
                        }
                    } else {
                        return None
                    }
                }
                self.0.execute(design, &cap.unwrap()).and_then(|cap|
                    Some((target.clone(), cap)))
            }
        }

        bitwise_patterns!{ $($rest)* }
    };

    { $name:ident(_,_) => $repr:ident; $($rest:tt)* } => {
        pub struct $name<P1, P2>(P1, P2);

        impl<P1, P2> $name<P1, P2> {
            pub fn new(pat1: P1, pat2: P2) -> $name<P1, P2> {
                $name(pat1, pat2)
            }
        }

        impl<T: NetOrValue, P1: Pattern<T>, P2: Pattern<T>> Pattern<T> for $name<P1, P2> {
            type Capture = (T, P1::Capture, P2::Capture);

            fn execute(&self, design: &Design, target: &T) -> Option<Self::Capture> {
                let mut cap1 = None;
                let mut cap2 = None;
                for net in target.iter() {
                    if let Ok((cell_ref, offset)) = design.find_cell(net) {
                        if let CellRepr::$repr(arg1, arg2) = &*cell_ref.repr() {
                            assert!(T::accumulate(&mut cap1, arg1[offset]));
                            assert!(T::accumulate(&mut cap2, arg2[offset]));
                        } else {
                            return None
                        }
                    } else {
                        return None
                    }
                }
                self.0.execute(design, &cap1.unwrap()).and_then(|cap1|
                    self.1.execute(design, &cap2.unwrap()).and_then(|cap2|
                        Some((target.clone(), cap1, cap2))))
            }
        }

        bitwise_patterns!{ $($rest)* }
    }
}

bitwise_patterns! {
    PBuf(_) => Buf;
    PNot(_) => Not;

    PAnd(_, _) => And;
    POr(_, _) => Or;
    PXor(_, _) => Xor;
}

pub struct PMux<P1, P2, P3>(P1, P2, P3);

impl<P1, P2, P3> PMux<P1, P2, P3> {
    pub fn new(pat1: P1, pat2: P2, pat3: P3) -> PMux<P1, P2, P3> {
        PMux(pat1, pat2, pat3)
    }
}

impl<T: NetOrValue, P1: Pattern<Net>, P2: Pattern<T>, P3: Pattern<T>> Pattern<T> for PMux<P1, P2, P3> {
    type Capture = (T, P1::Capture, P2::Capture, P3::Capture);

    fn execute(&self, design: &Design, target: &T) -> Option<Self::Capture> {
        let mut cap1 = None;
        let mut cap2 = None;
        let mut cap3 = None;
        for net in target.iter() {
            if let Ok((cell_ref, offset)) = design.find_cell(net) {
                if let CellRepr::Mux(arg1, arg2, arg3) = &*cell_ref.repr() {
                    if !NetOrValue::accumulate(&mut cap1, *arg1) {
                        return None
                    }
                    assert!(T::accumulate(&mut cap2, arg2[offset]));
                    assert!(T::accumulate(&mut cap3, arg3[offset]));
                } else {
                    return None
                }
            } else {
                return None
            }
        }
        self.0.execute(design, &cap1.unwrap()).and_then(|cap1|
            self.1.execute(design, &cap2.unwrap()).and_then(|cap2|
                self.2.execute(design, &cap3.unwrap()).and_then(|cap3|
                    Some((target.clone(), cap1, cap2, cap3)))))
    }
}
