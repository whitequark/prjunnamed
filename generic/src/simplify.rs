use prjunnamed_netlist::{Design, Trit, Value};
use prjunnamed_pattern::{netlist_replace, patterns::*};

pub fn simplify(design: &mut Design) -> bool {
    let rules = netlist_replace! {
        let design;

        [PBuf [PAny@a]]              => a;

        [PNot [PConst@a]]            => a.not();
        [PNot [PNot [PAny@a]]]       => a;

        [PAnd [PConst@a] [PConst@b]] => a.and(b);
        [PAnd [PAny@a]   [POnes]]    => a;
        [PAnd [POnes]    [PAny@a]]   => a;
        [PAnd [PAny@a]   [PZero]]    => Value::zero(a.len());
        [PAnd [PZero]    [PAny@a]]   => Value::zero(a.len());

        [POr  [PConst@a] [PConst@b]] => a.or(b);
        [POr  [PAny@a]   [PZero]]    => a;
        [POr  [PZero]    [PAny@a]]   => a;
        [POr  [PAny@a]   [POnes]]    => Value::ones(a.len());
        [POr  [POnes]    [PAny@a]]   => Value::ones(a.len());

        [PXor [PConst@a] [PConst@b]] => a.xor(b);
        [PXor [PAny@a]   [PZero]]    => a;
        [PXor [PZero]    [PAny@a]]   => a;
        [PXor [PAny@a]   [POnes]]    => design.add_not(a);
        [PXor [POnes]    [PAny@a]]   => design.add_not(a);
        [PXor [PAny@a]   [PUndef]]   => Value::undef(a.len());
        [PXor [PUndef]   [PAny@a]]   => Value::undef(a.len());
        [PXor [PAny@a]   [PAny@b]]   if a == b => Value::zero(a.len());

        [PMux [POnes]    [PAny@a]   [PAny]]         => a;
        [PMux [PZero]    [PAny]     [PAny@b]]       => b;
        [PMux [PAny]     [PAny@a]   [PUndef]]       => a;
        [PMux [PAny]     [PUndef]   [PAny@b]]       => b;
        [PMux [PAny]     [PAny@a]   [PAny@b]]       if a == b => a;

        [PMux@y [PAny@s] [POnes]    [PZero]]        => Value::from(s).sext(y.len());
        [PMux@y [PAny@s] [PZero]    [POnes]]        => design.add_not(s).sext(y.len());

        [PAnd [PNot [PAny@a]] [PNot [PAny@b]]]      => design.add_not(design.add_or (a, b));
        [POr  [PNot [PAny@a]] [PNot [PAny@b]]]      => design.add_not(design.add_and(a, b));

        [PXor [PNot [PAny@a]] [PNot [PAny@b]]]      => design.add_xor(a, b);
        [PXor [PNot [PAny@a]] [PAny@b]]             => design.add_not(design.add_xor(a, b));
        [PXor [PAny@a]        [PNot [PAny@b]]]      => design.add_not(design.add_xor(a, b));

        [PMux [PNot [PAny@s]] [PAny@a] [PAny@b]]    => design.add_mux(s, b, a);

        [PAdc   [PConst@a] [PConst@b] [PConst@c]]   => a.adc(b, c);
        [PAdc@y [PAny@a]   [PZero]    [PZero]]      => a.zext(y.len());
        [PAdc@y [PZero]    [PAny@b]   [PZero]]      => b.zext(y.len());
        [PAdc@y [PZero]    [PZero]    [PAny@c]]     => Value::from(c).zext(y.len());

        [PEq  [PConst@a] [PConst@b]]    => a.eq(b);
        [PEq  [PAny@a]   [POnes]]       if a.len() == 1 => a;
        [PEq  [POnes]    [PAny@a]]      if a.len() == 1 => a;
        [PEq  [PAny@a]   [PZero]]       if a.len() == 1 => design.add_not(a);
        [PEq  [PZero]    [PAny@a]]      if a.len() == 1 => design.add_not(a);
        [PEq  [PAny@a]   [PAny@b]]      if a == b => Trit::One;

        [PULt [PConst@a] [PConst@b]]    => a.ult(b);
        [PULt [PAny]     [PZero]]       => Trit::Zero;
        [PULt [POnes]    [PAny]]        => Trit::Zero;
        [PULt [PHasX]    [PAny]]        => Trit::Undef;
        [PULt [PAny]     [PHasX]]       => Trit::Undef;
        [PULt [PAny@a]   [PAny@b]]      if a == b => Trit::Zero;

        [PSLt [PConst@a] [PConst@b]]    => a.slt(b);
        [PSLt [PHasX]    [PAny]]        => Trit::Undef;
        [PSLt [PAny]     [PHasX]]       => Trit::Undef;
        [PSLt [PAny@a]   [PAny@b]]      if a == b => Trit::Zero;

        [PShl    [PAny@a] [PConst@b] [PAny@s]]  => a.shl(b, s);
        [PShl    [PAny@a] [PAny]     [PZero]]   => a;
        [PShl@y  [PZero]  [PAny]     [PAny]]    => Value::zero(y.len());

        [PUShr   [PAny@a] [PConst@b] [PAny@s]]  => a.ushr(b, s);
        [PUShr   [PAny@a] [PAny]     [PZero]]   => a;
        [PUShr@y [PZero]  [PAny]     [PAny]]    => Value::zero(y.len());

        [PSShr   [PAny@a] [PConst@b] [PAny@s]]  => a.sshr(b, s);
        [PSShr   [PAny@a] [PAny]     [PZero]]   => a;
        [PSShr@y [PZero]  [PAny]     [PAny]]    => Value::zero(y.len());
        [PSShr@y [POnes]  [PAny]     [PAny]]    => Value::ones(y.len());

        [PXShr   [PAny@a] [PConst@b] [PAny@s]]  => a.xshr(b, s);
        [PXShr   [PAny@a] [PAny]     [PZero]]   => a;
        [PXShr@y [PZero]  [PAny]     [PAny]]    => Value::zero(y.len());

        [PMul    [PConst@a] [PConst@b]] => a.mul(b);
        [PMul@y  [PAny]     [PHasX]]    => Value::undef(y.len());
        [PMul@y  [PHasX]    [PAny]]     => Value::undef(y.len());
        [PMul@y  [PAny]     [PZero]]    => Value::zero(y.len());
        [PMul@y  [PZero]    [PAny]]     => Value::zero(y.len());
        [PMul    [PAny@a]   [PPow2@b]]  => a.shl(Trit::One, b);
        [PMul    [PPow2@a]  [PAny@b]]   => b.shl(Trit::One, a);

        // [PUDiv   [PConst@a] [PConst@b]] => a.udiv(b);
        [PUDiv@y [PZero]    [PAny]]     => Value::zero(y.len());
        [PUDiv@y [PAny]     [PZero]]    => Value::undef(y.len());
        [PUDiv   [PAny@a]   [PPow2@b]]  => a.ushr(Trit::One, b);

        // [PUMod   [PConst@a] [PConst@b]] => a.umod(b);
        [PUMod@y [PZero]    [PAny]]     => Value::zero(y.len());
        [PUMod@y [PAny]     [PZero]]    => Value::undef(y.len());
        [PUMod   [PAny@a]   [PPow2@b]]  =>
            if (b as usize) < a.len() { Value::from(&a[..(b as usize)]).zext(a.len()) } else { a };

        [PSDivTrunc@y [PZero] [PAny]]   => Value::zero(y.len());
        [PSDivTrunc@y [PAny]  [PZero]]  => Value::undef(y.len());
        [PSModTrunc@y [PZero] [PAny]]   => Value::zero(y.len());
        [PSModTrunc@y [PAny]  [PZero]]  => Value::undef(y.len());

        [PSDivFloor@y [PZero] [PAny]]   => Value::zero(y.len());
        [PSDivFloor@y [PAny]  [PZero]]  => Value::undef(y.len());
        [PSModFloor@y [PZero] [PAny]]   => Value::zero(y.len());
        [PSModFloor@y [PAny]  [PZero]]  => Value::undef(y.len());
    };

    for value in design.iter_cells().map(|cell_ref| cell_ref.output()) {
        // Fine rules are more powerful, but some rules are coarse-only.
        if rules(design, &value) {
            continue;
        }
        for net in &value {
            rules(design, &Value::from(net));
        }
    }
    design.compact()
}

#[cfg(test)]
mod test {
    use prjunnamed_netlist::{Const, Design, Net, Trit, Value};
    use prjunnamed_pattern::{assert_netlist, netlist_matches, patterns::*};

    use super::simplify;

    macro_rules! assert_simplify {
        ( $( |$design:ident| $build:expr ),+ ; $( $match:tt )+ ) => {
            let rules = netlist_matches! {
                $( $match )+
            };
            $(
                let mut $design = Design::new();
                $design.add_output("y", $build);
                $design.apply();
                let design_before = $design.clone();
                simplify(&mut $design);
                assert_netlist!($design, rules, "simplify failed on:\n{}\nresult:{}", design_before, $design);
            )+
        };
    }

    fn iter_interesting_consts() -> impl Iterator<Item = Const> {
        ["0", "1", "X", "00", "11", "XX", "01", "10"].into_iter().map(Const::from_str)
    }

    fn iter_has_undef_consts() -> impl Iterator<Item = Const> {
        ["X", "XX", "0X", "X1"].into_iter().map(Const::from_str)
    }

    fn iter_interesting_const_pairs() -> impl Iterator<Item = (Const, Const)> {
        iter_interesting_consts().flat_map(|value1| {
            iter_interesting_consts().filter_map(move |value2| {
                if value1.len() == value2.len() {
                    Some((value1.clone(), value2))
                } else {
                    None
                }
            })
        })
    }

    #[test]
    fn test_not_const_eval() {
        for value in iter_interesting_consts() {
            assert_simplify!(
                |design| design.add_not(&value);
                [PConst@a] => (a == value.not());
            );
        }
    }

    #[test]
    fn test_not_not() {
        assert_simplify!(
            |ds| ds.add_not(ds.add_not(ds.add_input("a", 2)));
            [PInput ("a")] => true;
        );
    }

    #[test]
    fn test_and_const_eval() {
        for (value1, value2) in iter_interesting_const_pairs() {
            assert_simplify!(
                |ds| ds.add_and(&value1, &value2);
                [PConst@a] => (a == value1.and(&value2));
            );
        }
    }

    #[test]
    fn test_and_fold() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_and(Const::zero(size), ds.add_input("a", size)),
                |ds| ds.add_and(ds.add_input("a", size), Const::zero(size));
                [PZero] => true;
            );
            assert_simplify!(
                |ds| ds.add_and(Const::ones(size), ds.add_input("a", size)),
                |ds| ds.add_and(ds.add_input("a", size), Const::ones(size));
                [PInput ("a")] => true;
            );
        }
    }

    #[test]
    fn test_or_const_eval() {
        for (value1, value2) in iter_interesting_const_pairs() {
            assert_simplify!(
                |ds| ds.add_or(&value1, &value2);
                [PConst@a] => a == value1.or(&value2);
            );
        }
    }

    #[test]
    fn test_or_fold() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_or(Const::zero(size), ds.add_input("a", size)),
                |ds| ds.add_or(ds.add_input("a", size), Const::zero(size));
                [PInput ("a")] => true;
            );
            assert_simplify!(
                |ds| ds.add_or(Const::ones(size), ds.add_input("a", size)),
                |ds| ds.add_or(ds.add_input("a", size), Const::ones(size));
                [POnes] => true;
            );
        }
    }

    #[test]
    fn test_xor_const_eval() {
        for (value1, value2) in iter_interesting_const_pairs() {
            assert_simplify!(
                |ds| ds.add_xor(&value1, &value2);
                [PConst@a] => a == value1.xor(&value2);
            );
        }
    }

    #[test]
    fn test_xor_fold() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_xor(Const::zero(size), ds.add_input("a", size)),
                |ds| ds.add_xor(ds.add_input("a", size), Const::zero(size));
                [PInput ("a")] => true;
            );
            assert_simplify!(
                |ds| ds.add_xor(Const::ones(size), ds.add_input("a", size)),
                |ds| ds.add_xor(ds.add_input("a", size), Const::ones(size));
                [PNot [PInput ("a")]] => true;
            );
            assert_simplify!(
                |ds| ds.add_xor(Const::undef(size), ds.add_input("a", size)),
                |ds| ds.add_xor(ds.add_input("a", size), Const::undef(size));
                [PUndef] => true;
            );
            assert_simplify!(
                |ds| {let a = ds.add_input("a", size); ds.add_xor(&a, &a)};
                [PZero] => true;
            );
        }
    }

    #[test]
    fn test_mux_fold() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_mux(Net::ZERO, ds.add_input("a", size), ds.add_input("b", size));
                [PInput ("b")] => true;
            );
            assert_simplify!(
                |ds| ds.add_mux(Net::ONE, ds.add_input("a", size), ds.add_input("b", size));
                [PInput ("a")] => true;
            );
            assert_simplify!(
                |ds| ds.add_mux(ds.add_input("s", 1)[0], ds.add_input("a", size), Const::undef(size));
                [PInput ("a")] => true;
            );
            assert_simplify!(
                |ds| ds.add_mux(ds.add_input("s", 1)[0], Const::undef(size), ds.add_input("b", size));
                [PInput ("b")] => true;
            );
            assert_simplify!(
                |ds| { let a = ds.add_input("a", size); ds.add_mux(ds.add_input("s", 1)[0], &a, &a) };
                [PInput ("a")] => true;
            );
            assert_simplify!(
                |ds| ds.add_mux(ds.add_input("s", 1)[0], Const::ones(size), Const::zero(size));
                [PSExt [PAny@s]] if s.len() == 1 => true;
            );
        }
    }

    #[test]
    fn test_demorgan() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_and(ds.add_not(ds.add_input("a", size)), ds.add_not(ds.add_input("b", size)));
                [PNot [POr [PInput ("a")] [PInput ("b")]]] => true;
            );
            assert_simplify!(
                |ds| ds.add_or(ds.add_not(ds.add_input("a", size)), ds.add_not(ds.add_input("b", size)));
                [PNot [PAnd [PInput ("a")] [PInput ("b")]]] => true;
            );
        }
    }

    #[test]
    fn test_xor_not_push() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_xor(ds.add_not(ds.add_input("a", size)), ds.add_not(ds.add_input("b", size)));
                [PXor [PInput ("a")] [PInput ("b")]] => true;
            );
            assert_simplify!(
                |ds| ds.add_xor(ds.add_not(ds.add_input("a", size)), ds.add_input("b", size)),
                |ds| ds.add_xor(ds.add_input("a", size), ds.add_not(ds.add_input("b", size)));
                [PNot [PXor [PInput ("a")] [PInput ("b")]]] => true;
            );
        }
    }

    #[test]
    fn test_mux_flip() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_mux(ds.add_not(ds.add_input("s", 1))[0], ds.add_input("a", size), ds.add_input("b", size));
                [PMux [PInput ("s")] [PInput ("b")] [PInput ("a")]] => true;
            );
        }
    }

    #[test]
    fn test_adc_const_eval() {
        for carry in [Trit::Zero, Trit::One, Trit::Undef] {
            for (value1, value2) in iter_interesting_const_pairs() {
                assert_simplify!(
                    |ds| ds.add_adc(&value1, &value2, carry);
                    [PConst@a] => a == value1.adc(&value2, carry);
                );
            }
        }
    }

    #[test]
    fn test_adc_fold() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_adc(Const::zero(size), ds.add_input("a", size), Net::ZERO),
                |ds| ds.add_adc(ds.add_input("a", size), Const::zero(size), Net::ZERO);
                [PZExt [PInput ("a")]] => true;
            );
            assert_simplify!(
                |ds| ds.add_adc(Const::zero(size), Const::zero(size), ds.add_input("c", 1)[0]);
                [PZExt [PInput ("c")]] => true;
            );
        }
    }

    #[test]
    fn test_eq_const_eval() {
        for (value1, value2) in iter_interesting_const_pairs() {
            assert_simplify!(
                |ds| ds.add_eq(&value1, &value2);
                [PConst@a] => a == Const::from(value1.eq(&value2));
            );
        }
    }

    #[test]
    fn test_eq_fold() {
        assert_simplify!(
            |ds| ds.add_eq(Const::ones(1), ds.add_input("a", 1)),
            |ds| ds.add_eq(ds.add_input("a", 1), Const::ones(1));
            [PInput ("a")] => true;
        );
        assert_simplify!(
            |ds| ds.add_eq(Const::zero(1), ds.add_input("a", 1)),
            |ds| ds.add_eq(ds.add_input("a", 1), Const::zero(1));
            [PNot [PInput ("a")]] => true;
        );
        for size in [1, 2] {
            assert_simplify!(
                |ds| {let a = ds.add_input("a", size); ds.add_eq(&a, &a)};
                [POnes] => true;
            );
        }
    }

    #[test]
    fn test_ult_const_eval() {
        for (value1, value2) in iter_interesting_const_pairs() {
            assert_simplify!(
                |ds| ds.add_ult(&value1, &value2);
                [PConst@a] => a == Const::from(value1.ult(&value2));
            );
        }
    }

    #[test]
    fn test_ult_fold() {
        for size in [1, 2] {
            assert_simplify!(
                |ds| ds.add_ult(ds.add_input("a", size), Value::zero(size));
                [PZero] => true;
            );
            assert_simplify!(
                |ds| ds.add_ult(Value::ones(size), ds.add_input("a", size));
                [PZero] => true;
            );
            for a in iter_has_undef_consts().filter(|c| c.len() == size) {
                assert_simplify!(
                    |ds| ds.add_ult(&a, ds.add_input("a", size)),
                    |ds| ds.add_ult(ds.add_input("a", size), &a);
                    [PUndef] => true;
                );
            }
            assert_simplify!(
                |ds| {let a = ds.add_input("a", size); ds.add_ult(&a, &a)};
                [PZero] => true;
            );
        }
    }

    #[test]
    fn test_slt_const_eval() {
        for (value1, value2) in iter_interesting_const_pairs() {
            assert_simplify!(
                |ds| ds.add_slt(&value1, &value2);
                [PConst@a] => a == Const::from(value1.slt(&value2));
            );
        }
    }

    #[test]
    fn test_slt_fold() {
        for size in [1, 2] {
            for a in iter_has_undef_consts().filter(|c| c.len() == size) {
                assert_simplify!(
                    |ds| ds.add_slt(&a, ds.add_input("a", size)),
                    |ds| ds.add_slt(ds.add_input("a", size), &a);
                    [PUndef] => true;
                );
            }
            assert_simplify!(
                |ds| {let a = ds.add_input("a", size); ds.add_slt(&a, &a)};
                [PZero] => true;
            );
        }
    }

    #[test]
    fn test_shl_fold() {
        for size in [2, 4] {
            for size2 in [2, 4] {
                assert_simplify!(
                    |ds| ds.add_shl(Value::zero(size), ds.add_input("a", size2), 1);
                    [PZero] => true;
                );
                assert_simplify!(
                    |ds| ds.add_shl(ds.add_input("a", size), ds.add_input("b", size2), 0);
                    [PInput ("a")] => true;
                );
            }
        }
    }
}
