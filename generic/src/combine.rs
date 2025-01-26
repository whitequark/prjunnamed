use prjunnamed_netlist::{Design, Trit, Value};
use prjunnamed_pattern::{netlist_rules, patterns::*};

pub fn combine(design: &mut Design) {
    let rules = netlist_rules! {
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

        [PMux [POnes]    [PAny@a]   [PAny]]       => a;
        [PMux [PZero]    [PAny]     [PAny@b]]     => b;
        [PMux [PAny]     [PAny@a]   [PUndef]]     => a;
        [PMux [PAny]     [PUndef]   [PAny@b]]     => b;
        [PMux [PAny]     [PAny@a]   [PAny@b]]     if (a == b) => a;

        [PAnd [PNot [PAny@a]] [PNot [PAny@b]]]    => design.add_not(design.add_or (a, b));
        [POr  [PNot [PAny@a]] [PNot [PAny@b]]]    => design.add_not(design.add_and(a, b));

        [PXor [PNot [PAny@a]] [PNot [PAny@b]]]    => design.add_xor(a, b);
        [PXor [PNot [PAny@a]] [PAny@b]]           => design.add_not(design.add_xor(a, b));
        [PXor [PAny@a]        [PNot [PAny@b]]]    => design.add_not(design.add_xor(a, b));

        [PMux [PNot [PAny@s]] [PAny@a] [PAny@b]]  => design.add_mux(s, b, a);

        [PAdc   [PConst@a] [PConst@b] [PConst@c]] => a.adc(b, c);
        [PAdc@y [PAny@a]   [PZero]    [PZero]]    => a.zext(y.len());
        [PAdc@y [PZero]    [PAny@b]   [PZero]]    => b.zext(y.len());
        [PAdc@y [PZero]    [PZero]    [PAny@c]]   => Value::from(c).zext(y.len());

        [PEq  [PConst@a] [PConst@b]] => a.eq(b);
        [PEq  [PAny@a]   [POnes]]    if (a.len() == 1) => a;
        [PEq  [POnes]    [PAny@a]]   if (a.len() == 1) => a;
        [PEq  [PAny@a]   [PZero]]    if (a.len() == 1) => design.add_not(a);
        [PEq  [PZero]    [PAny@a]]   if (a.len() == 1) => design.add_not(a);
        [PEq  [PAny@a]   [PAny@b]]   if (a == b) => Trit::One;

        [PULt [PConst@a] [PConst@b]] => a.ult(b);
        [PULt [PAny]     [PZero]]    => Trit::Zero;
        [PULt [POnes]    [PAny]]     => Trit::Zero;
        [PULt [PAny@a]   [PAny@b]]   if (a == b) => Trit::Zero;

        [PSLt [PConst@a] [PConst@b]] => a.slt(b);
        [PSLt [PAny@a]   [PAny@b]]   if (a == b) => Trit::Zero;
    };

    loop {
        for value in design.iter_cells().map(|cell_ref| cell_ref.output()) {
            // Fine rules are more powerful, but some rules are coarse-only.
            let mut matched = false;
            for net in &value {
                if rules(design, &Value::from(net)) {
                    matched = true;
                }
            }
            if !matched {
                rules(design, &value);
            }
        }
        if !design.apply() {
            break
        }
        design.compact();
    }
}
