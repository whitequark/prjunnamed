use prjunnamed_netlist::{Design, Trit, Value};
use prjunnamed_pattern::{netlist_rules, generic::*};

pub fn combine(design: &mut Design) {
    let rules = netlist_rules! {
        with(design);

        [PBuf@y [PAny@a]]              => design.replace_value(y, a);

        [PNot@y [PConst@a]]            => design.replace_value(y, a.not());
        [PNot@y [PNot [PAny@a]]]       => design.replace_value(y, a);

        [PAnd@y [PConst@a] [PConst@b]] => design.replace_value(y, a.and(b));
        [PAnd@y [PAny@a]   [POnes]]    => design.replace_value(y, a);
        [PAnd@y [POnes]    [PAny@a]]   => design.replace_value(y, a);
        [PAnd@y [PAny]     [PZero]]    => design.replace_value(&y, Value::zero(y.len()));
        [PAnd@y [PZero]    [PAny]]     => design.replace_value(&y, Value::zero(y.len()));

        [POr@y  [PConst@a] [PConst@b]] => design.replace_value(y, a.or(b));
        [POr@y  [PAny@a]   [PZero]]    => design.replace_value(y, a);
        [POr@y  [PZero]    [PAny@a]]   => design.replace_value(y, a);
        [POr@y  [PAny]     [POnes]]    => design.replace_value(&y, Value::ones(y.len()));
        [POr@y  [POnes]    [PAny]]     => design.replace_value(&y, Value::ones(y.len()));

        [PAnd@y [PNot [PAny@a]] [PNot [PAny@b]]]  => design.replace_value(y, design.add_not(design.add_or (a, b)));
        [POr@y  [PNot [PAny@a]] [PNot [PAny@b]]]  => design.replace_value(y, design.add_not(design.add_and(a, b)));

        [PXor@y [PConst@a] [PConst@b]] => design.replace_value(y, a.xor(b));
        [PXor@y [PAny@a]   [PZero]]    => design.replace_value(y, a);
        [PXor@y [PZero]    [PAny@a]]   => design.replace_value(y, a);
        [PXor@y [PAny@a]   [POnes]]    => design.replace_value(y, design.add_not(a));
        [PXor@y [POnes]    [PAny@a]]   => design.replace_value(y, design.add_not(a));
        [PXor@y [PAny]     [PUndef]]   => design.replace_value(&y, Value::undef(y.len()));
        [PXor@y [PUndef]   [PAny]]     => design.replace_value(&y, Value::undef(y.len()));

        [PMux@y [POnes]    [PAny@a]   [PAny]]     => design.replace_value(y, a);
        [PMux@y [PZero]    [PAny]     [PAny@b]]   => design.replace_value(y, b);
        [PMux@y [PAny]     [PAny@a]   [PUndef]]   => design.replace_value(y, a);
        [PMux@y [PAny]     [PUndef]   [PAny@b]]   => design.replace_value(y, b);
        [PMux@y [PAny]     [PAny@a]   [PAny@b]]   if (a == b) => design.replace_value(y, a);

        [PAdc@y [PConst@a] [PConst@b] [PConst@c]] => design.replace_value(y, a.adc(b, c[0]));
        [PAdc@y [PAny@a]   [PZero]    [PZero]]    => design.replace_value(&y, a.zext(y.len()));
        [PAdc@y [PZero]    [PAny@b]   [PZero]]    => design.replace_value(&y, b.zext(y.len()));
        [PAdc@y [PZero]    [PZero]    [PAny@c]]   => design.replace_value(&y, c.zext(y.len()));

        [PEq@y  [PConst@a] [PConst@b]] => design.replace_value(y, a.eq(b));
        [PULt@y [PConst@a] [PConst@b]] => design.replace_value(y, a.ult(b));
        [PSLt@y [PConst@a] [PConst@b]] => design.replace_value(y, a.slt(b));

        [PEq@y  [PAny@a] [PAny@b]]     if (a == b) => design.replace_value(y, Trit::One);
        [PULt@y [PAny@a] [PAny@b]]     if (a == b) => design.replace_value(y, Trit::Zero);
        [PSLt@y [PAny@a] [PAny@b]]     if (a == b) => design.replace_value(y, Trit::Zero);

        [PULt@y [PAny]  [PZero]]       => design.replace_value(y, Trit::Zero);
        [PULt@y [POnes] [PAny]]        => design.replace_value(y, Trit::Zero);
    };

    for cell_ref in design.iter_cells() {
        // rules(design, &cell_ref.output());
        for net in &cell_ref.output() {
            rules(design, &Value::from(net));
        }
    }
    design.compact();
}
