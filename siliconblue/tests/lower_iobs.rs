use std::collections::BTreeMap;

use prjunnamed_netlist::assert_isomorphic;

use prjunnamed_siliconblue::SiliconBlueTarget;

// I hate rustfmt.
macro_rules! parse {
    ($source:expr) => {{
        let target = SiliconBlueTarget::new(BTreeMap::new());
        let design = prjunnamed_netlist::parse(Some(target.clone()), $source).unwrap();
        (target, design)
    }};
}

#[test]
fn test_lower_iob_input() {
    let (target, mut design) = parse! {r#"
        &"io":1
        %0:1 = iob &"io" o=X en=0
        %1:0 = output "x" %0
    "#};
    target.lower_iobs(&mut design);
    let (_, mut gold) = parse! {r#"
        &"io":1
        %0:0 = output "x" %1+0
        %1:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(000001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=X
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=0
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"
            io@"PACKAGE_PIN_B"=&_
        }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_iob_output() {
    let (target, mut design) = parse! {r#"
        &"io":1
        %0:1 = iob &"io" o=%1 en=1
        %1:1 = input "o"
        %2:0 = output "i" %0
    "#};
    target.lower_iobs(&mut design);
    let (_, mut gold) = parse! {r#"
        &"io":1
        %0:1 = input "o"
        %1:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(011001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=%0
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=0
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"
            io@"PACKAGE_PIN_B"=&_
        }
        %4:0 = output "i" %1+0
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_iob_tristate() {
    let (target, mut design) = parse! {r#"
        &"io":1
        %0:1 = iob &"io" o=%1 en=%2
        %1:1 = input "o"
        %2:1 = input "oe"
        %3:0 = output "i" %0
    "#};
    target.lower_iobs(&mut design);
    let (_, mut gold) = parse! {r#"
        &"io":1
        %0:1 = input "o"
        %1:1 = input "oe"
        %2:0 = output "i" %3+0
        %3:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(101001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=%0
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=%1
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"
            io@"PACKAGE_PIN_B"=&_
        }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_iob_tristate_inv() {
    let (target, mut design) = parse! {r#"
        &"io":1
        %0:1 = iob &"io" o=%1 en=!%2
        %1:1 = input "o"
        %2:1 = input "t"
        %3:0 = output "i" %0
    "#};
    target.lower_iobs(&mut design);
    let (_, mut gold) = parse! {r#"
        &"io":1
        %0:1 = input "o"
        %1:1 = input "t"
        %2:0 = output "i" %4+0
        %3:1 = not %1
        %4:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(101001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=%0
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=%3
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"
            io@"PACKAGE_PIN_B"=&_
        }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_iob_tristate_wide() {
    let (target, mut design) = parse! {r#"
        &"io":4
        %0:4 = input "o"
        %4:1 = input "oe"
        %5:4 = iob &"io":4 o=%0:4 en=%4
        %9:0 = output "i" %5:4
    "#};
    target.lower_iobs(&mut design);
    let (_, mut gold) = parse! {r#"
        &"io":4
        %0:4 = input "o"
        %4:1 = input "oe"
        %5:0 = output "i" {%15+0 %12+0 %9+0 %6+0}
        %6:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(101001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=%0+0
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=%4
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"+0
            io@"PACKAGE_PIN_B"=&_
        }
        %9:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(101001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=%0+1
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=%4
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"+1
            io@"PACKAGE_PIN_B"=&_
        }
        %12:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(101001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=%0+2
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=%4
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"+2
            io@"PACKAGE_PIN_B"=&_
        }
        %15:3 = target "SB_IO" {
            p@"PIN_TYPE"=const(101001)
            p@"PULLUP"=const(0)
            p@"NEG_TRIGGER"=const(0)
            p@"IS_GB"=const(0)
            p@"IO_STANDARD"=string("SB_LVCMOS")
            i@"D_OUT_0"=%0+3
            i@"D_OUT_1"=X
            i@"OUTPUT_ENABLE"=%4
            i@"CLOCK_ENABLE"=1
            i@"INPUT_CLK"=X
            i@"OUTPUT_CLK"=X
            i@"LATCH_INPUT_VALUE"=X
            io@"PACKAGE_PIN"=&"io"+3
            io@"PACKAGE_PIN_B"=&_
        }
    "#};
    assert_isomorphic!(design, gold);
}
