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
fn test_lower_ff_simple() {
    let (target, mut design) = parse! {r#"
        %0:1 = input "d"
        %1:1 = input "c"
        %2:1 = dff %0 clk=%1 init=0
        %3:0 = output "q" %2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:1 = input "d"
        %1:1 = input "c"
        %2:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(X)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%0
            i@"C"=%1
            i@"R"=0
            i@"E"=1
        }
        %3:0 = output "q" %2
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_sync() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:2 = dff %0:2 clk=%2 rst=%3,10 en=%4 en>rst init=00
        %7:0 = output "q" %5:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%0+0
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %6:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%0+1
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %7:0 = output "q" { %6 %5 }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_sync_neg() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:2 = dff %0:2 clk=!%2 rst=!%3,10 en=!%4 en>rst init=00
        %7:0 = output "q" %5:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:1 = not %3
        %6:1 = not %4
        %7:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(1)
            i@"D"=%0+0
            i@"C"=%2
            i@"R"=%5
            i@"E"=%6
        }
        %8:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(1)
            i@"D"=%0+1
            i@"C"=%2
            i@"R"=%5
            i@"E"=%6
        }
        %9:0 = output "q" { %8 %7 }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_sync_remap() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:2 = dff %0:2 clk=%2 rst=%3,10 en=%4 rst>en init=00
        %7:0 = output "q" %5:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:1 = or %3 %4
        %6:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%0+0
            i@"C"=%2
            i@"R"=%3
            i@"E"=%5
        }
        %7:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%0+1
            i@"C"=%2
            i@"R"=%3
            i@"E"=%5
        }
        %8:0 = output "q" { %7 %6 }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_sync_inv() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:2 = dff %0:2 clk=%2 rst=%3,10 en=%4 en>rst init=11
        %7:0 = output "q" %5:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:1 = not %0+0
        %6:1 = not %0+1
        %7:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%5
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %8:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(0)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%6
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %9:1 = not %7
        %10:1 = not %8
        %11:0 = output "q" { %10 %9 }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_async() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:2 = dff %0:2 clk=%2 clr=%3,10 en=%4 init=00
        %7:0 = output "q" %5:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%0+0
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %6:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%0+1
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %7:0 = output "q" { %6 %5 }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_async_neg() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:2 = dff %0:2 clk=!%2 clr=!%3,10 en=!%4 init=00
        %7:0 = output "q" %5:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:1 = not %3
        %6:1 = not %4
        %7:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(1)
            i@"D"=%0+0
            i@"C"=%2
            i@"R"=%5
            i@"E"=%6
        }
        %8:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(1)
            i@"D"=%0+1
            i@"C"=%2
            i@"R"=%5
            i@"E"=%6
        }
        %9:0 = output "q" { %8 %7 }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_async_inv() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:2 = dff %0:2 clk=%2 clr=%3,10 en=%4 init=11
        %7:0 = output "q" %5:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "r"
        %4:1 = input "e"
        %5:1 = not %0+0
        %6:1 = not %0+1
        %7:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%5
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %8:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%6
            i@"C"=%2
            i@"R"=%3
            i@"E"=%4
        }
        %9:1 = not %7
        %10:1 = not %8
        %11:0 = output "q" { %10 %9 }
    "#};
    assert_isomorphic!(design, gold);
}

#[test]
fn test_lower_ff_unmap_reset() {
    let (target, mut design) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "clr"
        %4:1 = input "rst"
        %5:1 = input "e"
        %6:2 = dff %0:2 clk=%2 clr=%3,10 rst=%4,01 en=%5 en>rst init=XX
        %8:0 = output "q" %6:2
    "#};
    target.lower_ffs(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:2 = input "d"
        %2:1 = input "c"
        %3:1 = input "clr"
        %4:1 = input "rst"
        %5:1 = input "e"
        %6:2 = mux %4 01 %0:2
        %8:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(0)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%6+0
            i@"C"=%2
            i@"R"=%3
            i@"E"=%5
        }
        %9:1 = target "SB_DFF" {
            p@"RESET_VALUE"=const(1)
            p@"IS_RESET_ASYNC"=const(1)
            p@"IS_C_INVERTED"=const(0)
            i@"D"=%6+1
            i@"C"=%2
            i@"R"=%3
            i@"E"=%5
        }
        %10:0 = output "q" { %9 %8 }
    "#};
    assert_isomorphic!(design, gold);
}
