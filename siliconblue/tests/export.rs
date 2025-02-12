use std::collections::BTreeMap;

use prjunnamed_netlist::{assert_isomorphic, Target};

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
fn test_export_lut4_carry() {
    let (target, mut design) = parse! {r#"
        %0:4 = input "i"
        %4:1 = input "ci"
        %5:2 = target "SB_LUT4_CARRY" {
            p@"LUT_INIT"=0001001000110100
            p@"IS_I3_CI"=0
            i@"I"=%0:4
            i@"CI"=%4
        }
        %7:0 = output "o" %5+0
        %8:0 = output "co" %5+1
    "#};
    target.export(&mut design);
    let (_, mut gold) = parse! {r#"
        %0:4 = input "i"
        %4:1 = input "ci"
        %5:1 = "SB_LUT4" {
            p@"LUT_INIT"=0001001000110100
            i@"I0"=%0+0
            i@"I1"=%0+1
            i@"I2"=%0+2
            i@"I3"=%0+3
            o@"O"=0:1
        }
        %6:1 = "SB_CARRY" {
            i@"I0"=%0+1
            i@"I1"=%0+2
            i@"CI"=%4
            o@"CO"=0:1
        }
        %7:0 = output "o" %5
        %8:0 = output "co" %6
    "#};
    assert_isomorphic!(design, gold);
}
