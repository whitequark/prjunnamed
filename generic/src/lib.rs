use prjunnamed_netlist::Design;

mod decision;
mod simplify;
mod merge;
mod split;
mod lower;
mod iob_insert;

pub use decision::decision;
pub use lower::lower;
pub use iob_insert::iob_insert;

pub fn canonicalize(design: &mut Design) {
    for iter in 1.. {
        if cfg!(feature = "trace") {
            eprintln!(">canonicalize #{}", iter);
        }
        let did_simplify = simplify::simplify(design);
        let did_merge = merge::merge(design);
        let did_split = split::split(design);
        if !(did_simplify || did_merge || did_split) {
            if cfg!(feature = "trace") {
                eprintln!(">canonicalize done");
            }
            break;
        }
    }
}
