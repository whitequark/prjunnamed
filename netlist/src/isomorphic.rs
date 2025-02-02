use std::fmt::Display;
use std::collections::{BTreeMap, BTreeSet};

use crate::{CellRepr, Design, IoNet, Net, Value};

#[derive(Debug)]
pub enum NotIsomorphic {
    NoOutputLeft(String),
    NoOutputRight(String),
    OutputSizeMismatch(String),
    IoSizeMismatch(String),
    NameSizeMismatch(String),
    ValueSizeMismatch(Value, Value),
    NetMismatch(Net, Net),
    IoNetMismatch(IoNet, IoNet),
}

impl Display for NotIsomorphic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NotIsomorphic::NoOutputLeft(name) => write!(f, "output {:?} is missing in the left design", name),
            NotIsomorphic::NoOutputRight(name) => write!(f, "output {:?} is missing in the right design", name),
            NotIsomorphic::OutputSizeMismatch(name) => write!(f, "size of output {:?} does not match", name),
            NotIsomorphic::IoSizeMismatch(name) => write!(f, "size of IO {:?} does not match", name),
            NotIsomorphic::NameSizeMismatch(name) => write!(f, "size of name cell {:?} does not match", name),
            NotIsomorphic::ValueSizeMismatch(value_l, value_r) => {
                write!(f, "size of values {} and {} do not match", value_l, value_r)
            }
            NotIsomorphic::NetMismatch(net_l, net_r) => write!(f, "nets {} and {} are not isomorphic", net_l, net_r),
            NotIsomorphic::IoNetMismatch(io_net_l, io_net_r) => {
                write!(f, "IO nets {} and {} are not isomorphic", io_net_l, io_net_r)
            }
        }
    }
}

// Beware: this function will ignore instances that have no output bits.
pub fn isomorphic(lft: &Design, rgt: &Design) -> Result<(), NotIsomorphic> {
    let mut queue: BTreeSet<(Net, Net)> = BTreeSet::new();
    fn queue_vals(queue: &mut BTreeSet<(Net, Net)>, val_l: &Value, val_r: &Value) -> Result<(), NotIsomorphic> {
        if val_l.len() != val_r.len() {
            return Err(NotIsomorphic::ValueSizeMismatch(val_l.clone(), val_r.clone()));
        }
        for (net_l, net_r) in val_l.iter().zip(val_r) {
            queue.insert((net_l, net_r));
        }
        Ok(())
    }

    let mut visited: BTreeSet<(Net, Net)> = BTreeSet::new();
    visited.insert((Net::UNDEF, Net::UNDEF));
    visited.insert((Net::ZERO, Net::ZERO));
    visited.insert((Net::ONE, Net::ONE));
    let mut outputs_l = BTreeMap::new();
    let mut names_l = BTreeMap::new();
    for cell in lft.iter_cells() {
        match &*cell.repr() {
            CellRepr::Output(name, value) => {
                outputs_l.insert(name.clone(), value.clone());
            }
            CellRepr::Name(name, value) => {
                names_l.insert(name.clone(), value.clone());
            }
            _ => (),
        }
    }
    let mut outputs_r = BTreeMap::new();
    let mut names_r = BTreeMap::new();
    for cell in rgt.iter_cells() {
        match &*cell.repr() {
            CellRepr::Output(name, value) => {
                outputs_r.insert(name.clone(), value.clone());
            }
            CellRepr::Name(name, value) => {
                names_r.insert(name.clone(), value.clone());
            }
            _ => (),
        }
    }
    for (name, value_l) in &outputs_l {
        if let Some(value_r) = outputs_r.get(name) {
            if value_l.len() != value_r.len() {
                return Err(NotIsomorphic::OutputSizeMismatch(name.clone()));
            }
            for (net_l, net_r) in value_l.iter().zip(value_r) {
                queue.insert((net_l, net_r));
            }
        } else {
            return Err(NotIsomorphic::NoOutputRight(name.clone()));
        }
    }
    for name in outputs_r.keys() {
        if !outputs_l.contains_key(name) {
            return Err(NotIsomorphic::NoOutputLeft(name.clone()));
        }
    }
    for (name, value_l) in &names_l {
        if let Some(value_r) = names_r.get(name) {
            if value_l.len() != value_r.len() {
                return Err(NotIsomorphic::NameSizeMismatch(name.clone()));
            }
            for (net_l, net_r) in value_l.iter().zip(value_r) {
                queue.insert((net_l, net_r));
            }
        }
    }
    let mut ios = BTreeSet::new();
    ios.insert((IoNet::FLOATING, IoNet::FLOATING));
    for (name, _) in lft.iter_ios() {
        if let (Some(io_l), Some(io_r)) = (lft.get_io(name), rgt.get_io(name)) {
            if io_l.len() != io_r.len() {
                return Err(NotIsomorphic::IoSizeMismatch(name.to_owned()));
            }
            for (ionet_l, ionet_r) in io_l.iter().zip(io_r.iter()) {
                ios.insert((ionet_l, ionet_r));
            }
        }
    }
    while let Some((net_l, net_r)) = queue.pop_first() {
        if visited.contains(&(net_l, net_r)) {
            continue;
        }
        if net_l.as_const().is_some() || net_r.as_const().is_some() {
            // (const, const) pairs already added to visitted at the beginning
            return Err(NotIsomorphic::NetMismatch(net_l, net_r));
        }
        let (cell_l, bit_l) = lft.find_cell(net_l).unwrap();
        let (cell_r, bit_r) = rgt.find_cell(net_r).unwrap();
        let out_l = cell_l.output();
        let out_r = cell_r.output();
        if bit_l != bit_r || out_l.len() != out_r.len() {
            return Err(NotIsomorphic::NetMismatch(net_l, net_r));
        }
        for (net_l, net_r) in out_l.iter().zip(out_r) {
            visited.insert((net_l, net_r));
        }
        match (&*cell_l.repr(), &*cell_r.repr()) {
            (CellRepr::Buf(val_l), CellRepr::Buf(val_r)) | (CellRepr::Not(val_l), CellRepr::Not(val_r)) => {
                queue_vals(&mut queue, val_l, val_r)?
            }
            (CellRepr::And(arg1_l, arg2_l), CellRepr::And(arg1_r, arg2_r))
            | (CellRepr::Or(arg1_l, arg2_l), CellRepr::Or(arg1_r, arg2_r))
            | (CellRepr::Xor(arg1_l, arg2_l), CellRepr::Xor(arg1_r, arg2_r))
            | (CellRepr::Eq(arg1_l, arg2_l), CellRepr::Eq(arg1_r, arg2_r))
            | (CellRepr::ULt(arg1_l, arg2_l), CellRepr::ULt(arg1_r, arg2_r))
            | (CellRepr::SLt(arg1_l, arg2_l), CellRepr::SLt(arg1_r, arg2_r))
            | (CellRepr::Mul(arg1_l, arg2_l), CellRepr::Mul(arg1_r, arg2_r))
            | (CellRepr::UDiv(arg1_l, arg2_l), CellRepr::UDiv(arg1_r, arg2_r))
            | (CellRepr::UMod(arg1_l, arg2_l), CellRepr::UMod(arg1_r, arg2_r))
            | (CellRepr::SDivTrunc(arg1_l, arg2_l), CellRepr::SDivTrunc(arg1_r, arg2_r))
            | (CellRepr::SDivFloor(arg1_l, arg2_l), CellRepr::SDivFloor(arg1_r, arg2_r))
            | (CellRepr::SModTrunc(arg1_l, arg2_l), CellRepr::SModTrunc(arg1_r, arg2_r))
            | (CellRepr::SModFloor(arg1_l, arg2_l), CellRepr::SModFloor(arg1_r, arg2_r)) => {
                queue_vals(&mut queue, arg1_l, arg1_r)?;
                queue_vals(&mut queue, arg2_l, arg2_r)?;
            }
            (CellRepr::Mux(arg1_l, arg2_l, arg3_l), CellRepr::Mux(sel_r, arg2_r, arg3_r)) => {
                queue.insert((*arg1_l, *sel_r));
                queue_vals(&mut queue, arg2_l, arg2_r)?;
                queue_vals(&mut queue, arg3_l, arg3_r)?;
            }
            (CellRepr::Adc(arg1_l, arg2_l, arg3_l), CellRepr::Adc(arg1_r, arg2_r, arg3_r)) => {
                queue_vals(&mut queue, arg1_l, arg1_r)?;
                queue_vals(&mut queue, arg2_l, arg2_r)?;
                queue.insert((*arg3_l, *arg3_r));
            }
            (CellRepr::Shl(arg1_l, arg2_l, stride_l), CellRepr::Shl(arg1_r, arg2_r, stride_r))
            | (CellRepr::UShr(arg1_l, arg2_l, stride_l), CellRepr::UShr(arg1_r, arg2_r, stride_r))
            | (CellRepr::SShr(arg1_l, arg2_l, stride_l), CellRepr::SShr(arg1_r, arg2_r, stride_r))
            | (CellRepr::XShr(arg1_l, arg2_l, stride_l), CellRepr::XShr(arg1_r, arg2_r, stride_r)) => {
                queue_vals(&mut queue, arg1_l, arg1_r)?;
                queue_vals(&mut queue, arg2_l, arg2_r)?;
                if stride_l != stride_r {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            (CellRepr::Dff(ff_l), CellRepr::Dff(ff_r)) => {
                queue_vals(&mut queue, &ff_l.data, &ff_r.data)?;
                queue.insert((ff_l.clock.net(), ff_r.clock.net()));
                queue.insert((ff_l.clear.net(), ff_r.clear.net()));
                queue.insert((ff_l.reset.net(), ff_r.reset.net()));
                queue.insert((ff_l.enable.net(), ff_r.enable.net()));
                if ff_l.clock.is_positive() != ff_r.clock.is_positive()
                    || ff_l.clear.is_positive() != ff_r.clear.is_positive()
                    || ff_l.reset.is_positive() != ff_r.reset.is_positive()
                    || ff_l.enable.is_positive() != ff_r.enable.is_positive()
                    || (ff_l.reset_over_enable != ff_r.reset_over_enable
                        && !ff_l.reset.is_always(false)
                        && !ff_l.enable.is_always(true))
                    || ff_l.clear_value != ff_r.clear_value
                    || ff_l.reset_value != ff_r.reset_value
                    || ff_l.init_value != ff_r.init_value
                {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            (CellRepr::Iob(iob_l), CellRepr::Iob(iob_r)) => {
                for (io_net_l, io_net_r) in iob_l.io.iter().zip(iob_r.io.iter()) {
                    if !ios.contains(&(io_net_l, io_net_r)) {
                        return Err(NotIsomorphic::IoNetMismatch(io_net_l, io_net_r));
                    }
                }
                queue_vals(&mut queue, &iob_l.output, &iob_r.output)?;
                queue.insert((iob_l.enable.net(), iob_r.enable.net()));
                if iob_l.enable.is_positive() != iob_r.enable.is_positive() {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            (CellRepr::Target(target_cell_l), CellRepr::Target(target_cell_r)) => {
                for (io_net_l, io_net_r) in target_cell_l.ios.iter().zip(target_cell_r.ios.iter()) {
                    if !ios.contains(&(io_net_l, io_net_r)) {
                        return Err(NotIsomorphic::IoNetMismatch(io_net_l, io_net_r));
                    }
                }
                if target_cell_l.kind != target_cell_r.kind || target_cell_l.params != target_cell_r.params {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
                queue_vals(&mut queue, &target_cell_l.inputs, &target_cell_r.inputs)?;
            }
            (CellRepr::Other(inst_l), CellRepr::Other(inst_r)) => {
                if inst_l.kind != inst_r.kind || inst_l.params != inst_r.params || inst_l.outputs != inst_r.outputs {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
                for (name, value_l) in &inst_l.inputs {
                    let Some(value_r) = inst_r.inputs.get(name) else {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    };
                    queue_vals(&mut queue, value_l, value_r)?;
                }
                for name in inst_r.inputs.keys() {
                    if !inst_l.inputs.contains_key(name) {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    }
                }
                for (name, io_value_l) in &inst_l.ios {
                    let Some(io_value_r) = inst_r.ios.get(name) else {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    };
                    for (io_net_l, io_net_r) in io_value_l.iter().zip(io_value_r.iter()) {
                        if !ios.contains(&(io_net_l, io_net_r)) {
                            return Err(NotIsomorphic::IoNetMismatch(io_net_l, io_net_r));
                        }
                    }
                }
                for name in inst_r.ios.keys() {
                    if !inst_l.ios.contains_key(name) {
                        return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                    }
                }
            }
            (CellRepr::Input(name_l, _), CellRepr::Input(name_r, _)) => {
                if name_l != name_r {
                    return Err(NotIsomorphic::NetMismatch(net_l, net_r));
                }
            }
            _ => return Err(NotIsomorphic::NetMismatch(net_l, net_r)),
        }
    }
    Ok(())
}

#[macro_export]
macro_rules! assert_isomorphic {
    ( $lft:ident, $rgt:ident ) => {
        $lft.apply();
        $rgt.apply();
        let result = prjunnamed_netlist::isomorphic(&$lft, &$rgt);
        if let Err(error) = result {
            panic!("{}\nleft design:\n{}\nright design:\n{}", error, $lft, $rgt);
        }
    };
}
