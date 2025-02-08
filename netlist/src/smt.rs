use std::{borrow::Cow, cell::RefCell, collections::BTreeMap};

use crate::{AssignCell, Cell, Const, ControlNet, Design, MatchCell, Net, Trit, Value};

#[cfg(feature = "easy-smt")]
pub mod easy_smt;

#[derive(Debug, Clone)]
pub enum SmtResponse {
    Sat,
    Unsat,
    Unknown,
}

pub trait SmtEngine {
    type Bool: Clone;
    type BitVec: Clone;

    fn build_bool_lit(&self, value: bool) -> Self::Bool;
    fn build_bool_eq(&self, arg1: Self::Bool, arg2: Self::Bool) -> Self::Bool;
    fn build_bool_ite(&self, cond: Self::Bool, if_true: Self::Bool, if_false: Self::Bool) -> Self::Bool;
    fn build_bool_let(&self, var: &str, expr: Self::Bool, body: impl FnOnce(Self::Bool) -> Self::Bool) -> Self::Bool;
    fn build_not(&self, arg: Self::Bool) -> Self::Bool;
    fn build_and(&self, args: &[Self::Bool]) -> Self::Bool;
    fn build_or(&self, args: &[Self::Bool]) -> Self::Bool;
    fn build_xor(&self, args: &[Self::Bool]) -> Self::Bool;

    fn build_bitvec_lit(&self, value: &Const) -> Self::BitVec;
    fn build_bitvec_eq(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::Bool;
    fn build_bitvec_ite(&self, cond: Self::Bool, if_true: Self::BitVec, if_false: Self::BitVec) -> Self::BitVec;
    fn build_bitvec_let(
        &self,
        var: &str,
        expr: Self::BitVec,
        body: impl FnOnce(Self::BitVec) -> Self::BitVec,
    ) -> Self::BitVec;
    fn build_concat(&self, arg_msb: Self::BitVec, arg_lsb: Self::BitVec) -> Self::BitVec;
    fn build_extract(&self, index_msb: usize, index_lsb: usize, arg: Self::BitVec) -> Self::BitVec;
    fn build_bvnot(&self, arg1: Self::BitVec) -> Self::BitVec;
    fn build_bvand(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvor(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvxor(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvadd(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvcomp(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvult(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::Bool;
    fn build_bvslt(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::Bool;
    fn build_bvshl(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvlshr(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvashr(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvmul(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvudiv(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvurem(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvsdiv(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;
    fn build_bvsrem(&self, arg1: Self::BitVec, arg2: Self::BitVec) -> Self::BitVec;

    type Error;

    fn declare_bool_const(&self, name: &str) -> Result<Self::Bool, Self::Error>;
    fn declare_bitvec_const(&self, name: &str, width: usize) -> Result<Self::BitVec, Self::Error>;
    fn assert(&mut self, term: Self::Bool) -> Result<(), Self::Error>;

    fn check(&mut self) -> Result<SmtResponse, Self::Error>;
    fn get_bool(&self, term: &Self::Bool) -> Result<bool, Self::Error>;
    fn get_bitvec(&self, term: &Self::BitVec) -> Result<Const, Self::Error>;
}

pub struct SmtBuilder<'a, SMT: SmtEngine> {
    design: &'a Design,
    engine: SMT,
    curr: RefCell<BTreeMap<Net, SMT::BitVec>>,
    past: RefCell<BTreeMap<Net, SMT::BitVec>>,
    eqs: RefCell<Vec<SMT::Bool>>,
}

impl<'a, SMT: SmtEngine> SmtBuilder<'a, SMT> {
    pub fn new(design: &'a Design, engine: SMT) -> Self {
        Self {
            design,
            engine,
            curr: RefCell::new(BTreeMap::new()),
            past: RefCell::new(BTreeMap::new()),
            eqs: RefCell::new(Vec::new()),
        }
    }

    fn trit(&self, trit: Trit) -> SMT::BitVec {
        match trit {
            Trit::Undef => unimplemented!("undef cannot be lowered to SMT-LIB"),
            Trit::Zero => self.engine.build_bitvec_lit(&Const::zero(1)),
            Trit::One => self.engine.build_bitvec_lit(&Const::ones(1)),
        }
    }

    fn concat(&self, bv_elems: impl IntoIterator<IntoIter: DoubleEndedIterator<Item = SMT::BitVec>>) -> SMT::BitVec {
        let mut bv_result = None;
        for bv_elem in bv_elems.into_iter().rev() {
            if let Some(bv_msb) = bv_result {
                bv_result = Some(self.engine.build_concat(bv_msb, bv_elem));
            } else {
                bv_result = Some(bv_elem)
            }
        }
        bv_result.expect("SMT bit vectors cannot be empty")
    }

    fn curr_net(&self, net: Net) -> Result<SMT::BitVec, SMT::Error> {
        if let Some(trit) = net.as_const() {
            return Ok(self.trit(trit));
        }
        let bv_net = self.engine.declare_bitvec_const(&format!("n{}", net.as_cell_index().unwrap()), 1)?;
        self.curr.borrow_mut().insert(net, bv_net.clone());
        Ok(bv_net)
    }

    fn curr_value(&self, value: &Value) -> Result<SMT::BitVec, SMT::Error> {
        Ok(self.concat(value.iter().map(|net| self.curr_net(net)).collect::<Result<Vec<_>, _>>()?.into_iter()))
    }

    fn past_net(&self, net: Net) -> Result<SMT::BitVec, SMT::Error> {
        if let Some(trit) = net.as_const() {
            return Ok(self.trit(trit));
        }
        let bv_net = self.engine.declare_bitvec_const(&format!("p{}", net.as_cell_index().unwrap()), 1)?;
        self.past.borrow_mut().insert(net, bv_net.clone());
        Ok(bv_net)
    }

    fn past_value(&self, value: &Value) -> Result<SMT::BitVec, SMT::Error> {
        Ok(self.concat(value.iter().map(|net| self.past_net(net)).collect::<Result<Vec<_>, _>>()?.into_iter()))
    }

    fn net(&self, net: Net) -> Result<SMT::BitVec, SMT::Error> {
        if let Ok(index) = net.as_cell_index() {
            if !self.design.is_valid_cell_index(index) {
                return self.curr_net(net); // FIXME: is this even sound?
            }
        }
        match self.design.find_cell(net) {
            Ok((cell_ref, _offset)) if matches!(&*cell_ref.get(), Cell::Dff(_)) => self.past_net(net),
            _ => self.curr_net(net),
        }
    }

    fn value(&self, value: &Value) -> Result<SMT::BitVec, SMT::Error> {
        Ok(self.concat(value.iter().map(|net| self.net(net)).collect::<Result<Vec<_>, _>>()?.into_iter()))
    }

    fn control_net(&self, control_net: ControlNet) -> Result<SMT::Bool, SMT::Error> {
        let active = if control_net.is_positive() { Const::ones(1) } else { Const::zero(1) };
        Ok(self.engine.build_bitvec_eq(self.net(control_net.net())?, self.engine.build_bitvec_lit(&active)))
    }

    fn async_net(&self, control_net: ControlNet) -> Result<SMT::Bool, SMT::Error> {
        let inactive = if control_net.is_positive() { Const::zero(1) } else { Const::ones(1) };
        let active = if control_net.is_positive() { Const::ones(1) } else { Const::zero(1) };
        Ok(self.engine.build_and(&[
            self.engine.build_bitvec_eq(self.curr_net(control_net.net())?, self.engine.build_bitvec_lit(&active)),
            self.engine.build_bitvec_eq(self.past_net(control_net.net())?, self.engine.build_bitvec_lit(&inactive)),
        ]))
    }

    fn cell(&self, output: &Value, cell: &Cell) -> Result<SMT::BitVec, SMT::Error> {
        fn resize(value: &Value, width: usize) -> Value {
            if width <= value.len() {
                value.slice(..width)
            } else {
                value.zext(width)
            }
        }

        let adjust_shift = |value: &Value, amount: &Value, stride: u32| -> Result<SMT::BitVec, SMT::Error> {
            Ok(self.engine.build_bvmul(
                self.value(&resize(amount, value.len()))?,
                self.engine.build_bitvec_lit(&Const::from_uint(stride as u128, value.len())),
            ))
        };

        let bv_to_bool = |value| self.engine.build_bitvec_eq(value, self.engine.build_bitvec_lit(&Const::ones(1)));
        let bool_to_bv = |value| {
            self.engine.build_bitvec_ite(
                value,
                self.engine.build_bitvec_lit(&Const::ones(1)),
                self.engine.build_bitvec_lit(&Const::zero(1)),
            )
        };

        let bv_cell = match &*cell {
            Cell::Buf(arg) => self.value(arg)?,
            Cell::Not(arg) => self.engine.build_bvnot(self.value(arg)?),
            Cell::And(arg1, arg2) => self.engine.build_bvand(self.value(arg1)?, self.value(arg2)?),
            Cell::Or(arg1, arg2) => self.engine.build_bvor(self.value(arg1)?, self.value(arg2)?),
            Cell::Xor(arg1, arg2) => self.engine.build_bvxor(self.value(arg1)?, self.value(arg2)?),
            Cell::Mux(arg1, arg2, arg3) => self.engine.build_bitvec_ite(
                self.engine.build_bitvec_eq(self.net(*arg1)?, self.engine.build_bitvec_lit(&Const::ones(1))),
                self.value(arg2)?,
                self.value(arg3)?,
            ),
            Cell::Adc(arg1, arg2, arg3) => {
                if arg1.is_empty() {
                    self.net(*arg3)?
                } else {
                    self.engine.build_bvadd(
                        self.engine.build_bvadd(
                            self.engine.build_concat(self.engine.build_bitvec_lit(&Const::zero(1)), self.value(arg1)?),
                            self.engine.build_concat(self.engine.build_bitvec_lit(&Const::zero(1)), self.value(arg2)?),
                        ),
                        self.engine
                            .build_concat(self.engine.build_bitvec_lit(&Const::zero(arg1.len())), self.net(*arg3)?),
                    )
                }
            }
            Cell::Eq(arg1, arg2) => self.engine.build_bvcomp(self.value(arg1)?, self.value(arg2)?),
            Cell::ULt(arg1, arg2) => bool_to_bv(self.engine.build_bvult(self.value(arg1)?, self.value(arg2)?)),
            Cell::SLt(arg1, arg2) => bool_to_bv(self.engine.build_bvslt(self.value(arg1)?, self.value(arg2)?)),
            Cell::Shl(arg1, arg2, stride) => {
                self.engine.build_bvshl(self.value(arg1)?, adjust_shift(arg1, arg2, *stride)?)
            }
            Cell::UShr(arg1, arg2, stride) => {
                self.engine.build_bvlshr(self.value(arg1)?, adjust_shift(arg1, arg2, *stride)?)
            }
            Cell::SShr(arg1, arg2, stride) => {
                self.engine.build_bvashr(self.value(arg1)?, adjust_shift(arg1, arg2, *stride)?)
            }
            Cell::XShr(_arg1, _arg2, _stride) => unimplemented!("undef cannot be lowered to SMT-LIB"),
            Cell::Mul(arg1, arg2) => self.engine.build_bvmul(self.value(arg1)?, self.value(arg2)?),
            Cell::UDiv(arg1, arg2) => self.engine.build_bvudiv(self.value(arg1)?, self.value(arg2)?),
            Cell::UMod(arg1, arg2) => self.engine.build_bvurem(self.value(arg1)?, self.value(arg2)?),
            Cell::SDivTrunc(arg1, arg2) => self.engine.build_bvsdiv(self.value(arg1)?, self.value(arg2)?),
            Cell::SDivFloor(_arg1, _arg2) => unimplemented!(),
            Cell::SModTrunc(arg1, arg2) => self.engine.build_bvsrem(self.value(arg1)?, self.value(arg2)?),
            Cell::SModFloor(_arg1, _arg2) => unimplemented!(),
            Cell::Match(MatchCell { value, enable, patterns }) => {
                let build_patcomp = |value: &Value, pattern: &Const| -> Result<SMT::Bool, SMT::Error> {
                    let mut bv_ands = vec![self.engine.build_bool_lit(true)];
                    for (index, mask) in pattern.iter().enumerate() {
                        if mask != Trit::Undef {
                            bv_ands.push(self.engine.build_bitvec_eq(self.net(value[index])?, self.net(mask.into())?))
                        }
                    }
                    Ok(self.engine.build_and(&bv_ands[..]))
                };
                let mut bv_matches = None;
                for alternates in patterns {
                    let mut bv_ors = vec![self.engine.build_bool_lit(false)];
                    for pattern in alternates {
                        bv_ors.push(build_patcomp(value, pattern)?);
                    }
                    let bv_ors = bool_to_bv(self.engine.build_or(&bv_ors[..]));
                    if let Some(prev_bv_matches) = bv_matches {
                        bv_matches = Some(self.engine.build_concat(bv_ors, prev_bv_matches));
                    } else {
                        bv_matches = Some(bv_ors);
                    }
                }
                let bv_enable = self.net(*enable)?;
                self.engine.build_bitvec_let("m", bv_matches.unwrap(), |bv_matches| {
                    let bv_all_cold = self.engine.build_bitvec_lit(&Const::zero(patterns.len()));
                    let mut bv_one_hot = bv_all_cold.clone();
                    for index in (0..patterns.len()).rev() {
                        bv_one_hot = self.engine.build_bitvec_ite(
                            bv_to_bool(self.engine.build_extract(index, index, bv_matches.clone())),
                            self.engine.build_bitvec_lit(&Const::one_hot(patterns.len(), index)),
                            bv_one_hot,
                        );
                    }
                    self.engine.build_bitvec_ite(bv_to_bool(bv_enable), bv_one_hot, bv_all_cold)
                })
            }
            Cell::Assign(AssignCell { value, enable, update, offset }) => self.engine.build_bitvec_ite(
                self.engine.build_bitvec_eq(self.net(*enable)?, self.engine.build_bitvec_lit(&Const::ones(1))),
                self.value(&{
                    let mut nets = Vec::from_iter(value.iter());
                    nets[*offset..(*offset + update.len())].copy_from_slice(&update[..]);
                    Value::from_iter(nets)
                })?,
                self.value(value)?,
            ),
            Cell::Dff(flip_flop) => {
                // The use of `has_...` is only required because any X in reset/clear values cause a panic right now.
                let build_reset = |data| -> Result<SMT::BitVec, SMT::Error> {
                    Ok(self.engine.build_bitvec_ite(
                        self.control_net(flip_flop.reset)?,
                        self.engine.build_bitvec_lit(&flip_flop.reset_value),
                        data,
                    ))
                };
                let build_enable = |data| -> Result<SMT::BitVec, SMT::Error> {
                    Ok(self.engine.build_bitvec_ite(
                        self.control_net(flip_flop.enable)?,
                        data,
                        self.past_value(&output)?,
                    ))
                };
                let mut data = self.value(&flip_flop.data)?;
                if flip_flop.has_reset() && flip_flop.has_enable() {
                    if flip_flop.reset_over_enable {
                        data = build_reset(build_enable(data)?)?;
                    } else {
                        data = build_enable(build_reset(data)?)?;
                    }
                } else if flip_flop.has_reset() {
                    data = build_reset(data)?;
                } else if flip_flop.has_enable() {
                    data = build_enable(data)?;
                }
                // FIXME: simultaneous clock+clear must evaluate to undef
                let value = if flip_flop.has_clock() {
                    self.engine.build_bitvec_ite(self.async_net(flip_flop.clock)?, data, self.past_value(&output)?)
                } else {
                    self.engine.build_bitvec_lit(&flip_flop.init_value)
                };
                if flip_flop.has_clear() {
                    self.engine.build_bitvec_ite(
                        self.async_net(flip_flop.clear)?,
                        self.engine.build_bitvec_lit(&flip_flop.clear_value),
                        value,
                    )
                } else {
                    value
                }
            }
            Cell::Memory(_memory) => unimplemented!("memories are not lowered to SMT-LIB yet"),
            Cell::Iob(_io_buffer) => unimplemented!("IO buffers are not lowered to SMT-LIB yet"),
            Cell::Target(_target_cell) => unimplemented!("target cells cannot be lowered to SMT-LIB yet"),
            Cell::Other(_) => unreachable!("instances cannot be lowered to SMT-LIB"),
            Cell::Input(_, _) | Cell::Output(_, _) | Cell::Name(_, _) => unreachable!(),
        };

        Ok(bv_cell)
    }

    pub fn add_cell(&mut self, output: &Value, cell: &Cell) -> Result<(), SMT::Error> {
        match cell {
            // Declare the nets used by the cell so that it is present in the counterexample even if unused.
            Cell::Input(_, _) => self.curr_value(output).map(|_| ()),
            _ => self.engine.assert(self.engine.build_bitvec_eq(self.curr_value(output)?, self.cell(output, cell)?)),
        }
    }

    pub fn replace_cell(&mut self, output: &Value, old_cell: &Cell, new_cell: &Cell) -> Result<(), SMT::Error> {
        self.add_cell(output, old_cell)?;
        self.eqs.borrow_mut().push(self.engine.build_bitvec_eq(self.curr_value(output)?, self.cell(output, new_cell)?));
        Ok(())
    }

    pub fn replace_net(&mut self, from_net: Net, to_net: Net) -> Result<(), SMT::Error> {
        self.eqs.borrow_mut().push(self.engine.build_bitvec_eq(self.curr_net(from_net)?, self.net(to_net)?));
        Ok(())
    }

    pub fn replace_void_net(&mut self, from_net: Net, to_net: Net) -> Result<(), SMT::Error> {
        self.engine.assert(self.engine.build_bitvec_eq(self.curr_net(from_net)?, self.net(to_net)?))
    }

    pub fn replace_dff_net(&mut self, from_net: Net, to_net: Net) -> Result<(), SMT::Error> {
        // Essentially a single induction step.
        self.engine.assert(self.engine.build_bitvec_eq(self.past_net(from_net)?, self.past_net(to_net)?))?;
        self.eqs.borrow_mut().push(self.engine.build_bitvec_eq(self.curr_net(from_net)?, self.curr_net(to_net)?));
        Ok(())
    }

    pub fn check(&mut self) -> Result<Option<SmtExample>, SMT::Error> {
        if self.eqs.borrow().len() == 0 {
            return Ok(None);
        }
        let not_and_eqs = self.engine.build_not(self.engine.build_and(&self.eqs.borrow()[..]));
        self.engine.assert(not_and_eqs)?;
        match self.engine.check()? {
            SmtResponse::Unknown => panic!("SMT solver returned unknown"),
            SmtResponse::Unsat => Ok(None),
            SmtResponse::Sat => {
                let (mut curr, mut past) = (BTreeMap::new(), BTreeMap::new());
                for (net, bv_net) in self.curr.borrow().iter() {
                    curr.insert(*net, self.engine.get_bitvec(bv_net)?[0]);
                }
                for (net, bv_net) in self.past.borrow().iter() {
                    past.insert(*net, self.engine.get_bitvec(bv_net)?[0]);
                }
                Ok(Some(SmtExample { curr, past }))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtExample {
    curr: BTreeMap<Net, Trit>,
    past: BTreeMap<Net, Trit>,
}

impl SmtExample {
    pub fn get_net(&self, net: Net) -> Option<Trit> {
        self.curr.get(&net).cloned()
    }

    pub fn get_value<'a>(&self, value: impl Into<Cow<'a, Value>>) -> Option<Const> {
        let mut result = Const::EMPTY;
        for net in &*value.into() {
            result.push(self.get_net(net)?);
        }
        Some(result)
    }

    pub fn get_past_net(&self, net: Net) -> Option<Trit> {
        self.past.get(&net).cloned()
    }

    pub fn get_past_value<'a>(&self, value: impl Into<Cow<'a, Value>>) -> Option<Const> {
        let mut result = Const::EMPTY;
        for net in &*value.into() {
            result.push(self.get_past_net(net)?);
        }
        Some(result)
    }
}
