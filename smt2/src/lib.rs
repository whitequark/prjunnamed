use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io;

use easy_smt::{Context, ContextBuilder, Response, SExpr, SExprData};
use prjunnamed_netlist::{CellRef, Cell, Design, Net, Value};

fn unimplemented_undef() -> ! {
    unimplemented!("SMT emitter does not support X values")
}

struct SmtEmitter<'a, 'b> {
    design: &'a Design,
    context: &'b mut Context,
    prefix: String,
    declared: BTreeSet<String>,
    inputs: BTreeMap<String, SExpr>,
    outputs: BTreeMap<String, SExpr>,
}

impl<'a, 'b> SmtEmitter<'a, 'b> {
    fn new(design: &'a Design, context: &'b mut Context, prefix: impl Into<String>) -> SmtEmitter<'a, 'b> {
        SmtEmitter {
            design,
            context,
            prefix: prefix.into(),
            declared: BTreeSet::new(),
            inputs: BTreeMap::new(),
            outputs: BTreeMap::new(),
        }
    }

    fn net_ref(&mut self, net: Net) -> io::Result<SExpr> {
        if net == Net::UNDEF {
            unimplemented_undef();
        } else if net == Net::ZERO {
            Ok(self.context.binary(1, 0))
        } else if net == Net::ONE {
            Ok(self.context.binary(1, 1))
        } else {
            let (cell_ref, offset) = self.design.find_cell(net).expect("invalid cell reference");
            let cell_name_sexpr = self.cell_ref(cell_ref)?;
            Ok(self.context.extract(offset as i32, offset as i32, cell_name_sexpr))
        }
    }

    fn value_ref(&mut self, value: &Value) -> io::Result<SExpr> {
        let mut value_sexpr = None;
        for net in value.iter() {
            let sexpr = self.net_ref(net)?;
            value_sexpr = Some(match value_sexpr {
                None => sexpr,
                Some(value_sexpr) => self.context.concat(sexpr, value_sexpr),
            })
        }
        Ok(value_sexpr.expect("zero length value"))
    }

    fn cell_ref(&mut self, cell_ref: CellRef) -> io::Result<SExpr> {
        let name = match &*cell_ref.get() {
            Cell::Input(name, _width) => format!("<{}", name),
            _ => format!("%{}", cell_ref.debug_index()),
        };
        let name = format!("|{}{}|", self.prefix, name);
        if !self.declared.contains(&name) {
            let width_sexpr = self.context.numeral(cell_ref.output_len());
            let bit_vec_sort_sexpr = self.context.bit_vec_sort(width_sexpr);
            self.context.declare_const(name.clone(), bit_vec_sort_sexpr)?;
            self.declared.insert(name.clone());
        }
        Ok(self.context.atom(name))
    }

    fn cell_def(&mut self, cell_ref: CellRef) -> io::Result<()> {
        let body_sexpr = match &*cell_ref.get() {
            Cell::Buf(arg) => self.value_ref(arg)?,
            Cell::Not(arg) => {
                let arg_sexpr = self.value_ref(arg)?;
                self.context.bvnot(arg_sexpr)
            }
            Cell::And(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvand(arg1_sexpr, arg2_sexpr)
            }
            Cell::Or(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvor(arg1_sexpr, arg2_sexpr)
            }
            Cell::Xor(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvxor(arg1_sexpr, arg2_sexpr)
            }
            Cell::Mux(arg1, arg2, arg3) => {
                let arg1_sexpr = self.net_ref(*arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                let arg3_sexpr = self.value_ref(arg3)?;
                let eq1_sexpr = self.context.eq(arg1_sexpr, self.context.binary(1, 1));
                self.context.ite(eq1_sexpr, arg2_sexpr, arg3_sexpr)
            }
            Cell::Adc(arg1, arg2, arg3) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                let arg3_sexpr = self.net_ref(*arg3)?;
                self.context.bvadd(
                    self.context.bvadd(
                        self.context.concat(self.context.binary(1, 0), arg1_sexpr),
                        self.context.concat(self.context.binary(1, 0), arg2_sexpr),
                    ),
                    self.context.concat(self.context.binary(arg1.len(), 0), arg3_sexpr),
                )
            }
            Cell::Eq(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.eq(arg1_sexpr, arg2_sexpr)
            }
            Cell::ULt(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvult(arg1_sexpr, arg2_sexpr)
            }
            Cell::SLt(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvslt(arg1_sexpr, arg2_sexpr)
            }
            Cell::Shl(arg1, arg2, 1) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvshl(arg1_sexpr, arg2_sexpr)
            }
            Cell::UShr(arg1, arg2, 1) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvlshr(arg1_sexpr, arg2_sexpr)
            }
            Cell::SShr(arg1, arg2, 1) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvashr(arg1_sexpr, arg2_sexpr)
            }
            Cell::XShr(_arg1, _arg2, 1) => unimplemented_undef(),
            Cell::Shl(_, _, _) | Cell::UShr(_, _, _) | Cell::SShr(_, _, _) | Cell::XShr(_, _, _) => {
                unimplemented!("shifts with non-1 stride are not implemented yet")
            }
            Cell::Mul(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvmul(arg1_sexpr, arg2_sexpr)
            }
            Cell::UDiv(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvudiv(arg1_sexpr, arg2_sexpr)
            }
            Cell::UMod(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvurem(arg1_sexpr, arg2_sexpr)
            }
            Cell::SDivTrunc(_arg1, _arg2) => {
                unimplemented!("waiting on https://github.com/elliottt/easy-smt/pull/35");
                // let arg1_sexpr = self.value_ref(arg1)?;
                // let arg2_sexpr = self.value_ref(arg2)?;
                // self.context.bvsdiv(arg1_sexpr, arg2_sexpr)
            }
            Cell::SDivFloor(_arg1, _arg2) => todo!(),
            Cell::SModTrunc(arg1, arg2) => {
                let arg1_sexpr = self.value_ref(arg1)?;
                let arg2_sexpr = self.value_ref(arg2)?;
                self.context.bvsrem(arg1_sexpr, arg2_sexpr)
            }
            Cell::SModFloor(_arg1, _arg2) => {
                unimplemented!("waiting on https://github.com/elliottt/easy-smt/pull/35");
                // let arg1_sexpr = self.value_ref(arg1)?;
                // let arg2_sexpr = self.value_ref(arg2)?;
                // self.context.bvsmod(arg1_sexpr, arg2_sexpr)
            }
            Cell::Match { .. } => unimplemented!("matches are not implemented yet"),
            Cell::Assign { .. } => unimplemented!("assigns are not implemented yet"),
            Cell::Dff(_flip_flop) => unimplemented!("flip-flops are not implemented yet"),
            Cell::Memory(_memory) => unimplemented!("memories are not implemented yet"),
            Cell::Iob(_io_buffer) => unimplemented!("IOs are not implemented yet"),
            Cell::Other(_instance) => unimplemented!("instances are not implemented yet"),
            Cell::Target(_target_cell) => unimplemented!("target cells are not implemented yet"),
            Cell::Input(name, _width) => {
                let mangled_name = self.cell_ref(cell_ref)?;
                self.inputs.insert(name.to_owned(), mangled_name);
                return Ok(());
            }
            Cell::Output(name, value) => {
                let value_sexpr = self.value_ref(value)?;
                let mangled_name = format!("|{}>{}|", self.prefix, name);
                let width_sexpr = self.context.numeral(value.len());
                let bit_vec_sort_sexpr = self.context.bit_vec_sort(width_sexpr);
                self.context.define_fun(&mangled_name, vec![], bit_vec_sort_sexpr, value_sexpr)?;
                self.outputs.insert(name.to_owned(), self.context.atom(mangled_name));
                return Ok(());
            }
            Cell::Name(_, _value) => {
                return Ok(());
            }
        };
        let mangled_name = self.cell_ref(cell_ref)?;
        let eq_sexpr = self.context.eq(mangled_name, body_sexpr);
        self.context.assert(eq_sexpr)?;
        Ok(())
    }

    fn emit(mut self) -> io::Result<(BTreeMap<String, SExpr>, BTreeMap<String, SExpr>)> {
        for cell_ref in self.design.iter_cells() {
            self.cell_def(cell_ref)?;
        }
        Ok((self.inputs, self.outputs))
    }
}

pub fn verify_transformation(design: &mut Design, transform: impl FnOnce(&mut Design)) -> io::Result<()> {
    let mut context = ContextBuilder::new().solver("z3", ["-smt2", "-in"]).build()?;

    let (inputs_before, outputs_before) = SmtEmitter::new(design, &mut context, "before").emit()?;

    let design_before = design.clone();
    transform(design);

    let (inputs_after, outputs_after) = SmtEmitter::new(design, &mut context, "after").emit()?;

    for (input_name, before_mangled) in inputs_before.iter() {
        let after_mangled = *inputs_after.get(input_name).expect("input names must match");
        context.assert(context.eq(*before_mangled, after_mangled))?;
    }

    let mut output_eq_sexprs = vec![];
    for (output_name, before_mangled) in outputs_before.iter() {
        let after_mangled = *outputs_after.get(output_name).expect("output names must match");
        output_eq_sexprs.push(context.eq(*before_mangled, after_mangled));
    }
    context.assert(context.not(context.or_many(output_eq_sexprs.into_iter())))?;

    // We are asking the solver to find a counterexample for our assertion that the two models
    // always have the same output. Getting `unsat` here means there isn't one, i.e. transformation is sound.
    match context.check()? {
        Response::Unknown => panic!("SMT solver could not confirm or deny correctness"),
        Response::Unsat => Ok(()),
        Response::Sat => {
            let environment: HashMap<SExpr, SExpr> = HashMap::from_iter(context.get_value(
                inputs_before.values().chain(outputs_before.values()).chain(outputs_after.values()).copied().collect(),
            )?);
            let get_value = |mangled: SExpr| {
                let value_sexpr = environment.get(&mangled).expect("solver should return a value");
                match context.get(*value_sexpr) {
                    SExprData::List(_sexprs) => panic!("solver should return an atom"),
                    SExprData::Atom(value) => value,
                }
            };

            let mut message = "SMT solver found a counterexample:\n".to_owned();
            for (input, mangled) in inputs_before {
                message += &format!("{} = {}\n", input, get_value(mangled));
            }
            for (output, before_mangled) in outputs_before {
                let after_mangled = *outputs_after.get(&output).unwrap();
                message += &format!(
                    "{} = {} (before), {} (after)\n",
                    output,
                    get_value(before_mangled),
                    get_value(after_mangled)
                );
            }
            message += &format!("\ndesign before transformation:\n{}", design_before);
            message += &format!("\ndesign after transformation:\n{}", design);
            panic!("{}", message);
        }
    }
}
