use prjunnamed_netlist::{Design, CellRepr, Value, Net, CellRef};

fn lower_horiz_or(design: &Design, value: Value) -> Net {
    let mut nets = Vec::from_iter(value.iter());
    while nets.len() > 1 {
        for chunk in std::mem::take(&mut nets).chunks(2) {
            if chunk.len() == 2 {
                nets.push(design.add_or1(chunk[0], chunk[1]))
            } else {
                nets.push(chunk[0]);
            }
        }
    }
    *nets.first().unwrap_or(&Net::ZERO)
}

fn lower_shift(
    design: &Design,
    cell: CellRef,
    value: &Value,
    shcnt: &Value,
    stride: u32,
    shift: impl Fn(&Value, usize) -> Value,
    overflow: Value,
) {
    let mut stride = stride as usize;
    let mut value = value.clone();
    for (index, bit) in shcnt.iter().enumerate() {
        if stride < value.len() {
            let shval = shift(&value, stride);
            value = design.add_mux(bit, shval, value);
            stride *= 2;
        } else {
            let mut did_overflow = bit;
            for bit in &shcnt[index + 1..] {
                did_overflow = design.add_or1(did_overflow, bit);
            }
            value = design.add_mux(did_overflow, overflow, value);
            break;
        }
    }
    cell.replace(CellRepr::Buf(value));
}

pub fn lower(design: &mut Design) {
    if cfg!(feature = "trace") {
        eprintln!(">lower"); // FIXME: more detailed tracing
    }
    for cell in design.iter_cells() {
        match &*cell.repr() {
            CellRepr::Eq(a, b) => {
                if a.len() == 0 {
                    cell.replace(CellRepr::Buf(Value::ones(1)));
                } else {
                    let xor = design.add_xor(a, b);
                    cell.replace(CellRepr::Not(lower_horiz_or(design, xor).into()));
                }
            }
            CellRepr::ULt(a, b) => {
                let b_inv = design.add_not(b);
                let sub = design.add_adc(a, b_inv, Net::ONE);
                cell.replace(CellRepr::Not(sub.msb().into()));
            }
            CellRepr::SLt(a, b) => {
                let a_inv = Value::from(&a[..a.len() - 1]).concat(design.add_not(a.msb()));
                let b_inv = design.add_not(&b[..b.len() - 1]).concat(b.msb());
                let sub = design.add_adc(a_inv, b_inv, Net::ONE);
                cell.replace(CellRepr::Not(sub.msb().into()));
            }
            CellRepr::Shl(a, b, stride) => {
                lower_shift(
                    design,
                    cell,
                    a,
                    b,
                    *stride,
                    |value, shcnt| Value::zero(shcnt).concat(Value::from(&value[..value.len() - shcnt])),
                    Value::zero(a.len()),
                );
            }
            CellRepr::UShr(a, b, stride) => {
                let shift = |value: &Value, shcnt| value.slice(shcnt..).zext(a.len());
                lower_shift(design, cell, a, b, *stride, shift, Value::zero(a.len()));
            }
            CellRepr::SShr(a, b, stride) => {
                let shift = |value: &Value, shcnt| value.slice(shcnt..).sext(a.len());
                lower_shift(design, cell, a, b, *stride, shift, Value::from(a.msb()).sext(a.len()));
            }
            CellRepr::XShr(a, b, stride) => {
                let shift = |value: &Value, shcnt| value.slice(shcnt..).concat(Value::undef(shcnt));
                lower_shift(design, cell, a, b, *stride, shift, Value::undef(a.len()));
            }
            CellRepr::Mul(a, b) => {
                let mut value = Value::zero(a.len());
                for (index, bit) in b.iter().enumerate() {
                    value = design.add_adc(
                        value,
                        Value::zero(index).concat(design.add_mux(bit, a, Value::zero(a.len()))),
                        Net::ZERO,
                    );
                }
                cell.replace(CellRepr::Buf(value.slice(..a.len())));
            }
            CellRepr::UDiv(..)
            | CellRepr::UMod(..)
            | CellRepr::SDivTrunc(..)
            | CellRepr::SModTrunc(..)
            | CellRepr::SDivFloor(..)
            | CellRepr::SModFloor(..) => {
                todo!()
            }
            _ => (),
        }
    }
    design.compact();
}
