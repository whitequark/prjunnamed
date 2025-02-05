use std::{borrow::Cow, fmt::Display};

use crate::{CellRef, Cell, Const, ControlNet, Design, IoNet, IoValue, MemoryPortRelation, Net, ParamValue, Trit, Value};

struct DisplayFn<'a, F: for<'b> Fn(&Design, &mut std::fmt::Formatter<'b>) -> std::fmt::Result>(&'a Design, F);

impl<F: Fn(&Design, &mut std::fmt::Formatter) -> std::fmt::Result> Display for DisplayFn<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.1(self.0, f)
    }
}

impl Design {
    fn write_string(&self, f: &mut std::fmt::Formatter, str: &str) -> std::fmt::Result {
        write!(f, "\"")?;
        for byte in str.as_bytes() {
            if (byte.is_ascii_graphic() || matches!(byte, b' ' | b'\t')) && *byte != b'"' {
                write!(f, "{}", *byte as char)?;
            } else {
                assert!(byte.is_ascii());
                write!(f, "\\{:02x}", byte)?;
            }
        }
        write!(f, "\"")?;
        Ok(())
    }

    fn write_net(&self, f: &mut std::fmt::Formatter, net: Net) -> std::fmt::Result {
        if let Some(index) = net.as_cell_index() {
            if !self.is_valid_cell_index(index) {
                return write!(f, "%_{}", index);
            }
        }
        match self.find_cell(net) {
            Ok((cell_ref, offset)) => {
                if cell_ref.output().len() == 1 {
                    write!(f, "%{}", cell_ref.debug_index())
                } else {
                    write!(f, "%{}+{}", cell_ref.debug_index(), offset)
                }
            }
            Err(trit) => write!(f, "{}", trit),
        }
    }

    fn write_value(&self, f: &mut std::fmt::Formatter, value: &Value) -> std::fmt::Result {
        if value.is_empty() {
            return write!(f, "{{}}");
        } else if value.len() == 1 {
            return self.write_net(f, value[0]);
        } else if let Some(value) = value.as_const() {
            return write!(f, "{}", value);
        } else if value
            .iter()
            .any(|net| net.as_cell_index().map(|index| !self.is_valid_cell_index(index)).unwrap_or(false))
        {
            // Value contains newly added cells that we can't look up. Don't try to make
            // the display nicer, just make sure it doesn't panic.
            write!(f, "{{")?;
            for net in value.iter().rev() {
                write!(f, " ")?;
                self.write_net(f, net)?;
            }
            write!(f, " }}")?;
            return Ok(());
        } else if let Ok((cell_ref, _offset)) = self.find_cell(value[0]) {
            if *value == cell_ref.output() {
                if value.len() == 1 {
                    return write!(f, "%{}", cell_ref.debug_index());
                } else {
                    return write!(f, "%{}:{}", cell_ref.debug_index(), value.len());
                }
            }
        }

        enum Chunk {
            Slice { cell_index: usize, output_len: usize, count: usize },
            Net(Net),
        }
        write!(f, "{{")?;
        let mut index = 0;
        let mut chunks = vec![];
        while index < value.len() {
            if let Ok((cell_ref_a, 0)) = self.find_cell(value[index]) {
                let count = value[index..]
                    .iter()
                    .enumerate()
                    .take_while(|(addend, net)| {
                        if let Ok((cell_ref_b, offset_b)) = self.find_cell(**net) {
                            cell_ref_a == cell_ref_b && *addend == offset_b
                        } else {
                            false
                        }
                    })
                    .count();
                if count > 0 {
                    chunks.push(Chunk::Slice {
                        cell_index: cell_ref_a.debug_index(),
                        output_len: cell_ref_a.output_len(),
                        count,
                    });
                    index += count;
                    continue;
                }
            }
            chunks.push(Chunk::Net(value[index]));
            index += 1;
        }
        for chunk in chunks.into_iter().rev() {
            write!(f, " ")?;
            match chunk {
                Chunk::Slice { cell_index, output_len, count } => {
                    if output_len == 1 && count == 1 {
                        write!(f, "%{}", cell_index)?;
                    } else if count == 1 {
                        write!(f, "%{}+0", cell_index)?;
                    } else {
                        write!(f, "%{}:{}", cell_index, count)?;
                    }
                }
                Chunk::Net(net) => {
                    self.write_net(f, net)?;
                }
            }
        }
        write!(f, " }}")
    }

    fn write_io_net(&self, f: &mut std::fmt::Formatter, io_net: IoNet) -> std::fmt::Result {
        if io_net.is_floating() {
            write!(f, "&_")
        } else {
            write!(f, "&")?;
            match self.find_io(io_net) {
                Some((name, offset)) => {
                    self.write_string(f, name)?;
                    if self.get_io(name).unwrap().len() > 1 {
                        write!(f, "+{}", offset)?;
                    }
                    Ok(())
                }
                None => write!(f, "??"),
            }
        }
    }

    fn write_io_value(&self, f: &mut std::fmt::Formatter, io_value: &IoValue) -> std::fmt::Result {
        if io_value.is_empty() {
            write!(f, "{{}}")
        } else if io_value.len() == 1 {
            self.write_io_net(f, io_value[0])
        } else if io_value.iter().all(IoNet::is_floating) {
            write!(f, "&_:{}", io_value.len())
        } else {
            if let Some((name, _offset)) = self.find_io(io_value[0]) {
                if self.get_io(name).unwrap() == *io_value {
                    write!(f, "&")?;
                    self.write_string(f, name)?;
                    write!(f, ":{}", io_value.len())?;
                    return Ok(());
                }
            }
            write!(f, "{{")?;
            for io_net in io_value.iter().rev() {
                write!(f, " ")?;
                self.write_io_net(f, io_net)?;
            }
            write!(f, " }}")
        }
    }

    fn write_cell(&self, f: &mut std::fmt::Formatter, cell_ref: CellRef) -> std::fmt::Result {
        let write_control_net = |f: &mut std::fmt::Formatter, control_net: ControlNet| -> std::fmt::Result {
            if control_net.is_negative() {
                write!(f, "!")?;
            };
            self.write_net(f, control_net.net())
        };

        let write_control = |f: &mut std::fmt::Formatter, name: &str, control_net: ControlNet| -> std::fmt::Result {
            write!(f, "{}=", name)?;
            write_control_net(f, control_net)
        };

        let write_common = |f: &mut std::fmt::Formatter, name: &str, args: &[&Value]| -> std::fmt::Result {
            write!(f, "{}", name)?;
            for arg in args {
                write!(f, " ")?;
                self.write_value(f, arg)?;
            }
            Ok(())
        };

        let write_shift =
            |f: &mut std::fmt::Formatter, name: &str, arg1: &Value, arg2: &Value, stride: u32| -> std::fmt::Result {
                write!(f, "{} ", name)?;
                self.write_value(f, arg1)?;
                write!(f, " ")?;
                self.write_value(f, arg2)?;
                write!(f, " #{stride}")?;
                Ok(())
            };

        let write_param_value = |f: &mut std::fmt::Formatter, value: &ParamValue| -> std::fmt::Result {
            match value {
                ParamValue::Const(value) => write!(f, "const({})", value)?,
                ParamValue::Int(value) => write!(f, "int({})", value)?,
                ParamValue::Float(value) => write!(f, "float({})", value)?,
                ParamValue::String(value) => {
                    write!(f, "string(")?;
                    self.write_string(f, value)?;
                    write!(f, ")")?;
                }
            }
            Ok(())
        };

        let write_cell_argument = |f: &mut std::fmt::Formatter, sigil: &str, name: &str| -> std::fmt::Result {
            write!(f, "  {sigil}@")?;
            self.write_string(f, name)?;
            write!(f, "=")?;
            Ok(())
        };

        write!(f, "%{}:{} = ", cell_ref.debug_index(), cell_ref.output_len())?;
        match &*cell_ref.get() {
            Cell::Buf(arg) => write_common(f, "buf", &[arg])?,
            Cell::Not(arg) => write_common(f, "not", &[arg])?,
            Cell::And(arg1, arg2) => write_common(f, "and", &[arg1, arg2])?,
            Cell::Or(arg1, arg2) => write_common(f, "or", &[arg1, arg2])?,
            Cell::Xor(arg1, arg2) => write_common(f, "xor", &[arg1, arg2])?,
            Cell::Mux(arg1, arg2, arg3) => {
                write!(f, "mux ")?;
                self.write_net(f, *arg1)?;
                write!(f, " ")?;
                self.write_value(f, arg2)?;
                write!(f, " ")?;
                self.write_value(f, arg3)?;
            }
            Cell::Adc(arg1, arg2, arg3) => {
                write!(f, "adc ")?;
                self.write_value(f, arg1)?;
                write!(f, " ")?;
                self.write_value(f, arg2)?;
                write!(f, " ")?;
                self.write_net(f, *arg3)?;
            }

            Cell::Eq(arg1, arg2) => write_common(f, "eq", &[arg1, arg2])?,
            Cell::ULt(arg1, arg2) => write_common(f, "ult", &[arg1, arg2])?,
            Cell::SLt(arg1, arg2) => write_common(f, "slt", &[arg1, arg2])?,

            Cell::Shl(arg1, arg2, stride) => write_shift(f, "shl", arg1, arg2, *stride)?,
            Cell::UShr(arg1, arg2, stride) => write_shift(f, "ushr", arg1, arg2, *stride)?,
            Cell::SShr(arg1, arg2, stride) => write_shift(f, "sshr", arg1, arg2, *stride)?,
            Cell::XShr(arg1, arg2, stride) => write_shift(f, "xshr", arg1, arg2, *stride)?,

            Cell::Mul(arg1, arg2) => write_common(f, "mul", &[arg1, arg2])?,
            Cell::UDiv(arg1, arg2) => write_common(f, "udiv", &[arg1, arg2])?,
            Cell::UMod(arg1, arg2) => write_common(f, "umod", &[arg1, arg2])?,
            Cell::SDivTrunc(arg1, arg2) => write_common(f, "sdiv_trunc", &[arg1, arg2])?,
            Cell::SDivFloor(arg1, arg2) => write_common(f, "sdiv_floor", &[arg1, arg2])?,
            Cell::SModTrunc(arg1, arg2) => write_common(f, "smod_trunc", &[arg1, arg2])?,
            Cell::SModFloor(arg1, arg2) => write_common(f, "smod_floor", &[arg1, arg2])?,

            Cell::Match(match_cell) => {
                write!(f, "match")?;
                if match_cell.enable != Net::ONE {
                    write!(f, " en=")?;
                    self.write_net(f, match_cell.enable)?;
                }
                write!(f, " ")?;
                self.write_value(f, &match_cell.value)?;
                let multiline = match_cell
                    .patterns
                    .iter()
                    .map(|alternates| alternates.iter().map(Const::len).sum::<usize>())
                    .sum::<usize>()
                    > 80;
                write!(f, " {{")?;
                if multiline {
                    writeln!(f)?;
                }
                for alternates in &match_cell.patterns {
                    if multiline {
                        write!(f, "  ")?;
                    } else {
                        write!(f, " ")?;
                    }
                    if alternates.len() == 1 {
                        let pattern = &alternates[0];
                        write!(f, "{pattern}")?;
                    } else {
                        write!(f, "[")?;
                        for (index, pattern) in alternates.iter().enumerate() {
                            if index > 0 {
                                write!(f, " ")?;
                            }
                            write!(f, "{pattern}")?;
                        }
                        write!(f, "]")?;
                    }
                    if multiline {
                        writeln!(f)?;
                    }
                }
                if !multiline {
                    write!(f, " ")?;
                }
                write!(f, "}}")?;
            }
            Cell::Assign(assign_cell) => {
                write!(f, "assign")?;
                if assign_cell.enable != Net::ONE {
                    write!(f, " en=")?;
                    self.write_net(f, assign_cell.enable)?;
                }
                write!(f, " ")?;
                self.write_value(f, &assign_cell.value)?;
                write!(f, " ")?;
                self.write_value(f, &assign_cell.update)?;
                if assign_cell.offset != 0 {
                    write!(f, " at=#{}", assign_cell.offset)?;
                }
            }

            Cell::Dff(flip_flop) => {
                write_common(f, "dff", &[&flip_flop.data])?;
                write_control(f, " clk", flip_flop.clock)?;
                if flip_flop.has_clear() {
                    write_control(f, " clr", flip_flop.clear)?;
                    if flip_flop.clear_value != flip_flop.init_value {
                        write!(f, ",{}", flip_flop.clear_value)?;
                    }
                }
                if flip_flop.has_reset() {
                    write_control(f, " rst", flip_flop.reset)?;
                    if flip_flop.reset_value != flip_flop.init_value {
                        write!(f, ",{}", flip_flop.reset_value)?;
                    }
                }
                if flip_flop.has_enable() {
                    write_control(f, " en", flip_flop.enable)?;
                }
                if flip_flop.has_reset() && flip_flop.has_enable() {
                    if flip_flop.reset_over_enable {
                        write!(f, " rst>en")?;
                    } else {
                        write!(f, " en>rst")?;
                    }
                }
                if flip_flop.has_init_value() {
                    write!(f, " init={}", flip_flop.init_value)?;
                }
            }
            Cell::Memory(memory) => {
                writeln!(f, "memory depth=#{} width=#{} {{", memory.depth, memory.width)?;
                for write_port in &memory.write_ports {
                    write!(f, "  write addr=")?;
                    self.write_value(f, &write_port.addr)?;
                    write!(f, " data=")?;
                    self.write_value(f, &write_port.data)?;
                    if !write_port.mask.is_ones() {
                        write!(f, " mask=")?;
                        self.write_value(f, &write_port.mask)?;
                    }
                    write_control(f, " clk", write_port.clock)?;
                    writeln!(f)?;
                }
                for read_port in &memory.read_ports {
                    write!(f, "  read addr=")?;
                    self.write_value(f, &read_port.addr)?;
                    write!(f, " width=#{}", read_port.data_len)?;
                    if let Some(ref flip_flop) = read_port.flip_flop {
                        write_control(f, " clk", flip_flop.clock)?;
                        if flip_flop.has_clear() {
                            write_control(f, " clr", flip_flop.clear)?;
                            if flip_flop.clear_value != flip_flop.init_value {
                                write!(f, ",{}", flip_flop.clear_value)?;
                            }
                        }
                        if flip_flop.has_reset() {
                            write_control(f, " rst", flip_flop.reset)?;
                            if flip_flop.reset_value != flip_flop.init_value {
                                write!(f, ",{}", flip_flop.reset_value)?;
                            }
                        }
                        if flip_flop.has_enable() {
                            write_control(f, " en", flip_flop.enable)?;
                        }
                        if flip_flop.has_reset() && flip_flop.has_enable() {
                            if flip_flop.reset_over_enable {
                                write!(f, " rst>en")?;
                            } else {
                                write!(f, " en>rst")?;
                            }
                        }
                        if flip_flop.has_init_value() {
                            write!(f, " init={}", flip_flop.init_value)?;
                        }
                        write!(f, " [")?;
                        for (index, relation) in flip_flop.relations.iter().enumerate() {
                            match relation {
                                MemoryPortRelation::Undefined => write!(f, "undef")?,
                                MemoryPortRelation::ReadBeforeWrite => write!(f, "rdfirst")?,
                                MemoryPortRelation::Transparent => write!(f, "trans")?,
                            }
                            if index < flip_flop.relations.len() - 1 {
                                write!(f, " ")?;
                            }
                        }
                        write!(f, "]")?;
                    }
                    writeln!(f)?;
                }
                let fully_undef_rows_at_end = memory
                    .init_value
                    .iter()
                    .rev()
                    .enumerate()
                    .find(|(_index, trit)| !matches!(trit, Trit::Undef))
                    .map(|(index, _trit)| index)
                    .unwrap_or(memory.width * memory.depth)
                    / memory.width;
                for index in 0..(memory.depth - fully_undef_rows_at_end) {
                    write!(f, "  init ")?;
                    for trit in memory.init_value[(index * memory.width)..((index + 1) * memory.width)].iter().rev() {
                        write!(f, "{trit}")?;
                    }
                    writeln!(f)?;
                }
                write!(f, "}}")?;
            }
            Cell::Iob(io_buffer) => {
                write!(f, "iob ")?;
                self.write_io_value(f, &io_buffer.io)?;
                write!(f, " o=")?;
                self.write_value(f, &io_buffer.output)?;
                write_control(f, " en", io_buffer.enable)?;
            }
            Cell::Other(instance) => {
                self.write_string(f, instance.kind.as_str())?;
                writeln!(f, " {{")?;
                for (name, value) in instance.params.iter() {
                    write_cell_argument(f, "p", name)?;
                    write_param_value(f, value)?;
                    writeln!(f)?;
                }
                for (name, value) in instance.inputs.iter() {
                    write_cell_argument(f, "i", name)?;
                    self.write_value(f, value)?;
                    writeln!(f)?;
                }
                for (name, range) in instance.outputs.iter() {
                    write_cell_argument(f, "o", name)?;
                    writeln!(f, "{}:{}", range.start, range.len())?;
                }
                for (name, value) in instance.ios.iter() {
                    write_cell_argument(f, "io", name)?;
                    self.write_io_value(f, value)?;
                    writeln!(f)?;
                }
                write!(f, "}}")?;
            }
            Cell::Target(target_cell) => {
                write!(f, "target ")?;
                let prototype = self.target_prototype(target_cell);
                self.write_string(f, &target_cell.kind)?;
                writeln!(f, " {{")?;
                for (param, value) in prototype.params.iter().zip(target_cell.params.iter()) {
                    write_cell_argument(f, "p", &param.name)?;
                    write_param_value(f, value)?;
                    writeln!(f)?;
                }
                for input in &prototype.inputs {
                    write_cell_argument(f, "i", &input.name)?;
                    self.write_value(f, &target_cell.inputs.slice(input.range.clone()))?;
                    writeln!(f)?;
                }
                for io in &prototype.ios {
                    write_cell_argument(f, "io", &io.name)?;
                    self.write_io_value(f, &target_cell.ios.slice(io.range.clone()))?;
                    writeln!(f)?;
                }
                write!(f, "}}")?;
            }

            Cell::Input(name, _size) => {
                write!(f, "input ")?;
                self.write_string(f, name)?;
            }
            Cell::Output(name, value) => {
                write!(f, "output ")?;
                self.write_string(f, name)?;
                write!(f, " ")?;
                self.write_value(f, value)?;
            }
            Cell::Name(name, value) => {
                write!(f, "name ")?;
                self.write_string(f, name)?;
                write!(f, " ")?;
                self.write_value(f, value)?;
            }
        }
        Ok(())
    }

    pub fn display_net(&self, net: impl Into<Net>) -> impl Display + '_ {
        let net = net.into();
        DisplayFn(self, move |design: &Design, f| design.write_net(f, net))
    }

    pub fn display_value<'a, 'b: 'a>(&'a self, value: impl Into<Cow<'b, Value>>) -> impl Display + 'a {
        let value = value.into();
        DisplayFn(self, move |design: &Design, f| design.write_value(f, &value))
    }

    pub fn display_cell<'a>(&'a self, value: CellRef<'a>) -> impl Display + 'a {
        DisplayFn(self, move |design: &Design, f| design.write_cell(f, value))
    }
}

impl Display for Design {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(target) = self.target() {
            write!(f, "target ")?;
            self.write_string(f, target.name())?;
            for (name, value) in target.options() {
                write!(f, " ")?;
                self.write_string(f, &name)?;
                write!(f, "=")?;
                self.write_string(f, &value)?;
            }
            writeln!(f)?;
        }

        for (name, io_value) in self.iter_ios() {
            write!(f, "&")?;
            self.write_string(f, name)?;
            writeln!(f, ":{}", io_value.len())?;
        }

        if f.alternate() {
            for cell_ref in self.iter_cells() {
                self.write_cell(f, cell_ref)?;
                writeln!(f)?;
            }
        } else {
            for cell_ref in self.iter_cells_topo() {
                self.write_cell(f, cell_ref)?;
                writeln!(f)?;
            }
        }

        Ok(())
    }
}
