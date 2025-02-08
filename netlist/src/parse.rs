use std::{collections::BTreeMap, fmt::Display, ops::Range, str::FromStr, sync::Arc};

use yap::{one_of, types::WithContext, IntoTokens, TokenLocation, Tokens};

use crate::{
    AssignCell, MatchCell, create_target, Cell, Const, ControlNet, Design, FlipFlop, Instance, IoBuffer, IoNet,
    IoValue, Memory, MemoryPortRelation, MemoryReadFlipFlop, MemoryReadPort, MemoryWritePort, Net, ParamValue, Target,
    TargetCell, Value,
};

#[derive(Debug)]
struct Context {
    design: Design,
    is_empty: bool,
    cell_map: BTreeMap<usize, Value>,        // source cell index -> value
    late_map: BTreeMap<(usize, usize), Net>, // source cell index + net offset -> buffer
}

impl Context {
    fn new(target: Option<Arc<dyn Target>>) -> Context {
        Context {
            design: Design::with_target(target),
            is_empty: true,
            cell_map: BTreeMap::new(),
            late_map: BTreeMap::new(),
        }
    }

    fn add_io(&mut self, name: String, width: usize) -> IoValue {
        self.is_empty = false;
        self.design.add_io(name, width)
    }

    fn get_io(&self, name: impl AsRef<str>) -> IoValue {
        self.design.get_io(name).expect("name should reference an IO")
    }

    fn get_io_with_width(&self, name: impl AsRef<str>, width: usize) -> IoValue {
        let value = self.get_io(name);
        assert_eq!(value.len(), width, "IO width should match reference width");
        value
    }

    fn add_cell(&mut self, index: usize, width: usize, cell: Cell) -> Value {
        self.is_empty = false;
        let value = self.design.add_cell(cell);
        assert_eq!(value.len(), width, "cell width should match declaration width");
        assert_eq!(self.cell_map.insert(index, value.clone()), None, "cell indices cannot be reused");
        value
    }

    fn get_cell(&mut self, index: usize, offsets: Range<usize>) -> Value {
        if let Some(value) = self.cell_map.get(&index) {
            value.slice(offsets)
        } else {
            let mut nets = vec![];
            for offset in offsets {
                let net = self.late_map.entry((index, offset)).or_insert_with(|| self.design.add_void(1).unwrap_net());
                nets.push(*net);
            }
            Value::from(nets)
        }
    }

    fn finalize(mut self) -> Design {
        for ((index, offset), net) in self.late_map.into_iter() {
            if let Some(output) = self.cell_map.get(&index) {
                if offset < output.len() {
                    self.design.replace_net(net, output[offset]);
                } else {
                    panic!("late cell reference %{}+{} out of bounds for %{}:{}", index, offset, index, output.len());
                }
            } else {
                panic!("unresolved late cell index %{}", index)
            }
        }
        self.design.apply();
        self.design
    }
}

fn parse_space(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> bool {
    t.skip_while(|c| *c == ' ' || *c == '\t') > 0
}

fn parse_symbol(t: &mut WithContext<impl Tokens<Item = char>, Context>, symbol: char) -> Option<()> {
    if !t.token(symbol) {
        return None;
    }
    Some(())
}

fn parse_decimal<T: FromStr>(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<T> {
    t.take_while(|c| c.is_digit(10) || *c == '-').parse::<T, String>().ok()
}

fn parse_string_char(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<u8> {
    match t.next() {
        Some('"' | '\\') => None,
        Some(char) if char.is_ascii() => Some(char as u8),
        _ => None,
    }
}

fn parse_string_escape(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<u8> {
    parse_symbol(t, '\\')?;
    if let (Some(hi @ ('0'..='9' | 'a'..='f')), Some(lo @ ('0'..='9' | 'a'..='f'))) = (t.next(), t.next()) {
        u8::from_str_radix(&format!("{hi}{lo}"), 16).ok()
    } else {
        None
    }
}

fn parse_string(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
    parse_symbol(t, '"')?;
    let bytes = t
        .many(|t| {
            one_of!(t;
                parse_string_char(t),
                parse_string_escape(t)
            )
        })
        .collect::<Vec<u8>>();
    parse_symbol(t, '"')?;
    String::from_utf8(bytes).ok()
}

fn parse_const(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Const> {
    t.take_while(|c| *c == 'X' || *c == '0' || *c == '1').parse::<Const, String>().ok().and_then(|value| {
        if !value.is_empty() {
            Some(value)
        } else {
            None
        }
    })
}

fn parse_keyword(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
    let name: String = t.take_while(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '>')).collect();
    if name.is_empty() {
        return None;
    }
    Some(name)
}

fn parse_keyword_eq(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
    let keyword = parse_keyword(t)?;
    parse_space(t);
    parse_symbol(t, '=')?;
    parse_space(t);
    Some(keyword)
}

#[must_use]
fn parse_keyword_eq_expect(t: &mut WithContext<impl Tokens<Item = char>, Context>, expected: &str) -> Option<()> {
    let keyword = parse_keyword_eq(t)?;
    if keyword != expected {
        return None;
    }
    Some(())
}

fn parse_io_name(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
    parse_symbol(t, '&')?;
    parse_string(t)
}

fn parse_io_name_size(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<(String, usize)> {
    let name = parse_io_name(t)?;
    parse_symbol(t, ':')?;
    let size = parse_decimal(t)?;
    Some((name, size))
}

fn parse_io_name_offset(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<(String, usize)> {
    let name = parse_io_name(t)?;
    parse_symbol(t, '+')?;
    let offset = parse_decimal(t)?;
    Some((name, offset))
}

fn parse_io_net(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoNet> {
    one_of!(t;
        parse_symbol(t, '&').and_then(|()| parse_symbol(t, '_')).map(|()| IoNet::FLOATING),
        parse_io_name_offset(t).map(|(name, offset)| t.context().get_io(name)[offset]),
        parse_io_name(t).map(|name| t.context().get_io_with_width(name, 1)[0])
    )
}

fn parse_io_value_floating(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
    parse_symbol(t, '&')?;
    parse_symbol(t, '_')?;
    parse_symbol(t, ':')?;
    let size = parse_decimal(t)?;
    Some(IoValue::from_iter(std::iter::repeat_n(IoNet::FLOATING, size)))
}

fn parse_io_value_concat(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
    let mut value = IoValue::EMPTY;
    parse_symbol(t, '{')?;
    let parts = Vec::from_iter(
        t.many(|t| {
            parse_space(t);
            parse_io_net(t)
        })
        .as_iter(),
    );
    for part in parts.into_iter().rev() {
        value.extend([part]);
    }
    parse_space(t);
    parse_symbol(t, '}')?;
    Some(value)
}

fn parse_io_value(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
    one_of!(t;
        parse_io_value_concat(t),
        parse_io_value_floating(t),
        parse_io_name_size(t).and_then(|(name, size)| Some(t.context().get_io(name).slice(..size))),
        parse_io_net(t).map(IoValue::from),
    )
}

fn parse_cell_index(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<usize> {
    parse_symbol(t, '%')?;
    parse_decimal(t)
}

fn parse_cell_index_size(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<(usize, usize)> {
    let cell_index = parse_cell_index(t)?;
    parse_symbol(t, ':')?;
    let net_count = parse_decimal(t)?;
    Some((cell_index, net_count))
}

fn parse_cell_index_offset(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<(usize, usize)> {
    let cell_index = parse_cell_index(t)?;
    parse_symbol(t, '+')?;
    let net_offset = parse_decimal(t)?;
    Some((cell_index, net_offset))
}

fn parse_value_part(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Value> {
    one_of!(t;
        parse_const(t).map(Value::from),
        parse_cell_index_offset(t).and_then(|(cell_index, net_offset)| {
            Some(Value::from(t.context_mut().get_cell(cell_index, net_offset..net_offset+1)))
        }),
        parse_cell_index_size(t).and_then(|(cell_index, net_count)| {
            Some(t.context_mut().get_cell(cell_index, 0..net_count))
        }),
        parse_cell_index(t).and_then(|cell_index| {
            Some(t.context_mut().get_cell(cell_index, 0..1))
        }),
    )
}

fn parse_value_concat(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Value> {
    let mut value = Value::EMPTY;
    parse_symbol(t, '{')?;
    let parts = Vec::from_iter(
        t.many(|t| {
            parse_space(t);
            parse_value_part(t)
        })
        .as_iter(),
    );
    for part in parts.into_iter().rev() {
        value.extend(part);
    }
    parse_space(t);
    parse_symbol(t, '}')?;
    Some(value)
}

fn parse_target_option(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<(String, String)> {
    parse_space(t);
    let name = parse_string(t)?;
    parse_space(t);
    parse_symbol(t, '=')?;
    parse_space(t);
    let value = parse_string(t)?;
    Some((name, value))
}

fn parse_target(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<()> {
    parse_space(t);
    let keyword = parse_keyword(t)?;
    if keyword != "target" {
        return None;
    }
    parse_space(t);
    let name = parse_string(t)?;
    let mut options = BTreeMap::new();
    while let Some((name, value)) = parse_target_option(t) {
        if options.insert(name, value).is_some() {
            panic!("target option is specified more than once");
        }
    }
    parse_space(t);
    parse_symbol(t, '\n')?;
    let context = t.context_mut();
    if !context.is_empty {
        panic!("target specification must be the first line of the design");
    }
    context.design = Design::with_target(Some(create_target(&name, options).unwrap()));
    context.is_empty = false;
    Some(())
}

fn parse_io(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
    parse_space(t);
    let (name, size) = parse_io_name_size(t)?;
    parse_space(t);
    parse_symbol(t, '\n')?;
    let io_value = t.context_mut().add_io(name, size);
    t.context_mut().design.apply();
    Some(io_value)
}

fn parse_cell(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Value> {
    fn parse_value_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Value> {
        parse_space(t);
        one_of!(t;
            parse_value_part(t),
            parse_value_concat(t)
        )
    }

    fn parse_net_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Net> {
        parse_space(t);
        parse_value_part(t).map(|value| {
            assert_eq!(value.len(), 1, "reference should be a single net");
            value[0]
        })
    }

    fn parse_control_net_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<ControlNet> {
        parse_space(t);
        let negated = parse_symbol(t, '!').is_some();
        let net = parse_net_arg(t)?;
        if negated {
            Some(ControlNet::Neg(net))
        } else {
            Some(ControlNet::Pos(net))
        }
    }

    fn parse_control_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>, name: &str) -> Option<ControlNet> {
        parse_space(t);
        parse_keyword_eq_expect(t, name)?;
        parse_control_net_arg(t)
    }

    fn parse_int_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<usize> {
        parse_space(t);
        parse_symbol(t, '#')?;
        parse_decimal(t)
    }

    fn parse_string_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
        parse_space(t);
        parse_string(t)
    }

    fn parse_dff_reset_control_net_arg(
        t: &mut WithContext<impl Tokens<Item = char>, Context>,
        name: &str,
    ) -> Option<(ControlNet, Option<Const>)> {
        parse_control_arg(t, name).map(|control_net| {
            let init_value = t.optional(|t| {
                parse_space(t);
                parse_symbol(t, ',')?;
                parse_space(t);
                parse_const(t)
            });
            (control_net, init_value)
        })
    }

    fn parse_reset_over_enable_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<bool> {
        parse_space(t);
        one_of!(t;
            parse_keyword(t).filter(|kw| kw == "rst>en").map(|_| true),
            parse_keyword(t).filter(|kw| kw == "en>rst").map(|_| false),
        )
    }

    fn parse_dff_init_value_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Const> {
        parse_space(t);
        parse_keyword_eq_expect(t, "init")?;
        parse_const(t)
    }

    fn parse_builtin(t: &mut WithContext<impl Tokens<Item = char>, Context>, size: usize) -> Option<Cell> {
        let name = parse_keyword(t)?;
        Some(match name.as_ref() {
            "buf" => Cell::Buf(parse_value_arg(t)?),
            "not" => Cell::Not(parse_value_arg(t)?),
            "and" => Cell::And(parse_value_arg(t)?, parse_value_arg(t)?),
            "or" => Cell::Or(parse_value_arg(t)?, parse_value_arg(t)?),
            "xor" => Cell::Xor(parse_value_arg(t)?, parse_value_arg(t)?),
            "mux" => Cell::Mux(parse_net_arg(t)?, parse_value_arg(t)?, parse_value_arg(t)?),
            "adc" => Cell::Adc(parse_value_arg(t)?, parse_value_arg(t)?, parse_net_arg(t)?),
            "eq" => Cell::Eq(parse_value_arg(t)?, parse_value_arg(t)?),
            "ult" => Cell::ULt(parse_value_arg(t)?, parse_value_arg(t)?),
            "slt" => Cell::SLt(parse_value_arg(t)?, parse_value_arg(t)?),
            "shl" => Cell::Shl(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "ushr" => Cell::UShr(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "sshr" => Cell::SShr(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "xshr" => Cell::XShr(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "mul" => Cell::Mul(parse_value_arg(t)?, parse_value_arg(t)?),
            "udiv" => Cell::UDiv(parse_value_arg(t)?, parse_value_arg(t)?),
            "umod" => Cell::UMod(parse_value_arg(t)?, parse_value_arg(t)?),
            "sdiv_trunc" => Cell::SDivTrunc(parse_value_arg(t)?, parse_value_arg(t)?),
            "sdiv_floor" => Cell::SDivFloor(parse_value_arg(t)?, parse_value_arg(t)?),
            "smod_trunc" => Cell::SModTrunc(parse_value_arg(t)?, parse_value_arg(t)?),
            "smod_floor" => Cell::SModFloor(parse_value_arg(t)?, parse_value_arg(t)?),
            "match" => {
                let enable = t
                    .optional(|t| {
                        parse_space(t);
                        parse_keyword_eq_expect(t, "en")?;
                        parse_net_arg(t)
                    })
                    .unwrap_or(Net::ONE);
                let value = parse_value_arg(t)?;
                let mut patterns = Vec::new();
                parse_space(t);
                parse_symbol(t, '{');
                parse_space(t);
                parse_symbol(t, '\n');
                while let Some(()) = t.optional(|t| {
                    parse_space(t);
                    let mut alternates = Vec::new();
                    if let Some(()) = parse_symbol(t, '[') {
                        while let Some(()) = t.optional(|t| {
                            parse_space(t);
                            alternates.push(parse_const(t)?);
                            Some(())
                        }) {}
                        parse_space(t);
                        parse_symbol(t, ']')?;
                    } else {
                        alternates.push(parse_const(t)?);
                    }
                    parse_space(t);
                    parse_symbol(t, '\n');
                    patterns.push(alternates);
                    Some(())
                }) {}
                parse_space(t);
                parse_symbol(t, '}');
                Cell::Match(MatchCell { value, enable, patterns })
            }
            "assign" => {
                let enable = t
                    .optional(|t| {
                        parse_space(t);
                        parse_keyword_eq_expect(t, "en")?;
                        parse_net_arg(t)
                    })
                    .unwrap_or(Net::ONE);
                let value = parse_value_arg(t)?;
                let update = parse_value_arg(t)?;
                let offset = t
                    .optional(|t| {
                        parse_space(t);
                        parse_keyword_eq_expect(t, "at")?;
                        parse_symbol(t, '#')?;
                        parse_decimal(t)
                    })
                    .unwrap_or(0);
                Cell::Assign(AssignCell { value, enable, update, offset })
            }
            "dff" => {
                let data = parse_value_arg(t)?;
                let clock = parse_control_arg(t, "clk")?;
                let (clear, clear_value) = t
                    .optional(|t| parse_dff_reset_control_net_arg(t, "clr"))
                    .unwrap_or((ControlNet::Pos(Net::ZERO), None));
                let (reset, reset_value) = t
                    .optional(|t| parse_dff_reset_control_net_arg(t, "rst"))
                    .unwrap_or((ControlNet::Pos(Net::ZERO), None));
                let enable = t.optional(|t| parse_control_arg(t, "en")).unwrap_or(ControlNet::Pos(Net::ONE));
                let reset_over_enable = t.optional(|t| parse_reset_over_enable_arg(t)).unwrap_or(false);
                let init_value =
                    t.optional(|t| parse_dff_init_value_arg(t)).unwrap_or_else(|| Const::undef(data.len()));
                Cell::Dff(FlipFlop {
                    data,
                    clock,
                    clear,
                    clear_value: clear_value.unwrap_or_else(|| init_value.clone()),
                    reset,
                    reset_value: reset_value.unwrap_or_else(|| init_value.clone()),
                    enable,
                    reset_over_enable,
                    init_value,
                })
            }
            "memory" => {
                parse_space(t);
                parse_keyword_eq_expect(t, "depth")?;
                parse_symbol(t, '#')?;
                let depth = parse_decimal(t)?;
                parse_space(t);
                parse_keyword_eq_expect(t, "width")?;
                parse_symbol(t, '#')?;
                let width = parse_decimal(t)?;
                parse_space(t);
                parse_symbol(t, '{')?;
                parse_space(t);
                parse_symbol(t, '\n')?;
                let mut init_value = Const::EMPTY;
                let mut write_ports = Vec::new();
                let mut read_ports = Vec::new();
                while let Some(()) = t.optional(|t| {
                    parse_space(t);
                    let keyword = parse_keyword(t)?;
                    parse_space(t);
                    match keyword.as_str() {
                        "init" => {
                            init_value.extend(parse_const(t)?);
                        }
                        "write" => {
                            parse_keyword_eq_expect(t, "addr")?;
                            let addr = parse_value_arg(t)?;
                            parse_space(t);
                            parse_keyword_eq_expect(t, "data")?;
                            let data = parse_value_arg(t)?;
                            parse_space(t);
                            let mask = t
                                .optional(|t| {
                                    parse_keyword_eq_expect(t, "mask")?;
                                    parse_value_arg(t)
                                })
                                .unwrap_or_else(|| Value::ones(data.len()));
                            let clock = parse_control_arg(t, "clk")?;
                            write_ports.push(MemoryWritePort { addr, data, mask, clock })
                        }
                        "read" => {
                            parse_keyword_eq_expect(t, "addr")?;
                            let addr = parse_value_arg(t)?;
                            parse_space(t);
                            parse_keyword_eq_expect(t, "width")?;
                            parse_symbol(t, '#')?;
                            let width = parse_decimal(t)?;
                            let flip_flop = t.optional(|t| {
                                let clock = parse_control_arg(t, "clk")?;
                                let (clear, clear_value) = t
                                    .optional(|t| parse_dff_reset_control_net_arg(t, "clr"))
                                    .unwrap_or((ControlNet::Pos(Net::ZERO), None));
                                let (reset, reset_value) = t
                                    .optional(|t| parse_dff_reset_control_net_arg(t, "rst"))
                                    .unwrap_or((ControlNet::Pos(Net::ZERO), None));
                                let enable =
                                    t.optional(|t| parse_control_arg(t, "en")).unwrap_or(ControlNet::Pos(Net::ONE));
                                let reset_over_enable = t.optional(|t| parse_reset_over_enable_arg(t)).unwrap_or(false);
                                let init_value =
                                    t.optional(|t| parse_dff_init_value_arg(t)).unwrap_or_else(|| Const::undef(width));
                                let mut relations = vec![];
                                parse_space(t);
                                parse_symbol(t, '[');
                                while let Some(()) = t.optional(|t| {
                                    parse_space(t);
                                    let keyword = parse_keyword(t)?;
                                    relations.push(match keyword.as_str() {
                                        "undef" => MemoryPortRelation::Undefined,
                                        "rdfirst" => MemoryPortRelation::ReadBeforeWrite,
                                        "trans" => MemoryPortRelation::Transparent,
                                        _ => return None,
                                    });
                                    Some(())
                                }) {}
                                parse_space(t);
                                parse_symbol(t, ']');
                                Some(MemoryReadFlipFlop {
                                    clock,
                                    clear,
                                    clear_value: clear_value.unwrap_or_else(|| init_value.clone()),
                                    reset,
                                    reset_value: reset_value.unwrap_or_else(|| init_value.clone()),
                                    enable,
                                    reset_over_enable,
                                    init_value,
                                    relations,
                                })
                            });
                            read_ports.push(MemoryReadPort { addr, data_len: width, flip_flop })
                        }
                        _ => return None,
                    }
                    parse_space(t);
                    parse_symbol(t, '\n')?;
                    Some(())
                }) {}
                parse_space(t);
                parse_symbol(t, '}')?;
                Cell::Memory(Memory {
                    depth,
                    width,
                    init_value: init_value.concat(Const::undef((depth * width).checked_sub(init_value.len()).unwrap())),
                    write_ports,
                    read_ports,
                })
            }
            "iobuf" => {
                parse_space(t);
                let io = parse_io_value(t)?;
                parse_space(t);
                parse_keyword_eq_expect(t, "o")?;
                let output = parse_value_arg(t)?;
                let enable = parse_control_arg(t, "en")?;
                Cell::IoBuf(IoBuffer { io, output, enable })
            }
            "target" => {
                parse_space(t);
                let instance = parse_instance(t)?;
                let target = t.context().design.target().expect("no target specified");
                let prototype = target.prototype(&instance.kind).expect("no prototype for target cell");
                let mut target_cell = TargetCell::new(instance.kind.clone(), prototype);
                for (name, value) in instance.params {
                    let param = prototype.get_param(&name).expect("unknown parameter");
                    if !param.kind.is_valid(&value) {
                        panic!("invalid value for parameter {name}");
                    }
                    target_cell.params[param.index] = value;
                }
                for (name, value) in instance.inputs {
                    let input = prototype.get_input(&name).expect("unknown input");
                    if value.len() != input.len() {
                        panic!("width mismatch for input {name}");
                    }
                    target_cell.inputs[input.range.clone()].copy_from_slice(&value[..]);
                }
                for (name, value) in instance.ios {
                    let io = prototype.get_io(&name).expect("unknown io");
                    if value.len() != io.len() {
                        panic!("width mismatch for io {name}");
                    }
                    target_cell.ios[io.range.clone()].copy_from_slice(&value[..]);
                }
                if !instance.outputs.is_empty() {
                    panic!("target instance should not have explicit outputs");
                }
                Cell::Target(target_cell)
            }
            "input" => Cell::Input(parse_string_arg(t)?, size),
            "output" => Cell::Output(parse_string_arg(t)?, parse_value_arg(t)?),
            "name" => Cell::Name(parse_string_arg(t)?, parse_value_arg(t)?),
            _ => return None,
        })
    }

    fn parse_instance(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<Instance> {
        let mut instance = Instance {
            kind: parse_string(t)?,
            params: BTreeMap::new(),
            inputs: BTreeMap::new(),
            outputs: BTreeMap::new(),
            ios: BTreeMap::new(),
        };
        parse_space(t);
        parse_symbol(t, '{')?;
        parse_space(t);
        parse_symbol(t, '\n')?;
        while let Some(()) = t.optional(|t| {
            parse_space(t);
            let keyword = parse_keyword(t)?;
            parse_symbol(t, '@')?;
            let name = parse_string(t)?;
            parse_space(t);
            parse_symbol(t, '=')?;
            parse_space(t);
            match keyword.as_str() {
                "io" => {
                    let io_value = parse_io_value(t)?;
                    assert!(instance.ios.insert(name, io_value).is_none(), "duplicate IO name in instance");
                }
                "i" => {
                    let value = parse_value_arg(t)?;
                    assert!(instance.inputs.insert(name, value).is_none(), "duplicate input name in instance");
                }
                "o" => {
                    let start: usize = parse_decimal(t)?;
                    parse_symbol(t, ':')?;
                    let end: usize = parse_decimal(t)?;
                    assert!(
                        instance.outputs.insert(name, start..start + end).is_none(),
                        "duplicate output name in instance"
                    );
                }
                "p" => {
                    let keyword = parse_keyword(t)?;
                    parse_symbol(t, '(')?;
                    parse_space(t);
                    let value = match keyword.as_str() {
                        "const" => ParamValue::Const(parse_const(t)?),
                        "int" => ParamValue::Int(parse_decimal(t)?),
                        "string" => ParamValue::String(parse_string(t)?),
                        "float" => todo!(),
                        _ => return None,
                    };
                    parse_space(t);
                    parse_symbol(t, ')')?;
                    assert!(instance.params.insert(name, value).is_none(), "duplicate parameter name in instance");
                }
                _ => return None,
            }
            parse_space(t);
            parse_symbol(t, '\n')?;
            Some(())
        }) {}
        parse_space(t);
        parse_symbol(t, '}')?;
        Some(instance)
    }

    parse_space(t);
    let (index, size) = parse_cell_index_size(t)?;
    parse_space(t);
    parse_symbol(t, '=')?;
    parse_space(t);
    let cell = one_of!(t;
        parse_builtin(t, size),
        parse_instance(t).map(Cell::Other),
    )?;
    parse_space(t);
    parse_symbol(t, '\n')?;
    Some(t.context_mut().add_cell(index, size, cell))
}

fn parse_line(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> bool {
    if one_of!(t;
        parse_target(t).is_some(),
        parse_io(t).is_some(),
        parse_cell(t).is_some(),
        { parse_space(t); t.token('\n') }
    ) {
        true
    } else {
        false
    }
}

#[derive(Debug)]
pub struct ParseError {
    source: String,
    offset: usize,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "failed to parse near offset {}: {:?}", self.offset, &self.source[self.offset..])
    }
}

impl std::error::Error for ParseError {}

pub fn parse(target: Option<Arc<dyn Target>>, source: &str) -> Result<Design, ParseError> {
    let context = Context::new(target);
    let mut tokens = source.into_tokens().with_context(context);
    while parse_line(&mut tokens) {}
    parse_space(&mut tokens);
    let (mut tokens, context) = tokens.into_parts();
    if !tokens.eof() {
        return Err(ParseError { source: String::from(source), offset: tokens.location().offset() });
    }
    Ok(context.finalize())
}

impl FromStr for Design {
    type Err = crate::ParseError;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        crate::parse(None, source)
    }
}
