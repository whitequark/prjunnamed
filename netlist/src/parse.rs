use std::{collections::BTreeMap, fmt::Display, ops::Range, str::FromStr};

use yap::{one_of, types::WithContext, IntoTokens, TokenLocation, Tokens};

use crate::{CellRepr, Const, ControlNet, Design, FlipFlop, Instance, IoBuffer, IoNet, IoValue, Net, ParamValue, Value};

#[derive(Debug)]
struct Context {
    design: Design,
    next_cell: usize,
    cell_map: BTreeMap<usize, Value>,        // source cell index -> value
    late_map: BTreeMap<(usize, usize), Net>, // source cell index + net offset -> buffer
}

impl Context {
    fn new() -> Context {
        Context { design: Design::new(), next_cell: 0, cell_map: BTreeMap::new(), late_map: BTreeMap::new() }
    }

    fn add_io(&mut self, name: String, width: usize) -> IoValue {
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

    fn add_cell(&mut self, index: usize, width: usize, repr: CellRepr) -> Value {
        let value = self.design.add_cell(repr);
        assert_eq!(value.len(), width, "cell width should match declaration width");
        assert!(index >= self.next_cell, "cell index should monotonically grow");
        self.next_cell += value.len().max(1);
        self.cell_map.insert(index, value.clone());
        value
    }

    fn get_cell(&mut self, index: usize, offsets: Range<usize>) -> Value {
        if let Some(value) = self.cell_map.get(&index) {
            value.slice(offsets)
        } else {
            let mut nets = vec![];
            for offset in offsets {
                let net = self.late_map.entry((index, offset)).or_insert_with(|| self.design.add_buf(Net::UNDEF)[0]);
                nets.push(*net);
            }
            Value::from(nets)
        }
    }

    fn finalize(self) -> Design {
        for ((index, offset), net) in self.late_map.into_iter() {
            if let Some(output) = self.cell_map.get(&index) {
                if offset < output.len() {
                    let (cell_ref, _offset) = self.design.find_cell(net).unwrap();
                    cell_ref.replace(CellRepr::Buf(output[offset].into()));
                } else {
                    panic!("late cell reference %{}+{} out of bounds for %{}:{}", index, offset, index, output.len());
                }
            } else {
                panic!("unresolved late cell index %{}", index)
            }
        }
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

fn parse_binary(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<usize> {
    usize::from_str_radix(&t.take_while(|c| c.is_digit(2)).collect::<String>(), 2).ok()
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
        if value.len() > 0 {
            Some(value)
        } else {
            None
        }
    })
}

fn parse_keyword(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
    let name: String = t.take_while(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '>')).collect();
    if name.len() == 0 {
        return None;
    }
    Some(name)
}

fn parse_io_name(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
    parse_symbol(t, '#')?;
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
        parse_io_name_offset(t).map(|(name, offset)| t.context().get_io(name)[offset]),
        parse_io_name(t).map(|name| t.context().get_io_with_width(name, 1)[0])
    )
}

fn parse_io_value(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
    one_of!(t;
        parse_io_net(t).map(IoValue::from),
        parse_io_value_concat(t)
    )
}

fn parse_io_value_concat(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
    let mut value = IoValue::EMPTY;
    parse_symbol(t, '{')?;
    let mut parts = t.many(|t| {
        parse_space(t);
        parse_io_net(t)
    });
    for part in parts.as_iter() {
        value = value.concat(part)
    }
    parse_space(t);
    parse_symbol(t, '}')?;
    Some(value)
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
    let mut parts = t.many(|t| {
        parse_space(t);
        parse_value_part(t)
    });
    for part in parts.as_iter() {
        value = value.concat(part)
    }
    parse_space(t);
    parse_symbol(t, '}')?;
    Some(value)
}

fn parse_io(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
    parse_space(t);
    let (name, size) = parse_io_name_size(t)?;
    parse_space(t);
    t.token('\n');
    Some(t.context_mut().add_io(name, size))
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

    fn parse_control_net_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>, name: &str) -> Option<ControlNet> {
        parse_space(t);
        let negated = parse_symbol(t, '!').is_some();
        let keyword = parse_keyword(t)?;
        if keyword != name {
            return None;
        }
        parse_space(t);
        parse_symbol(t, '=')?;
        let net = parse_net_arg(t)?;
        if negated {
            Some(ControlNet::Neg(net))
        } else {
            Some(ControlNet::Pos(net))
        }
    }

    fn parse_int_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<usize> {
        parse_space(t);
        parse_binary(t)
    }

    fn parse_string_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<String> {
        parse_space(t);
        parse_string(t)
    }

    fn parse_io_value_arg(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<IoValue> {
        parse_space(t);
        let keyword = parse_keyword(t)?;
        if keyword != "io" {
            return None;
        }
        parse_space(t);
        parse_symbol(t, '=')?;
        parse_space(t);
        parse_io_value(t)
    }

    fn parse_dff_reset_control_net_arg(
        t: &mut WithContext<impl Tokens<Item = char>, Context>,
        name: &str,
    ) -> Option<(ControlNet, Option<Const>)> {
        parse_control_net_arg(t, name).map(|control_net| {
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
        let keyword = parse_keyword(t)?;
        if keyword != "init" {
            return None;
        }
        parse_space(t);
        parse_symbol(t, '=')?;
        parse_space(t);
        parse_const(t)
    }

    fn parse_builtin(t: &mut WithContext<impl Tokens<Item = char>, Context>, size: usize) -> Option<CellRepr> {
        let name = parse_keyword(t)?;
        Some(match name.as_ref() {
            "buf" => CellRepr::Buf(parse_value_arg(t)?),
            "not" => CellRepr::Not(parse_value_arg(t)?),
            "and" => CellRepr::And(parse_value_arg(t)?, parse_value_arg(t)?),
            "or" => CellRepr::Or(parse_value_arg(t)?, parse_value_arg(t)?),
            "xor" => CellRepr::Xor(parse_value_arg(t)?, parse_value_arg(t)?),
            "mux" => CellRepr::Mux(parse_net_arg(t)?, parse_value_arg(t)?, parse_value_arg(t)?),
            "adc" => CellRepr::Adc(parse_value_arg(t)?, parse_value_arg(t)?, parse_net_arg(t)?),
            "eq" => CellRepr::Eq(parse_value_arg(t)?, parse_value_arg(t)?),
            "ult" => CellRepr::ULt(parse_value_arg(t)?, parse_value_arg(t)?),
            "slt" => CellRepr::SLt(parse_value_arg(t)?, parse_value_arg(t)?),
            "shl" => CellRepr::Shl(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "ushr" => CellRepr::UShr(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "sshr" => CellRepr::SShr(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "xshr" => CellRepr::XShr(parse_value_arg(t)?, parse_value_arg(t)?, parse_int_arg(t)? as u32),
            "mul" => CellRepr::Mul(parse_value_arg(t)?, parse_value_arg(t)?),
            "udiv" => CellRepr::UDiv(parse_value_arg(t)?, parse_value_arg(t)?),
            "umod" => CellRepr::UMod(parse_value_arg(t)?, parse_value_arg(t)?),
            "sdiv_trunc" => CellRepr::SDivTrunc(parse_value_arg(t)?, parse_value_arg(t)?),
            "sdiv_floor" => CellRepr::SDivFloor(parse_value_arg(t)?, parse_value_arg(t)?),
            "smod_trunc" => CellRepr::SModTrunc(parse_value_arg(t)?, parse_value_arg(t)?),
            "smod_floor" => CellRepr::SModFloor(parse_value_arg(t)?, parse_value_arg(t)?),
            "dff" => {
                let data = parse_value_arg(t)?;
                let clock = parse_control_net_arg(t, "clk")?;
                let (clear, clear_value) = t
                    .optional(|t| parse_dff_reset_control_net_arg(t, "clr"))
                    .unwrap_or((ControlNet::Pos(Net::ZERO), None));
                let (reset, reset_value) = t
                    .optional(|t| parse_dff_reset_control_net_arg(t, "rst"))
                    .unwrap_or((ControlNet::Pos(Net::ZERO), None));
                let enable = t.optional(|t| parse_control_net_arg(t, "en")).unwrap_or(ControlNet::Pos(Net::ONE));
                let reset_over_enable = t.optional(|t| parse_reset_over_enable_arg(t)).unwrap_or(false);
                let init_value =
                    t.optional(|t| parse_dff_init_value_arg(t)).unwrap_or_else(|| Const::undef(data.len()));
                CellRepr::Dff(FlipFlop {
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
            "iob" => CellRepr::Iob(IoBuffer {
                output: parse_value_arg(t)?,
                enable: parse_control_net_arg(t, "en")?,
                io: parse_io_value_arg(t)?,
            }),
            "input" => CellRepr::Input(parse_string_arg(t)?, size),
            "output" => CellRepr::Output(parse_string_arg(t)?, parse_value_arg(t)?),
            "name" => CellRepr::Name(parse_string_arg(t)?, parse_value_arg(t)?),
            _ => return None,
        })
    }

    fn parse_instance(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> Option<CellRepr> {
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
        t.token('\n');
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
                },
                "i" => {
                    let value = parse_value_arg(t)?;
                    assert!(instance.inputs.insert(name, value).is_none(), "duplicate input name in instance");
                }
                "o" => {
                    let start: usize = parse_decimal(t)?;
                    parse_space(t);
                    parse_symbol(t, ':')?;
                    parse_space(t);
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
                        _ => return None
                    };
                    parse_space(t);
                    parse_symbol(t, ')')?;
                    assert!(
                        instance.params.insert(name, value).is_none(),
                        "duplicate parameter name in instance"
                    );

                }
                _ => return None,
            }
            parse_space(t);
            t.token('\n');
            Some(())
        }) {}
        parse_space(t);
        parse_symbol(t, '}')?;
        Some(CellRepr::Other(instance))
    }

    parse_space(t);
    let (index, size) = parse_cell_index_size(t)?;
    parse_space(t);
    parse_symbol(t, '=')?;
    parse_space(t);
    let repr = one_of!(t;
        parse_builtin(t, size),
        parse_instance(t),
    )?;
    parse_space(t);
    t.token('\n');
    Some(t.context_mut().add_cell(index, size, repr))
}

fn parse_line(t: &mut WithContext<impl Tokens<Item = char>, Context>) -> bool {
    if one_of!(t;
        parse_io(t).is_some(),
        parse_cell(t).is_some()
    ) {
        t.context_mut().design.apply();
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
        write!(f, "failed to parse near: {:?}", &self.source[self.offset..])
    }
}

impl std::error::Error for ParseError {}

// The unit tests below rely on `buf` cells and pure cells not being removed.
// They could be modified to use a primary output to keep the cells alive but it's probably not worth it.
fn parse_without_compacting(source: &str) -> Result<Design, ParseError> {
    let context = Context::new();
    let mut tokens = source.into_tokens().with_context(context);
    while parse_line(&mut tokens) {}
    let (mut tokens, context) = tokens.into_parts();
    if !tokens.eof() {
        return Err(ParseError { source: String::from(source), offset: tokens.location().offset() });
    }
    Ok(context.finalize())
}

pub fn parse(source: &str) -> Result<Design, ParseError> {
    parse_without_compacting(source).map(|mut design| {
        design.replace_bufs();
        design.compact();
        design
    })
}

#[cfg(test)]
mod test {
    fn onewaytrip(text: &str, expect: &str) {
        let design = super::parse_without_compacting(text).map_err(|err| panic!("{}", err)).unwrap();
        assert_eq!(format!("{}", design), format!("{}", expect))
    }

    fn roundtrip(text: &str) {
        onewaytrip(text, text); // one way both ways
    }

    #[test]
    fn test_const() {
        roundtrip("%0:1 = buf 0\n");
        roundtrip("%0:1 = buf 1\n");
        roundtrip("%0:1 = buf X\n");
        roundtrip("%0:2 = buf 10\n");
        roundtrip("%0:2 = buf 1X\n");
        roundtrip("%0:3 = buf 01X\n");
    }

    #[test]
    fn test_concat() {
        roundtrip("%0:0 = buf {}\n");
        onewaytrip("%0:1 = buf { 0 }\n", "%0:1 = buf 0\n");
        onewaytrip("%0:2 = buf { 0 1 }\n", "%0:2 = buf 10\n");
    }

    #[test]
    fn test_reference() {
        roundtrip("%0:1 = buf 0\n%1:1 = buf %0\n");
        roundtrip("%0:2 = buf 00\n%2:1 = buf %0+0\n");
        roundtrip("%0:2 = buf 00\n%2:1 = buf %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:2 = buf %0:2\n");
        roundtrip("%0:2 = buf 00\n%2:2 = buf { %0+1 %0:1 }\n");
    }

    #[test]
    fn test_escaping() {
        roundtrip("#\"foo bar\":1\n");
        roundtrip("#\"foo\\22\":1\n");
        roundtrip("#\"foo\\7f\":1\n");
    }

    #[test]
    fn test_ios() {
        roundtrip("#\"some\":1\n");
    }

    #[test]
    fn test_cells() {
        roundtrip("%0:1 = buf 0\n%1:1 = buf %0\n");
        roundtrip("%0:2 = buf 00\n%2:1 = and %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = or %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = xor %0+0 %0+1\n");
        roundtrip("%0:3 = buf 000\n%3:1 = mux %0+0 %0+1 %0+2\n");
        roundtrip("%0:3 = buf 000\n%3:2 = adc %0+0 %0+1 %0+2\n");
        roundtrip("%0:2 = buf 00\n%2:1 = eq %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = ult %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = slt %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = shl %0+0 %0+1 1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = ushr %0+0 %0+1 10\n");
        roundtrip("%0:2 = buf 00\n%2:1 = sshr %0+0 %0+1 11\n");
        roundtrip("%0:2 = buf 00\n%2:1 = xshr %0+0 %0+1 100\n");
        roundtrip("%0:2 = buf 00\n%2:1 = mul %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = udiv %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = umod %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = sdiv_trunc %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = sdiv_floor %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = smod_trunc %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = smod_floor %0+0 %0+1\n");
        roundtrip("%0:2 = buf 00\n%2:1 = dff %0+0 clk=%0+1\n");
        roundtrip("#\"purr\":1\n%0:2 = buf 00\n%2:1 = iob %0+0 en=%0+1 io=#\"purr\"\n");
        roundtrip("%0:0 = \"instance\" {\n}\n");
        roundtrip("%0:2 = input \"awa\"\n");
        roundtrip("%0:2 = buf 00\n%2:0 = output \"bite\" %0:2\n");
        roundtrip("%0:2 = buf 00\n%2:0 = name \"meow\" %0:2\n");
    }

    #[test]
    fn test_dffs() {
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1\n");
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1 init=1\n");
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1 clr=%0+2\n");
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1 rst=%0+2\n");
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1 en=%0+2\n");
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1 rst=%0+2 en=%0+3 rst>en\n");
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1 rst=%0+2 en=%0+3 en>rst\n");
        roundtrip("%0:5 = buf 00000\n%5:1 = dff %0+0 clk=%0+1 clr=%0+2 rst=%0+3 en=%0+4 en>rst init=1\n");
    }

    #[test]
    fn test_instances() {
        roundtrip("%0:1 = buf 0\n%1:0 = \"TBUF\" {\n  i@\"EN\"=%0\n}\n");
        roundtrip("%0:2 = \"TBUF\" {\n  o@\"I\"=0:2\n}\n");
        roundtrip("#\"pin\":1\n%0:0 = \"TBUF\" {\n  io@\"PIN\"=#\"pin\"\n}\n");
    }

    #[test]
    fn test_instance_params() {
        roundtrip("%0:0 = \"CONFIG\" {\n  p@\"A\"=const(10X)\n}\n");
        roundtrip("%0:0 = \"CONFIG\" {\n  p@\"A\"=int(15)\n}\n");
        roundtrip("%0:0 = \"CONFIG\" {\n  p@\"A\"=int(-33)\n}\n");
        roundtrip("%0:0 = \"CONFIG\" {\n  p@\"A\"=string(\"x\")\n}\n");
        roundtrip("%0:0 = \"CONFIG\" {\n  p@\"A\"=string(\"x\\7f\")\n}\n");
    }
}
