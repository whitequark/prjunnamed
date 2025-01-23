use crate::{CellRepr, Design, IoValue, Net, Value};

#[derive(Debug)]
pub struct Builder {
    design: Design,
}

macro_rules! builder_fn {
    () => {};
    ($func:ident( $($arg:ident : $ty:ty),+ ) => $repr:ident $body:tt; $($rest:tt)*) => {
        pub fn $func(&mut self, $( $arg: $ty ),+) -> Value {
            self.design.add_cell(CellRepr::$repr $body).output()
        }

        builder_fn!{ $($rest)* }
    }
}

impl Builder {
    pub fn new() -> Builder {
        Builder { design: Design::new() }
    }

    pub fn input(&mut self, name: &str, width: usize) -> Value {
        self.design.add_cell(CellRepr::TopInput(name.to_owned(), width)).output()
    }

    pub fn output(&mut self, name: &str, value: Value) {
        self.design.add_cell(CellRepr::TopOutput(name.to_owned(), value));
    }

    pub fn io_value(&mut self, name: &str, width: usize) -> IoValue {
        self.design.add_io(name.to_owned(), width)
    }

    builder_fn!{
        buf(arg: Value) => Buf(arg);
        not(arg: Value) => Not(arg);
        and(arg1: Value, arg2: Value) => And(arg1, arg2);
        or(arg1: Value, arg2: Value) => Or(arg1, arg2);
        xor(arg1: Value, arg2: Value) => Xor(arg1, arg2);
        mux(arg1: Net, arg2: Value, arg3: Value) => Mux(arg1, arg2, arg3);

        add(arg1: Value, arg2: Value) => Add(arg1, arg2);
        sub(arg1: Value, arg2: Value) => Sub(arg1, arg2);
        // TODO: rest of 'em
    }
}
