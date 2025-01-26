use prjunnamed_netlist::Design;

pub trait Pattern<Target> {
    type Capture;

    fn execute(&self, design: &Design, target: &Target) -> Option<Self::Capture>;
}

#[macro_export]
macro_rules! netlist_rules {
    { [ $($rule:tt)* ] $($rest:tt)* } => {
        |design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value| -> bool {
            netlist_rules! { @TOP@ design value [ $($rule)* ] $($rest)* }
        }
    };
    { let $design:ident; $($rest:tt)* } => {
        |$design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value| -> bool {
            netlist_rules! { @TOP@ $design value $($rest)* }
        }
    };
    { @TOP@  $design:ident $value:ident $($rest:tt)* } => {
        if $value.len() > 0 {
            use prjunnamed_pattern::Pattern;
            netlist_rules! { @RULE@ $design $value $($rest)* }
        }
        false
    };
    { @RULE@ $design:ident $value:ident } => {};
    { @RULE@ $design:ident $value:ident [ $($pat:tt)* ] $( if $guard:tt )? => $replace:expr; $($rest:tt)* } => {
        let pattern = netlist_rules!( @NEW@ [ $($pat)* ] );
        match pattern.execute($design, $value) {
            Some(netlist_rules!( @PAT@ [ $($pat)* ] )) if true $( && $guard )? => {
                let replace = $replace;
                #[allow(unexpected_cfgs)]
                if cfg!(feature = "trace") {
                    eprintln!(">match {}: {} => {}",
                        stringify!([ $($pat)* ] $( if $guard )?),
                        $design.display_value(&*$value),
                        $design.display_value(&Value::from(replace.clone()))
                    );
                }
                $design.replace_value($value, replace);
                return true
            }
            _ => ()
        }
        netlist_rules! { @RULE@ $design $value $($rest)* }
    };
    ( @NEW@ [ $pat:ident $( @ $cap:ident )? $( [ $($arg:tt)+ ] )* ] ) => {
        $pat::new($( netlist_rules!( @NEW@ [ $($arg)+ ] ) ),*)
    };
    ( @PAT@ [ $pat:ident $( [ $($arg:tt)+ ] )* ] ) => {
        (_, $( netlist_rules!( @PAT@ [ $($arg)+ ] ) ),*)
    };
    ( @PAT@ [ $pat:ident @ $cap:ident $( [ $($arg:tt)+ ] )* ] ) => {
        ($cap, $( netlist_rules!( @PAT@ [ $($arg)+ ] ) ),*)
    };
}

mod traits;
mod simple;
mod bitwise;
mod shift;
mod arithmetic;

pub use traits::NetOrValue;

pub mod patterns {
    pub use crate::simple::*;
    pub use crate::bitwise::*;
    pub use crate::shift::*;
    pub use crate::arithmetic::*;
}
