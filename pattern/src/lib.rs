use prjunnamed_netlist::Design;

pub trait Pattern<Target> {
    type Capture;

    fn execute(&self, design: &Design, target: &Target) -> Option<Self::Capture>;
}

#[macro_export]
macro_rules! netlist_matches {
    { [ $($rule:tt)* ] $($rest:tt)* } => {
        |design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value| {
            prjunnamed_pattern::netlist_matches! { @TOP@ design value [ $($rule)* ] $($rest)* }
        }
    };
    { let $design:ident; $($rest:tt)* } => {
        |$design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value| {
            prjunnamed_pattern::netlist_matches! { @TOP@ $design value $($rest)* }
        }
    };
    { @TOP@ $design:ident $value:ident $($rest:tt)* } => {
        {
            if $value.len() > 0 {
                use prjunnamed_pattern::Pattern;
                prjunnamed_pattern::netlist_matches! { @RULE@ $design $value $($rest)* }
            } else {
                None
            }
        }
    };
    { @RULE@ $design:ident $value:ident } => { None };
    { @RULE@ $design:ident $value:ident [ $($pat:tt)+ ] $( if $guard:expr )? => $result:expr; $($rest:tt)* } => {
        {
            let pattern = prjunnamed_pattern::netlist_matches!( @NEW@ [ $($pat)+ ] );
            match pattern.execute($design, $value) {
                Some(prjunnamed_pattern::netlist_matches!( @PAT@ [ $($pat)+ ] )) if true $( && $guard )? => {
                    if cfg!(feature = "trace") {
                        eprintln!(">match {}: {}",
                            stringify!([ $($pat)* ] $( if $guard )?),
                            $design.display_value(&*$value)
                        );
                    }
                    Some($result.into())
                }
                _ => prjunnamed_pattern::netlist_matches! { @RULE@ $design $value $($rest)* }
            }
        }
    };
    ( @NEW@ [ $pat:ident $( @ $cap:ident )? $( ( $($exparg:tt)+ ) )+ $( [ $($patarg:tt)+ ] )* ] ) => {
        $pat::new( $( $($exparg)+ ),+ , $( prjunnamed_pattern::netlist_matches!( @NEW@ [ $($patarg)+ ] ) ),*)
    };
    ( @NEW@ [ $pat:ident $( @ $cap:ident )? $( [ $($patarg:tt)+ ] )* ] ) => {
        $pat::new( $( prjunnamed_pattern::netlist_matches!( @NEW@ [ $($patarg)+ ] ) ),*)
    };
    ( @PAT@ [ $pat:ident $( ( $($exparg:tt)+ ) )* $( [ $($patarg:tt)+ ] )* ] ) => {
        (_, $( prjunnamed_pattern::netlist_matches!( @PAT@ [ $($patarg)+ ] ) ),*)
    };
    ( @PAT@ [ $pat:ident @ $cap:ident $( ( $($exparg:tt)+ ) )* $( [ $($patarg:tt)+ ] )* ] ) => {
        ($cap, $( prjunnamed_pattern::netlist_matches!( @PAT@ [ $($patarg)+ ] ) ),*)
    };
}

#[macro_export]
macro_rules! netlist_replace {
    { [ $($rule:tt)* ] $($rest:tt)* } => {
        |design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value| -> bool {
            prjunnamed_pattern::netlist_replace! { @TOP@ design value [ $($rule)* ] $($rest)* }
        }
    };
    { let $design:ident; $($rest:tt)* } => {
        |$design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value| -> bool {
            prjunnamed_pattern::netlist_replace! { @TOP@ $design value $($rest)* }
        }
    };
    { @TOP@ $design:ident $value:ident $($rest:tt)* } => {
        let result: Option<Value> = prjunnamed_pattern::netlist_matches! { @TOP@ $design $value $($rest)* };
        if let Some(replace) = result {
            #[allow(unexpected_cfgs)]
            if cfg!(feature = "trace") {
                eprintln!(">replace => {}",
                    $design.display_value(&prjunnamed_netlist::Value::from(replace.clone()))
                );
            }
            $design.replace_value($value, replace);
            true
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! assert_netlist {
    ($design:expr , $check:expr $( , $( $assertarg:tt)+ )?) => {
        {
            $design.apply();
            let mut matches = $design.iter_cells().all(|cell_ref| {
                if let prjunnamed_netlist::CellRepr::Output(_name, value) = &*cell_ref.repr() {
                    $check(&$design, value).unwrap_or(false)
                } else {
                    true
                }
            });
            if !matches {
                eprintln!("{}", $design);
            }
            assert!(matches $( , $( $assertarg )+ )?);
        }
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
