pub trait Pattern {
    type Capture;

    fn execute(&self, design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value) -> Option<Self::Capture>;
}

#[macro_export]
macro_rules! netlist_rules {
    { with($design:ident); [ $($pat:tt)* ] => $run:expr; $($rest:tt)* } => {
        |$design: &prjunnamed_netlist::Design, value: &prjunnamed_netlist::Value| -> bool {
            use prjunnamed_pattern::Pattern;
            if value.len() > 0 {
                netlist_rules! { @RULE@ $design value [ $($pat)* ] => $run; $($rest)* }
            }
            false
        }
    };
    { @RULE@ $design:ident $value:ident } => {};
    { @RULE@ $design:ident $value:ident [ $($pat:tt)* ] $( if $cond:tt )? => $run:expr; $($rest:tt)* } => {
        let pattern = netlist_rules!( @NEW@ [ $($pat)* ] );
        if let Some(netlist_rules!( @PAT@ [ $($pat)* ] )) = pattern.execute($design, $value) {
            if true $( && $cond )? {
                $run;
                return true
            }
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

pub mod generic;
