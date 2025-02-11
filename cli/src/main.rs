use std::{collections::BTreeMap, fs::File, io::Write};

use prjunnamed_netlist::Design;

fn process(design: &mut Design) {
    match design.target() {
        None => {
            prjunnamed_generic::decision(design);
            prjunnamed_generic::canonicalize(design);
            prjunnamed_generic::lower(design);
            prjunnamed_generic::canonicalize(design);
        }
        Some(ref target) => {
            prjunnamed_generic::unname(design);
            target.synthesize(design).expect("synthesis failed")
        }
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    prjunnamed_siliconblue::register();

    let mut input = String::new();
    let mut output = String::new();
    let mut target = None::<String>;
    {
        let mut parser = argparse::ArgumentParser::new();
        parser.refer(&mut target).add_option(&["-t", "--target"], argparse::StoreOption, "Target platform");
        parser.refer(&mut input).add_argument("INPUT", argparse::Store, "Input file");
        parser.refer(&mut output).add_argument("OUTPUT", argparse::Store, "Output file");
        parser.parse_args_or_exit();
    }

    let target = target.map(|name| {
        prjunnamed_netlist::create_target(name.as_str(), BTreeMap::new()).unwrap_or_else(|err| panic!("{}", err))
    });

    if input.ends_with(".uir") {
        let mut design = prjunnamed_netlist::parse(target, &std::fs::read_to_string(input)?)?;
        process(&mut design);
        if output.is_empty() {
            print!("{}", design);
            println!("; cell counts:");
            for (class, amount) in design.statistics() {
                println!("; {:>7} {}", amount, class);
            }
        } else {
            if output.ends_with(".uir") {
                write!(&mut File::create(output)?, "{design}")?;
            } else if output.ends_with(".json") {
                prjunnamed_yosys_json::export(
                    &mut File::create(output)?,
                    BTreeMap::from_iter([("top".to_owned(), design)]),
                )?;
            } else {
                panic!("don't know what to do with output {output:?}")
            }
        }
    } else if input.ends_with(".json") {
        let mut design_bundle = prjunnamed_yosys_json::import(target.clone(), &mut File::open(input)?)?;
        for (_name, design) in design_bundle.iter_mut() {
            process(design);
        }
        if output.ends_with(".json") {
            prjunnamed_yosys_json::export(&mut File::create(output)?, design_bundle)?;
        } else {
            panic!("don't know what to do with output {output:?}")
        }
    } else {
        panic!("don't know what to do with input {input:?}")
    }

    Ok(())
}

fn main() {
    env_logger::init();
    if let Err(error) = run() {
        eprintln!("error: {}", error);
        std::process::exit(1)
    }
}
