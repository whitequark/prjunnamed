use std::{collections::BTreeMap, fs::File};

use prjunnamed_generic::{canonicalize, lower};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    prjunnamed_siliconblue::register();

    let mut input = String::new();
    let mut output = String::new();
    let mut target = None::<String>;
    {
        let mut parser = argparse::ArgumentParser::new();
        parser.refer(&mut input).add_argument("INPUT", argparse::Store, "Input JSON");
        parser.refer(&mut output).add_argument("OUTPUT", argparse::Store, "Output JSON");
        parser.refer(&mut target).add_option(&["-t", "--target"], argparse::StoreOption, "Target platform");
        parser.parse_args_or_exit();
    }

    let target = target.map(|name| {
        prjunnamed_netlist::create_target(name.as_str(), BTreeMap::new()).unwrap_or_else(|err| panic!("{}", err))
    });

    let mut design_bundle = prjunnamed_yosys_json::import(target.clone(), &mut File::open(input)?)?;

    for (name, design) in design_bundle.iter_mut() {
        print!("; {} (initial)\n{:#}\n", name, design);

        match target {
            Some(ref target) => target.synthesize(design).expect("synthesis failed"),
            None => {
                canonicalize(design);
                lower(design);
                canonicalize(design);
            }
        }

        print!("; {} (final)\n{}\n", name, design);
    }

    if !output.is_empty() {
        prjunnamed_yosys_json::export(&mut File::create(output)?, design_bundle)?;
    }

    Ok(())
}
