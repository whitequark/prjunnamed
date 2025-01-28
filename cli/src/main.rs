use std::fs::File;

use prjunnamed_generic::{canonicalize, lower};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = String::new();
    let mut output = String::new();
    {
        let mut parser = argparse::ArgumentParser::new();
        parser.refer(&mut input).add_argument("INPUT", argparse::Store, "Input JSON");
        parser.refer(&mut output).add_argument("OUTPUT", argparse::Store, "Output JSON");
        parser.parse_args_or_exit();
    }

    let mut design_bundle = prjunnamed_yosys_json::import(&mut File::open(input)?)?;

    for (name, design) in design_bundle.iter_mut() {
        print!("; {} (initial)\n{}\n", name, design);

        // prjunnamed_smt2::verify_transformation(design, canonicalize)?;
        canonicalize(design);

        lower(design);

        canonicalize(design);

        print!("; {} (final)\n{}\n", name, design);
    }

    if !output.is_empty() {
        prjunnamed_yosys_json::export(&mut File::create(output)?, design_bundle)?;
    }

    Ok(())
}
