use std::fs::File;

use prjunnamed_yosys_json::{import, export};
use prjunnamed_pass::combine;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = String::new();
    let mut output = String::new();
    {
        let mut parser = argparse::ArgumentParser::new();
        parser.refer(&mut input)
            .add_argument("INPUT", argparse::Store, "Input JSON");
        parser.refer(&mut output)
            .add_argument("OUTPUT", argparse::Store, "Output JSON");
        parser.parse_args_or_exit();
    }

    let mut design_bundle = import(&mut File::open(input)?)?;

    for design in design_bundle.values_mut() {
        combine(design);
    }

    export(&mut File::create(output)?, design_bundle)?;

    Ok(())
}
