use std::fs::File;

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
        print!("; {} (initial)\n{}", name, design);

        prjunnamed_generic::combine(design);
        print!("; {} (combine 1)\n{}", name, design);

        prjunnamed_generic::lower(design);
        print!("; {} (lower)\n{}", name, design);

        prjunnamed_generic::iob_insert(design);
        print!("; {} (iob_insert)\n{}", name, design);

        prjunnamed_generic::combine(design);
        print!("; {} (combine 2)\n{}", name, design);
    }

    prjunnamed_yosys_json::export(&mut File::create(output)?, design_bundle)?;

    Ok(())
}
