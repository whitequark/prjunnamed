/// This library covers the Lattice iCE65 and iCE40 FPGA families (acquired with SiliconBlue).
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use prjunnamed_netlist::{
    CellRepr, Const, Design, Instance, Net, ParamValue, Target, TargetCell, TargetImportError, TargetPrototype, Value,
};

#[derive(Debug)]
pub struct SiliconBlueTarget {
    prototypes: BTreeMap<String, TargetPrototype>,
}

impl SiliconBlueTarget {
    pub fn new(options: BTreeMap<String, String>) -> Arc<Self> {
        if !options.is_empty() {
            panic!("SiliconBlue target doesn't take options");
        }
        let mut prototypes = BTreeMap::new();
        prototypes.insert(
            "SB_LUT4".into(),
            TargetPrototype::new_pure()
                .add_param_bits("LUT_INIT", Const::undef(16))
                .add_input("I", Const::undef(4)) // synthetic; vendor uses separate I0-I3 ports
                .add_output("O", 1),
        );
        prototypes.insert(
            "SB_CARRY".into(),
            TargetPrototype::new_pure()
                .add_input("I0", Const::undef(1))
                .add_input("I1", Const::undef(1))
                .add_input("CI", Const::undef(1))
                .add_output("CO", 1),
        );
        prototypes.insert(
            // actually corresponds to SB_DFF* vendor cells
            "SB_DFF".into(),
            TargetPrototype::new_has_state()
                .add_param_bits("RESET_VALUE", Const::undef(1)) // synthetic
                .add_param_bool("IS_RESET_ASYNC", false) // synthetic
                .add_param_bool("IS_C_INVERTED", false) // synthetic
                .add_input("D", Const::undef(1))
                .add_input_invertible("C", Const::undef(1), "IS_C_INVERTED")
                .add_input("E", Const::ones(1))
                .add_input("R", Const::zero(1))
                .add_output("Q", 1),
        );
        prototypes.insert(
            "SB_GB".into(),
            TargetPrototype::new_pure()
                .add_input("I", Const::undef(1)) // synthetic; USER_SIGNAL_TO_GLOBAL_BUFFER
                .add_output("O", 1), // synthetic; GLOBAL_BUFFER_OUTPUT
        );
        prototypes.insert(
            // actually corresponds to several vendor cells:
            // - SB_IO
            // - SB_GB_IO (when IS_GB is set)
            // - SB_IO_DS (when IO_STANDARD is differential)
            // - SB_IO_OD (when IO_STANDARD is OPEN_DRAIN)
            // TODO: SB_IO_I3C
            "SB_IO".into(),
            TargetPrototype::new_has_effects()
                .add_param_bits("PIN_TYPE", Const::zero(6))
                .add_param_bool("PULLUP", false)
                .add_param_bits("NEG_TRIGGER", Const::zero(1))
                .add_param_bool("IS_GB", false) // synthetic
                .add_param_string_enum("IO_STANDARD", &[
                    "SB_LVCMOS",
                    "SB_SSTL2_CLASS_1",
                    "SB_SSTL2_CLASS_2",
                    "SB_SSTL18_FULL",
                    "SB_SSTL18_HALF",
                    "SB_MDDR10",
                    "SB_MDDR8",
                    "SB_MDDR4",
                    "SB_MDDR2",
                    "SB_LVDS_INPUT",
                    "SB_LVDS_OUTPUT",
                    "SB_LVDS_IO",
                    "OPEN_DRAIN", // synthetic; used to mark SB_IO_OD
                ])
                // synthetic for SB_IO_OD cell (it has all of these without underscores for some unhinged reason),
                // except for PACKAGE_PIN_B and GLOBAL_BUFFER_OUTPUT which it lacks
                .add_input("D_OUT_0", Const::undef(1))
                .add_input("D_OUT_1", Const::undef(1))
                .add_input("OUTPUT_ENABLE", Const::zero(1))
                .add_input("CLOCK_ENABLE", Const::ones(1))
                .add_input("INPUT_CLK", Const::undef(1))
                .add_input("OUTPUT_CLK", Const::undef(1))
                .add_input("LATCH_INPUT_ENABLE", Const::undef(1))
                .add_output("D_IN_0", 1)
                .add_output("D_IN_1", 1)
                .add_output("GLOBAL_BUFFER_OUTPUT", 1)
                .add_io("PACKAGE_PIN", 1)
                .add_io("PACKAGE_PIN_B", 1),
        );
        // TODO: iCE65 RAM (or just represent it as this cell with READ_MODE = WRITE_MODE = 0?)
        prototypes.insert(
            "SB_RAM40_4K".into(),
            TargetPrototype::new_has_state()
                .add_param_int_enum("READ_MODE", &[0, 1, 2, 3])
                .add_param_int_enum("WRITE_MODE", &[0, 1, 2, 3])
                .add_param_bits("INIT", Const::undef(4096)) // synthetic; vendor has INIT_0..INIT_F
                .add_param_bool("IS_RCLK_INVERTED", false) // synthetic
                .add_param_bool("IS_WCLK_INVERTED", false) // synthetic
                .add_input_invertible("RCLK", Const::undef(1), "IS_RCLK_INVERTED") // synthetic on *NR cells
                .add_input("RCLKE", Const::undef(1))
                .add_input("RE", Const::undef(1))
                .add_input_invertible("WCLK", Const::undef(1), "IS_WCLK_INVERTED") // synthetic on *NW cells
                .add_input("WCLKE", Const::undef(1))
                .add_input("WE", Const::undef(1))
                .add_input("RADDR", Const::undef(11))
                .add_input("WADDR", Const::undef(11))
                .add_input("WDATA", Const::undef(16))
                .add_input("MASK", Const::undef(16))
                .add_output("RDATA", 16),
        );
        // TODO: iCE65 PLL
        prototypes.insert(
            // actually corresponds to several vendor cells (selected by MODE parameter)
            "SB_PLL40".into(),
            TargetPrototype::new_has_state()
                .add_param_string_enum("MODE", &[
                    "SB_PLL40_CORE",
                    "SB_PLL40_PAD",
                    "SB_PLL40_2_PAD",
                    "SB_PLL40_2F_CORE",
                    "SB_PLL40_2F_PAD",
                ]) // synthetic
                .add_param_string_enum("FEEDBACK_PATH", &["SIMPLE", "DELAY", "PHASE_AND_DELAY", "EXTERNAL"])
                .add_param_string_enum("DELAY_ADJUSTMENT_MODE_FEEDBACK", &["FIXED", "DYNAMIC"])
                .add_param_string_enum("DELAY_ADJUSTMENT_MODE_RELATIVE", &["FIXED", "DYNAMIC"])
                .add_param_bits("SHIFTREG_DIV_MODE", Const::zero(2))
                .add_param_bits("FDA_FEEDBACK", Const::zero(4))
                .add_param_bits("FDA_RELATIVE", Const::zero(4))
                .add_param_string_enum("PLLOUT_SELECT_PORTA", &[
                    "GENCLK",
                    "GENCLK_HALF",
                    "SHIFTREG_0deg",
                    "SHIFTREG_90deg",
                ]) // synthetic for SB_PLL40_CORE, SB_PLL40_PAD
                .add_param_string_enum("PLLOUT_SELECT_PORTB", &[
                    "GENCLK",
                    "GENCLK_HALF",
                    "SHIFTREG_0deg",
                    "SHIFTREG_90deg",
                ])
                .add_param_bits("DIVR", Const::zero(4))
                .add_param_bits("DIVF", Const::zero(7))
                .add_param_bits("DIVQ", Const::zero(3))
                .add_param_bits("FILTER_RANGE", Const::zero(3))
                .add_param_bits("ENABLE_ICEGATE_PORTA", Const::zero(1)) // synthetic for SB_PLL40_CORE, SB_PLL40_PAD
                .add_param_bits("ENABLE_ICEGATE_PORTB", Const::zero(1))
                .add_param_bits("TEST_MODE", Const::zero(1))
                .add_input("REFERENCECLK", Const::undef(1)) // SB_PLL40_*CORE only
                .add_input("EXTFEEDBACK", Const::undef(1))
                .add_input("DYNAMICDELAY", Const::undef(8))
                .add_input("BYPASS", Const::undef(1))
                .add_input("RESETB", Const::undef(1))
                .add_input("LATCHINPUTVALUE", Const::undef(1))
                .add_input("SDI", Const::undef(1))
                .add_input("SCLK", Const::undef(1))
                .add_output("PLLOUTCOREA", 1) // synthetic for SB_PLL40_CORE, SB_PLL40_PAD
                .add_output("PLLOUTGLOBALA", 1) // synthetic for SB_PLL40_CORE, SB_PLL40_PAD
                .add_output("PLLOUTCOREB", 1)
                .add_output("PLLOUTGLOBALB", 1)
                .add_output("LOCK", 1)
                .add_output("SDO", 1)
                .add_io("PACKAGEPIN", 1), // SB_PLL40_*PAD only
        );
        prototypes.insert(
            "SB_WARMBOOT".into(),
            TargetPrototype::new_has_effects()
                .add_input("S0", Const::undef(1))
                .add_input("S1", Const::undef(1))
                .add_input("BOOT", Const::zero(1)),
        );
        prototypes.insert(
            "SB_MAC16".into(),
            TargetPrototype::new_has_state()
                .add_param_bits("NEG_TRIGGER", Const::zero(1))
                .add_param_bits("A_REG", Const::zero(1))
                .add_param_bits("B_REG", Const::zero(1))
                .add_param_bits("C_REG", Const::zero(1))
                .add_param_bits("D_REG", Const::zero(1))
                .add_param_bits("TOP_8x8_MULT_REG", Const::zero(1))
                .add_param_bits("BOT_8x8_MULT_REG", Const::zero(1))
                .add_param_bits("PIPELINE_16x16_MULT_REG1", Const::zero(1))
                .add_param_bits("PIPELINE_16x16_MULT_REG2", Const::zero(1))
                .add_param_bits("TOPOUTPUT_SELECT", Const::zero(2))
                .add_param_bits("BOTOUTPUT_SELECT", Const::zero(2))
                .add_param_bits("TOPADDSUB_LOWERINPUT", Const::zero(2))
                .add_param_bits("BOTADDSUB_LOWERINPUT", Const::zero(2))
                .add_param_bits("TOPADDSUB_UPPERINPUT", Const::zero(1))
                .add_param_bits("BOTADDSUB_UPPERINPUT", Const::zero(1))
                .add_param_bits("TOPADDSUB_CARRYSELECT", Const::zero(2))
                .add_param_bits("BOTADDSUB_CARRYSELECT", Const::zero(2))
                .add_param_bits("MODE_8x8", Const::zero(1))
                .add_param_bits("A_SIGNED", Const::zero(1))
                .add_param_bits("B_SIGNED", Const::zero(1))
                .add_input("A", Const::undef(16))
                .add_input("B", Const::undef(16))
                .add_input("C", Const::undef(16))
                .add_input("D", Const::undef(16))
                .add_input_invertible("CLK", Const::undef(1), "NEG_TRIGGER")
                .add_input("CE", Const::undef(1))
                .add_input("IRSTTOP", Const::undef(1))
                .add_input("IRSTBOT", Const::undef(1))
                .add_input("ORSTTOP", Const::undef(1))
                .add_input("ORSTBOT", Const::undef(1))
                .add_input("AHOLD", Const::undef(1))
                .add_input("BHOLD", Const::undef(1))
                .add_input("CHOLD", Const::undef(1))
                .add_input("DHOLD", Const::undef(1))
                .add_input("OHOLDTOP", Const::undef(1))
                .add_input("OHOLDBOT", Const::undef(1))
                .add_input("OLOADTOP", Const::undef(1))
                .add_input("OLOADBOT", Const::undef(1))
                .add_input("ADDSUBTOP", Const::undef(1))
                .add_input("ADDSUBBOT", Const::undef(1))
                .add_input("CI", Const::undef(1))
                .add_input("ACCUMCI", Const::undef(1))
                .add_input("SIGNEXTIN", Const::undef(1))
                .add_output("O", 32)
                .add_output("CO", 1)
                .add_output("ACCUMCO", 1)
                .add_output("SIGNEXTOUT", 1),
        );
        prototypes.insert(
            "SB_SPRAM256KA".into(),
            TargetPrototype::new_has_state()
                .add_input("ADDRESS", Const::undef(14))
                .add_input("DATAIN", Const::undef(16))
                .add_input("MASKWREN", Const::undef(4))
                .add_input("WREN", Const::undef(1))
                .add_input("CHIPSELECT", Const::undef(1))
                .add_input("CLOCK", Const::undef(1))
                .add_input("STANDBY", Const::undef(1))
                .add_input("SLEEP", Const::undef(1))
                .add_input("POWEROFF", Const::undef(1))
                .add_output("DATAOUT", 16),
        );
        // TODO: SB_I2C, SB_SPI, SB_FILTER_50NS, SB_I2C_FIFO
        // TODO: SB_LSOSC, SB_HSOSC, SB_LFOSC, SB_HFOSC
        // TODO: SB_IR_DRV, SB_RGB_DRV, SB_LED_DRV_CUR, SB_LEDD_IP
        // TODO: SB_BARCODE_DRV, SB_IR400_DRV, SB_IR500_DRV, SB_RGBA_DRV
        // TODO: SB_LEDDA_IP, SB_IR_IP

        Arc::new(SiliconBlueTarget { prototypes })
    }
}

impl Target for SiliconBlueTarget {
    fn name(&self) -> &str {
        "siliconblue"
    }

    fn options(&self) -> BTreeMap<String, String> {
        BTreeMap::new()
    }

    fn prototype(&self, name: &str) -> Option<&TargetPrototype> {
        self.prototypes.get(name)
    }

    fn import(&self, design: &mut Design) -> Result<(), TargetImportError> {
        for cell_ref in design.iter_cells() {
            let CellRepr::Other(instance) = &*cell_ref.repr() else { continue };
            let orig_kind = &instance.kind[..];
            let mut instance = instance.clone();
            match orig_kind {
                "GND" | "VCC" => {
                    for (name, _value) in &instance.params {
                        return Err(TargetImportError::unknown_parameter(cell_ref, name));
                    }
                    for (name, _value) in &instance.inputs {
                        return Err(TargetImportError::unknown_input(cell_ref, name));
                    }
                    for (name, _value) in &instance.ios {
                        return Err(TargetImportError::unknown_io(cell_ref, name));
                    }
                    if !instance.outputs.is_empty() {
                        for (name, range) in &instance.outputs {
                            if name != "Y" {
                                return Err(TargetImportError::unknown_output(cell_ref, name));
                            } else if range.len() != 1 {
                                return Err(TargetImportError::output_size_mismatch(cell_ref, name));
                            }
                        }
                        let value = match orig_kind {
                            "GND" => Value::zero(1),
                            "VCC" => Value::ones(1),
                            _ => unreachable!(),
                        };
                        design.replace_value(cell_ref.output(), value);
                    }
                    cell_ref.unalive();
                    continue;
                }
                "SB_LUT4" => {
                    let mut input = Value::EMPTY;
                    for index in 0..4 {
                        let name = format!("I{index}");
                        if let Some(input_bit) = instance.inputs.remove(&name) {
                            if input_bit.len() != 1 {
                                return Err(TargetImportError::input_size_mismatch(cell_ref, name));
                            }
                            input.extend(input_bit);
                        } else {
                            input.extend([Net::UNDEF]);
                        }
                    }
                    if !input.is_undef() {
                        if instance.inputs.insert("I".into(), input).is_some() {
                            return Err(TargetImportError::unknown_input(cell_ref, "I"));
                        }
                    }
                }
                "SB_DFF" | "SB_DFFR" | "SB_DFFS" | "SB_DFFSR" | "SB_DFFSS" | "SB_DFFE" | "SB_DFFER" | "SB_DFFES"
                | "SB_DFFESR" | "SB_DFFESS" | "SB_DFFN" | "SB_DFFNR" | "SB_DFFNS" | "SB_DFFNSR" | "SB_DFFNSS"
                | "SB_DFFNE" | "SB_DFFNER" | "SB_DFFNES" | "SB_DFFNESR" | "SB_DFFNESS" => {
                    instance.kind = "SB_DFF".into();
                    let mut kind = orig_kind.strip_prefix("SB_DFF").unwrap();
                    if let Some(rest) = kind.strip_prefix('N') {
                        instance.add_param("IS_C_INVERTED", true);
                        kind = rest;
                    }
                    if let Some(rest) = kind.strip_prefix('E') {
                        kind = rest;
                    }
                    match kind {
                        "" => (),
                        "R" => {
                            instance.add_param("RESET_VALUE", Const::zero(1));
                            instance.add_param("IS_RESET_ASYNC", true);
                        }
                        "S" => {
                            instance.rename_input("S", "R");
                            instance.add_param("RESET_VALUE", Const::ones(1));
                            instance.add_param("IS_RESET_ASYNC", true);
                        }
                        "SR" => {
                            instance.add_param("RESET_VALUE", Const::zero(1));
                            instance.add_param("IS_RESET_ASYNC", false);
                        }
                        "SS" => {
                            instance.rename_input("S", "R");
                            instance.add_param("RESET_VALUE", Const::ones(1));
                            instance.add_param("IS_RESET_ASYNC", false);
                        }
                        _ => unreachable!(),
                    }
                }
                "SB_GB" => {
                    instance.rename_input("USER_SIGNAL_TO_GLOBAL_BUFFER", "I");
                    instance.rename_output("GLOBAL_BUFFER_OUTPUT", "O");
                }
                "SB_GB_IO" => {
                    instance.kind = "SB_IO".into();
                    instance.add_param("IS_GB", true);
                }
                "SB_IO_DS" => {
                    instance.kind = "SB_IO".into();
                }
                "SB_IO_OD" => {
                    instance.kind = "SB_IO".into();
                    instance.add_param("IO_STANDARD", "OPEN_DRAIN");
                    instance.rename_input("DOUT0", "D_OUT_0");
                    instance.rename_input("DOUT1", "D_OUT_1");
                    instance.rename_input("OUTPUTENABLE", "OUTPUT_ENABLE");
                    instance.rename_input("INPUTCLK", "INPUT_CLK");
                    instance.rename_input("OUTPUTCLK", "OUTPUT_CLK");
                    instance.rename_input("CLOCKENABLE", "CLOCK_ENABLE");
                    instance.rename_input("LATCHINPUTVALUE", "LATCH_INPUT_VALUE");
                    instance.rename_output("DIN0", "D_IN_0");
                    instance.rename_output("DIN1", "D_IN_1");
                    instance.rename_io("PACKAGEPIN", "PACKAGE_PIN");
                }
                // TODO: lower SB_RAM256x16, SB_RAM512x8, SB_RAM1024x4, SB_RAM2048x2 here.
                //
                // you may think that it is an easy task that you can do when you have spare 30 minutes.
                //
                // you are horribly wrong.
                //
                // these cells fear neither God nor Satan.  you get to figure out the weird mapping of *ADDR bits,
                // and the weird mapping of RDATA bits, and the weird mapping of WDATA bits, and also swizzle
                // the entire INIT parameter.  you will end up cursing whatever gods you believe in for not striking
                // you down with a merciful lightning bolt or perhaps burning out your eyes before you ever gazed
                // upon the SB_RAM40 simulation model.
                //
                // you will also have to figure out how to implement output bit swizzling (and resizing) with our
                // raw_import model which unfortunately is not really fit for the task.
                "SB_RAM40_4K" | "SB_RAM40_4KNR" | "SB_RAM40_4KNW" | "SB_RAM40_4KNRNW" => {
                    let mut kind = orig_kind.strip_prefix("SB_RAM40_4K").unwrap();
                    if let Some(rest) = kind.strip_prefix("NR") {
                        instance.add_param("IS_RCLK_INVERTED", true);
                        instance.rename_input("RCLKN", "RCLK");
                        kind = rest;
                    }
                    if let Some(rest) = kind.strip_prefix("NW") {
                        instance.add_param("IS_WCLK_INVERTED", true);
                        instance.rename_input("WCLKN", "WCLK");
                        kind = rest;
                    }
                    assert!(kind.is_empty());
                    instance.kind = "SB_RAM40_4K".into();
                    let mut init = Const::new();
                    for index in 0..16 {
                        let param_name = format!("INIT_{index:01X}");
                        if let Some(value) = instance.params.remove(&param_name) {
                            let ParamValue::Const(value) = value else {
                                return Err(TargetImportError::parameter_type_mismatch(cell_ref, param_name));
                            };
                            if value.len() != 256 {
                                return Err(TargetImportError::parameter_value_invalid(
                                    cell_ref,
                                    param_name,
                                    ParamValue::Const(value),
                                ));
                            }
                            init.extend(value);
                        } else {
                            init.extend(Const::undef(256));
                        }
                    }
                    instance.add_param("INIT", init);
                }
                "SB_PLL40_CORE" | "SB_PLL40_PAD" | "SB_PLL40_2_PAD" | "SB_PLL40_2F_CORE" | "SB_PLL40_2F_PAD" => {
                    instance.kind = "SB_PLL40".into();
                    instance.add_param("MODE", orig_kind);
                    if matches!(orig_kind, "SB_PLL40_CORE" | "SB_PLL40_PAD") {
                        instance.rename_param("PLLOUT_SELECT", "PLLOUT_SELECT_PORTA");
                        instance.rename_param("ENABLE_ICEGATE", "ENABLE_ICEGATE_PORTA");
                        instance.rename_output("PLLOUTCORE", "PLLOUTCOREA");
                        instance.rename_output("PLLOUTGLOBAL", "PLLOUTGLOBALA");
                    }
                }
                _ => {}
            }
            if let Some(prototype) = self.prototypes.get(&instance.kind) {
                if let Some(value) = instance.params.get_mut("IO_STANDARD") {
                    if let ParamValue::String(value) = value {
                        if value.starts_with("SB_LVCMOS") && value != "SB_LVCMOS" {
                            eprintln!("fix your shit please");
                            *value = "SB_LVCMOS".into();
                        }
                    }
                }

                cell_ref.unalive();
                let value = prototype
                    .instance_to_target_cell(design, &instance)
                    .map_err(|cause| TargetImportError::new(cell_ref, cause))?;
                design.replace_value(cell_ref.output(), value);
            }
        }
        design.compact();
        Ok(())
    }

    fn export(&self, design: &mut Design) {
        fn take_param_unwrap_const(instance: &mut Instance, name: &str) -> Const {
            match instance.params.remove(name) {
                Some(ParamValue::Const(value)) => value,
                _ => unreachable!(),
            }
        }

        fn take_param_unwrap_string(instance: &mut Instance, name: &str) -> String {
            match instance.params.remove(name) {
                Some(ParamValue::String(value)) => value,
                _ => unreachable!(),
            }
        }

        for cell_ref in design.iter_cells() {
            let CellRepr::Target(target_cell) = &*cell_ref.repr() else { continue };
            let prototype = design.target_prototype(target_cell);
            let mut instance = prototype.target_cell_to_instance(target_cell);
            let mut removed_outputs = BTreeSet::new();
            match target_cell.kind.as_str() {
                "SB_LUT4" => {
                    let input = instance.inputs.remove("I").unwrap();
                    for index in 0..4 {
                        instance.inputs.insert(format!("I{index}"), Value::from(input[index]));
                    }
                }
                "SB_DFF" => {
                    if take_param_unwrap_const(&mut instance, "IS_C_INVERTED").is_ones() {
                        instance.kind.push('N');
                    }
                    let enable = instance.inputs.get("E").unwrap();
                    if enable.is_ones() {
                        instance.inputs.remove("E");
                    } else {
                        instance.kind.push('E');
                    }
                    let reset_value = take_param_unwrap_const(&mut instance, "RESET_VALUE");
                    if reset_value.is_undef() {
                        instance.inputs.remove("R");
                    } else {
                        if take_param_unwrap_const(&mut instance, "IS_RESET_ASYNC").is_zero() {
                            instance.kind.push('S');
                        }
                        if reset_value.is_ones() {
                            instance.kind.push('S');
                            instance.rename_input("R", "S");
                        } else {
                            instance.kind.push('R');
                        }
                    }
                }
                "SB_GB" => {
                    instance.rename_input("I", "USER_SIGNAL_TO_GLOBAL_BUFFER");
                    instance.rename_output("O", "GLOBAL_BUFFER_OUTPUT");
                }
                "SB_IO" => {
                    match instance.get_param_string("IO_STANDARD").unwrap() {
                        "SB_LVCMOS" | "SB_SSTL2_CLASS_1" | "SB_SSTL2_CLASS_2" | "SB_SSTL18_FULL" | "SB_SSTL18_HALF"
                        | "SB_MDDR10" | "SB_MDDR8" | "SB_MDDR4" | "SB_MDDR2" => {
                            instance.ios.remove("PACKAGE_PIN_B");
                        }
                        "SB_LVDS_INPUT" | "SB_LVDS_OUTPUT" | "SB_LVDS_IO" => {
                            instance.params.remove("PULLUP");
                            instance.kind = "SB_IO_DS".into();
                        }
                        "OPEN_DRAIN" => {
                            instance.params.remove("PULLUP");
                            instance.params.remove("IO_STANDARD");
                            instance.ios.remove("PACKAGE_PIN_B");
                            instance.rename_input("D_OUT_0", "DOUT0");
                            instance.rename_input("D_OUT_1", "DOUT1");
                            instance.rename_input("OUTPUT_ENABLE", "OUTPUTENABLE");
                            instance.rename_input("INPUT_CLK", "INPUTCLK");
                            instance.rename_input("OUTPUT_CLK", "OUTPUTCLK");
                            instance.rename_input("CLOCK_ENABLE", "CLOCKENABLE");
                            instance.rename_input("LATCH_INPUT_VALUE", "LATCHINPUTVALUE");
                            instance.rename_output("D_IN_0", "DIN0");
                            instance.rename_output("D_IN_1", "DIN1");
                            instance.rename_io("PACKAGE_PIN", "PACKAGEPIN");
                            instance.kind = "SB_IO_OD".into();
                        }
                        _ => unreachable!(),
                    }
                    if take_param_unwrap_const(&mut instance, "IS_GB").is_ones() {
                        assert_eq!(instance.kind, "SB_IO");
                        instance.kind = "SB_GB_IO".into();
                    } else {
                        removed_outputs.insert("GLOBAL_BUFFER_OUTPUT");
                    }
                }
                "SB_RAM40_4K" => {
                    for (param, suffix, name_from, name_to) in
                        [("IS_RCLK_INVERTED", "NR", "RCLK", "RCLKN"), ("IS_WCLK_INVERTED", "NW", "WCLK", "WCLKN")]
                    {
                        if take_param_unwrap_const(&mut instance, param).is_ones() {
                            instance.kind.push_str(suffix);
                            instance.rename_input(name_from, name_to);
                        }
                    }
                    let init_value = take_param_unwrap_const(&mut instance, "INIT");
                    for index in 0..16 {
                        instance.add_param(
                            format!("INIT_{index:01X}"),
                            init_value.slice(index * 0x100..(index + 1) * 0x100),
                        );
                    }
                }
                "SB_PLL40" => {
                    let mode = take_param_unwrap_string(&mut instance, "MODE");
                    if matches!(mode.as_str(), "SB_PLL40_CORE" | "SB_PLL40_PAD") {
                        instance.rename_param("PLLOUT_SELECT_PORTA", "PLLOUT_SELECT");
                        instance.rename_param("ENABLE_ICEGATE_PORTA", "ENABLE_ICEGATE");
                        instance.rename_output("PLLOUTCOREA", "PLLOUTCORE");
                        instance.rename_output("PLLOUTGLOBALA", "PLLOUTGLOBAL");
                        instance.params.remove("PLLOUT_SELECT_PORTB");
                        instance.params.remove("ENABLE_ICEGATE_PORTB");
                        removed_outputs.insert("PLLOUTCOREB");
                        removed_outputs.insert("PLLOUTGLOBALB");
                    } else if mode == "SB_PLL40_2_PAD" {
                        instance.params.remove("PLLOUT_SELECT_PORTA");
                    }
                    if mode.ends_with("_CORE") {
                        instance.ios.remove("PACKAGEPIN");
                    } else {
                        instance.inputs.remove("REFERENCECLK");
                    }
                    instance.kind = mode;
                }
                _ => (),
            }
            // perform output reconstruction surgery on the instance
            let mut new_output_map = vec![];
            let mut index = 0;
            instance.outputs.retain(|name, range| {
                if removed_outputs.contains(&name.as_str()) {
                    false
                } else {
                    let orig_range = range.clone();
                    let instance_range = index..index + range.len();
                    *range = instance_range.clone();
                    index = range.end;
                    new_output_map.push((orig_range, instance_range));
                    true
                }
            });
            let instance_output = design.add_other(instance);
            let mut new_output = Value::undef(cell_ref.output_len());
            for (orig_range, instance_range) in new_output_map {
                new_output[orig_range].copy_from_slice(&instance_output[instance_range]);
            }
            design.replace_value(cell_ref.output(), new_output);
            cell_ref.unalive();
        }
        design.compact();
    }

    fn validate(&self, _design: &Design, _cell: &TargetCell) {
        // TODO:
        // - SB_IO:
        //   - validate PACKAGE_PIN_B floating if IO not differential
        //   - validate PULLUP off if IO differential or open-drain
        // - SB_PLL40: validate ports / parameters unused according to mode
        // - SB_MAC16: validate parameters
    }
}

pub fn register() {
    prjunnamed_netlist::register_target("siliconblue", |options| Ok(SiliconBlueTarget::new(options)));
}
