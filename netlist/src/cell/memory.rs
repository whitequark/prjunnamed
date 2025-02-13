use crate::{Const, ControlNet, Design, FlipFlop, Net, Value};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Memory {
    pub depth: usize,
    pub width: usize,
    pub init_value: Const,
    pub write_ports: Vec<MemoryWritePort>,
    pub read_ports: Vec<MemoryReadPort>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemoryWritePort {
    pub addr: Value,
    pub data: Value,
    pub mask: Value,
    pub clock: ControlNet,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemoryReadPort {
    pub addr: Value,
    pub data_len: usize,
    pub flip_flop: Option<MemoryReadFlipFlop>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemoryReadFlipFlop {
    pub clock: ControlNet,
    pub clear: ControlNet, // async reset
    pub reset: ControlNet, // sync reset
    pub enable: ControlNet,
    pub reset_over_enable: bool,

    pub clear_value: Const,
    pub reset_value: Const,
    pub init_value: Const,

    pub relations: Vec<MemoryPortRelation>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum MemoryPortRelation {
    #[default]
    Undefined,
    ReadBeforeWrite,
    Transparent,
}

impl Memory {
    pub fn output_len(&self) -> usize {
        self.read_ports.iter().map(|port| port.data_len).sum()
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        for write_port in &self.write_ports {
            write_port.visit(&mut f);
        }
        for read_port in &self.read_ports {
            read_port.visit(&mut f);
        }
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        for write_port in &mut self.write_ports {
            write_port.visit_mut(&mut f);
        }
        for read_port in &mut self.read_ports {
            read_port.visit_mut(&mut f);
        }
    }

    pub fn read_port_output_slice(&self, port_index: usize) -> std::ops::Range<usize> {
        let mut start = 0;
        for port in &self.read_ports[..port_index] {
            start += port.data_len;
        }
        let port = &self.read_ports[port_index];
        start..start + port.data_len
    }

    // creates a transparency emulation mux, to be used by both sync-to-async conversion and transparency emulation.
    // the data and mask given must be the same width as the read port.  the result is new data and mask:
    // if the write port is writing to the same address as the read port is reading, the write data will be
    // multiplexed onto the newly-returned data according to the write mask, and the new mask will be an OR of
    // the input mask and the write mask.  otherwise, the returned data and mask are the same as the input.
    // the mask can be None if the caller doesn't need to track it.
    fn transparency_mux(
        &self,
        design: &Design,
        read_port_index: usize,
        write_port_index: usize,
        data: Value,
        mask: Option<Value>,
    ) -> (Value, Option<Value>) {
        let read_port = &self.read_ports[read_port_index];
        let write_port = &self.write_ports[write_port_index];

        // adjust write data/mask to read port width
        let write_wide_log2 = write_port.wide_log2(self);
        let read_wide_log2 = read_port.wide_log2(self);
        let (write_addr, read_addr, write_data, write_mask) = match write_wide_log2.cmp(&read_wide_log2) {
            std::cmp::Ordering::Less => {
                // read wider than write: demux write data/mask using lower write addr bits
                let wide_log2_diff = read_wide_log2 - write_wide_log2;
                let select = write_port.addr.slice(..wide_log2_diff);
                let write_addr = write_port.addr.slice(wide_log2_diff..);
                let write_data =
                    design.add_shl(write_port.data.zext(read_port.data_len), &select, write_port.data.len() as u32);
                let write_mask =
                    design.add_shl(write_port.mask.zext(read_port.data_len), &select, write_port.mask.len() as u32);
                (write_addr, read_port.addr.clone(), write_data, write_mask)
            }
            std::cmp::Ordering::Equal => {
                (write_port.addr.clone(), read_port.addr.clone(), write_port.data.clone(), write_port.mask.clone())
            }
            std::cmp::Ordering::Greater => {
                // write wider than read: select write data/mask slices from wrport using lower read addr bits
                let wide_log2_diff = write_wide_log2 - read_wide_log2;
                let select = read_port.addr.slice(..wide_log2_diff);
                let read_addr = read_port.addr.slice(wide_log2_diff..);
                let write_data = design
                    .add_ushr(&write_port.data, &select, write_port.data.len() as u32)
                    .slice(..read_port.data_len);
                let write_mask = design
                    .add_ushr(&write_port.mask, &select, write_port.mask.len() as u32)
                    .slice(..read_port.data_len);
                (write_port.addr.clone(), read_addr, write_data, write_mask)
            }
        };

        // compare the relevant address bits
        let max_addr_width = std::cmp::max(read_addr.len(), write_addr.len());
        let addr_eq = design.add_eq(read_addr.zext(max_addr_width), write_addr.zext(max_addr_width));

        // perform actual muxing
        let mut new_data = Value::new();
        for ((data_bit, write_data_bit), mask_bit) in data.iter().zip(&write_data).zip(&write_mask) {
            let sel_write = design.add_and1(addr_eq, mask_bit);
            let new_data_bit = design.add_mux1(sel_write, write_data_bit, data_bit);
            new_data.push(new_data_bit);
        }
        let new_mask = mask.map(|mask| design.add_mux(addr_eq, design.add_or(&mask, write_mask), mask));

        (new_data, new_mask)
    }

    pub fn unmap_read_dff(&mut self, design: &Design, port_index: usize, output: &mut Value) {
        let read_port = &mut self.read_ports[port_index];
        let Some(port_flip_flop) = read_port.flip_flop.take() else {
            return;
        };
        let read_port = &self.read_ports[port_index];
        let new_port_output = design.add_void(read_port.data_len);
        let mut data = new_port_output.clone();
        for (write_port_index, relation) in port_flip_flop.relations.into_iter().enumerate() {
            if relation == MemoryPortRelation::Transparent {
                (data, _) = self.transparency_mux(design, port_index, write_port_index, data, None);
            }
        }
        let q = design.add_dff(FlipFlop {
            data,
            clock: port_flip_flop.clock,
            clear: port_flip_flop.clear,
            reset: port_flip_flop.reset,
            enable: port_flip_flop.enable,
            reset_over_enable: port_flip_flop.reset_over_enable,
            clear_value: port_flip_flop.clear_value,
            reset_value: port_flip_flop.reset_value,
            init_value: port_flip_flop.init_value,
        });
        let output_slice = self.read_port_output_slice(port_index);
        design.replace_value(output.slice(output_slice.clone()), q);
        output[output_slice.clone()].copy_from_slice(&new_port_output[..]);
    }

    pub fn unmap_init_reset_transparency(
        &mut self,
        design: &Design,
        port_index: usize,
        include_transparency: bool,
        output: &mut Value,
    ) {
        let read_port = &self.read_ports[port_index];
        let port_flip_flop = read_port.flip_flop.as_ref().unwrap();

        // create transparency data and mask values. data is the value that should override the read data,
        // and mask is the validity mask corresponding to it.
        // if not unmapping transparency, just set them to (X, 0).
        let mut data = Value::undef(read_port.data_len);
        let mut mask = Some(Value::zero(read_port.data_len));
        if include_transparency {
            for (write_port_index, &relation) in port_flip_flop.relations.iter().enumerate() {
                if relation == MemoryPortRelation::Transparent {
                    (data, mask) = self.transparency_mux(design, port_index, write_port_index, data, mask);
                }
            }
        }
        let mask = mask.unwrap();

        // now delay the above by one cycle, and also mix in the unmapped clear/reset/init into it.
        let read_port = &mut self.read_ports[port_index];
        let port_flip_flop = read_port.flip_flop.as_mut().unwrap();
        let data = design.add_dff(FlipFlop {
            data,
            clock: port_flip_flop.clock,
            clear: port_flip_flop.clear,
            reset: port_flip_flop.reset,
            enable: port_flip_flop.enable,
            reset_over_enable: port_flip_flop.reset_over_enable,
            clear_value: std::mem::replace(&mut port_flip_flop.clear_value, Const::undef(read_port.data_len)),
            reset_value: std::mem::replace(&mut port_flip_flop.reset_value, Const::undef(read_port.data_len)),
            init_value: std::mem::replace(&mut port_flip_flop.init_value, Const::undef(read_port.data_len)),
        });
        let mask = design.add_dff(FlipFlop {
            data: mask,
            clock: port_flip_flop.clock,
            clear: port_flip_flop.clear,
            reset: port_flip_flop.reset,
            enable: port_flip_flop.enable,
            reset_over_enable: port_flip_flop.reset_over_enable,
            clear_value: Const::ones(read_port.data_len),
            reset_value: Const::ones(read_port.data_len),
            init_value: Const::ones(read_port.data_len),
        });
        if include_transparency {
            for relation in &mut port_flip_flop.relations {
                if *relation == MemoryPortRelation::Transparent {
                    *relation = MemoryPortRelation::Undefined;
                }
            }
        }
        port_flip_flop.clear = ControlNet::ZERO;
        port_flip_flop.reset = ControlNet::ZERO;

        // perform the actual muxing.
        let new_port_output = design.add_void(read_port.data_len);
        let mut mux = Value::new();
        for ((new_output_bit, data_bit), mask_bit) in new_port_output.iter().zip(&data).zip(&mask) {
            let mux_bit = design.add_mux1(mask_bit, data_bit, new_output_bit);
            mux.push(mux_bit);
        }

        // and do the replacement.
        let output_slice = self.read_port_output_slice(port_index);
        design.replace_value(output.slice(output_slice.clone()), mux);
        output[output_slice.clone()].copy_from_slice(&new_port_output[..]);
    }
}

impl MemoryWritePort {
    pub fn wide_log2(&self, memory: &Memory) -> usize {
        (self.data.len() / memory.width).ilog2() as usize
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        self.addr.visit(&mut f);
        self.data.visit(&mut f);
        self.mask.visit(&mut f);
        self.clock.visit(&mut f);
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        self.addr.visit_mut(&mut f);
        self.data.visit_mut(&mut f);
        self.mask.visit_mut(&mut f);
        self.clock.visit_mut(&mut f);
    }
}

impl MemoryReadPort {
    pub fn asynchronous(addr: impl Into<Value>, data_len: usize) -> Self {
        Self { addr: addr.into(), data_len, flip_flop: None }
    }

    pub fn clocked(addr: impl Into<Value>, data_len: usize, clock: impl Into<ControlNet>) -> Self {
        Self {
            addr: addr.into(),
            data_len,
            flip_flop: Some(MemoryReadFlipFlop {
                clock: clock.into(),
                clear: ControlNet::ZERO,
                reset: ControlNet::ZERO,
                enable: ControlNet::ONE,
                reset_over_enable: false,
                clear_value: Const::undef(data_len),
                reset_value: Const::undef(data_len),
                init_value: Const::undef(data_len),
                relations: vec![],
            }),
        }
    }

    pub fn wide_log2(&self, memory: &Memory) -> usize {
        (self.data_len / memory.width).ilog2() as usize
    }

    pub fn visit(&self, mut f: impl FnMut(Net)) {
        self.addr.visit(&mut f);
        if let Some(ref flip_flop) = self.flip_flop {
            flip_flop.clock.visit(&mut f);
            flip_flop.clear.visit(&mut f);
            flip_flop.reset.visit(&mut f);
            flip_flop.enable.visit(&mut f);
        }
    }

    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Net)) {
        self.addr.visit_mut(&mut f);
        if let Some(ref mut flip_flop) = self.flip_flop {
            flip_flop.clock.visit_mut(&mut f);
            flip_flop.clear.visit_mut(&mut f);
            flip_flop.reset.visit_mut(&mut f);
            flip_flop.enable.visit_mut(&mut f);
        }
    }
}

impl MemoryReadFlipFlop {
    pub fn with_clock(self, clock: impl Into<ControlNet>) -> Self {
        Self { clock: clock.into(), ..self }
    }

    pub fn with_clear(self, clear: impl Into<ControlNet>) -> Self {
        Self { clear: clear.into(), ..self }
    }

    pub fn with_clear_value(self, clear: impl Into<ControlNet>, clear_value: impl Into<Const>) -> Self {
        Self { clear: clear.into(), clear_value: clear_value.into(), ..self }
    }

    pub fn with_reset(self, reset: impl Into<ControlNet>) -> Self {
        Self { reset: reset.into(), reset_over_enable: false, ..self }
    }

    pub fn with_reset_value(self, reset: impl Into<ControlNet>, reset_value: impl Into<Const>) -> Self {
        Self { reset: reset.into(), reset_over_enable: false, reset_value: reset_value.into(), ..self }
    }

    pub fn with_enable(self, enable: impl Into<ControlNet>) -> Self {
        Self { enable: enable.into(), reset_over_enable: true, ..self }
    }

    pub fn with_init(self, value: impl Into<Const>) -> Self {
        let value = value.into();
        Self { clear_value: value.clone(), reset_value: value.clone(), init_value: value, ..self }
    }

    pub fn has_clock(&self) -> bool {
        !self.clock.is_const()
    }

    pub fn has_enable(&self) -> bool {
        !self.enable.is_always(true)
    }

    pub fn has_reset(&self) -> bool {
        !self.reset.is_always(false)
    }

    pub fn has_reset_value(&self) -> bool {
        !self.reset_value.is_undef()
    }

    pub fn has_clear(&self) -> bool {
        !self.clear.is_always(false)
    }

    pub fn has_clear_value(&self) -> bool {
        !self.clear_value.is_undef()
    }

    pub fn has_init_value(&self) -> bool {
        !self.init_value.is_undef()
    }

    pub fn remap_reset_over_enable(&mut self, design: &Design) {
        if self.reset_over_enable {
            return;
        }
        self.reset_over_enable = true;
        if self.reset.is_always(false) || self.enable.is_always(true) {
            return;
        }
        let reset = self.reset.into_pos(design);
        let enable = self.enable.into_pos(design);
        self.reset = ControlNet::Pos(design.add_and(reset, enable).unwrap_net());
    }

    pub fn remap_enable_over_reset(&mut self, design: &Design) {
        if !self.reset_over_enable {
            return;
        }
        self.reset_over_enable = false;
        if self.reset.is_always(false) || self.enable.is_always(true) {
            return;
        }
        let reset = self.reset.into_pos(design);
        let enable = self.enable.into_pos(design);
        self.enable = ControlNet::Pos(design.add_or(reset, enable).unwrap_net());
    }
}
