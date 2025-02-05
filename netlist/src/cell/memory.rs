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

    pub fn unmap_read_dff(&mut self, design: &Design, port_index: usize, output: &mut Value) {
        let read_port = &mut self.read_ports[port_index];
        let Some(port_flip_flop) = read_port.flip_flop.take() else {
            return;
        };
        let new_port_output = design.add_void(read_port.data_len);
        let mut data = new_port_output.clone();
        for (write_port, relation) in self.write_ports.iter().zip(port_flip_flop.relations) {
            if relation == MemoryPortRelation::Transparent {
                // TODO: support wide ports
                assert_eq!(write_port.data.len(), read_port.data_len, "wide ports not currently supported");
                let max_addr_width = std::cmp::max(read_port.addr.len(), write_port.addr.len());
                let addr_eq = design.add_eq(read_port.addr.zext(max_addr_width), write_port.addr.zext(max_addr_width));
                let mut new_data = Value::EMPTY;
                for ((data_bit, write_data_bit), mask_bit) in data.iter().zip(&write_port.data).zip(&write_port.mask) {
                    let sel_write = design.add_and1(addr_eq, mask_bit);
                    let new_data_bit = design.add_mux1(sel_write, write_data_bit, data_bit);
                    new_data.push(new_data_bit);
                }
                data = new_data;
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
