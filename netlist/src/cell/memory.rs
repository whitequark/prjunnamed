use crate::{Const, ControlNet, Net, Value};

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
}

impl MemoryWritePort {
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
}
