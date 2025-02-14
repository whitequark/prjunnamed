//! This library contains various common utilities for writing target-specific memory lowering passes.
//!
//! Target-specific memory lowering passes are organized roughly as follows:
//!
//! - for each memory in the design:
//!   - a list of candidate lowerings is assembled:
//!     - if a lowering mode (ff / lutram / blockram / hugeram) is explicitly selected, only the relevant
//!       target cells types are considered
//!     - for each available type of target cell:
//!       - hard requirements are checked, and the target cell is rejected if they are unmet, eg:
//!         - memories with more write ports than the target cell are rejected
//!         - memories with asynchronous read ports are rejected if not supported by target cell
//!       - a set of candidate "swizzle" transformations is assembled, for rearranging the memory geometry
//!         to match the target cell
//!         - the candidate swizzles are created according to target-specific rules, with some help from
//!           common functions for eg. legalizing write mask granularity
//!       - the best swizzle is selected, according to some metric (such as inserted soft mux depth or number
//!         of used target cells)
//!       - when a memory needs to be split/duplicated because of excessive read port count, each of the
//!         split/duplicated sub-memories will have its own swizzle
//!       - if a swizzle is egregiously bad (uses more resources than the entire FPGA has available), it is
//!         rejected
//!     - if applicable, a "fallback" lowering candidate is inserted into the list of candidates
//!       - no fallback lowering if multiple write port domains present
//!       - lowering to FFs for RAMs (very expensive)
//!       - lowering to LUTs for ROMs (somewhat expensive)
//!   - if no candidates are available, synthesis is aborted with a fatal error
//!   - one of the candidate lowerings is picked, according to some target-specific heuristic
//!     - initial heuristic will simply switch between target cells based on memory depth
//!     - in the future, we will want to take target resource counts into account (moving the depth threshold
//!       to avoid overfilling the FPGA)
//!   - if the "fallback" lowering candidate has been selected, the common lowering code is called to perform it
//!   - otherwise, target cell lowering is performed:
//!     - the memory is split into sub-memories (using common code), as required to satisfy max read port count,
//!       then each sub-memory is processed independently
//!     - various fixup transformations (implemented in common code, but driven by target code) are performed on
//!       the memory to match it with target cell capabilities:
//!       - sync read ports are converted to async if required
//!       - read port enable / clear / reset / initial value are unmapped and emulated if not supported
//!       - transparency is unmapped and emulated if not supported
//!       - read-first relations are emulated if not supported
//!     - the swizzle (computed earlier) is applied to the memory (using common code), aligning its geometry
//!       with the target cell
//!     - the memory is consumed and converted into actual target cells
//!     - any target-specific post-processing (such as merging output pipeline registers) is performed

use prjunnamed_netlist::{Cell, Const, ControlNet, Design, FlipFlop, Memory, MemoryPortRelation, Value};

/// Describes a "swizzle" transformation, used to align memory geometry to target requirements.
///
/// This structure is constructed by the target, with some help from common code.
///
/// The swizzle transformation involves the following steps:
///
/// 1. The data swizzle is applied to the write data, write mask, and read data signals.  This is used
///    to insert dummy data bits to ensure that target cell's write mask granularity requirements are met.
///
/// 2. The address bits selected by `soft_addr_bits_mask` are removed from all ports, and implemented using soft
///    logic.  This has the following effects:
///
///    - memory depth is divided by two (for each removed address bit)
///    - memory width is multiplied by two (for each removed address bit)
///    - for each write port:
///      - if the removed address bit was implicit (as part of a wide port), the port width doesn't change
///      - otherwise, the port width is multiplied by two, and a mux is inserted
///    - for each write port:
///      - if the removed address bit was implicit (as part of a wide port), the port width doesn't change
///      - otherwise, the port width is multiplied by two, and write mask is adjusted with address decoding logic
///
///    This part of the transformation is used to deal with memories that have excessively asymmetric port widths.
///
/// 3. The `wide_log2` of every write port is adjusted up to the factor requested in `write_wide_log2`, by doubling
///    port width and inserting write address decode logic as necessary.  It is an error if the requested factor
///    is smaller than the current one (after applying step #2).
///
///    This is used for funny cases like iCE40 memories, which require using 16-bit write ports to have per-bit
///    write masks.
///
/// 4. The `wide_log2` of every read port is adjusted up to the factor requested in `read_wide_log2`, by doubling
///    port width and inserting muxes as necessary.  It is an error if the requested factor is smaller than the
///    current one (after applying step #2).
///
///    This is used for obscure cases requiring a *minimum* port width asymmetry such as the Xilinx `RAM64X8SW` cell.
///
/// 5. The memory depth is adjusted to be at most `2 ** hard_addr_bits`.  Further, all read and write ports are
///    adjusted to have an address signal that is exactly `hard_addr_bits - port.wide_log2()` bits.
///
///    If the memory has larger depth than this limit, it is split up into `2 ** hard_addr_bits`-deep chunks,
///    the chunks are assembled "side-by-side" (converting depth to width), and appropriate read multiplexers
///    and write address decoders are inserted.
///
/// 6. The memory is cut along its width, into `data_width_unit`-sized chunks, which are returned as individual
///    [`Memory`] structures.  The last chunk is padded with dummy bits.
#[derive(Debug, Clone)]
pub struct MemorySwizzle {
    /// The data swizzle.  In the first step, the data width of the memory is adjusted to the length of this
    /// vector.  Each bit of the new memory width is described by an entry of this vector.  A `Some(idx)` means
    /// that the bit should correspond to the given bit slice in the original memory, while a `None` means
    /// a dummy bit inserted for legalization purposes.
    pub data_swizzle: Vec<Option<usize>>,
    pub soft_addr_bits_mask: u32,
    pub write_wide_log2: Vec<usize>,
    pub read_wide_log2: Vec<usize>,
    pub hard_addr_bits: usize,
    pub data_width_unit: usize,
}

/// An extension trait for `Memory` with assorted memory lowering utility functions.
pub trait MemoryExt {
    /// Returns a new memory, with the same dimensions and write ports as this one, but only the selected
    /// subset of read ports.
    ///
    /// `output` should be the output value of the memory.  This function will slice out the bits corresponding
    /// to the selected read ports, and return them.
    fn extract_read_ports(&self, ports: &[usize], output: &Value) -> (Memory, Value);

    /// Converts a synchronous read port to an asynchronous read port, by effectively extracting a flip-flop.
    /// If transparency relations are involved, soft transparency logic is inserted.
    ///
    /// `output` is the output value of the memory cell.  This function performs a `replace_value` on the bits
    /// corresponding to the converted port, and changes them in-place in the argument to newly-added void nets
    /// that are to be driven by the newly-converted port.  Thus, the original memory cell must be unalived, and
    /// `replace_value` must be called on the new value of `output`, possibly after further lowering.
    ///
    /// If the given read port is already asynchronous, the function will return without doing anything.
    fn unmap_read_dff(&mut self, design: &Design, port_index: usize, output: &mut Value);

    /// Unmaps the following features from a synchronous read port:
    ///
    /// - reset
    /// - clear
    /// - initial value
    /// - if `include_transparency` is true, all `MemoryPortRelation::Transparent` relations
    ///
    /// If none of the above are used on the given port, the function will return without doing anything.
    ///
    /// Note that, if any of the above features is unmapped, all of reset, clear, and initial value can be unmapped
    /// for free (it would actually be more complex to *not* unmap them).  Thus, we do not have granular controls
    /// for them.
    ///
    /// This function must not be called on asynchronous read ports.
    fn unmap_init_reset_transparency(
        &mut self,
        design: &Design,
        port_index: usize,
        include_transparency: bool,
        output: &mut Value,
    );

    /// Emulates all read-before-write relations in the memory.
    ///
    /// This function has strict preconditions:
    ///
    /// - all read ports must be synchronous and have the same clock
    /// - a single write port cannot have both read-before-write and transparent relations
    ///
    /// If there are no read-before-write relations in the memory, this function will return without doing anything.
    ///
    /// The read-before-write relations are emulated by delaying all write ports with read-before-write relations
    /// by half a cycle:  the clock polarity of the relevant write ports is flipped, and flip-flops (clocked by
    /// the original clock) are added on the data, mask, and address inputs.
    fn emulate_read_before_write(&mut self, design: &Design);

    /// Performs a [`MemorySwizzle`] transformation on a memory, and returns a new memory with the corresponding output
    /// that needs to be driven.
    fn swizzle(&self, output: &Value, swizzle: &MemorySwizzle) -> (Memory, Value);
}

// creates a transparency emulation mux, to be used by both sync-to-async conversion and transparency emulation.
// the data and mask given must be the same width as the read port.  the result is new data and mask:
// if the write port is writing to the same address as the read port is reading, the write data will be
// multiplexed onto the newly-returned data according to the write mask, and the new mask will be an OR of
// the input mask and the write mask.  otherwise, the returned data and mask are the same as the input.
// the mask can be None if the caller doesn't need to track it.
fn transparency_mux(
    memory: &Memory,
    design: &Design,
    read_port_index: usize,
    write_port_index: usize,
    data: Value,
    mask: Option<Value>,
) -> (Value, Option<Value>) {
    let read_port = &memory.read_ports[read_port_index];
    let write_port = &memory.write_ports[write_port_index];

    // adjust write data/mask to read port width
    let write_wide_log2 = write_port.wide_log2(memory);
    let read_wide_log2 = read_port.wide_log2(memory);
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
            let write_data =
                design.add_ushr(&write_port.data, &select, write_port.data.len() as u32).slice(..read_port.data_len);
            let write_mask =
                design.add_ushr(&write_port.mask, &select, write_port.mask.len() as u32).slice(..read_port.data_len);
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

impl MemoryExt for Memory {
    fn extract_read_ports(&self, ports: &[usize], output: &Value) -> (Memory, Value) {
        let mut new_memory = Memory {
            depth: self.depth,
            width: self.width,
            init_value: self.init_value.clone(),
            write_ports: self.write_ports.clone(),
            read_ports: vec![],
        };
        let mut new_output = Value::new();
        for &port_index in ports {
            new_memory.read_ports.push(self.read_ports[port_index].clone());
            let output_slice = self.read_port_output_slice(port_index);
            new_output.extend(output.slice(output_slice));
        }
        (new_memory, new_output)
    }

    fn unmap_read_dff(&mut self, design: &Design, port_index: usize, output: &mut Value) {
        let read_port = &mut self.read_ports[port_index];
        let Some(port_flip_flop) = read_port.flip_flop.take() else {
            return;
        };
        let read_port = &self.read_ports[port_index];
        let new_port_output = design.add_void(read_port.data_len);
        let mut data = new_port_output.clone();
        for (write_port_index, relation) in port_flip_flop.relations.into_iter().enumerate() {
            if relation == MemoryPortRelation::Transparent {
                (data, _) = transparency_mux(self, design, port_index, write_port_index, data, None);
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

    fn unmap_init_reset_transparency(
        &mut self,
        design: &Design,
        port_index: usize,
        include_transparency: bool,
        output: &mut Value,
    ) {
        let read_port = &self.read_ports[port_index];
        let port_flip_flop = read_port.flip_flop.as_ref().unwrap();

        let has_init = !port_flip_flop.init_value.is_undef();
        let has_reset = !port_flip_flop.reset.is_always(false);
        let has_clear = !port_flip_flop.clear.is_always(false);

        // create transparency data and mask values. data is the value that should override the read data,
        // and mask is the validity mask corresponding to it.
        // if not unmapping transparency, just set them to (X, 0).
        let mut data = Value::undef(read_port.data_len);
        let mut mask = Some(Value::zero(read_port.data_len));
        let mut has_transparency = false;
        if include_transparency {
            for (write_port_index, &relation) in port_flip_flop.relations.iter().enumerate() {
                if relation == MemoryPortRelation::Transparent {
                    (data, mask) = transparency_mux(self, design, port_index, write_port_index, data, mask);
                    has_transparency = true;
                }
            }
        }
        let mask = mask.unwrap();

        if !has_init && !has_reset && !has_clear && !has_transparency {
            return;
        }

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
            init_value: if has_init { Const::ones(read_port.data_len) } else { Const::undef(read_port.data_len) },
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

    fn emulate_read_before_write(&mut self, design: &Design) {
        let mut rdfirst_write_ports = vec![false; self.write_ports.len()];
        let mut transparent_write_ports = vec![false; self.write_ports.len()];

        for port in &self.read_ports {
            let port_flip_flop = port.flip_flop.as_ref().unwrap();
            assert_eq!(port_flip_flop.clock, self.read_ports[0].flip_flop.as_ref().unwrap().clock);
            for (write_port_index, &relation) in port_flip_flop.relations.iter().enumerate() {
                match relation {
                    MemoryPortRelation::Undefined => (),
                    MemoryPortRelation::ReadBeforeWrite => rdfirst_write_ports[write_port_index] = true,
                    MemoryPortRelation::Transparent => transparent_write_ports[write_port_index] = true,
                }
            }
        }

        let init_undef = self.init_value.is_undef();

        for (port_index, port) in self.write_ports.iter_mut().enumerate() {
            if !rdfirst_write_ports[port_index] {
                continue;
            }
            assert!(!transparent_write_ports[port_index]);
            port.addr = design.add_dff(FlipFlop::new(std::mem::take(&mut port.addr), port.clock));
            port.data = design.add_dff(FlipFlop::new(std::mem::take(&mut port.data), port.clock));
            port.mask =
                design.add_dff(FlipFlop::new(std::mem::take(&mut port.mask), port.clock).with_init(if init_undef {
                    Const::undef(port.data.len())
                } else {
                    Const::zero(port.data.len())
                }));
            port.clock = !port.clock;
        }
    }

    fn swizzle(&self, _output: &Value, _swizzle: &MemorySwizzle) -> (Memory, Value) {
        todo!()
    }
}

// bitblasts all memories in the design to individual FFs.  to be used on small memories only, or you'll quickly run out
// of logic cells.  meant to be used by target code to mop up tiny memories after the large ones have been mapped
// to target-specific cells.
pub fn lower_memory(design: &mut Design) {
    for cell_ref in design.iter_cells() {
        let Cell::Memory(memory) = &*cell_ref.get() else { continue };
        // this pass can only possibly work on memories where all write ports have the same clock.
        // since we're the mapper of last resort, just panic if this is not the case.
        let mut write_clock = None;
        for write_port in &memory.write_ports {
            if write_clock.is_none() {
                write_clock = Some(write_port.clock);
            } else if write_clock != Some(write_port.clock) {
                panic!("trying to lower memory with multiple write clocks");
            }
        }
        let mut memory = memory.clone();
        let mut output = cell_ref.output();
        cell_ref.unalive();
        // convert all read ports to async first.
        for port_index in 0..memory.read_ports.len() {
            memory.unmap_read_dff(design, port_index, &mut output);
        }
        // create the FF cells for all memory rows and implement the write ports.
        // if we have no write ports, just use const drivers.
        let mut rows = vec![];
        for row_index in 0..memory.depth {
            let init = memory.init_value.slice(row_index * memory.width..(row_index + 1) * memory.width);
            if memory.write_ports.is_empty() {
                rows.push(Value::from(init));
            } else {
                let q = design.add_void(memory.width);
                let mut data = q.clone();
                for port in &memory.write_ports {
                    let wide_log2 = port.wide_log2(&memory);
                    let row_addr = row_index >> wide_log2;
                    if port.addr.len() < 32 && row_addr >= (1 << port.addr.len()) {
                        // row not reachable by this port due to short address input
                        continue;
                    }
                    // true iff the write port is currently writing to this row
                    let addr_match = design.add_eq(&port.addr, Const::from_uint(row_addr as u128, port.addr.len()));
                    let port_row = row_index % (1 << wide_log2);
                    // in case of wide ports, extract the data and mask parts that correspond to the current row
                    let port_slice = port_row * memory.width..(port_row + 1) * memory.width;
                    let port_data = port.data.slice(port_slice.clone());
                    let port_mask = port.mask.slice(port_slice);
                    // multiplex our data onto the chain
                    for index in 0..memory.width {
                        let sel = design.add_and1(addr_match, port_mask[index]);
                        data[index] = design.add_mux1(sel, port_data[index], data[index]);
                    }
                }
                design.replace_value(&q, design.add_dff(FlipFlop::new(data, write_clock.unwrap()).with_init(init)));
                rows.push(q);
            }
        }
        // now implement the read ports as multiplexer trees.
        for (port_index, port) in memory.read_ports.iter().enumerate() {
            let wide_log2 = port.wide_log2(&memory);
            // start off by gathering rows into proper wide rows in case of wide read ports.
            let mut port_rows =
                Vec::from_iter(rows.chunks_exact(1 << wide_log2).map(|chunk| Value::from_iter(chunk.iter().flatten())));
            // now create the mux tree bottom-up, halving the size of the port_rows array each time
            for addr_bit in &port.addr {
                port_rows = Vec::from_iter(port_rows.chunks(2).map(|pair| {
                    if pair.len() == 2 {
                        design.add_mux(addr_bit, &pair[1], &pair[0])
                    } else {
                        // we may be reading out-of-bounds. could also use a mux-with-undef here, but there's litle point.
                        pair[0].clone()
                    }
                }))
            }
            let port_output = if port_rows.is_empty() {
                // edge case: if the memory is 0-depth, we end up with empty array; just spit out undef in that case
                assert_eq!(memory.depth, 0);
                Value::undef(port.data_len)
            } else {
                // it is possible we get here with more than 1 entry in the port_rows array.  this happens for read ports
                // with short address inputs that cannot actually address all of the memory. in that case, ignoring this
                // fact and just grabbing 0th entry is the correct thing to do.
                port_rows[0].clone()
            };
            let output_slice = memory.read_port_output_slice(port_index);
            design.replace_value(output.slice(output_slice), port_output);
        }
    }
    design.apply();
}
