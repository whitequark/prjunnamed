use prjunnamed_netlist::{Cell, Const, Design, FlipFlop, Value};

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
            if memory.read_ports[port_index].flip_flop.is_some() {
                memory.unmap_read_dff(design, port_index, &mut output);
            }
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
                    if port.addr.len() < 32 && row_index >= (1 << port.addr.len()) {
                        // row not reachable by this port due to short address input
                        continue;
                    }
                    // true iff the write port is currently writing to this row
                    let addr_match =
                        design.add_eq(&port.addr, Const::from_uint((row_index >> wide_log2) as u128, port.addr.len()));
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
