#![allow(non_snake_case)]
#![allow(unused_variables)] // TODO: remove this!

use crate::cpu::Cpu;

/// Executes given opcode with cpu.
///
/// Returns `true` if interrupted.
pub fn exec(cpu: &mut Cpu, code: u16) -> bool {
    let bits = |size: usize, offset: usize| (code >> offset) & ((1 << size) - 1);
    let bit = |offset: usize| code & (1 << offset) != 0;

    match code >> 13 {
        0b000 => {
            let Rs = bits(3, 3) as usize;
            let Rd = bits(3, 0) as usize;
            let Op = bits(2, 11);

            if Op == 0b11 {
                // Add/Subtract

                let I = bit(10);
                let Op = bit(9);
                let Rn = bits(3, 6);

                // Exec
                cpu.set_reg(Rd, 32);
            } else {
                // Move shifted register

                let PreOffset = bits(5, 6);
                let Offset = if PreOffset != 0 { PreOffset as i32 } else { 32 }; // 1 ~ 32

                match Op {
                    0b00 => {

                    }
                    0b01 => {

                    }
                    0b10 => {

                    }
                    _ => {
                        // unexcepted logic
                    }
                }

                // Exec
            }
        }
        // mv/cmp/add/sub immediate
        0b001 => {
            let Op = bits(2, 11);
            let Rd = bits(3, 8);
            let Offset = bits(8, 0);

            // Exec
        }
        0b010 => {
            if (code >> 12) & 0b1 != 0 {
                let LH = bit(11);
                let BS = bit(10);
                let R0 = bits(3, 6);
                let Rb = bits(3, 3);
                let Rd = bits(3, 0);

                if bit(9) {
                    // Load/store sign-extended byte/halfword
                } else {
                    // Load/store with register offset
                }
            } else if bit(11) {
                // PC-related load

                let Rd = bits(4, 8);
                let Word = bits(8, 0);

            } else if bit(10) {
                // HI register operations/branch exchange

                let Op = bits(2, 8);
                let H1 = bit(7);
                let H2 = bit(6);
                let RsHs = bits(3, 3);
                let RdHd = bits(3, 0);
            } else {
                // ALU operations

                let Op = bits(4, 6);
                let Rs = bits(3, 3);
                let Rd = bits(3, 0);
            }
        }
        // Load/store with immediate offset
        0b011 => {
            let B = bit(12);
            let L = bit(11);
            let Offset = bits(5, 6);
            let Rb = bits(3, 3);
            let Rd = bits(3, 0);
        }
        0b100 => {
            if bit(12) {
                // SP-relative load/store

                let L = bit(11);
                let Rd = bits(3, 8);
                let Word = bits(8, 0);
            } else {
                // Load/store halfword

                let L = bit(11);
                let Offset = bits(5, 6);
                let Rb = bits(3, 3);
                let Rd = bits(3, 0);
            }
        }
        0b101 => {
            if !bit(12) {
                // Load address

                let Sp = bit(11);
                let Rd = bits(3, 8);
                let Word = bits(8, 0);
            } else if bit(10) {
                // Push/pop registers

                let L = bit(11);
                let R = bit(8);
                let Rlist = bits(8, 0);
            } else {
                // Add offset to stack pointer

                let S = bit(7);
                let SWord = bits(7, 0);
            }
        }
        0b110 => {
            // if (code >> 8) & 0b11111 == 0b11111 {
            //     // software interrupt
            //     return true;
            // }

            if !bit(12) {
                // Multiple load/store

                let L = bit(11);
                let Rb = bits(3, 8);
                let Rlist = bits(8, 0);
            } else {
                let Cond = bits(4, 8);

                if Cond == 0b1111 {
                    // Conditional branch

                    let Soffset = bits(8, 0);
                } else {
                    // Software interupt

                    let Soffset = bits(8, 0);
                }
            }
        }
        0b111 => {
            if bit(12) {
                // Long branch with link

                let H = bit(11);
                let Offset = bits(11, 0);
            } else {
                // Unconditional branch

                let Offset = bits(11, 0);
            }
        }
        _ => unreachable!(),
    }

    false
}
