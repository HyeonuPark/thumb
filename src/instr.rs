#![allow(non_snake_case)]

use crate::cpu::{Cpu, SP, LR, PC};

fn carry_add(left: i32, right: i32) -> bool {
    (left as u32).overflowing_add(right as u32).1
}

fn carry_sub(left: i32, right: i32) -> bool {
    (left as u32).overflowing_sub(right as u32).1
}

fn simulated_add(left: i32, right: i32) -> (i32, bool, bool) {
    let (value, overflow) = left.overflowing_add(right);
    let carry = carry_add(left, right);
    (value, carry, overflow)
}

fn simulated_sub(left: i32, right: i32) -> (i32, bool, bool) {
    let (value, overflow) = left.overflowing_sub(right);
    let carry = carry_sub(left, right);
    (value, carry, overflow)
}

/// Executes given opcode with cpu.
///
/// Returns `true` if interrupted.
pub fn exec(cpu: &mut Cpu) -> bool {
    let code = cpu.read_u16(cpu.reg(PC) as u32);
    let bits = |size: usize, offset: usize| ((code >> offset) & ((1 << size) - 1));
    let bit = |offset: usize| code & (1 << offset) != 0;

    match code >> 13 {
        0b000 => {
            let Rs = bits(3, 3);
            let Rd = bits(3, 0);
            let Op = bits(2, 11);

            if Op == 0b11 { // Add/Subtract
                let Offset3 = bits(3, 6);
                let left = cpu.reg(Rs);
                let right = if bit(10) { Offset3 } else { cpu.reg(Offset3) };

                if bit(9) { // ADD Rd, Rs, (#Offset3 | Rn)
                    let (value, carry, overflow) = simulated_add(left, right);

                    cpu.set_reg(Rd, value);
                    cpu.set_nzcv(value, carry, overflow);
                } else { // SUB Rd, Rs, (#Offset3 | Rn)
                    let (value, carry, overflow) = simulated_sub(left, right);

                    cpu.set_reg(Rd, value);
                    cpu.set_nzcv(value, carry, overflow);
                }
            } else { // Move shifted register

                let left = cpu.reg(Rs);
                let Offset5 = bits(5, 6);

                match Op {
                    0b00 => { // LSL Rd, Rs, #Offset5
                        let right = Offset5; // 0 ~ 31
                        let value = left << right;

                        cpu.set_reg(Rd, value);
                        cpu.set_nz(value);
                        if right > 0 {
                            cpu.flag_c = (left << (right - 1)) < 0;
                        }
                    }
                    0b01 => { // LSR Rd, Rs, #Offset5
                        let value;
                        let flag_c;

                        if Offset5 != 0 { // 32
                            value = 0;
                            flag_c = left < 0;
                        } else { // 1 ~ 31: Offset5 + 1
                            let right = Offset5 + 1;
                            value = ((left as u32) >> right) as i32;
                            flag_c = left & (1 << (right - 1)) != 0;
                        };

                        cpu.set_reg(Rd, value);
                        cpu.set_nzc(value, flag_c);
                    }
                    0b10 => { // ASR Rd, Rs, #Offset5
                        let value;
                        let flag_c;

                        if Offset5 != 0 { // 32
                            value = if left > 0 { 0 } else { -1 };
                            flag_c = left < 0;
                        } else { // 1 ~ 31: Offset5 + 1
                            let right = Offset5 + 1;
                            value = left >> right;
                            flag_c = left & (1 << (right - 1)) != 0;
                        };

                        cpu.set_reg(Rd, value);
                        cpu.set_nzc(value, flag_c);
                    }
                    _ => unreachable!()
                }
            }

            cpu.next_pc();
        }

        0b001 => { // move/compare/add/subtract immediate
            let Op = bits(2, 11);
            let Rd = bits(3, 8);
            let right = bits(8, 0);

            match Op {
                0 => { // MOV Rd, #Offset8
                    cpu.set_reg(Rd, right);
                    cpu.set_nz(right);
                }
                1 => { // CMP Rd, #Offset8
                    let left = cpu.reg(Rd);
                    let (value, carry, overflow) = simulated_sub(left, right);

                    cpu.set_nzcv(value, carry, overflow);
                }
                2 => { // ADD Rd, #Offset8
                    let left = cpu.reg(Rd);
                    let (value, carry, overflow) = simulated_add(left, right);

                    cpu.set_reg(Rd, value);
                    cpu.set_nzcv(value, carry, overflow);

                    // let value = cpu.add_nzcv(cpu.reg(Rd), right);
                }
                3 => { // SUB Rd, #Offset8
                    let left = cpu.reg(Rd);
                    let (value, carry, overflow) = simulated_sub(left, right);

                    cpu.set_reg(Rd, value);
                    cpu.set_nzcv(value, carry, overflow);
                }
                _ => unreachable!(),
            }

            cpu.next_pc();
        }
        0b010 => {
            if bit(12) {
                let Ro = bits(3, 6);
                let Rb = bits(3, 3);
                let Rd = bits(3, 0);

                let address = (cpu.reg(Rb) + cpu.reg(Ro)) as u32;

                if bit(9) { // Load/store sign-extended byte/halfword
                    match (bit(10), bit(11)) { // S, H
                        (false, false) => { // STRH Rd, [Rb, Ro]
                            let value = cpu.reg(Rd) as u16;
                            cpu.write_u16(address, value);
                        }
                        (false, true) => { // LDRH Rd, [Rb, Ro]
                            let value = cpu.read_u16(address);
                            cpu.set_reg(Rd, value as i32);
                        }
                        (true, false) => { // LDSB Rd, [Rb, Ro]
                            let value = cpu.read_u8(address);
                            cpu.set_reg(Rd, value as i32);
                        }
                        (true, true) => { // LDSH Rd, [Rb, Ro]
                            let value = cpu.read_u16(address);
                            cpu.set_reg(Rd, value as i32);
                        }
                    }
                } else { // Load/store with register offset
                    match (bit(10), bit(11)) { // L, B
                        (false, false) => { // STR Rd, [Rb, Ro]
                            let value = cpu.reg(Rd);
                            cpu.write_i32(address, value);
                        }
                        (false, true) => { // STRB Rd, [Rb, Ro]
                            let value = cpu.reg(Rd) as u8;
                            cpu.write_u8(address, value);
                        }
                        (true, false) => { // LDR Rd, [Rb, Ro]
                            let value = cpu.read_i32(address);
                            cpu.set_reg(Rd, value);
                        }
                        (true, true) => { // LDRB Rd, [Rb, Ro]
                            let value = cpu.read_u8(address);
                            cpu.set_reg(Rd, value as i32);
                        }
                    }
                }

                cpu.next_pc();
            } else if bit(11) { // PC-related load
                // LDR Rd, [PC, #Imm]

                let Rd = bits(4, 8);
                let Word = bits(8, 0);

                let address = (((Word << 2) as i32) + ((cpu.reg(PC) + 4) & !2)) as u32;
                let value = cpu.read_i32(address);

                cpu.set_reg(Rd, value);
                cpu.next_pc();
            } else if bit(10) { // HI register operations/branch exchange

                let Op = bits(2, 8);
                let H1 = bit(7);
                let H2 = bit(6);
                let Rs = bits(3, 3) + if H2 { 8 } else { 0 };
                let Rd = bits(3, 0) + if H1 { 8 } else { 0 };

                match Op {
                    0 => { // ADD Rd, Hs ; ADD Hd, Rs ; ADD Hd, Hs
                        let left = cpu.reg(Rd);
                        let right = cpu.reg(Rs);
                        let value = left.wrapping_add(right);

                        cpu.set_reg(Rd, value);

                        // what happen on this (i mean logic not assert_eq code)
                        assert_eq!(Rd, PC, "cpu.next_pc();");
                        cpu.next_pc();
                    }
                    1 => { // CMP Rd, Hs ; CMP Hd, Rs ; CMP Hd, Hs
                        let left = cpu.reg(Rd);
                        let right = cpu.reg(Rs);

                        let (value, carry, overflow) = simulated_sub(left, right);

                        cpu.set_nzcv(value, carry, overflow);
                        cpu.next_pc();
                    }
                    2 => { // MOV Rd, Hs ; MOV Hd, Rs ; MOV Hd, Hs
                        let value = cpu.reg(Rs);

                        if Rd == PC {
                            cpu.set_reg(PC, value)
                        } else {
                            cpu.set_reg(Rd, value);
                            cpu.next_pc();
                        }
                    }
                    3 => { // BX Rs ; BX Hs
                        let pc = cpu.reg(Rs);
                        // TODO: return error
                        assert_eq!(pc & 1, 0, "jump addr should be even number");

                        if H1 { // BLX Rs ; BLX Hs
                            // TODO: check PC also even number? (should be always)
                            let lr = (cpu.reg(PC) + 2) | 1;
                            cpu.set_reg(LR, lr);
                            cpu.set_reg(PC, pc);
                        } else { // BX Rs ; BX Hs
                            cpu.set_reg(PC, pc);
                        }
                    }
                    _ => unreachable!(),
                }
            } else { // ALU operations
                let Op = bits(4, 6);
                let Rs = bits(3, 3);
                let Rd = bits(3, 0);

                let left = cpu.reg(Rd);
                let right = cpu.reg(Rs);

                match Op {
                    0 => { // AND Rd, Rs ; Rd:= Rd & Rs
                        let value = left & right;

                        cpu.set_reg(Rd, value);
                        cpu.set_nz(value);
                    }
                    1 => { // EOR Rd, Rs ; Rd:= Rd EOR Rs
                        let value = left ^ right;

                        cpu.set_reg(Rd, value);
                        cpu.set_nz(value);
                    }
                    2 => { // LSL Rd, Rs ; Rd := Rd << Rs
                        let value;
                        let flag_c;

                        if right >= 32 {
                            value = 0;
                            flag_c = right == 32 && left & 1 != 0;
                        } else if right < 0 {
                            value = 0;
                            flag_c = false;
                        } else if right == 0 {
                            value = left;
                            flag_c = cpu.flag_c;
                        } else {
                            value = left << right;
                            flag_c = (left << right - 1) < 0;
                        }

                        cpu.set_reg(Rd, value);
                        cpu.set_nzc(value, flag_c);
                    }
                    3 => { // LSR Rd, Rs ; Rd := Rd >>> Rs
                        let value;
                        let flag_c;

                        if right >= 32 {
                            value = 0;
                            flag_c = right == 32 && left < 0;
                        } else if right < 0 {
                            value = 0;
                            flag_c = false;
                        } else if right == 0 {
                            value = left;
                            flag_c = cpu.flag_c;
                        } else {
                            value = ((left as u32) >> right) as i32;
                            flag_c = ((left as u32) >> (right - 1)) & 1 != 0;
                        }

                        cpu.set_reg(Rd, value);
                        cpu.set_nzc(value, flag_c);
                    }
                    4 => { // ASR Rd, Rs ; Rd := Rd ASR Rs
                        let value;
                        let flag_c;

                        if right < 0 || right >= 32 {
                            value = if left > 0 { 0 } else { -1 };
                            flag_c = value < 0;
                        } else if right == 0 {
                            value = left;
                            flag_c = cpu.flag_c;
                        } else {
                            value = left >> right;
                            flag_c = left & (1 << right - 1) != 0;
                        }

                        cpu.set_reg(Rd, value);
                        cpu.set_nzc(value, flag_c);
                    }
                    5 => { // ADC Rd, Rs ; Rd := Rd + Rs + C-bit
                        let Lvalue = (left as u32 as u64)
                            .wrapping_add(right as u32 as u64)
                            .wrapping_add(cpu.flag_c as u64);

                        let value = Lvalue as i32;

                        cpu.set_reg(Rd, value);
                        cpu.set_nzcv(
                            value,
                            Lvalue != (value as u32 as u64),
                            left > 0 && right > 0 && value < 0 ||
                            left < 0 && right < 0 && value > 0
                        );
                    }
                    6 => { // SBC Rd, Rs ; Rd := Rd - Rs - NOT C-bit
                        let Lvalue = (left as u32 as u64)
                            .wrapping_sub(right as u32 as u64)
                            .wrapping_sub(cpu.flag_c as u64);

                        let value = left
                            .wrapping_sub(right)
                            .wrapping_sub(cpu.flag_c as i32);

                        cpu.set_reg(Rd, value);
                        cpu.set_nzcv(
                            value,
                            Lvalue != (value as u32 as u64),
                            left > 0 && right > 0 && value < 0 ||
                            left < 0 && right < 0 && value > 0
                        );
                    }
                    7 => { // ROR Rd, Rs ; Rd := Rd ROR Rs
                        let right = (right as u32) & 31;
                        let value = left.rotate_right(right);
                        let flag_c = ((left as u32) >> (right - 1)) & 1_u32 != 0;

                        cpu.set_reg(Rd, value);
                        cpu.set_nzc(value, flag_c);
                    }
                    8 => { // TST Rd, Rs ; set condition codes on Rd & Rs
                        let value = left & right;

                        cpu.set_nz(value);
                    }
                    9 => { // NEG Rd, Rs ; Rd = -Rs
                        let Lvalue = (!right as u32 as u64) + 1;
                        let value = Lvalue as i32;

                        cpu.set_reg(Rd, value);
                        cpu.set_nzcv(
                            value,
                            Lvalue > 0xFFFFFFFFu64, // ???
                            right & value < 0 // ???
                        )
                    }
                    10 => { // CMP Rd, Rs ; set condition codes on Rd - Rs
                        let (value, carry, overflow) = simulated_sub(left, right);

                        cpu.set_nzcv(value, carry, overflow);
                    }
                    11 => { // CMN Rd, Rs ; set condition codes on Rd + Rs
                        let (value, carry, overflow) = simulated_add(left, right);

                        cpu.set_nzcv(value, carry, overflow);
                    }
                    12 => { // ORR Rd, Rs ; Rd := Rd OR Rs
                        let value = left | right;

                        cpu.set_reg(Rd, value);
                        cpu.set_nz(value);
                    }
                    13 => { // MUL Rd, Rs ; Rd := Rs * Rd
                        let Svalue = (left as i64) * (right as i64);
                        let value = left * right;

                        assert_eq!(value as i64, Svalue); // GUARD!

                        cpu.set_reg(Rd, value);
                        cpu.set_nz(value);
                        cpu.flag_c |= (value as i64) != Svalue; // FAIL when larget result
                        cpu.flag_v = false; // FAIL when large result
                    }
                    14 => { // BIC Rd, Rs ; Rd := Rd & NOT Rs
                        let value = left | !right;

                        cpu.set_reg(Rd, value);
                        cpu.set_nz(value);
                    }
                    15 => { // MVN Rd, Rs ; Rd := NOT Rs
                        let value = !right;

                        cpu.set_reg(Rd, value);
                        cpu.set_nz(value);
                    }
                    _ => unreachable!(),
                }

                cpu.next_pc();
            }
        }
        0b011 => { // Load/store with immediate offset
            let Offset = bits(5, 6);
            let Rb = bits(3, 3);
            let Rd = bits(3, 0);

            let address = (cpu.reg(Rb) + Offset) as u32;

            match (bit(11), bit(12)) { // L, B
                (false, false) => { // STR Rd, [Rb, #Imm]
                    let value = cpu.reg(Rd);
                    cpu.write_i32(address, value);
                }
                (false, true) => { // STRB Rd, [Rb, #Imm]
                    let value = cpu.reg(Rd) as u8;
                    cpu.write_u8(address, value);
                }
                (true, false) => { // LDR Rd, [Rb, #Imm]
                    let value = cpu.read_i32(address);
                    cpu.set_reg(Rd, value);
                }
                (true, true) => { // LDRB Rd, [Rb, #Imm]
                    let value = cpu.read_u8(address);
                    cpu.set_reg(Rd, value as i32);
                }
            }

            cpu.next_pc();
        }
        0b100 => {
            if bit(12) { // SP-relative load/store
                let Rd = bits(3, 8);
                let Word = bits(8, 0);

                let address = (cpu.reg(SP) + Word) as u32;

                if bit(11) { // LDR Rd, [SP, #Imm]
                    let value = cpu.read_i32(adderss);
                    cpu.set_reg(Rd, value);
                } else { // STR Rd, [SP, #Imm]
                    let value = cpu.reg(Rd);
                    cpu.write_i32(adderss, value);
                }
            } else { // Load/store halfword
                let Offset = bits(5, 6);
                let Rb = bits(3, 3);
                let Rd = bits(3, 0);

                let address = (cpu.reg(Rb) + Offset) as u32;

                if bit(11) { // LDRH Rd, [Rb, #Imm]
                    let value = cpu.read_u16(adderss);
                    cpu.set_reg(Rd, value as i32);
                } else { // STRH Rd, [Rb, #Imm]
                    let value = cpu.reg(Rd) as i16;
                    cpu.write_i16(adderss, value);
                }
            }

            cpu.next_pc();
        }
        0b101 => if !bit(12) { // Load address
            let Rd = bits(3, 8);
            let Word = bits(8, 0);

            let base = if bit(11) { // ADD Rd, SP, #Imm
                cpu.reg(SP)
            } else { // ADD Rd, PC, #Imm
                (cpu.reg(PC) + 4) & !1
            };

            let value = base.wrapping_add(Word as i32);

            cpu.set_reg(Rd, value);
            cpu.next_pc();
        } else {
            if bit(9) {
                if bit(8) {
                    panic!();
                } else {
                    let Op = bits(2, 6);
                    let Rs = bits(3, 3);
                    let Rd = bits(3, 0);

                    let value = cpu.reg(Rs);

                    if bit(11) {
                        let value = match Op {
                            0 => { // SXTH Rd, Rs
                                value as i16 as i32
                            }
                            1 => { // SXTB Rd, Rs
                                value as i8 as i32
                            }
                            2 => { // UXTH Rd, Rs
                                value as u16 as i32
                            }
                            3 => { // UXTB Rd, Rs
                                value as u8 as i32
                            }
                            _ => {
                                unreachable!()
                            }
                        };

                        cpu.set_value(Rd, value);
                    } else {
                        let value = match Op {
                            0 => { // REV Rd, Rs
                                value.swap_bytes()
                            }
                            1 => { // REV16 Rd, Rs
                                panic!();
                            }
                            2 => { // INVALID
                                panic!();
                            }
                            3 => { // REVSH Rd, Rs
                                panic!();
                            }
                            _ => {
                                unreachable!();
                            }
                        };

                        cpu.set_value(Rd, value);
                    }

                    cpu.next_pc();
                }
            } else {
                if bit(10) { // Push/pop registers
                    let R = bit(8);
                    let Rlist = bits(8, 0);

                    if bit(11) { // L
                        for i in 0..8 { // POP { Rlist }
                            if code.imm16 & (1 << i) != 0 {
                                let sp = cpu.reg(SP) as u32;
                                regs[i] = cpu.read_i32(sp);
                                cpu.set_reg(SP, sp as i32 + 4);
                            }
                        }

                        if R { // POP { ..., PC }
                            let sp = cpu.reg(SP) as u32;
                            let pc = cpu.read_i32(sp);

                            cpu.set_reg(SP, sp as i32 + 4);
                            cpu.set_reg(PC, pc);
                        } else {
                            cpu.next_pc();
                        }
                    } else {
                        if R { // PUSH { ..., LR }
                            let sp = cpu.reg(SP) - 4;
                            let lr = cpu.reg(LR);

                            cpu.set_reg(SP, sp);
                            cpu.set_reg(LR, lr);
                        }

                        for i in (0..8).rev() { // PUSH { Rlist }
                            if code.imm16 & (1 << i) != 0 {
                                let sp = cpu.reg(SP) - 4;
                                memory.write_i32(sp as u32, regs[i]);
                                cpu.set_reg(SP, sp);
                            }
                        }
                    }
                } else { // Add offset to stack pointer
                    let SWord = bits(7, 0);

                    let offset = if bit(7) { -SWord } else { SWord }; // S? -word : word
                    let value = cpu.reg(SP) + offset;

                    cpu.set_reg(SP, value);
                    cpu.next_pc();
                }
            }
        },
        0b110 => {
            if !bit(12) { // Multiple load/store

                let L = bit(11);
                let Rb = bits(3, 8);
                let Rlist = bits(8, 0);

                TODO();

                cpu.next_pc();
            } else { // Conditional branch or Software interupt
                let Cond = bits(4, 8);
                let Soffset = bits(8, 0) as i8;

                let jump = match Cond {
                    0 => { // BEQ label
                        cpu.flag_z
                    }
                    1 => { // BNE label
                        !cpu.flag_z
                    }
                    2 => { // BCS label
                        cpu.flag_c
                    }
                    3 => { // BCC label
                        !cpu.flag_c
                    }
                    4 => { // BMI label
                        cpu.flag_n
                    }
                    5 => { // BPL label
                        !cpu.flag_n
                    }
                    6 => { // BVS label
                        cpu.flag_v
                    }
                    7 => { // BVC label
                        !cpu.flag_v
                    }
                    8 => { // BHI label
                        cpu.flag_c && !cpu.flag_z
                    }
                    9 => { // BLS label
                        !cpu.flag_c || cpu.flag_z
                    }
                    10 => { // BGE label
                        cpu.flag_n == cpu.flag_v
                    }
                    11 => { // BLT label
                        cpu.flag_n != cpu.flag_v
                    }
                    12 => { // BGT label
                        !cpu.flag_z && cpu.flag_n == cpu.flag_v
                    }
                    13 => { // BLE label
                        cpu.flag_z || cpu.flag_n != cpu.flag_v
                    }
                    14 => {
                        panic!();
                    }
                    15 => { // SVC
                        TODO("return SOffset");
                        return true; // TODO: return SOffset
                    }
                };

                if jump {
                    let pc = cpu.reg(PC) + 4 + (Soffset << 1) as i32;
                    cpu.set_reg(PC, pc);
                } else {
                    cpu.next_pc();
                }
            }
        }
        0b111 => {
            if bit(12) { // Long branch with link
                let Offset = bits(11, 0);

                if !bit(11) { // !H
                    let lr = cpu.reg(PC) + (Offset << 12);
                    cpu.set_reg(LR, lr);
                } else { // H
                    let mut lr = cpu.reg(LR); // unwrap()?
                    lr += Offset << 1;

                    if lr & (1 << 22) != 0 {
                        lr = !8388607; // magic number!
                    }

                    let pc = cpu.reg(PC) + 4;

                    cpu.set_reg(PC, lr);
                    cpu.set_reg(LR, pc);
                }
            } else { // Unconditional branch
                let Offset = bits(11, 0);

                let value = (
                    (Offset as i32) << 1
                    | (if bit(10) { !((1 << 11) - 1) } else { 0 })
                ) + 4;

                cpu.set_reg(PC, value);
            }
        }
        _ => unreachable!(),
    }

    false
}
