use byteorder::{LE, ReadBytesExt, WriteBytesExt};

use crate::instr;

pub const SP: usize = 13;
pub const LR: usize = 14;
pub const PC: usize = 15;
pub const REGS_SIZE: usize = 16;

#[derive(Debug, Default)]
pub struct Cpu {
    regs: [i32; REGS_SIZE],
    memory: Vec<Segment>,
    pub flag_v: bool,
    pub flag_c: bool,
    pub flag_z: bool,
    pub flag_n: bool,
}

#[derive(Debug)]
struct Segment {
    offset: u32,
    buffer: Vec<u8>,
}

impl Cpu {
    pub fn new(firmware: &[u8]) -> Self {
        use std::io::Write;

        let mut cpu = Cpu::default();
        const FIRMWARE_ADDRESS: u32 = 0x08000000;

        cpu.mmap(FIRMWARE_ADDRESS, 256 * 1024); // FIRMWARE
        let written = cpu.mem_mut(FIRMWARE_ADDRESS).write(firmware);
        assert_eq!(written.unwrap(), firmware.len());

        cpu.mmap(0x60000000, 192 * 1024); // RAM
        cpu.mmap(0x20000000, 64 * 1024); // SRAM (+ STACK)
        cpu.mmap(0xE0000000, 16 * 1024); // SYSCALLs

        cpu
    }

    fn mmap(&mut self, offset: u32, length: u32) {
        self.memory.push(Segment {
            offset,
            buffer: vec![0; length as usize],
        });

        self.memory.sort_by_key(|seg| seg.offset)
    }

    pub fn exec(&mut self) {
        loop {
            if instr::exec(self) {
                return;
            }
        }
    }

    pub fn reg(&self, idx: usize) -> i32 {
        self.regs[idx]
    }

    pub fn set_reg(&mut self, idx: usize, value: i32) {
        self.regs[idx] = value;
    }

    pub fn set_nz(&mut self, value: i32) {
        self.flag_n = value < 0;
        self.flag_z = value == 0;
    }

    pub fn set_nzc(&mut self, value: i32, flag_c: bool) {
        self.flag_n = value < 0;
        self.flag_z = value == 0;
        self.flag_c = flag_c;
    }

    pub fn set_nzcv(&mut self, value: i32, flag_c: bool, flag_v: bool) {
        self.flag_n = value < 0;
        self.flag_z = value == 0;
        self.flag_c = flag_c;
        self.flag_v = flag_v;
    }

    pub fn next_pc(&mut self) {
        self.regs[PC as usize] += 2;
    }

    fn mem(&self, offset: u32) -> &[u8] {
        let seg = self.memory.iter()
            .rev()
            .find(|seg| seg.offset <= offset as u32)
            .unwrap();

        let start = (offset as u32 - seg.offset) as usize;

        &seg.buffer[start..]
    }

    fn mem_mut(&mut self, offset: u32) -> &mut [u8] {
        let mut seg = self.memory.iter_mut()
            .rev()
            .find(|seg| seg.offset <= offset as u32)
            .unwrap();

        let start = (offset as u32 - seg.offset) as usize;

        &mut seg.buffer[start..]
    }

    pub fn read_u8(&self, addr: u32) -> u8 {
        self.mem(addr).read_u8().unwrap()
    }

    pub fn read_u16(&self, addr: u32) -> u16 {
        self.mem(addr).read_u16::<LE>().unwrap()
    }

    pub fn read_u32(&self, addr: u32) -> u32 {
        self.mem(addr).read_u32::<LE>().unwrap()
    }

    pub fn read_i8(&self, addr: u32) -> i8 {
        self.mem(addr).read_i8().unwrap()
    }

    pub fn read_i16(&self, addr: u32) -> i16 {
        self.mem(addr).read_i16::<LE>().unwrap()
    }

    pub fn read_i32(&self, addr: u32) -> i32 {
        self.mem(addr).read_i32::<LE>().unwrap()
    }

    pub fn write_u8(&mut self, addr: u32, value: u8) {
        self.mem_mut(addr).write_u8(value).unwrap()
    }

    pub fn write_u16(&mut self, addr: u32, value: u16) {
        self.mem_mut(addr).write_u16::<LE>(value).unwrap()
    }

    pub fn write_u32(&mut self, addr: u32, value: u32) {
        self.mem_mut(addr).write_u32::<LE>(value).unwrap()
    }

    pub fn write_i8(&mut self, addr: u32, value: i8) {
        self.mem_mut(addr).write_i8(value).unwrap()
    }

    pub fn write_i16(&mut self, addr: u32, value: i16) {
        self.mem_mut(addr).write_i16::<LE>(value).unwrap()
    }

    pub fn write_i32(&mut self, addr: u32, value: i32) {
        self.mem_mut(addr).write_i32::<LE>(value).unwrap()
    }
}
