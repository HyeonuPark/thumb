
use byteorder::{LE, ReadBytesExt, WriteBytesExt};

use crate::instr;

pub const PC: usize = 15;
pub const REGS_SIZE: usize = 16;

#[derive(Debug, Default)]
pub struct Cpu {
    regs: [i32; REGS_SIZE],
    memory: Vec<Segment>,
    flag_v: bool,
    flag_c: bool,
    flag_z: bool,
    flag_n: bool,
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
        let written = cpu.mem_mut(FIRMWARE_ADDRESS as i32).write(firmware);
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

    /// Returns `true` if interrupted
    #[inline]
    pub fn exec_once(&mut self) -> bool {
        let pc = self.reg(PC);
        self.set_reg(PC, pc + 2);
        let opcode = self.read_u16(pc);
        instr::exec(self, opcode)
    }

    pub fn exec(&mut self) {
        loop {
            if self.exec_once() {
                return
            }
        }
    }

    pub fn reg(&self, idx: usize) -> i32 {
        self.regs[idx]
    }

    pub fn set_reg(&mut self, idx: usize, value: i32) {
        self.regs[idx] = value;
    }

    fn mem(&self, offset: i32) -> &[u8] {
        let seg = self.memory.iter()
            .rev()
            .find(|seg| seg.offset <= offset as u32)
            .unwrap();

        let start = (offset as u32 - seg.offset) as usize;

        &seg.buffer[start..]
    }

    fn mem_mut(&mut self, offset: i32) -> &mut [u8] {
        let seg = self.memory.iter_mut()
            .rev()
            .find(|seg| seg.offset <= offset as u32)
            .unwrap();

        let start = (offset as u32 - seg.offset) as usize;

        &mut seg.buffer[start..]
    }

    pub fn read_u8(&self, addr: i32) -> u8 {
        self.mem(addr).read_u8().unwrap()
    }

    pub fn read_u16(&self, addr: i32) -> u16 {
        self.mem(addr).read_u16::<LE>().unwrap()
    }

    pub fn read_u32(&self, addr: i32) -> u32 {
        self.mem(addr).read_u32::<LE>().unwrap()
    }

    pub fn read_i8(&self, addr: i32) -> i8 {
        self.mem(addr).read_i8().unwrap()
    }

    pub fn read_i16(&self, addr: i32) -> i16 {
        self.mem(addr).read_i16::<LE>().unwrap()
    }

    pub fn read_i32(&self, addr: i32) -> i32 {
        self.mem(addr).read_i32::<LE>().unwrap()
    }

    pub fn write_u8(&mut self, addr: i32, value: u8) {
        self.mem_mut(addr).write_u8(value).unwrap()
    }

    pub fn write_u16(&mut self, addr: i32, value: u16) {
        self.mem_mut(addr).write_u16::<LE>(value).unwrap()
    }

    pub fn write_u32(&mut self, addr: i32, value: u32) {
        self.mem_mut(addr).write_u32::<LE>(value).unwrap()
    }

    pub fn write_i8(&mut self, addr: i32, value: i8) {
        self.mem_mut(addr).write_i8(value).unwrap()
    }

    pub fn write_i16(&mut self, addr: i32, value: i16) {
        self.mem_mut(addr).write_i16::<LE>(value).unwrap()
    }

    pub fn write_i32(&mut self, addr: i32, value: i32) {
        self.mem_mut(addr).write_i32::<LE>(value).unwrap()
    }
}
