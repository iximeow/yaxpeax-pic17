#[cfg(feature="use-serde")]
#[macro_use] extern crate serde_derive;
#[cfg(feature="use-serde")]
extern crate serde;
#[cfg(feature="use-serde")]
use serde::{Serialize, Deserialize};

extern crate yaxpeax_arch;
extern crate termion;

use yaxpeax_arch::{Arch, ColorSettings, Colorize, Decodable, LengthedInstruction, ShowContextual};

use std::fmt::{Display, Formatter};

use termion::color;

#[derive(Debug, Copy, Clone)]
pub struct Instruction {
    pub opcode: Opcode,
    pub operands: [Operand; 2]
}

#[cfg(feature="use-serde")]
#[derive(Debug, Serialize, Deserialize)]
pub struct PIC17;

#[cfg(not(feature="use-serde"))]
#[derive(Debug)]
pub struct PIC17;

impl Arch for PIC17 {
    type Address = u16;
    type Instruction = Instruction;
    type Operand = Operand;
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.opcode)?;
        match self.operands[0] {
            Operand::Nothing => return Ok(()),
            x @ _ => {
                write!(f, " {}", x)?;
            }
        };
        match self.operands[1] {
            Operand::Nothing => return Ok(()),
            x @ _ => {
                write!(f, ", {}", x)?;
            }
        };
        Ok(())
    }
}

impl LengthedInstruction for Instruction {
    type Unit = <PIC17 as Arch>::Address;
    fn min_size() -> Self::Unit {
        2
    }
    fn len(&self) -> Self::Unit {
        match self.opcode {
            _ => 2
        }
    }
}

impl Instruction {
    pub fn blank() -> Instruction {
        Instruction {
            opcode: Opcode::NOP,
            operands: [Operand::Nothing, Operand::Nothing]
        }
    }

    pub fn is_call(&self) -> bool {
        match self.opcode {
            Opcode::CALL | Opcode::LCALL => { true },
            _ => { false }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Opcode {
    Invalid(u8, u8),
    NOP,
    RETURN,
    SLEEP,
    CLRWDT,
    RETFIE,
    MOVWF,
    SUBWFB,
    SUBWF,
    DECF,
    IORWF,
    ANDWF,
    XORWF,
    ADDWF,
    ADDWFC,
    COMF,
    INCF,
    DECFSZ,
    RRCF,
    RLCF,
    SWAPF,
    INCFSZ,
    RRNCF,
    RLNCF,
    INFSNZ,
    DCFSNZ,
    CLRF,
    SETF,
    NEGW,
    DAW,
    BTG,
    CPFSLT,
    CPFSEQ,
    CPFSGT,
    MULWF,
    TSTFSZ,
    BSF,
    BCF,
    BTFSS,
    BTFSC,
    MOVFP,
    MOVPF,
    MOVLW,
    ADDLW,
    SUBLW,
    IORLW,
    XORLW,
    ANDLW,
    RETLW,
    LCALL,
    MOVLB,
    MOVLR,
    MULLW,
    TLRDL,
    TLRDH,
    TLWTL,
    TLWTH,
    TABLRDL,
    TABLRDLI,
    TABLRDH,
    TABLRDHI,
    TABLWTL,
    TABLWTLI,
    TABLWTH,
    TABLWTHI,
    GOTO,
    CALL
}

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Opcode::Invalid(a, b) => { write!(f, "invalid({:02x}{:02x})", a, b) },
            Opcode::NOP => { write!(f, "nop") },
            Opcode::RETURN => { write!(f, "return") },
            Opcode::SLEEP => { write!(f, "sleep") },
            Opcode::CLRWDT => { write!(f, "clrwdt") },
            Opcode::RETFIE => { write!(f, "retfie") },
            Opcode::MOVFP => { write!(f, "movfp") },
            Opcode::MOVPF => { write!(f, "movpf") },
            Opcode::TLRDL => { write!(f, "tlrdl") },
            Opcode::TLRDH => { write!(f, "tlrdh") },
            Opcode::TLWTL => { write!(f, "tlwtl") },
            Opcode::TLWTH => { write!(f, "tlwth") },
            Opcode::TABLRDL => { write!(f, "tablrdl") },
            Opcode::TABLRDLI => { write!(f, "tablrdli") },
            Opcode::TABLRDH => { write!(f, "tablrdh") },
            Opcode::TABLRDHI => { write!(f, "tablrdhi") },
            Opcode::TABLWTL => { write!(f, "tablwtl") },
            Opcode::TABLWTLI => { write!(f, "tablwtli") },
            Opcode::TABLWTH => { write!(f, "tablwth") },
            Opcode::TABLWTHI => { write!(f, "tablwthi") },
            Opcode::MOVWF => { write!(f, "movwf") },
            Opcode::SUBWFB => { write!(f, "subwfb") },
            Opcode::SUBWF => { write!(f, "subwf") },
            Opcode::DECF => { write!(f, "decf") },
            Opcode::IORWF => { write!(f, "iorwf") },
            Opcode::ANDWF => { write!(f, "andwf") },
            Opcode::XORWF => { write!(f, "xorwf") },
            Opcode::ADDWF => { write!(f, "addwf") },
            Opcode::ADDWFC => { write!(f, "addwfc") },
            Opcode::COMF => { write!(f, "comf") },
            Opcode::INCF => { write!(f, "incf") },
            Opcode::DECFSZ => { write!(f, "decfsz") },
            Opcode::RRCF => { write!(f, "rrcf") },
            Opcode::RLCF => { write!(f, "rlcf") },
            Opcode::SWAPF => { write!(f, "swapf") },
            Opcode::INCFSZ => { write!(f, "incfsz") },
            Opcode::RRNCF => { write!(f, "rrncf") },
            Opcode::RLNCF => { write!(f, "rlncf") },
            Opcode::INFSNZ => { write!(f, "infsnz") },
            Opcode::DCFSNZ => { write!(f, "dcfsnz") },
            Opcode::CLRF => { write!(f, "clrf") },
            Opcode::SETF => { write!(f, "setf") },
            Opcode::NEGW => { write!(f, "negw") },
            Opcode::DAW => { write!(f, "daw") },
            Opcode::BTG => { write!(f, "btg") },
            Opcode::CPFSLT => { write!(f, "cpfslt") },
            Opcode::CPFSEQ => { write!(f, "cpfseq") },
            Opcode::CPFSGT => { write!(f, "cpfsgt") },
            Opcode::MULWF => { write!(f, "mulwf") },
            Opcode::TSTFSZ => { write!(f, "tstfsz") },
            Opcode::BSF => { write!(f, "bsf") },
            Opcode::BCF => { write!(f, "bcf") },
            Opcode::BTFSS => { write!(f, "btfss") },
            Opcode::BTFSC => { write!(f, "btfsc") },
            Opcode::MOVLW => { write!(f, "movlw") },
            Opcode::ADDLW => { write!(f, "addlw") },
            Opcode::SUBLW => { write!(f, "sublw") },
            Opcode::IORLW => { write!(f, "iorlw") },
            Opcode::XORLW => { write!(f, "xorlw") },
            Opcode::ANDLW => { write!(f, "andlw") },
            Opcode::RETLW => { write!(f, "retlw") },
            Opcode::LCALL => { write!(f, "lcall") },
            Opcode::MOVLB => { write!(f, "movlb") },
            Opcode::MOVLR => { write!(f, "movlr") },
            Opcode::MULLW => { write!(f, "mullw") },
            Opcode::GOTO => { write!(f, "goto") },
            Opcode::CALL => { write!(f, "call") }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Operand {
    ImmediateU8(u8),
    ImmediateU32(u32),
    File(u8),
    W,
    Nothing
}

impl Operand {
    pub fn file_value(&self) -> u8 {
        match self {
            Operand::File(f) => *f,
            _ => { unreachable!() }
        }
    }
    pub fn imm8_value(&self) -> u8 {
        match self {
            Operand::ImmediateU8(i) => *i,
            _ => { unreachable!() }
        }
    }
    pub fn imm32_value(&self) -> u32 {
        match self {
            Operand::ImmediateU32(i) => *i,
            _ => { unreachable!() }
        }
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Operand::ImmediateU8(imm) => {
                write!(f, "#0x{:x}", imm)
            },
            Operand::ImmediateU32(imm) => {
                write!(f, "#0x{:x}", imm)
            },
            Operand::W => {
                write!(f, "W")
            },
            Operand::File(file) => {
                write!(f, "[banked 0x{:x}]", file)
            },
            Operand::Nothing => {
                write!(f, "<No Operand>")
            }
        }
    }
}

impl Decodable for Instruction {
    fn decode<T: IntoIterator<Item=u8>>(bytes: T) -> Option<Self> {
        let mut blank = Instruction::blank();
        match blank.decode_into(bytes) {
            Some(_) => Some(blank),
            None => None
        }
    }
    fn decode_into<T: IntoIterator<Item=u8>>(&mut self, bytes: T) -> Option<()> {
        let mut bytes_iter = bytes.into_iter();
        let word: Vec<u8> = bytes_iter.by_ref().take(2).collect();
        if word.len() != 2 {
            return None;
        }

        match word[1] {
            0x00 => {
                self.operands = [Operand::Nothing, Operand::Nothing];
                match word[0] {
                    0x00 => {
                        self.opcode = Opcode::NOP;
                        Some(())
                    },
                    0b00000010 => {
                        self.opcode = Opcode::RETURN;
                        Some(())
                    },
                    0b00000011 => {
                        self.opcode = Opcode::SLEEP;
                        Some(())
                    },
                    0b00000100 => {
                        self.opcode = Opcode::CLRWDT;
                        Some(())
                    },
                    0b00000101 => {
                        self.opcode = Opcode::RETFIE;
                        Some(())
                    },
                    _ => {
                        self.opcode = Opcode::Invalid(word[1], word[0]);
                        None
                    }
                }
            },
            0x01 => {
                self.opcode = Opcode::MOVWF;
                self.operands = [Operand::File(word[0]), Operand::Nothing];
                Some(())
            },
            x if x < 0x30 => {
                // TODO: consume
                let d = x & 0x01 == 0x01;
                self.opcode = [
                    Opcode::SUBWFB,
                    Opcode::SUBWF,
                    Opcode::DECF,
                    Opcode::IORWF,
                    Opcode::ANDWF,
                    Opcode::XORWF,
                    Opcode::ADDWF,
                    Opcode::ADDWFC,
                    Opcode::COMF,
                    Opcode::INCF,
                    Opcode::DECFSZ,
                    Opcode::RRCF,
                    Opcode::RLCF,
                    Opcode::SWAPF,
                    Opcode::INCFSZ,
                    Opcode::RRNCF,
                    Opcode::RLNCF,
                    Opcode::INFSNZ,
                    Opcode::DCFSNZ,
                    Opcode::CLRF,
                    Opcode::SETF,
                    Opcode::NEGW,
                    Opcode::DAW
                ][(x >> 1) as usize - 1];
                self.operands[0] = Operand::File(word[0]);
                self.operands[1] = if d {
                    Operand::File(word[0])
                } else {
                    Operand::W
                };
                Some(())
            },
            x if x < 0x40 => {
                self.operands = [Operand::File(word[0]), Operand::Nothing];
                self.opcode = match word[1] {
                    0x30 => Opcode::CPFSLT,
                    0x31 => Opcode::CPFSEQ,
                    0x32 => Opcode::CPFSGT,
                    0x33 => Opcode::MULWF,
                    0x34 => Opcode::TSTFSZ,
                    0x35 => { Opcode::Invalid(word[1], word[0]); return None },
                    0x36 => { Opcode::Invalid(word[1], word[0]); return None },
                    0x37 => { Opcode::Invalid(word[1], word[0]); return None },
                    0x38 => { self.operands[1] = Operand::ImmediateU8(0); Opcode::BTG },
                    0x39 => { self.operands[1] = Operand::ImmediateU8(1); Opcode::BTG },
                    0x3a => { self.operands[1] = Operand::ImmediateU8(2); Opcode::BTG },
                    0x3b => { self.operands[1] = Operand::ImmediateU8(3); Opcode::BTG },
                    0x3c => { self.operands[1] = Operand::ImmediateU8(4); Opcode::BTG },
                    0x3d => { self.operands[1] = Operand::ImmediateU8(5); Opcode::BTG },
                    0x3e => { self.operands[1] = Operand::ImmediateU8(6); Opcode::BTG },
                    0x3f => { self.operands[1] = Operand::ImmediateU8(7); Opcode::BTG },
                    _ => { unreachable!(); }
                };
                Some(())
            },
            x if x < 0x60 => {
                self.opcode = Opcode::MOVPF;
                self.operands[0] = Operand::File((word[1]) & 0x1f);
                self.operands[1] = Operand::File(word[0]);
                Some(())
            },
            x if x < 0x80 => {
                self.opcode = Opcode::MOVFP;
                self.operands[0] = Operand::File(word[0]);
                self.operands[1] = Operand::File((word[1]) & 0x1f);
                Some(())
            },
            x if x < 0xa0 => {
                self.opcode = [
                    Opcode::BSF,
                    Opcode::BCF,
                    Opcode::BTFSS,
                    Opcode::BTFSC,
                ][(((word[1]) >> 3) & 0x3) as usize];
                self.operands[0] = Operand::File(word[0]);
                self.operands[1] = Operand::ImmediateU8((word[1]) & 0x7);
                Some(())
            },
            x if x < 0xb0 => {
                self.opcode = [
                    Opcode::TLRDL,
                    Opcode::TLRDL,
                    Opcode::TLRDH,
                    Opcode::TLRDH,
                    Opcode::TLWTL,
                    Opcode::TLWTL,
                    Opcode::TLWTH,
                    Opcode::TLWTH,
                    Opcode::TABLRDL,
                    Opcode::TABLRDLI,
                    Opcode::TABLRDH,
                    Opcode::TABLRDHI,
                    Opcode::TABLWTL,
                    Opcode::TABLWTLI,
                    Opcode::TABLWTH,
                    Opcode::TABLWTHI
                ][(x & 0x0f) as usize];
                self.operands = [Operand::File(word[0]), Operand::Nothing];
                Some(())
            },
            x if x < 0xc0 => {
                self.opcode = [
                    Opcode::MOVLW,
                    Opcode::ADDLW,
                    Opcode::SUBLW,
                    Opcode::IORLW,
                    Opcode::XORLW,
                    Opcode::ANDLW,
                    Opcode::RETLW,
                    Opcode::LCALL,
                    Opcode::MOVLB, // BSR only gets low four...
                    Opcode::Invalid(word[1], word[0]),
                    Opcode::MOVLR, // These are weird ones. The Bank Select
                    Opcode::MOVLR, // Register only gets the high four bits.
                    Opcode::MULLW,
                    Opcode::Invalid(word[1], word[0]),
                    Opcode::Invalid(word[1], word[0]),
                    Opcode::Invalid(word[1], word[0])
                ][((word[1]) & 0x0f) as usize];
                self.operands = [Operand::ImmediateU8(word[0]), Operand::Nothing];
                Some(())
            },
            x if x < 0xe0 => {
                self.opcode = Opcode::GOTO;
                self.operands = [Operand::ImmediateU32(word[0] as u32 | (((word[1] as u32) & 0x1f) << 8)), Operand::Nothing];
                Some(())
            },
            _ => {
                self.opcode = Opcode::CALL;
                self.operands = [Operand::ImmediateU32(word[0] as u32 | (((word[1] as u32) & 0x1f) << 8)), Operand::Nothing];
                Some(())
            }
        }
    }
}

pub fn opcode_color(opcode: Opcode) -> &'static color::Fg<&'static color::Color> {
    match opcode {
        Opcode::Invalid(_, _) => &color::Fg(&color::Red),
        Opcode::NOP => &color::Fg(&color::Blue),
        Opcode::CPFSLT |
        Opcode::CPFSEQ |
        Opcode::CPFSGT |
        Opcode::TSTFSZ |
        Opcode::BTFSS |
        Opcode::BTFSC |
        Opcode::RETLW |
        Opcode::LCALL |
        Opcode::GOTO |
        Opcode::CALL |
        Opcode::RETURN => &color::Fg(&color::Green),
        Opcode::SLEEP |
        Opcode::CLRWDT |
        Opcode::RETFIE => &color::Fg(&color::Cyan),
        Opcode::MOVWF |
        Opcode::MOVFP |
        Opcode::MOVPF |
        Opcode::MOVLW |
        Opcode::MOVLB |
        Opcode::MOVLR => &color::Fg(&color::LightMagenta),
        Opcode::BSF |
        Opcode::BCF |
        Opcode::IORWF |
        Opcode::ANDWF |
        Opcode::XORWF |
        Opcode::IORLW |
        Opcode::XORLW |
        Opcode::ANDLW |
        Opcode::CLRF |
        Opcode::SETF |
        Opcode::BTG |
        Opcode::COMF |
        Opcode::RRCF |
        Opcode::RLCF |
        Opcode::RRNCF |
        Opcode::RLNCF |
        Opcode::SWAPF => &color::Fg(&color::LightYellow),

        Opcode::INFSNZ |
        Opcode::DCFSNZ |
        Opcode::DECFSZ |
        Opcode::INCFSZ |
        Opcode::SUBWFB |
        Opcode::SUBWF |
        Opcode::DECF |
        Opcode::ADDWF |
        Opcode::ADDWFC |
        Opcode::INCF |
        Opcode::MULWF |
        Opcode::NEGW |
        Opcode::DAW |
        Opcode::ADDLW |
        Opcode::SUBLW |
        Opcode::MULLW => &color::Fg(&color::Yellow),

        Opcode::TLRDL |
        Opcode::TLRDH |
        Opcode::TLWTL |
        Opcode::TLWTH |
        Opcode::TABLRDL |
        Opcode::TABLRDLI |
        Opcode::TABLRDH |
        Opcode::TABLRDHI |
        Opcode::TABLWTL |
        Opcode::TABLWTLI |
        Opcode::TABLWTH |
        Opcode::TABLWTHI => &color::Fg(&color::Magenta),
    }
}

impl <T: std::fmt::Write> Colorize<T> for Operand {
    fn colorize(&self, colors: Option<&ColorSettings>, out: &mut T) -> std::fmt::Result {
        match self {
            Operand::ImmediateU8(i) => {
                write!(out, "#{:02x}", i)
            },
            Operand::ImmediateU32(i) => {
                write!(out, "#{:08x}", i)
            },
            Operand::File(f) => {
                if *f < 0x10 {
                    write!(out, "{}0x{:02x}{}", color::Fg(color::Yellow), f, color::Fg(color::Reset))
                } else {
                    write!(out, "{}[banked 0x{:02x}]{}", color::Fg(color::Yellow), f, color::Fg(color::Reset))
                }
            },
            Operand::W => {
                write!(out, "{}W{}", color::Fg(color::Yellow), color::Fg(color::Reset))
            },
            _ => {
                Ok(())
            }
        }
    }
}

impl <T: std::fmt::Write> ShowContextual<<PIC17 as Arch>::Address, [Option<String>], T> for Instruction {
    fn contextualize(&self, colors: Option<&ColorSettings>, address: <PIC17 as Arch>::Address, context: Option<&[Option<String>]>, out: &mut T) -> std::fmt::Result {
        write!(out, "{}{}{}", opcode_color(self.opcode), self.opcode, color::Fg(color::Reset))?;

        match self.opcode {
            Opcode::LCALL => {
                write!(out, " ")?;
                match context.and_then(|c| c.get(0)) {
                    Some(Some(text)) => {
                        write!(out, "{}", text)
                    },
                    _ => {
                        match self.operands[0] {
                            Operand::ImmediateU8(i) => {
                                write!(out, "+#{:08x}", (i as u16) * 2)
                            }
                            _ => { unreachable!(); }
                        }
                    }
                }
            },
            Opcode::CALL |
            Opcode::GOTO => {
                match context.and_then(|c| c.get(0)) {
                    Some(Some(text)) => { write!(out, "{}", text) }
                    _ => {
                        match self.operands[0] {
                            Operand::ImmediateU32(i) => {
                                write!(out, " #{:08x}", (i as u16) * 2)
                            },
                            _ => { unreachable!() }
                        }
                    }
                }
            },
            _ => {
                match context.and_then(|c| c.get(0)) {
                    Some(Some(text)) => { write!(out, " {}", text)?; },
                    _ => {
                        match &self.operands[0] {
                            Operand::Nothing => {
                                return Ok(());
                            },
                            x @ _ => {
                                write!(out, " ")?;
                                x.colorize(colors, out)?;
                            }
                        };
                    }
                };

                match context.and_then(|c| c.get(1)) {
                    Some(Some(text)) => { write!(out, ", {}", text)?; },
                    _ => {
                        match &self.operands[1] {
                            Operand::Nothing => {
                                return Ok(());
                            },
                            x @ _ => {
                                write!(out, ", ")?;
                                x.colorize(colors, out)?;
                            }
                        };
                    }
                };
                Ok(())
            }
        }
    }
}
