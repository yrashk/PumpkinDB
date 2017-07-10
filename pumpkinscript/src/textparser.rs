// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use byteorder::{BigEndian, WriteBytesExt};
use nom::{IResult, ErrorKind};
use nom::{is_hex_digit, multispace, is_digit};

use num_bigint::{BigUint, Sign};
use num_traits::Zero;
pub use nom_config::Configured;
use core::str::FromStr;
use std::str;

use super::{Program, Packable, ParseError};

#[derive(Debug, Clone, Copy, Builder)]
#[builder(setter(into),field(public))]
/// Parsing configuration
pub struct Config {
    /// For all literal types (besides binaries: `0x...`), add type casting information
    /// For example, `1` will in fact become `1 "UINT" AS`, `"hello"` will become
    /// `"hello" "STRING" AS`
    ///
    /// This information is useful during type checking and, if sent to the engine,
    /// can be used to enforce types in runtime, where possible.
    pub type_literals: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            // Don't type literals by default because it is only useful
            // for type checking. Might incur a performance penalty in
            // the interpreter.
            type_literals: false,
        }
    }
}

fn prefix_instruction(instruction: &[u8]) -> Vec<u8> {
    let mut vec = Vec::new();
    vec.push(instruction.len() as u8 | 128u8);
    vec.extend_from_slice(instruction);
    vec
}

#[inline]
fn hex_digit(v: u8) -> u8 {
    match v {
        0x61u8...0x66u8 => v - 32 - 0x41 + 10,
        0x41u8...0x46u8 => v - 0x41 + 10,
        _ => v - 48,
    }
}

macro_rules! write_size {
    ($vec : expr, $size : expr) => {
      match $size {
        0...120 => $vec.push($size as u8),
        121...255 => {
            $vec.push(121u8);
            $vec.push($size as u8);
        }
        256...65535 => {
            $vec.push(122u8);
            $vec.push(($size >> 8) as u8);
            $vec.push($size as u8);
        }
        65536...4294967296 => {
            $vec.push(123u8);
            $vec.push(($size >> 24) as u8);
            $vec.push(($size >> 16) as u8);
            $vec.push(($size >> 8) as u8);
            $vec.push($size as u8);
        }
        _ => unreachable!()
      }
    };
}


fn bin(bin: &[u8]) -> Vec<u8> {
    let mut bin_ = Vec::new();
    for i in 0..bin.len() - 1 {
        if i % 2 != 0 {
            continue;
        }
        bin_.push((hex_digit(bin[i]) << 4) | hex_digit(bin[i + 1]));
    }
    let mut vec = Vec::new();
    let size = bin_.len();
    write_size!(vec, size);
    vec.extend_from_slice(bin_.as_slice());
    vec
}

fn string_to_vec(s: &[u8]) -> Vec<u8> {
    let s = unsafe { String::from_utf8_unchecked(s.to_vec()) }
        .replace("\\\"", "\"")
        .replace("\\n", "\n");
    let mut bin = Vec::new();
    let size = s.len();
    write_size!(bin, size);
    bin.extend_from_slice(s.as_bytes());
    bin
}

fn sized_vec(s: Vec<u8>) -> Vec<u8> {
    let mut vec = Vec::new();
    let size = s.len();
    write_size!(vec, size);
    vec.extend_from_slice(s.as_slice());
    vec
}

fn typed(config: &Config, t: &'static [u8], mut v: Vec<u8>) -> Vec<u8> {
    if config.type_literals {
        v.extend_from_slice(t);
        v.extend_from_slice(b"\x82AS");
    }
    v
}

fn is_instruction_char(s: u8) -> bool {
    (s >= b'a' && s <= b'z') || (s >= b'A' && s <= b'Z') ||
    (s >= b'0' && s <= b'9') || s == b'_' || s == b':' || s == b'-' || s == b'=' ||
    s == b'!' || s == b'#' ||
    s == b'$' || s == b'%' || s == b'@' || s == b'?' || s == b'/' || s == b'<' || s == b'>'
}


fn flatten_program(p: Vec<Vec<u8>>) -> Vec<u8> {
    let mut vec = Vec::new();
    for mut item in p {
        vec.append(&mut item);
    }
    vec
}

fn delim_or_end(i: &[u8]) -> IResult<&[u8], ()> {
    if i.len() == 0 || (i.len() >= 1 && (i[0] == b' ' || i[0] == b']')) {
        return IResult::Done(&i[0..], ());
    } else {
        IResult::Error(ErrorKind::Custom(0))
    }
}

fn eof(i: &[u8]) -> IResult<&[u8], Vec<u8>> {
    if i.len() == 0 {
        return IResult::Done(&i[0..], Vec::new());
    } else {
        IResult::Error(ErrorKind::Custom(1))
    }
}

fn is_multispace(s: u8) -> bool {
    s == b'\n' || s == b'\r' || s == b'\t' || s == b' '
}

named!(sign_ch<char>,
       do_parse!(
           sign_ch: alt!(tag!("+") | tag!("-")) >>
               ({
                   sign_ch[0] as char
               })));


named!(sign<Sign>,
    do_parse!(
        sign: sign_ch >>
        ({
            if sign == '-' {
                Sign::Minus
            } else {
                Sign::Plus
            }
        })));

named!(int_str<&[u8], String>,
       do_parse!(
           sign_opt: opt!(sign_ch)              >>
               num_part: take_while1!(is_digit) >>
               ({
                   let sign_str = if let Some(sign) = sign_opt { sign.to_string() } else { "".to_owned() };
                   (sign_str + str::from_utf8(num_part).unwrap())})));



named!(biguint<BigUint>,
    do_parse!(
        biguint: take_while1!(is_digit) >>
        delim_or_end                    >>
        (BigUint::from_str(str::from_utf8(biguint).unwrap()).unwrap())));

named_with_config!(Config, u8int<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| u8::from_str(&s))) >>
        lift_config!(tag!("u8"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut u8i = vec![];
            u8i.write_u8(n).unwrap();
            typed(&cfg, b"\x05UINT8", sized_vec(u8i))
        })));

named_with_config!(Config, u16int<Vec<u8>>,
     do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| u16::from_str(&s))) >>
        lift_config!(tag!("u16"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut u16i = vec![];
            u16i.write_u16::<BigEndian>(n).unwrap();
            typed(&cfg, b"\x06UINT16", sized_vec(u16i))
        })));

named_with_config!(Config, u32int<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| u32::from_str(&s))) >>
        lift_config!(tag!("u32"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut u32i = vec![];
            u32i.write_u32::<BigEndian>(n).unwrap();
            typed(&cfg, b"\x06UINT32", sized_vec(u32i))
        })));

named_with_config!(Config, u64int<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| u64::from_str(&s))) >>
        lift_config!(tag!("u64"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut u64i = vec![];
            u64i.write_u64::<BigEndian>(n).unwrap();
            typed(&cfg, b"\x06UINT64", sized_vec(u64i))
        })));

named_with_config!(Config, int8<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| i8::from_str(&s))) >>
        lift_config!(tag!("i8"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut i8 = vec![];
            i8.write_i8(n).unwrap();
            i8[0] ^= 1u8 << 7;
            typed(&cfg, b"\x04INT8", sized_vec(i8))
        })));

named_with_config!(Config, int16<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| i16::from_str(&s))) >>
        lift_config!(tag!("i16"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut i16 = vec![];
            i16.write_i16::<BigEndian>(n).unwrap();
            i16[0] ^= 1u8 << 7;
            typed(&cfg, b"\x05INT16", sized_vec(i16))
        })));

named_with_config!(Config, int32<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| i32::from_str(&s))) >>
        lift_config!(tag!("i32"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut i32 = vec![];
            i32.write_i32::<BigEndian>(n).unwrap();
            i32[0] ^= 1u8 << 7;
            typed(&cfg, b"\x05INT32", sized_vec(i32))
        })));

named_with_config!(Config, int64<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        n: lift_config!(map_res!(int_str, |s: String| i64::from_str(&s))) >>
        lift_config!(tag!("i64"))                  >>
        lift_config!(delim_or_end) >>
        ({
            let mut i64 = vec![];
            i64.write_i64::<BigEndian>(n).unwrap();
            i64[0] ^= 1u8 << 7;
            typed(&cfg, b"\x05INT64", sized_vec(i64))
        })));

named_with_config!(Config, sint<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        sign: lift_config!(sign) >>
        biguint: lift_config!(biguint) >>
        ({
            let mut bytes = if sign == Sign::Minus && !biguint.is_zero() {
                vec![0x00]
           } else {
                vec![0x01]
            };
           let big = biguint.to_bytes_be();
           let mut compv: Vec<u8> = vec![];
           //Encode with two's complement.
           if sign == Sign::Minus && !biguint.is_zero() {
                for byte in big {
                    compv.push(!byte);
                }
                let mut nextbit = true;
                for i in (0..compv.len()).rev() {
                    compv[i] =  match compv[i].checked_add(1) {
                        Some(v) => {
                            nextbit = false;
                            v
                        },
                        None => 0,
                    };
                    if !nextbit {
                        break;
                    }
                }
           } else {
               compv = big;
           }
           //compv[0] ^= 1u8 << 7;
           bytes.extend_from_slice(&compv);
           (typed(&cfg, b"\x03INT", sized_vec(bytes)))
        })));

named_with_config!(Config, uint<Vec<u8>>,
    do_parse!(
        cfg: config!() >>
        biguint: lift_config!(biguint) >>
        (typed(&cfg, b"\x04UINT", sized_vec(biguint.to_bytes_be())))));

named_with_config!(Config, int_sized<Vec<u8>>,
    do_parse!(
        int: alt!(u8int | int8 | u16int | int16 | u32int | int32 | u64int | int64 ) >>
            (int)));

named_with_config!(Config, float32<Vec<u8>>,
       do_parse!(
           cfg: config!() >>
           sign: lift_config!(opt!(sign_ch))           >>
           left: lift_config!(take_while1!(is_digit))  >>
           lift_config!(char!('.'))                    >>
           right: lift_config!(take_while1!(is_digit)) >>
           lift_config!(tag!("f32"))                   >>
           lift_config!(delim_or_end)                 >>
               ({
                   let mut bytes = vec![];
                   if let Some('-') = sign {
                       bytes.extend_from_slice(b"-");
                   }
                   bytes.extend_from_slice(left);
                   bytes.extend_from_slice(b".");
                   bytes.extend_from_slice(right);
                   let mut val = str::from_utf8(&bytes).unwrap().parse::<f32>().unwrap();
                   // a little tricky: +0.0f32 == -0.0f32, but they don't serialize
                   // to the same bytes. negative sign in the comparison left to indicate
                   // intent, but technically unnecessary
                   if val == -0.0f32 {
                       val = 0.0f32;
                   }
                   typed(&cfg, b"\x03F32", sized_vec(val.pack()))
               })));

named_with_config!(Config, float64<Vec<u8>>,
       do_parse!(
           cfg: config!() >>
           sign: lift_config!(opt!(sign_ch))           >>
           left: lift_config!(take_while1!(is_digit))  >>
           lift_config!(char!('.'))                    >>
           right: lift_config!(take_while1!(is_digit)) >>
           lift_config!(tag!("f64"))                   >>
           lift_config!(delim_or_end)                 >>
           ({
               let mut bytes = vec![];
               if let Some('-') = sign {
                   bytes.extend_from_slice(b"-");
               }
               bytes.extend_from_slice(left);
               bytes.extend_from_slice(b".");
               bytes.extend_from_slice(right);
               let mut val = str::from_utf8(&bytes).unwrap().parse::<f64>().unwrap();
               // see note on float32
               if val == -0.0f64 {
                   val = 0.0f64;
               }
               typed(&cfg, b"\x03F64", sized_vec(val.pack()))
           })));


named!(instruction<Vec<u8>>, do_parse!(
                        instruction: take_while1!(is_instruction_char)  >>
                              (prefix_instruction(instruction))));
named_with_config!(Config, instructionref<Vec<u8>>,
                  do_parse!(
                      cfg: config!() >>
                      lift_config!(tag!(b"'")) >>
                      w: lift_config!(instruction) >>
                      (typed(&cfg, b"\x07CLOSURE", sized_vec(w)))));
named!(binary<Vec<u8>>, do_parse!(
                              tag!(b"0x")                 >>
                         hex: take_while1!(is_hex_digit)  >>
                              (bin(hex))
));
named_with_config!(Config, string<Vec<u8>>,
                         alt!(do_parse!(
                           cfg: config!() >>
                           lift_config!(tag!(b"\"\"")) >> (typed(&cfg, b"\x06STRING", vec![0]))) |
                         do_parse!(
                           cfg: config!() >>
                           str: lift_config!(delimited!(char!('"'),
                                         escaped!(is_not!("\"\\"), '\\', one_of!("\"n\\")),
                                         char!('"'))) >>
                           (typed(&cfg, b"\x06STRING", string_to_vec(str))))));
named!(comment_, do_parse!(
                               char!('(')                            >>
                               many0!(alt!(is_not!("()") | comment_ | is_not!(")"))) >>
                               char!(')')                            >>
                               (&[])));
named!(comment<Vec<u8>>, do_parse!(comment_ >> (vec![])));
named_with_config!(Config, item<Vec<u8>>,
                       alt!(lift_config!(comment) | uint | lift_config!(binary) | string | sint | int_sized | float32 |
                            float64 | wrap | instructionref | lift_config!(instruction)));

fn unwrap_instruction(mut instruction: Vec<u8>) -> Vec<u8> {
    let mut vec = Vec::new();
    vec.extend_from_slice(b"`");
    vec.append(&mut instruction);
    vec
}

fn rewrap(cfg: &Config, prog: Vec<u8>) -> Vec<u8> {
    let mut program = &prog[..];
    let mut vec = Vec::new();
    let mut acc = Vec::new();
    let mut counter = 0;

    while program.len() > 0 {
        if let IResult::Done(rest, unwrap) = bin_unwrap(program) {
            if acc.len() > 0 {
                vec.append(&mut sized_vec(acc.clone()));
                acc.clear();
                counter += 1;
            }
            vec.extend_from_slice(&unwrap[1..]);
            vec.extend_from_slice(b"\x01\x01");
            vec.append(&mut prefix_instruction(b"WRAP"));

            counter += 1;
            program = rest;
        } else if let IResult::Done(rest, data) = super::binparser::data(program) {
            acc.extend_from_slice(data);
            program = rest;
        } else if let IResult::Done(rest, instruction) = super::binparser::instruction(program) {
            acc.extend_from_slice(instruction);
            program = rest;
        } else {
            panic!("invalid data {:?}", &program);
        }
    }
    if acc.len() > 0 {
        counter += 1;
        vec.append(&mut sized_vec(acc.clone()));
        acc.clear();
    }
    for _ in 0..counter - 1 {
        vec.append(&mut prefix_instruction(b"CONCAT"));
    }
    let res = if counter == 0 { sized_vec(vec) } else { vec };
    typed(cfg, b"\x07CLOSURE", res)
}

use super::binparser::instruction_tag;
named!(bin_instruction<Vec<u8>>, do_parse!(v: length_bytes!(instruction_tag) >> (Vec::from(v))));

named!(bin_unwrap<Vec<u8>>, do_parse!(
                              tag!(b"`")                   >>
                        instruction: alt!(bin_instruction | bin_unwrap)  >>
                              (unwrap_instruction(instruction))));

named!(unwrap<Vec<u8>>, do_parse!(
                              tag!(b"`")                 >>
                        instruction: alt!(instruction | unwrap)        >>
                              (unwrap_instruction(instruction))));
named_with_config!(Config, wrap<Vec<u8>>, do_parse!(
                         cfg: config!() >>
                         prog: delimited!(lift_config!(char!('[')), ws!(wrapped_program), lift_config!(char!(']'))) >>
                               (rewrap(cfg, prog))));
named_with_config!(Config, wrapped_item<Vec<u8>>, alt!(item | lift_config!(unwrap)));
named_with_config!(Config, wrapped_program<Vec<u8>>, alt!(lift_config!(do_parse!(
                               take_while!(is_multispace)                        >>
                            v: eof                                               >>
                               (v)))
                              | do_parse!(
                               take_while!(is_multispace)                        >>
                         item: separated_list!(complete!(multispace),
                                                complete!(wrapped_item))         >>
                               take_while!(is_multispace)                        >>
                               (flatten_program(item)))));

named_with_config!(Config, program<Vec<u8>>, alt!(lift_config!(do_parse!(
                               take_while!(is_multispace)                        >>
                            v: eof                                               >>
                               (v)))
                              | do_parse!(
                               take_while!(is_multispace)          >>
                         item: separated_list!(complete!(multispace),
                                                 complete!(item))                >>
                               take_while!(is_multispace)          >>
                               (flatten_program(item)))));

named_with_config!(Config, pub programs<Vec<Vec<u8>>>, do_parse!(
                         item: separated_list!(lift_config!(complete!(tag!(b"."))), program)   >>
                               (item)));


/// Parses human-readable PumpkinScript
///
/// The format is simple, it is a sequence of space-separated tokens,
/// with binaries represented as:
///
/// * `0x<hexadecimal>` (hexadecimal form)
/// * `"STRING"` (string form, newline and double quotes can be escaped with `\`)
/// * `integer` (integer form, will convert to a big endian big integer)
/// * `'instruction` (instruction in a binary form)
///
/// The rest of the instructions considered to be instructions.
///
/// One additional piece of syntax is code included within square
/// brackets: `[DUP]`. This means that the parser will take the code inside,
/// compile it to the binary form and add as a data push. This is useful for
/// instructions like EVAL. Inside of this syntax, you can use so-called "unwrapping"
/// syntax that can embed a value of a instruction into this code:
///
/// ```norun
/// PumpkinDB> 1 'a SET [`a] 'b SET 2 'a SET b EVAL
/// 0x01
/// ```
///
/// It is also possible to unwrap multiple levels:
///
/// ```norun
/// PumpkinDB> "A" 'a SET [[2 ``a DUP] EVAL] 'b SET "B" 'a SET b EVAL
/// 0x02 "A" "A"
/// ```
///
/// # Example
///
/// ```norun
/// parse("0xABCD DUP DROP DROP")
/// ```
///
/// It's especially useful for testing but there is a chance that there will be
/// a "suboptimal" protocol that allows to converse with PumpkinDB over telnet
pub fn parse_with_config(script: &str, config: Config) -> Result<Program, ParseError> {
    match program(Configured::new(config, script.as_bytes())) {
        IResult::Done(configured, x) => {
            let (_, rest) = configured.into();
            if rest.len() == 0 {
                Ok(x)
            } else {
                Err(ParseError::Superfluous(Vec::from(rest)))
            }
        }
        IResult::Incomplete(_) => Err(ParseError::Incomplete),
        IResult::Error(ErrorKind::Custom(code)) => Err(ParseError::Err(code)),
        _ => Err(ParseError::UnknownErr),
    }
}

pub fn parse(script: &str) -> Result<Program, ParseError> {
    parse_with_config(script, Default::default())
}

#[cfg(test)]
mod tests {
    use textparser::{parse, parse_with_config, programs, ConfigBuilder, Configured};
    use num_bigint::BigUint;
    use core::str::FromStr;

    #[test]
    fn test_empty() {
        let script = parse("").unwrap();
        let empty: Vec<u8> = vec![];
        assert_eq!(script, empty);
        let script = parse("  ").unwrap();
        assert_eq!(script, empty);
    }

    #[test]
    fn multiline() {
        let script_multiline = parse("\nHELP [\nDROP] \n1").unwrap();
        let script = parse("HELP [DROP] 1").unwrap();
        assert_eq!(script, script_multiline);
    }

    #[test]
    fn test_comment() {
        let script = parse("1 (hello) 2").unwrap();
        assert_eq!(script, parse("1 2").unwrap());
    }

    #[test]
    fn test_empty_comment() {
        let script = parse("1 () 2").unwrap();
        assert_eq!(script, parse("1 2").unwrap());
    }

    #[test]
    fn test_multiline_comment() {
        let script = parse("1 (hel\nlo) 2").unwrap();
        assert_eq!(script, parse("1 2").unwrap());
    }

    #[test]
    fn test_nested_comment() {
        let script = parse("1 (he(l\n) (l)o) 2").unwrap();
        assert_eq!(script, parse("1 2").unwrap());
    }

    #[test]
    fn superfluous() {
        assert!(parse("HELP [DROP]]").is_err());
    }

    #[test]
    fn test_instructionref() {
        let script = parse("'HELLO").unwrap();
        assert_eq!(script, vec![0x06, 0x85, b'H', b'E', b'L', b'L', b'O']);
    }

    #[test]
    fn test_one() {
        let script = parse("0xAABB").unwrap();
        assert_eq!(script, vec![2, 0xaa,0xbb]);
        let script = parse("HELLO").unwrap();
        assert_eq!(script, vec![0x85, b'H', b'E', b'L', b'L', b'O']);
    }

    #[test]
    fn test_uint() {
        let script = parse("1234567890").unwrap();
        let mut bytes = BigUint::from_str("1234567890").unwrap().to_bytes_be();
        let mut sized = Vec::new();
        sized.push(4);
        sized.append(&mut bytes);
        assert_eq!(script, sized);
    }

    #[test]
    fn test_uint8() {
        let script = parse("123u8").unwrap();
        assert_eq!(script, [1, 123u8]);
    }

    #[test]
    fn test_uint16() {
        let script = parse("123u16").unwrap();
        assert_eq!(script, [2, 0, 123]);
    }

    #[test]
    fn test_uint32() {
        let script = parse("123u32").unwrap();
        assert_eq!(script, [4, 0, 0, 0, 123]);
    }

    #[test]
    fn test_uint64() {
        let script = parse("123u64").unwrap();
        assert_eq!(script, [8, 0, 0, 0, 0, 0, 0, 0, 123]);
    }

    #[test]
    fn test_int8() {
        let script = parse("-123i8").unwrap();
        assert_eq!(script, [1, 5]);
        let script = parse("+123i8").unwrap();
        assert_eq!(script, [1, 251]);
        let script = parse("123i8").unwrap();
        assert_eq!(script, [1, 251]);
    }

    #[test]
    fn test_int16() {
        let script = parse("-123i16").unwrap();
        assert_eq!(script, [2, 127, 133]);
        let script = parse("+123i16").unwrap();
        assert_eq!(script, [2, 128, 123]);
        let script = parse("123i16").unwrap();
        assert_eq!(script, [2, 128, 123]);
    }

    #[test]
    fn test_int32() {
        let script = parse("-123i32").unwrap();
        assert_eq!(script, [4, 127, 255, 255, 133]);
        let script = parse("+123i32").unwrap();
        assert_eq!(script, [4, 128, 0, 0, 123]);
        let script = parse("123i32").unwrap();
        assert_eq!(script, [4, 128, 0, 0, 123]);
    }

    #[test]
    fn test_int64() {
        let script = parse("-123i64").unwrap();
        assert_eq!(script, [8, 127, 255, 255, 255, 255, 255, 255, 133]);
        let script = parse("+123i64").unwrap();
        assert_eq!(script, [8, 128, 0, 0, 0, 0, 0, 0, 123]);
        let script = parse("123i64").unwrap();
        assert_eq!(script, [8, 128, 0, 0, 0, 0, 0, 0, 123]);
    }

    #[test]
    fn test_many_uint() {
        let script = parse("1 2 3").unwrap();

        let mut vec = Vec::new();

        let mut bytes = BigUint::from_str("1").unwrap().to_bytes_be();
        vec.push(1);
        vec.append(&mut bytes);

        let mut bytes = BigUint::from_str("2").unwrap().to_bytes_be();
        vec.push(1);
        vec.append(&mut bytes);

        let mut bytes = BigUint::from_str("3").unwrap().to_bytes_be();
        vec.push(1);
        vec.append(&mut bytes);

        assert_eq!(script, vec);
    }

    #[test]
    fn test_uint_at_the_end_of_code() {
        let script = parse("[1]").unwrap();
        assert_eq!(script, parse("[0x01]").unwrap());
    }

    #[test]
    fn test_float32() {
        assert_eq!(parse("+1.3f32").unwrap(), parse("1.3f32").unwrap());
        assert_eq!(parse("1.3f32").unwrap(), vec![4, 191, 166, 102, 102]);
        assert_eq!(parse("-1.3f32").unwrap(), vec![4, 64, 89, 153, 153]);
    }

    #[test]
    fn test_float64() {
        assert_eq!(parse("+1.3f64").unwrap(), parse("1.3f64").unwrap());
        assert_eq!(parse("1.3f64").unwrap(), vec![8, 191, 244, 204, 204, 204, 204, 204, 205]);
        assert_eq!(parse("-1.3f64").unwrap(), vec![8, 64, 11, 51, 51, 51, 51, 51, 50]);
    }


    #[test]
    fn test_number_prefixed_instruction() {
        let script = parse("2DUP").unwrap();
        assert_eq!(script, b"\x842DUP");
    }

    #[test]
    fn test_extra_spaces() {
        let script = parse(" 0xAABB  \"Hi\" ").unwrap();
        assert_eq!(script, vec![2, 0xaa,0xbb, 2, b'H', b'i']);
        let script = parse("[ 0xAABB  \"Hi\" ]").unwrap();
        assert_eq!(script, vec![6, 2, 0xaa,0xbb, 2, b'H', b'i']);
    }

    #[test]
    fn test() {
        let script = parse("0xAABB DUP 0xFF00CC \"Hello\"").unwrap();

        assert_eq!(script, vec![0x02, 0xAA, 0xBB, 0x83, b'D', b'U', b'P',
                                0x03, 0xFF, 0x00, 0xCC, 0x05, b'H', b'e', b'l', b'l', b'o']);
    }


    #[test]
    fn test_empty_string() {
        let script = parse("\"\"").unwrap();

        assert_eq!(script, vec![0]);
    }

    #[test]
    fn test_string_escaping() {
        let script = parse(r#""\"1\"""#).unwrap();
        assert_eq!(script, vec![3, b'"', b'1', b'"']);
        let script = parse(r#""\n""#).unwrap();
        assert_eq!(script, vec![1, b'\n']);
    }

    #[test]
    fn test_wrap() {
        let script = parse("[DUP]").unwrap();
        let script_spaced = parse("[ DUP ]").unwrap();
        assert_eq!(script, vec![4, 0x83, b'D', b'U', b'P']);
        assert_eq!(script_spaced, vec![4, 0x83, b'D', b'U', b'P']);
    }

    #[test]
    fn test_empty_wrap() {
        let script = parse("[]").unwrap();
        assert_eq!(script, vec![0]);
    }

    #[test]
    fn test_programs() {
        let str = "SOMETHING : BURP DURP.\nBURP : DURP";
        let (_, mut progs) = programs(Configured::new(Default::default(), str.as_bytes())).unwrap();
        assert_eq!(Vec::from(progs.pop().unwrap()), parse("BURP : DURP").unwrap());
        assert_eq!(Vec::from(progs.pop().unwrap()), parse("SOMETHING : BURP DURP").unwrap());
    }


    #[test]
    fn unwrapping() {
        assert_eq!(parse("[`val DUP]").unwrap(), parse("val 1 WRAP [DUP] CONCAT").unwrap());
        assert_eq!(parse("[`val]").unwrap(), parse("val 1 WRAP").unwrap());
        assert_eq!(parse("[1 `val DUP]").unwrap(),
                   parse("[1] val 1 WRAP [DUP] CONCAT CONCAT").unwrap());
        assert_eq!(parse("[1 `val DUP `val]").unwrap(),
                   parse("[1] val 1 WRAP [DUP] val 1 WRAP CONCAT CONCAT CONCAT").unwrap());
        assert_eq!(parse("[1 `val]").unwrap(), parse("[1] val 1 WRAP CONCAT").unwrap());
    }

    #[test]
    fn nested_unwrapping() {
        assert_eq!(parse("[[``val DUP]]").unwrap(),
                   parse("val 1 WRAP [1 WRAP [DUP] CONCAT] CONCAT").unwrap());
        assert_eq!(parse("[[2 ``val DUP]]").unwrap(),
                   parse("[[2]] val 1 WRAP [1 WRAP [DUP] CONCAT CONCAT] CONCAT CONCAT").unwrap());
    }

    #[test]
    fn test_signed_ints() {
        assert_eq!(parse("+0").unwrap(), parse("-0").unwrap());
        assert_eq!(parse("+0").unwrap(), vec![2, 1, 0]);
        assert_eq!(parse("+1").unwrap(), vec![2, 1, 1]);
        assert_eq!(parse("-1").unwrap(), vec![2, 0, 255]);
    }

    #[test]
    fn test_typing() {
        let config = ConfigBuilder::default().type_literals(true).build().unwrap();
        assert_eq!(parse_with_config("0", config).unwrap(), parse("0 \"UINT\" AS").unwrap());
        assert_eq!(parse_with_config("+1", config).unwrap(), parse("+1 \"INT\" AS").unwrap());
        assert_eq!(parse_with_config("0u8", config).unwrap(), parse("0u8 \"UINT8\" AS").unwrap());
        assert_eq!(parse_with_config("0u16", config).unwrap(), parse("0u16 \"UINT16\" AS").unwrap());
        assert_eq!(parse_with_config("0u32", config).unwrap(), parse("0u32 \"UINT32\" AS").unwrap());
        assert_eq!(parse_with_config("0u64", config).unwrap(), parse("0u64 \"UINT64\" AS").unwrap());
        assert_eq!(parse_with_config("-1i8", config).unwrap(), parse("-1i8 \"INT8\" AS").unwrap());
        assert_eq!(parse_with_config("-1i16", config).unwrap(), parse("-1i16 \"INT16\" AS").unwrap());
        assert_eq!(parse_with_config("-1i32", config).unwrap(), parse("-1i32 \"INT32\" AS").unwrap());
        assert_eq!(parse_with_config("-1i64", config).unwrap(), parse("-1i64 \"INT64\" AS").unwrap());
        assert_eq!(parse_with_config("0.0f32", config).unwrap(), parse("0.0f32 \"F32\" AS").unwrap());
        assert_eq!(parse_with_config("0.0f64", config).unwrap(), parse("0.0f64 \"F64\" AS").unwrap());
        assert_eq!(parse_with_config("\"string\"", config).unwrap(), parse("\"string\" \"STRING\" AS").unwrap());
        assert_eq!(parse_with_config("[]", config).unwrap(), parse("[] \"CLOSURE\" AS").unwrap());
        assert_eq!(parse_with_config("'TEST", config).unwrap(), parse("'TEST \"CLOSURE\" AS").unwrap());
    }

}
