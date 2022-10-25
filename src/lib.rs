//! Simple random generator imlplementation based on linear feedback shift register (LFSR, Galois variation) on 256-bit polynome.
//! # What is this?
//!
//! **random-lfsr-256-galois** is minimalistic uniform-distributed pseudo-random number generator, with possibility of distortion of random sequence. It based on 256-bit LFSR polynome **x<sup>256</sup> + x<sup>254</sup> + x<sup>251</sup> + x<sup>246</sup>** and generates extremely more random combinations then standard 32-bit pseudo-random generator.
//!
//! This implementation developed for educational and entertainment purposes (e.g. games).
//! Do not use it in cryptographic projects, and if you do it for crypto you will get what you deserve.
//!
//! # Usage
//! ```
//! use random_lfsr_256_galois::LFSRGaloisBuilder;
//!
//! //Create PRNG with builder
//! let mut lfsr = LFSRGaloisBuilder::new().build();
//!
//! // Then get random value of type you need (up to 128bit)
//! let random_byte: u8 = lfsr.next();
//! let random_int: i32 = lfsr.next();
//! let random_uint64: u64 = lfsr.next();
//! let random_u128: u128 = lfsr.next();
//!
//! ```
//! Also you can distort register to break up LFSR sequence by calling [`LFSRGalois::shake`] function
//! at random moments of time, e.g. user actions (mouse clicks, pressing buttons)
//! or another external events such as receiving network packets.
//!
//! ```
//! use random_lfsr_256_galois::LFSRGaloisBuilder;
//!
//! let mut lfsr = LFSRGaloisBuilder::new().build();
//!
//! lfsr.shake()
//!
//! ```
//!
//! # License
//! **X11**
//!

mod utils;

use num_traits::PrimInt;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::time::SystemTime;

/// Polynome for 256bit LFSR
///
/// There is only one primitive polynome for 256bit Galois field
/// **x<sup>256</sup> + x<sup>254</sup> + x<sup>251</sup> + x<sup>246</sup>**
///
const LFSR_POLY: u128 = 0x0000a420;

/// Variations of initial payload of LFSR register.
///
/// - **Meander** - regular sequence of oxff00ff00 bytes. Used for tests.
/// - **Zeroed** - all zero payload. Used for tests.
/// - **Ones** - all ones payload. Used for tests.
/// - **Random** - payload filled with pseudo-random numbers by rand::Rng. This is default variation.
/// - **Custom** - user-defined payload (e.g. it may be loaded state of previously saved register).
pub enum InitRegisterPayload {
    /// Regular sequence of `0xff00ff00` bytes. Used for tests.
    Meander,
    /// All zero payload. Used for tests.
    Zeroed,
    /// All ones payload. Used for tests.
    Ones,
    /// Payload filled with pseudo-random numbers by [`rand::Rng`]. This is default variation.
    Random,
    /// User-defined payload (e.g. it may be loaded state of previously saved register).
    Custom(u128, u128),
}

/// Representation of the register itself.
/// 256 bit of LFSR splitted to two u128 values.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LFSRGalois {
    reg_hi: u128,
    reg_lo: u128,
}

impl LFSRGalois {
    /// Directly current register value.
    ///
    /// * `h` - high part of the register.
    /// * `l` - low part of the register
    /// There are no many reasons to setup values of the register already created,
    /// but there is possibility to do this.
    /// If you want to save intermediate values between i.g. two runs of program,
    /// use builder [`InitRegisterPayload::Custom`] instead.
    ///
    /// # Example
    /// ```
    /// use random_lfsr_256_galois::LFSRGaloisBuilder;
    ///
    /// let mut lfsr = LFSRGaloisBuilder::new().build();
    ///
    /// let mut low_part = 0u128;
    /// let mut high_part = 0u128;
    ///
    /// //...
    /// // Get values of variables above from external source.
    /// //...
    ///
    /// lfsr.setup(high_part, low_part);
    ///
    /// ```
    ///
    pub fn setup(&mut self, h: u128, l: u128) {
        self.reg_hi = h;
        self.reg_lo = l;
    }

    fn shift(&mut self, shift_count: usize) -> u128 {
        let mut output: u128 = 0u128;
        let mut count = shift_count;
        while count > 0 {
            count -= 1;

            let end_bit: u128 = self.reg_lo & 0x01;
            output <<= 1;
            output |= end_bit;

            if end_bit > 0 {
                self.reg_lo ^= LFSR_POLY;
            }

            let carry_bit: u128 = (self.reg_hi & 0x01) << 127;
            self.reg_lo >>= 1;
            self.reg_lo |= carry_bit;
            self.reg_hi >>= 1;
            self.reg_hi |= end_bit << 127;
        }
        output
    }

    /// Returns random value.
    ///
    /// The type and range of this value is in accordance to type of variable
    /// used to get it, so variable's type must be declared explicitly.
    ///
    ///  #Example
    ///  ```
    /// use random_lfsr_256_galois::LFSRGaloisBuilder;
    ///
    /// let mut lfsr = LFSRGaloisBuilder::new().build();
    ///
    /// let random_byte: u8 = lfsr.next(); // returns value in range (0; 256]
    /// let random_int: i32 = lfsr.next(); // returns value in range (-2<sup>31</sup>; 2<sup>31</sup>]
    /// let random_uint64: u64 = lfsr.next(); // return value in range (0; 2<sup>64</sup>]
    /// let random_u128: u128 = lfsr.next(); // return value in range (0; 2<sup>128</sup>]
    /// ```
    /// The function doesn't use unsafe code.
    ///
    pub fn next<T>(&mut self) -> T
    where
        T: PrimInt + std::ops::Sub,
    {
        let bit_count = std::mem::size_of::<T>() * (u8::BITS as usize);

        let output = self.shift(bit_count);
        if let Some(uresult) = T::from(output) {
            uresult
        } else {
            let mask: u128 = (1 << bit_count - 1) - 1;
            let masked_output = output & mask;
            let result;
            let dec;
            if masked_output > 0 {
                let iresult = (u128::MAX ^ (masked_output - 1)) & mask;
                result = T::from(iresult).unwrap();
                dec = T::from(0).unwrap();
            } else {
                result = T::from(mask).unwrap();
                dec = T::from(1).unwrap();
            }
            result - result - result - dec
        }
    }

    /// Make a little distortion to register sequence.
    ///
    /// This function takes last 4 binary digits of nanosecond counter of SystemTime::now()
    /// and make xor operation with lesser bits of register.
    /// Use this function in not often random moments of time (i.g. user actions) and
    /// this make the pseudorandom seqence really random.

    pub fn shake(&mut self) {
        let maybe_dur = SystemTime::now().duration_since(std::time::UNIX_EPOCH);
        if let Ok(dur) = maybe_dur {
            self.reg_lo ^= dur.as_nanos() & 0xFu128;
        }
        let _ = self.shift(4);
    }
}

/// Constructs an instance of [`LFSRGalois`].
///
/// Classic Builder-pattern constructor of object.
///
pub struct LFSRGaloisBuilder {
    warmup_count: usize,
    /// Init payload
    init_payload: InitRegisterPayload,
}

impl LFSRGaloisBuilder {
    /// Creates a new builder object.
    ///
    /// Creates builder object and returns it for further construction of [`LFSRGalois`] instance
    ///
    pub fn new() -> Self {
        LFSRGaloisBuilder {
            warmup_count: 256usize,
            init_payload: InitRegisterPayload::Random,
        }
    }

    /// Set initial payload of LFSR. See [`LFSRGalois::InitRegisterPayload`]
    pub fn set_initial_payload(&mut self, init_payload_: InitRegisterPayload) -> &mut Self {
        self.init_payload = init_payload_;
        self
    }

    /// Warmup LFSR before use.
    ///
    /// Set [`count`] of bits the LFSR shifts before firts use to shuffle initial payload.
    /// Default value is 256 bit (i.e. register makes one cyclic shift)
    pub fn warmup(&mut self, count: usize) -> &mut Self {
        self.warmup_count = count;
        self
    }

    /// Builds [`LFSRGalois`] instance.
    pub fn build(&self) -> LFSRGalois {
        let mut lfsr = LFSRGalois {
            reg_hi: 0u128,
            reg_lo: 0u128,
        };

        match self.init_payload {
            InitRegisterPayload::Meander => lfsr.setup(
                0xff00ff00ff00ff00ff00ff00ff00ff00,
                0xff00ff00ff00ff00ff00ff00ff00ff00,
            ),
            InitRegisterPayload::Zeroed => lfsr.setup(0u128, 0u128),
            InitRegisterPayload::Ones => lfsr.setup(u128::MAX, u128::MAX),
            InitRegisterPayload::Custom(hi, lo) => lfsr.setup(hi, lo),
            InitRegisterPayload::Random => {
                let mut rng = rand::thread_rng();
                let hi: u128 = rng.gen();
                let lo: u128 = rng.gen();
                lfsr.setup(hi, lo)
            }
        }

        if self.warmup_count > 0 {
            let _ = lfsr.shift(self.warmup_count);
        }
        lfsr
    }
}

/// # Tests
///
/// Although tests based on Berlekamp-Messey are enough to check correctness
/// of LFSR algorytm, here is some simple tests in "black box" style.
///
#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils;
    use rstest::*;
    use std::collections::HashMap;

    /// Check register is always stays filled by zeroes when initial payload is zeroed.
    #[test]
    fn zero_register_stays_zero() {
        let lfsr = LFSRGaloisBuilder::new()
            .set_initial_payload(InitRegisterPayload::Zeroed)
            .build();

        assert_eq!(lfsr.reg_hi, 0u128);
        assert_eq!(lfsr.reg_lo, 0u128);
    }

    /// Check no repeating values for 10000 sequental calls to [`LFSRGalois::next`] function
    /// on various non-zero initial payloads.
    #[rstest]
    #[case(InitRegisterPayload::Meander)]
    #[case(InitRegisterPayload::Ones)]
    #[case(InitRegisterPayload::Random)]
    #[case(InitRegisterPayload::Custom(0xDEADu128, 0xDEADu128))]
    fn first_10000_u32_never_repeat(#[case] payload: InitRegisterPayload) {
        let mut lfsr = LFSRGaloisBuilder::new()
            .set_initial_payload(payload)
            .build();

        let mut hash_map = HashMap::<i32, u32>::new();
        for _ in 0..10000 {
            let rnd: i32 = lfsr.next();
            if let Some(value) = hash_map.get(&rnd) {
                hash_map.insert(rnd, value + 1);
                assert!(false);
            } else {
                hash_map.insert(rnd, 1);
            }
        }
    }

    /// Check correctness of one-bit shift of payload with one leading 1.
    #[test]
    fn one_shift_of_one() {
        let mut lfsr = LFSRGaloisBuilder::new()
            .set_initial_payload(InitRegisterPayload::Custom(0u128, 1u128))
            .warmup(0)
            .build();

        let _ = lfsr.shift(1);
        assert_eq!(lfsr.reg_hi, 0x80000000000000000000000000000000u128);
        assert_eq!(lfsr.reg_lo, LFSR_POLY >> 1);
    }

    /// Check Berlekamp-Messey algorythm detects size of polynome correctly.
    #[test]
    fn test_berlekamp_messey() {
        let mut lfsr = LFSRGaloisBuilder::new()
            .set_initial_payload(InitRegisterPayload::Ones)
            .warmup(256)
            .build();

        const LEN: i32 = 640;
        let mut s: Vec<u8> = Vec::new();
        for _i in 0..LEN {
            let rnd: u8 = lfsr.next();
            for j in 0..8 {
                let mut bit = (rnd << j) & 0x80;
                if bit > 0 {
                    bit = 1;
                }
                s.push(bit);
            }
        }

        let bm = utils::bm_find(&s);
        assert_eq!(255, bm);
    }

    /// Check Berlekamp-Messey algorythm does not detect size of polynome correctly,
    /// when generated sequence distorted with **shake()** function call.
    #[test]
    fn non_correct_test_berlekamp_messey() {
        let mut lfsr = LFSRGaloisBuilder::new()
            .set_initial_payload(InitRegisterPayload::Ones)
            .warmup(256)
            .build();

        const LEN: i32 = 640;
        let mut s: Vec<u8> = Vec::new();
        for i in 0..LEN {
            let rnd: u8 = lfsr.next();
            if i == LEN / 2 {
                lfsr.shake();
            }
            for j in 0..8 {
                let mut bit = (rnd << j) & 0x80;
                if bit > 0 {
                    bit = 1;
                }
                s.push(bit);
            }
        }

        let bm = utils::bm_find(&s);
        assert_ne!(255, bm);
    }

    #[test]
    fn check_next_for_signed() {
        let mut lfsr = LFSRGaloisBuilder::new().build();

        for i in 0u128..255u128 {
            lfsr.setup(0u128, i);

            let r: i8 = lfsr.next();

            println!("Result{i} is {r}");
        }
    }
}
