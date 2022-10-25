# random_lfsr_256_galois

Simple random generator imlplementation based on linear feedback shift register (LFSR, Galois variation) on 256-bit polynome.
## What is this?

**random-lfsr-256-galois** is minimalistic uniform-distributed pseudo-random number generator, with possibility of distortion of random sequence. It based on 256-bit LFSR polynome **x<sup>256</sup> + x<sup>254</sup> + x<sup>251</sup> + x<sup>246</sup>** and generates extremely more random combinations then standard 32-bit pseudo-random generator.

This implementation developed for educational and entertainment purposes (e.g. games).
Do not use it in cryptographic projects, and if you do it for crypto you will get what you deserve.

## Usage
```rust
use random_lfsr_256_galois::LFSRGaloisBuilder;

//Create PRNG with builder
let mut lfsr = LFSRGaloisBuilder::new().build();

// Then get random value of type you need (up to 128bit)
let random_byte: u8 = lfsr.next();
let random_int: i32 = lfsr.next();
let random_uint64: u64 = lfsr.next();
let random_u128: u128 = lfsr.next();

```
Also you can distort register to break up LFSR sequence by calling [`LFSRGalois::shake`] function
at random moments of time, e.g. user actions (mouse clicks, pressing buttons)
or another external events such as receiving network packets.

```rust
use random_lfsr_256_galois::LFSRGaloisBuilder;

let mut lfsr = LFSRGaloisBuilder::new().build();

lfsr.shake()

```

## License
**X11**

