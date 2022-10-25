/// Simple realization of Berlekamp-Massey algorythm for testing purposes
///
/// * `s` - array of bytes when every byte can be `0u8` or `1u8`. i.e
/// one byte in input data represents one bit of researching sequence.
///
/// Function returns size of minimal generation polynome.
///
pub fn bm_find(s: &[u8]) -> i32 {
    let ulen = s.len();
    let len = ulen as i32;
    let mut N = 0i32;
    let mut L = 0i32;
    let mut m: i32 = -1i32;
    let mut d: u8;
    let mut b: Vec<u8> = vec![0; ulen];
    let mut c: Vec<u8> = vec![0; ulen];
    let mut t: Vec<u8> = vec![0; ulen];

    //Initialization
    b[0] = 1;
    c[0] = 1;

    //Algorithm core
    while N < len {
        let UN = N as usize;
        let UL = L as usize;
        d = s[UN];
        for i in 1..UL + 1 {
            d ^= c[i] & s[UN - i];
        }
        if d == 1 {
            t = c.clone(); //T(D)<-C(D)
            let mut i = 0;
            while i + N - m < len {
                let i1 = (i + N - m) as usize;
                let i0 = i as usize;
                c[i1] ^= b[i0];
                i += 1;
            }
            if L <= (N >> 1) {
                L = N + 1 - L;
                m = N;
                b = t.clone();
            }
        }
        N += 1;
    }
    return L;
}
