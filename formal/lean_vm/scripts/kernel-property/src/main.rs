//! `leanvm-kernel-property`: leanVM's vector kernels, one command per line of standard
//! input, its words separated by tabs, and one result line for each, so that
//! `lake exe kernel-property` (cli/KernelProperty.lean) can compare them with the Lean
//! definitions on generated inputs.
//!
//! Words are decimal `u64`s. An `E` word is two limbs, low first; a `K` word one limb.
//! The kernels run as compiled for this CPU: leanVM's `.cargo/config.toml` sets
//! `target-cpu=native`, so the wide arms are the ones this machine has.
//!
//!     caps                        the kernel arms compiled into this binary
//!     x8mul a.. b..  x8sum a.. b..  x8mix c.. k..  x8ie a.. b..  x8de a.. b..
//!                              the experimental tree's x8, coefficient layout
//!     p8mul a.. b..  p8sum a.. b..  p8lanes a.. b..  p8eo a.. b..
//!     p8base c.. k.. p8bspl c k..  p8xor t.. v..  p8fp a.. b.. t
//!     p8fl v.. t     p8mt a.. b.. c.. d..  p8ml a.. b..
//!                              the experimental tree's f128x8, plane layout
//!     bfold w.. r..   sixty-four `E` weights, `r..` rows of eight bytes, up to 64
//!     bcols w.. c..   sixty-four `E` weights, sixty-four rows as eight byte columns
//!                              the experimental tree's bit folds
//!     s8mul a.. b..  s8sum a.. b..  s8base c.. k..  (the stable tree's lanes)
//!     clmul p.. q..   wide p.. q..  mwide p q       carry-less products of words
//!     mapb i.. x..    mapf i.. x..  tbits x..       the byte operations
//!     twords r..      tbytes r..
//!
//! `a..`, `b..`, `c..`, `d..` and `v..` are eight `E` words, sixteen limbs; `t..` two
//! limbs; `k..`, `i..` and `r..` (mapb) `K` words or bytes, one limb each; `p..`, `q..`,
//! `w..`, `w..` (bfold, bcols) and `x..` as the line says. Results are space-separated
//! limbs, in the line's element order. A panic is printed as `panic <message>`.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use experimental_primitives::bit_fold::BitFold;
use experimental_primitives::field::f128x8 as pf;
use experimental_primitives::field::x8 as xf;
use experimental_primitives::field::{F128 as XE, F64 as XK};
use stable_primitives::field::lanes as sl;
use stable_primitives::field::{F128 as SE, F64 as SK};

/// One command's answer, or its panic.
fn run(line: &str) -> String {
    let words: Vec<String> = line.split('\t').map(ToString::to_string).collect();
    match catch_unwind(AssertUnwindSafe(|| dispatch(&words))) {
        Ok(s) => s,
        Err(e) => format!(
            "panic {}",
            e.downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default()
        ),
    }
}

fn dispatch(words: &[String]) -> String {
    let (cmd, rest) = words.split_first().expect("a command has a word");
    match cmd.as_str() {
        "caps" => caps(),
        // The experimental x8, coefficient layout.
        "x8mul" => e8s(x8mul(rest)),
        "x8sum" => e2(x8sum(rest)),
        "x8mix" => e8s(x8mix(rest)),
        "x8ie" => e16s(x8ie(rest)),
        "x8de" => e16s(x8de(rest)),
        // The experimental f128x8, plane layout.
        "p8mul" => e8s(p8mul(rest)),
        "p8sum" => e2(p8sum(rest)),
        "p8lanes" => e8s(p8lanes(rest)),
        "p8eo" => e16s(p8eo(rest)),
        "p8base" => e8s(p8base(rest)),
        "p8bspl" => e8s(p8bspl(rest)),
        "p8xor" => e8s(p8xor(rest)),
        "p8fp" => e8s(p8fp(rest)),
        "p8fl" => e8s(p8fl(rest)),
        "p8mt" => e4(p8mt(rest)),
        "p8ml" => e2(p8ml(rest)),
        // The experimental bit folds.
        "bfold" => bfold(rest),
        "bcols" => bcols(rest),
        // The stable lanes.
        "s8mul" => e8s(s8mul(rest)),
        "s8sum" => e2(s8sum(rest)),
        "s8base" => e8s(s8base(rest)),
        // Carry-less products of words.
        "clmul" => w8(clmul(rest)),
        "wide" => w2(wide(rest)),
        "mwide" => w4(mwide(rest)),
        // The byte operations.
        "mapb" => w8(mapb(rest)),
        "mapf" => w32(mapf(rest)),
        "tbits" => w8(tbits(rest)),
        "twords" => w64(twords(rest)),
        "tbytes" => w128(tbytes(rest)),
        _ => return "error unknown command".into(),
    }
}

/// The arms compiled into this binary, one word each.
fn caps() -> String {
    let mut arms = Vec::new();
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "vpclmulqdq"
    ))]
    arms.push("x8");
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512bw",
        target_feature = "avx512f",
        target_feature = "vpclmulqdq"
    ))]
    arms.push("p8-avx512");
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "vpclmulqdq",
        not(target_feature = "avx512f")
    ))]
    arms.push("p8-avx2");
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))]
    arms.push("gfni");
    #[cfg(not(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    )))]
    arms.push("bitfold-lookup");
    if arms.is_empty() {
        arms.push("portable");
    }
    arms.join(" ")
}

// ---------------------------------------------------------------------------
// Parsing and printing
// ---------------------------------------------------------------------------

/// The next `n` words as `u64`s.
fn limbs(rest: &[String], i: &mut usize, n: usize) -> Result<[u64; 128], String> {
    let mut out = [0u64; 128];
    for k in 0..n {
        *i += 1;
        out[k] = rest
            .get(*i - 1)
            .and_then(|w| w.parse().ok())
            .ok_or_else(|| "a missing or bad word".to_string())?;
    }
    Ok(out)
}

/// Eight `T`s from sixteen limbs, low first.
fn e8<T, F: Fn(u64, u64) -> T>(rest: &[String], i: &mut usize, mk: F) -> Result<[T; 8], String> {
    let w = limbs(rest, i, 16)?;
    Ok(core::array::from_fn(|k| mk(w[2 * k], w[2 * k + 1])))
}

/// Eight `u64`s from eight words.
fn w8u(rest: &[String], i: &mut usize) -> Result<[u64; 8], String> {
    let w = limbs(rest, i, 8)?;
    Ok(w[..8].try_into().unwrap())
}

fn expect_end(rest: &[String], i: &mut usize) -> Result<(), String> {
    if *i == rest.len() {
        Ok(())
    } else {
        Err("too many words".to_string())
    }
}

/// The two limbs of an `E` word, either tree's.
trait Limbs {
    fn limbs(&self) -> (u64, u64);
}
impl Limbs for XE {
    fn limbs(&self) -> (u64, u64) {
        (self.c0, self.c1)
    }
}
impl Limbs for SE {
    fn limbs(&self) -> (u64, u64) {
        (self.c0, self.c1)
    }
}

fn e2<T: Limbs>(x: T) -> String {
    let (a, b) = x.limbs();
    format!("{a} {b}")
}
fn e4<T: Limbs>(x: [T; 2]) -> String {
    e_words(x)
}
fn e8s<T: Limbs>(x: [T; 8]) -> String {
    e_words(x)
}
fn e16s<T: Limbs>(x: [T; 16]) -> String {
    e_words(x)
}
fn e_words<T: Limbs>(x: impl IntoIterator<Item = T>) -> String {
    x.into_iter()
        .map(|x| {
            let (a, b) = x.limbs();
            format!("{a} {b}")
        })
        .collect::<Vec<_>>()
        .join(" ")
}
fn w2(x: u128) -> String {
    format!("{} {}", (x & u128::from(u64::MAX)) as u64, (x >> 64) as u64)
}
fn w4(x: [u64; 2]) -> String {
    format!("{} {}", x[0], x[1])
}
fn w8(x: [u64; 8]) -> String {
    x.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ")
}
fn w32(x: [u64; 32]) -> String {
    x.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ")
}
fn w64(x: [u64; 64]) -> String {
    x.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ")
}
fn w128(x: [u64; 128]) -> String {
    x.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ")
}

// ---------------------------------------------------------------------------
// The experimental x8, coefficient layout
// ---------------------------------------------------------------------------

fn x8mul(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    let va = xf::F128x8::load(&a);
    let vb = xf::F128x8::load(&b);
    (va * vb).to_array()
}

fn x8sum(rest: &[String]) -> XE {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    xf::F128x8::load(&a)
        .mul_sum(xf::F128x8::load(&b))
        .reduce()
}

fn x8mix(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let c = e8(rest, &mut i, XE::new).unwrap();
    let k = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    let mut m = xf::Mixed8::ZERO;
    m.add(xf::F128x8::load(&c), xf::F64x8::load(&k.map(XK)));
    m.reduce().to_array()
}

fn x8ie(rest: &[String]) -> [XE; 16] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    let (x, y) = xf::F128x8::interleave(xf::F128x8::load(&a), xf::F128x8::load(&b));
    let mut out = [XE::ZERO; 16];
    out[..8].copy_from_slice(&x.to_array());
    out[8..].copy_from_slice(&y.to_array());
    out
}

fn x8de(rest: &[String]) -> [XE; 16] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    let (x, y) = xf::F128x8::deinterleave(xf::F128x8::load(&a), xf::F128x8::load(&b));
    let mut out = [XE::ZERO; 16];
    out[..8].copy_from_slice(&x.to_array());
    out[8..].copy_from_slice(&y.to_array());
    out
}

// ---------------------------------------------------------------------------
// The experimental f128x8, plane layout
// ---------------------------------------------------------------------------

fn p8mul(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    (pf::F128x8::from_array(&a) * pf::F128x8::from_array(&b)).to_array()
}

fn p8sum(rest: &[String]) -> XE {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    pf::F128x8::from_array(&a)
        .mul_unreduced(pf::F128x8::from_array(&b))
        .reduce()
}

fn p8lanes(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    pf::F128x8::from_array(&a)
        .mul_unreduced(pf::F128x8::from_array(&b))
        .reduce_lanes()
        .to_array()
}

fn p8eo(rest: &[String]) -> [XE; 16] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    let (x, y) = pf::F128x8::even_odd(pf::F128x8::from_array(&a), pf::F128x8::from_array(&b));
    let mut out = [XE::ZERO; 16];
    out[..8].copy_from_slice(&x.to_array());
    out[8..].copy_from_slice(&y.to_array());
    out
}

fn p8base(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let c = e8(rest, &mut i, XE::new).unwrap();
    let k = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    pf::F128x8::from_array(&c)
        .mul_base_unreduced(pf::F64x8::from_array(&k.map(XK)))
        .reduce_lanes()
        .to_array()
}

fn p8bspl(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let c = e2p(rest, &mut i);
    let k = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    pf::mul_base_splat8(c, &k.map(XK)).reduce_lanes().to_array()
}

fn p8xor(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let mut t = e8(rest, &mut i, XE::new).unwrap();
    let v = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    pf::xor_into8(&mut t, &v);
    t
}

fn p8fp(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    let t = e2p(rest, &mut i);
    expect_end(rest, &mut i).unwrap();
    pf::fold_pairs8_ext(&a, &b, t)
}

fn p8fl(rest: &[String]) -> [XE; 8] {
    let mut i = 0;
    let v = e8(rest, &mut i, XE::new).unwrap();
    let t = e2p(rest, &mut i);
    expect_end(rest, &mut i).unwrap();
    pf::fold_lones8_ext(&v, t)
}

fn p8mt(rest: &[String]) -> [XE; 2] {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    let c = e8(rest, &mut i, XE::new).unwrap();
    let d = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    let (m0, m1) = pf::msg_terms8_ext(&a, &b, &c, &d);
    [m0.reduce(), m1.reduce()]
}

fn p8ml(rest: &[String]) -> XE {
    let mut i = 0;
    let a = e8(rest, &mut i, XE::new).unwrap();
    let b = e8(rest, &mut i, XE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    pf::msg_lone8_ext(&a, &b).reduce()
}

/// Two limbs as one experimental `E`.
fn e2p(rest: &[String], i: &mut usize) -> XE {
    let w = limbs(rest, i, 2).unwrap();
    XE::new(w[0], w[1])
}

// ---------------------------------------------------------------------------
// The experimental bit folds
// ---------------------------------------------------------------------------

/// Sixty-four weights from the line, the fold's smallest row.
fn weights64(rest: &[String], i: &mut usize) -> [XE; 64] {
    core::array::from_fn(|_| {
        let w = limbs(rest, i, 2).unwrap();
        XE::new(w[0], w[1])
    })
}

/// `bfold w.. r..`: sixty-four weights, `n` rows of eight bytes, `1 <= n <= 64`; the 64
/// folded words and one word, whether the rows past the input all folded to zero.
fn bfold(rest: &[String]) -> String {
    let mut i = 0;
    let weights = weights64(rest, &mut i);
    let n = (rest.len() - i) / 8;
    if n < 1 || n > 64 || (rest.len() - i) % 8 != 0 {
        return "error a bad row count".into();
    }
    let mut rows: [[u8; 8]; 64] = core::array::from_fn(|_| [0; 8]);
    for p in 0..n {
        for b in 0..8 {
            let w = limbs(rest, &mut i, 1).unwrap()[0];
            if w > 255 {
                return "error a byte past 255".into();
            }
            rows[p][b] = w as u8;
        }
    }
    let fold = BitFold::new(&weights);
    let mut out = [XE::ZERO; 64];
    fold.fold_block::<8>(&rows[..n], &mut out);
    // The rows past the input fold to zero; say so with the last word.
    let tail = out[n..].iter().all(|x| x.c0 == 0 && x.c1 == 0) as u64;
    let mut ws: Vec<String> = out
        .iter()
        .flat_map(|x| [x.c0, x.c1].map(|w| w.to_string()))
        .collect();
    ws.push(tail.to_string());
    ws.join(" ")
}

/// `bcols w.. c..`: sixty-four weights, 64 rows as eight byte columns, `c[j][p]` byte `j` of
/// row `p`; the 64 folded words.
fn bcols(rest: &[String]) -> String {
    let mut i = 0;
    let weights = weights64(rest, &mut i);
    let mut cols: [[u8; 64]; 8] = core::array::from_fn(|_| [0; 64]);
    for b in 0..8 {
        for p in 0..64 {
            let w = limbs(rest, &mut i, 1).unwrap()[0];
            if w > 255 {
                return "error a byte past 255".into();
            }
            cols[b][p] = w as u8;
        }
    }
    let fold = BitFold::new(&weights);
    let mut out = [XE::ZERO; 64];
    fold.fold_columns::<8>(&cols, &mut out);
    out.iter()
        .flat_map(|x| [x.c0, x.c1].map(|w| w.to_string()))
        .collect::<Vec<_>>()
        .join(" ")
}

// ---------------------------------------------------------------------------
// The stable lanes
// ---------------------------------------------------------------------------

fn s8mul(rest: &[String]) -> [SE; 8] {
    let mut i = 0;
    let a = e8(rest, &mut i, SE::new).unwrap();
    let b = e8(rest, &mut i, SE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    (sl::F128x8::load(&a) * sl::F128x8::load(&b)).to_array()
}

fn s8sum(rest: &[String]) -> SE {
    let mut i = 0;
    let a = e8(rest, &mut i, SE::new).unwrap();
    let b = e8(rest, &mut i, SE::new).unwrap();
    expect_end(rest, &mut i).unwrap();
    sl::F128x8::load(&a)
        .mul_unreduced(sl::F128x8::load(&b))
        .sum()
}

fn s8base(rest: &[String]) -> [SE; 8] {
    let mut i = 0;
    let c = e8(rest, &mut i, SE::new).unwrap();
    let k = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    sl::F128x8::load(&c)
        .mul_base(sl::F64x8::load(&k.map(SK)))
        .to_array()
}

// ---------------------------------------------------------------------------
// Carry-less products of words
// ---------------------------------------------------------------------------

/// The low halves of eight 128-bit products.
fn clmul(rest: &[String]) -> [u64; 8] {
    let mut i = 0;
    let p = w8u(rest, &mut i).unwrap();
    let q = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    sl::clmul8_low(p, q)
}

/// The sum of eight 128-bit products, as low then high.
fn wide(rest: &[String]) -> u128 {
    let mut i = 0;
    let p = w8u(rest, &mut i).unwrap();
    let q = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    sl::Wide8::mul(p, q).sum()
}

/// One 128-bit product, as low then high.
fn mwide(rest: &[String]) -> [u64; 2] {
    let mut i = 0;
    let p = limbs(rest, &mut i, 1).unwrap()[0];
    let q = limbs(rest, &mut i, 1).unwrap()[0];
    expect_end(rest, &mut i).unwrap();
    let x = sl::mul_wide(p, q);
    [x as u64, (x >> 64) as u64]
}

// ---------------------------------------------------------------------------
// The byte operations
// ---------------------------------------------------------------------------

/// Every byte of `x..` through the map of images `i..` (eight bytes).
fn mapb(rest: &[String]) -> [u64; 8] {
    let mut i = 0;
    let images = w8u(rest, &mut i).unwrap().map(|b| b as u8);
    let x = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    sl::map_bytes(&sl::ByteMap::new(images), x)
}

/// Every 16-bit field of `x..` through the map of images `i..` (sixteen words), four
/// planes of eight words.
fn mapf(rest: &[String]) -> [u64; 32] {
    let mut i = 0;
    let images = limbs(rest, &mut i, 16).unwrap();
    let images = core::array::from_fn(|k| images[k] as u32);
    let x = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    let planes = sl::map_fields(&sl::Linear16::new(images), x);
    let mut out = [0u64; 32];
    for (p, plane) in planes.iter().enumerate() {
        out[p * 8..p * 8 + 8].copy_from_slice(plane);
    }
    out
}

/// The bit transpose of eight words.
fn tbits(rest: &[String]) -> [u64; 8] {
    let mut i = 0;
    let x = w8u(rest, &mut i).unwrap();
    expect_end(rest, &mut i).unwrap();
    sl::transpose_bits(x)
}

/// The word transpose of eight rows of eight words.
fn twords(rest: &[String]) -> [u64; 64] {
    let mut i = 0;
    let rows: [[u64; 8]; 8] = core::array::from_fn(|_| w8u(rest, &mut i).unwrap());
    expect_end(rest, &mut i).unwrap();
    let t = sl::transpose_words(&rows);
    let mut out = [0u64; 64];
    for (r, row) in t.iter().enumerate() {
        out[r * 8..r * 8 + 8].copy_from_slice(row);
    }
    out
}

/// The byte transpose of sixteen rows of eight words, sixty-four 128-bit words: word `n`
/// holds the sixteen bytes of its column, byte `b` at `8 * b`, each word as low then high.
fn tbytes(rest: &[String]) -> [u64; 128] {
    let mut i = 0;
    let rows: [[u64; 8]; 16] = core::array::from_fn(|_| w8u(rest, &mut i).unwrap());
    expect_end(rest, &mut i).unwrap();
    let t = sl::transpose_bytes(&rows);
    let mut out = [0u64; 128];
    for (n, w) in t.iter().enumerate() {
        out[2 * n] = *w as u64;
        out[2 * n + 1] = (*w >> 64) as u64;
    }
    out
}

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        if line.is_empty() {
            continue;
        }
        writeln!(out, "{}", run(&line)).expect("the driver reads every line");
        out.flush().expect("the driver reads every line");
    }
}
