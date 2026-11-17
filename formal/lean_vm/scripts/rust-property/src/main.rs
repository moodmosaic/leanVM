//! `leanvm-rust-property`: leanVM's production primitives, one command per line of standard input,
//! its words separated by tabs, and one result line for each, so that `lake exe rust-property`
//! (cli/RustProperty.lean) can compare them with the Lean definitions on generated inputs.
//!
//! Words are decimal `u64`s, bytes lowercase hexadecimal (`-` for none). The implementation `v` is
//! the verifier's field, `s` the stable prover's, `x` the experimental prover's.
//!
//!     kmul IMPL a b            ksq IMPL a           kinv IMPL a          kpow IMPL a e
//!     emul IMPL a0 a1 b0 b1    esq IMPL a0 a1       einv IMPL a0 a1      emulk IMPL a0 a1 k
//!     epow a0 a1 e             (the verifier's)
//!     emul2 a.. b..  emul4 a.. b..   (the experimental tree's, 2 or 4 products at once)
//!     keccakf w0..w24          one state, `keccak256::keccak_f`
//!     keccakfmany w..          any number of states, `keccak256::keccak_f_many`
//!     hash HEX                 `keccak256::hash`
//!     hashmany LEN HEX         `keccak256::hash_many` of inputs of LEN bytes
//!     hnew / hupdate HEX / hfinal     one `keccak256::Hasher`, kept between lines
//!     snew iv0..iv3 p0..p3 / sobserve c0 c1 / ssample / sgrind BITS
//!                              one `fiat_shamir_prover::FiatShamirState`, kept between lines
//!
//!     eqeval T n r.. x..       eqtable T r..        eqbig T r..  (`eq_table` against `eq_table_serial`)
//!     polyeval T point c..     mle T seed len point..
//!     fold width t e..         dot a.. b..          (the stable tree's)
//!     powers T n x0 x1         gpowers T n          gpow T i     indexmle T z..
//!     mulg T a                 divg T a
//!                              the multilinear helpers of a prover tree `T`, `s` or `x`; `mle` is of
//!                              the table `table_word(seed, i)`, `i < len`, zero after
//!
//! A panic is printed as `panic <message>`.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use experimental_primitives::field as xf;
use fiat_shamir_prover::{FiatShamirState, Sequential};
use stable_primitives::field as sf;
use verifier::{E, K};

struct Session {
    hasher: keccak256::Hasher,
    sponge: Option<FiatShamirState<E>>,
}

fn word(s: &str) -> Result<u64, String> {
    s.parse().map_err(|_| format!("not a word: {s}"))
}

fn words(ws: &[&str]) -> Result<Vec<u64>, String> {
    ws.iter().map(|w| word(w)).collect()
}

fn bytes(s: &str) -> Result<Vec<u8>, String> {
    if s == "-" {
        return Ok(Vec::new());
    }
    if s.len() % 2 != 0 {
        return Err("odd hexadecimal".into());
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| "not hexadecimal".to_string()))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "-".into();
    }
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn join(ws: impl IntoIterator<Item = u64>) -> String {
    ws.into_iter().map(|w| w.to_string()).collect::<Vec<_>>().join(" ")
}

fn k(imp: &str, op: &str, a: u64, b: u64) -> Result<u64, String> {
    Ok(match (imp, op) {
        ("v", "mul") => (K(a) * K(b)).0,
        ("v", "sq") => K(a).square().0,
        ("v", "inv") => K(a).inv().0,
        ("s", "mul") => (sf::F64(a) * sf::F64(b)).0,
        ("s", "sq") => sf::F64(a).square().0,
        ("s", "inv") => sf::F64(a).inv().0,
        ("s", "pow") => sf::F64(a).pow(b as u128).0,
        ("x", "mul") => (xf::F64(a) * xf::F64(b)).0,
        ("x", "sq") => xf::F64(a).square().0,
        ("x", "inv") => xf::F64(a).inv().0,
        ("x", "pow") => xf::F64(a).pow(b as u128).0,
        _ => return Err(format!("no {op} in {imp}")),
    })
}

fn e(imp: &str, op: &str, a: [u64; 2], b: [u64; 2]) -> Result<[u64; 2], String> {
    Ok(match imp {
        "v" => {
            let (x, y) = (E::new(a[0], a[1]), E::new(b[0], b[1]));
            let r = match op {
                "mul" => x * y,
                "sq" => x.square(),
                "inv" => x.inv(),
                "mulk" => x * K(b[0]),
                "pow" => x.pow(b[0]),
                _ => return Err(format!("no {op} in {imp}")),
            };
            [r.c0, r.c1]
        }
        "s" => {
            let (x, y) = (sf::F128::new(a[0], a[1]), sf::F128::new(b[0], b[1]));
            match op {
                "mul" => x * y,
                "sq" => x.square(),
                "inv" => x.inv(),
                "mulk" => x.mul_base(sf::F64(b[0])),
                _ => return Err(format!("no {op} in {imp}")),
            }
            .to_limbs()
        }
        "x" => {
            let (x, y) = (xf::F128::new(a[0], a[1]), xf::F128::new(b[0], b[1]));
            match op {
                "mul" => x * y,
                "sq" => x.square(),
                "inv" => x.inv(),
                "mulk" => x.mul_base(xf::F64(b[0])),
                _ => return Err(format!("no {op} in {imp}")),
            }
            .to_limbs()
        }
        _ => return Err(format!("no implementation {imp}")),
    })
}

/// Word `i` of the table of seed `seed`: any fixed mixing will do, the Lean driver has the same.
fn table_word(seed: u64, i: u64) -> u64 {
    seed.wrapping_add(i).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(23) ^ i
}

/// The multilinear helpers of one prover tree, on words.
macro_rules! tree {
    ($name:ident, $krate:ident) => {
        fn $name(line: &[&str]) -> Result<String, String> {
            use $krate::field::{self, F64, F128};
            use $krate::multilinear as ml;
            let es = |ws: &[u64]| -> Vec<F128> { ws.chunks(2).map(|c| F128::new(c[0], c[1])).collect() };
            let out = |zs: &[F128]| join(zs.iter().flat_map(|z| z.to_limbs()));
            Ok(match line {
                ["eqeval", n, rest @ ..] => {
                    let (n, ws) = (word(n)? as usize, es(&words(rest)?));
                    out(&[ml::eq_eval(&ws[..n], &ws[n..])])
                }
                ["eqtable", rest @ ..] => out(&ml::eq_table(&es(&words(rest)?))),
                ["eqbig", rest @ ..] => {
                    let r = es(&words(rest)?);
                    if ml::eq_table(&r) == ml::eq_table_serial(&r) { "same".into() } else { "differs".into() }
                }
                ["polyeval", p0, p1, rest @ ..] => {
                    out(&[ml::poly_eval(&es(&words(rest)?), F128::new(word(p0)?, word(p1)?))])
                }
                ["mle", seed, len, rest @ ..] => {
                    let (seed, len, point) = (word(seed)?, word(len)?, es(&words(rest)?));
                    let table: Vec<F64> = (0..len).map(|i| F64(table_word(seed, i))).collect();
                    let value = if table.len() == 1 << point.len() {
                        ml::mle_eval(&table, &point)
                    } else {
                        ml::mle_eval_par(&table, &point)
                    };
                    out(&[value])
                }
                ["powers", n, x0, x1] => out(&field::powers(F128::new(word(x0)?, word(x1)?), word(n)? as usize)),
                ["gpowers", n] => join(field::g_powers(word(n)? as usize).iter().map(|a| a.0)),
                ["gpow", i] => field::g_pow(word(i)? as usize).0.to_string(),
                ["indexmle", rest @ ..] => out(&[field::index_mle(&es(&words(rest)?))]),
                ["mulg", a] => field::mul_by_g(F64(word(a)?)).0.to_string(),
                ["divg", a] => field::div_by_g(F64(word(a)?)).0.to_string(),
                _ => return Err(format!("unknown command: {}", line.join(" "))),
            })
        }
    };
}

tree!(stable_tree, stable_primitives);
tree!(experimental_tree, experimental_primitives);

fn xs(ws: &[u64]) -> Vec<xf::F128> {
    ws.chunks(2).map(|c| xf::F128::new(c[0], c[1])).collect()
}

const TREE_OPS: [&str; 11] = [
    "eqeval", "eqtable", "eqbig", "polyeval", "mle", "powers", "gpowers", "gpow", "indexmle", "mulg", "divg",
];

fn run(session: &mut Session, line: &[&str]) -> Result<String, String> {
    Ok(match line {
        ["kmul", imp, a, b] => k(imp, "mul", word(a)?, word(b)?)?.to_string(),
        ["ksq", imp, a] => k(imp, "sq", word(a)?, 0)?.to_string(),
        ["kinv", imp, a] => k(imp, "inv", word(a)?, 0)?.to_string(),
        ["kpow", imp, a, n] => k(imp, "pow", word(a)?, word(n)?)?.to_string(),
        ["emul", imp, a0, a1, b0, b1] => join(e(imp, "mul", [word(a0)?, word(a1)?], [word(b0)?, word(b1)?])?),
        ["esq", imp, a0, a1] => join(e(imp, "sq", [word(a0)?, word(a1)?], [0, 0])?),
        ["einv", imp, a0, a1] => join(e(imp, "inv", [word(a0)?, word(a1)?], [0, 0])?),
        ["emulk", imp, a0, a1, b] => join(e(imp, "mulk", [word(a0)?, word(a1)?], [word(b)?, 0])?),
        ["epow", a0, a1, n] => join(e("v", "pow", [word(a0)?, word(a1)?], [word(n)?, 0])?),
        ["emul2", rest @ ..] if rest.len() == 8 => {
            let ws = words(rest)?;
            let (a, b) = (xs(&ws[..4]), xs(&ws[4..]));
            join(xf::mul2([a[0], a[1]], [b[0], b[1]]).iter().flat_map(|x| x.to_limbs()))
        }
        ["emul4", rest @ ..] if rest.len() == 16 => {
            let ws = words(rest)?;
            let (a, b) = (xs(&ws[..8]), xs(&ws[8..]));
            join(xf::mul4([a[0], a[1], a[2], a[3]], [b[0], b[1], b[2], b[3]]).iter().flat_map(|x| x.to_limbs()))
        }
        [op, "s", rest @ ..] if TREE_OPS.contains(op) => stable_tree(&[&[*op], rest].concat())?,
        [op, "x", rest @ ..] if TREE_OPS.contains(op) => experimental_tree(&[&[*op], rest].concat())?,
        ["fold", width, t0, t1, rest @ ..] => {
            let ws = words(rest)?;
            let table: Vec<sf::F128> = ws.chunks(2).map(|c| sf::F128::new(c[0], c[1])).collect();
            let folded = stable_primitives::multilinear::fold(&table, word(width)? as usize, sf::F128::new(word(t0)?, word(t1)?));
            join(folded.iter().flat_map(|z| z.to_limbs()))
        }
        ["dot", rest @ ..] if rest.len() % 4 == 0 => {
            let ws = words(rest)?;
            let es = |ws: &[u64]| -> Vec<sf::F128> { ws.chunks(2).map(|c| sf::F128::new(c[0], c[1])).collect() };
            let (a, b) = (es(&ws[..ws.len() / 2]), es(&ws[ws.len() / 2..]));
            join(sf::dot(&a, &b).to_limbs())
        }
        ["keccakf", rest @ ..] if rest.len() == 25 => {
            let mut state: [u64; 25] = words(rest)?.try_into().unwrap();
            keccak256::keccak_f(&mut state);
            join(state)
        }
        ["keccakfmany", rest @ ..] if rest.len() % 25 == 0 => {
            let ws = words(rest)?;
            let mut states: Vec<[u64; 25]> = ws.chunks(25).map(|c| c.try_into().unwrap()).collect();
            keccak256::keccak_f_many(&mut states);
            join(states.into_iter().flatten())
        }
        ["hash", data] => hex(&keccak256::hash(&bytes(data)?)),
        ["hashmany", len, data] => {
            let (len, data) = (word(len)? as usize, bytes(data)?);
            let n = if len == 0 { 0 } else { data.len() / len };
            let mut out = vec![0u8; 32 * n];
            keccak256::hash_many(&data[..n * len], len, &mut out);
            hex(&out)
        }
        ["hnew"] => {
            session.hasher = keccak256::Hasher::new();
            "ok".into()
        }
        ["hupdate", data] => {
            session.hasher.update(&bytes(data)?);
            "ok".into()
        }
        ["hfinal"] => hex(&session.hasher.finalize()),
        ["snew", rest @ ..] if rest.len() == 8 => {
            let ws = words(rest)?;
            session.sponge =
                Some(FiatShamirState::new(ws[..4].try_into().unwrap(), ws[4..].try_into().unwrap()));
            "ok".into()
        }
        ["sobserve", c0, c1] => {
            session.sponge.as_mut().ok_or("no sponge")?.observe(E::new(word(c0)?, word(c1)?));
            "ok".into()
        }
        ["ssample"] => {
            let x = session.sponge.as_mut().ok_or("no sponge")?.sample();
            join([x.c0, x.c1])
        }
        ["sgrind", bits] => match session.sponge.as_mut().ok_or("no sponge")?.grind::<Sequential>(word(bits)? as u32) {
            Some(nonce) => nonce.to_string(),
            None => "none".into(),
        },
        _ => return Err(format!("unknown command: {}", line.join(" "))),
    })
}

fn main() {
    // Panics are reported on the result line, not on standard error.
    std::panic::set_hook(Box::new(|_| {}));
    let mut session = Session { hasher: keccak256::Hasher::new(), sponge: None };
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("read standard input");
        if line.is_empty() {
            continue;
        }
        let ws: Vec<&str> = line.split('\t').collect();
        let result = match catch_unwind(AssertUnwindSafe(|| run(&mut session, &ws))) {
            Ok(Ok(result)) => result,
            Ok(Err(error)) => format!("error {error}"),
            Err(payload) => format!(
                "panic {}",
                payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "a panic without a message".into())
                    .replace('\n', " ")
            ),
        };
        writeln!(out, "{result}").expect("write standard output");
        out.flush().expect("flush standard output");
    }
}
