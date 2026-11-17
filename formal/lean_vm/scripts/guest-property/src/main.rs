//! `leanvm-guest-property`: the recursion guest on witnesses changed one hint at a time, one command
//! per line of standard input, its words separated by tabs, and one result line for each, so that
//! `lake exe guest-property` (cli/GuestProperty.lean) can ask which hints the guest constrains.
//!
//!     capture KIND             aggregate a node of a kind and keep the witness and the public input
//!                              the guest ran on: `sphincs`, `xmss`, `blob`, `both` (a signature of
//!                              each scheme and a blob), or `parent` (a node over two such children);
//!                              prints the hint streams, `name:entries:words` each
//!     change STREAM ENTRY WORD c0 c1   run the guest on the kept witness with one word of one entry
//!                              of one stream set to the word of limbs `c0`, `c1`: `refused <why>`,
//!                              `accepted`, or `same` if the word was that already
//!     flip STREAM ENTRY WORD BIT   run it with one bit of that word flipped (0..63 limb 0, 64..127
//!                              limb 1): likewise
//!     swap STREAM ENTRY OTHER  run it with two entries of one stream exchanged: likewise
//!     prove STREAM ENTRY WORD c0 c1    as `change`, then prove and verify what was accepted:
//!                              `proved`, or what refused
//!
//! Streams, entries and words are numbers, as `capture` printed them. A panic is printed as
//! `panic <message>`.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;

use aggregation::{AggregateClaims, AggregateProof, OutputClaims, aggregate, unified_guest};
use stable_lean_vm_core::{StableProver, cpu};
use stable_primitives::field::F128;
use verifier::E;

type Witness = Vec<(String, Vec<Vec<E>>)>;

/// What the last proof was asked to prove.
static CAPTURED: Mutex<Option<(Witness, [E; 2])>> = Mutex::new(None);

/// The stable prover, recording the witness and the public input it is handed.
struct Capture;

impl isa::Prover for Capture {
    fn init() {
        StableProver::init();
    }

    fn prove(
        program: &isa::Program,
        witness: &[(String, Vec<Vec<E>>)],
        public_input: [E; 2],
        log_inv_rate: usize,
    ) -> Result<(verifier::Proof, isa::Stats), String> {
        *CAPTURED.lock().unwrap() = Some((witness.to_vec(), public_input));
        StableProver::prove(program, witness, public_input, log_inv_rate)
    }

    fn map_collect<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
        StableProver::map_collect(n, f)
    }

    fn combine_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        StableProver::combine_rows(rows, weights)
    }

    fn dot_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        StableProver::dot_rows(rows, weights)
    }
}

type Node = (AggregateClaims, AggregateProof);

/// A node of signer `k`: its leanSPHINCS signature, its leanXMSS signature, its blob, as asked.
fn leaf(k: u8, sphincs: bool, xmss: bool, blob: bool) -> Result<Node, String> {
    let message = [k; 32];
    let raw_sphincs = if sphincs {
        vec![(lean_sphincs::key_gen(&[k; 32]), message, lean_sphincs::sign(&[k; 32], &message))]
    } else {
        Vec::new()
    };
    let raw_xmss = if xmss {
        let (secret, public) = lean_xmss::key_gen(&[k; 32]);
        vec![(public, message, lean_xmss::sign(&secret, &message, 7))]
    } else {
        Vec::new()
    };
    let matrix = if blob {
        let blob: lean_da::Blob = std::array::from_fn(|i| i as u128 ^ k as u128);
        Some(lean_da::BlobMatrix::build(&[blob]).map_err(|e| e.to_string())?)
    } else {
        None
    };
    aggregate::<Capture>(&[], raw_xmss, raw_sphincs, matrix.as_ref(), OutputClaims::All, 2)
        .map(|(claims, proof, _)| (claims, proof))
        .map_err(|e| format!("{e:?}"))
}

fn to_f128(witness: &Witness) -> Vec<(String, Vec<Vec<F128>>)> {
    witness
        .iter()
        .map(|(name, entries)| {
            let entries = entries.iter().map(|entry| entry.iter().map(|x| F128::new(x.c0, x.c1)).collect());
            (name.clone(), entries.collect())
        })
        .collect()
}

/// Run the guest on a witness: `accepted`, or why it was refused; with `prove`, prove and verify too.
fn guest(witness: &Witness, public_input: [E; 2], prove: bool) -> String {
    let public = public_input.map(|x| F128::new(x.c0, x.c1));
    let witness = to_f128(witness);
    if let Err(error) = cpu::execute(unified_guest(), &witness, public) {
        return format!("refused {:?} at {}", error.fault, error.site).replace('\n', " ").chars().take(300).collect();
    }
    if !prove {
        return "accepted".into();
    }
    match cpu::prove(unified_guest(), &witness, public, 2) {
        Err(error) => format!("refused in proving: {error:?}").replace('\n', " "),
        Ok((proof, _)) => match cpu::verify(unified_guest(), &public, &proof) {
            Ok(_) => "proved".into(),
            Err(error) => format!("refused by the verifier: {error:?}"),
        },
    }
}

fn number(s: &str) -> Result<usize, String> {
    s.parse().map_err(|_| format!("not a number: {s}"))
}

fn run(line: &[&str]) -> Result<String, String> {
    Ok(match line {
        ["capture", kind] => {
            match *kind {
                "sphincs" => leaf(1, true, false, false)?,
                "xmss" => leaf(1, false, true, false)?,
                "blob" => leaf(1, false, false, true)?,
                "both" => leaf(1, true, true, true)?,
                "parent" => {
                    let children = [leaf(1, true, false, true)?, leaf(2, true, false, false)?];
                    aggregate::<Capture>(&children, Vec::new(), Vec::new(), None, OutputClaims::All, 2)
                        .map(|(claims, proof, _)| (claims, proof))
                        .map_err(|e| format!("{e:?}"))?
                }
                _ => return Err("no such kind".into()),
            };
            let captured = CAPTURED.lock().unwrap();
            let (witness, public_input) = captured.as_ref().ok_or("nothing captured")?;
            if guest(witness, *public_input, false) != "accepted" {
                return Err("the guest refuses the honest witness".into());
            }
            witness
                .iter()
                .map(|(name, entries)| {
                    format!("{name}:{}:{}", entries.len(), entries.iter().map(Vec::len).max().unwrap_or(0))
                })
                .collect::<Vec<_>>()
                .join(" ")
        }
        [op @ ("change" | "prove"), stream, entry, word, c0, c1] => {
            let captured = CAPTURED.lock().unwrap();
            let (witness, public_input) = captured.as_ref().ok_or("nothing captured")?;
            let mut witness = witness.clone();
            let entries = &mut witness.get_mut(number(stream)?).ok_or("no such stream")?.1;
            let entry = entries.get_mut(number(entry)?).ok_or("no such entry")?;
            let slot = entry.get_mut(number(word)?).ok_or("no such word")?;
            let value = E::new(c0.parse().map_err(|_| "not a limb")?, c1.parse().map_err(|_| "not a limb")?);
            if *slot == value {
                return Ok("same".into());
            }
            *slot = value;
            guest(&witness, *public_input, *op == "prove")
        }
        ["flip", stream, entry, word, bit] => {
            let captured = CAPTURED.lock().unwrap();
            let (witness, public_input) = captured.as_ref().ok_or("nothing captured")?;
            let mut witness = witness.clone();
            let entries = &mut witness.get_mut(number(stream)?).ok_or("no such stream")?.1;
            let entry = entries.get_mut(number(entry)?).ok_or("no such entry")?;
            let slot = entry.get_mut(number(word)?).ok_or("no such word")?;
            let bit = number(bit)? % 128;
            *slot = if bit < 64 { E::new(slot.c0 ^ (1 << bit), slot.c1) } else { E::new(slot.c0, slot.c1 ^ (1 << (bit - 64))) };
            guest(&witness, *public_input, false)
        }
        ["swap", stream, entry, other] => {
            let captured = CAPTURED.lock().unwrap();
            let (witness, public_input) = captured.as_ref().ok_or("nothing captured")?;
            let mut witness = witness.clone();
            let entries = &mut witness.get_mut(number(stream)?).ok_or("no such stream")?.1;
            let (a, b) = (number(entry)?, number(other)?);
            if a >= entries.len() || b >= entries.len() {
                return Err("no such entry".into());
            }
            if entries[a] == entries[b] {
                return Ok("same".into());
            }
            entries.swap(a, b);
            guest(&witness, *public_input, false)
        }
        _ => return Err(format!("unknown command: {}", line.join(" "))),
    })
}

fn main() {
    // Panics are reported on the result line, not on standard error.
    std::panic::set_hook(Box::new(|_| {}));
    <Capture as isa::Prover>::init();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("read standard input");
        if line.is_empty() {
            continue;
        }
        let words: Vec<&str> = line.split('\t').collect();
        let result = match catch_unwind(AssertUnwindSafe(|| run(&words))) {
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
