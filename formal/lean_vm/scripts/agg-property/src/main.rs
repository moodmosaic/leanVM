//! `leanvm-agg-property`: leanVM's aggregation, one command per line of standard input, its words
//! separated by tabs, and one result line for each, so that `lake exe agg-property`
//! (cli/AggProperty.lean) can build trees of proofs and ask what each proves.
//!
//! A signer is a small number `k`, its secret key 32 bytes `k`; a message a small number `m`, 32
//! bytes `m`; a blob a number `s`, its symbol `i` the word `i ^ s`. A list of claims is
//! `k:m,k:m,…`, `-` for none. Proofs are numbered from 0 as they are made.
//!
//!     node CHILDREN SPHINCS XMSS BLOB      aggregate the proofs CHILDREN (`0,2`, `-` for none), the
//!                                          signatures of the two lists, and the blob (`-` for
//!                                          none), with every covered claim as output: `ok N`
//!     forged SPHINCS-CLAIM                 aggregate one leanSPHINCS signature of another message
//!                                          than the claim's: must be an error
//!     altered SCHEME WHAT K M POSITION BYTE   sign message M with signer K (`s` leanSPHINCS, `x`
//!                                          leanXMSS), change one byte of the signature (`sig`),
//!                                          of the message (`msg`) or of the public key (`key`),
//!                                          and aggregate the three: `native=B aggregate=…`, the
//!                                          crate's own `verify` of them and what `aggregate`
//!                                          answered, or `same` if the byte was that already
//!     badchild N SPHINCS XMSS BLOB         aggregate proof N alone, as a child with these claims:
//!                                          `ok verifies=B`, or `error …`
//!     verify N SPHINCS XMSS BLOB ORDER     whether proof N verifies for these claims, sorted
//!                                          (`sorted`) or as given (`given`): `true` or `false`
//!     bytes N                              the proof through `to_bytes` and `from_bytes`, verified
//!                                          for its own claims: `true`, `false` or `none`
//!     tamper N POSITION BYTE               the proof's bytes with one changed, decoded and verified
//!                                          for its own claims: `true`, `false`, `none`, or `same`
//!                                          if the byte was that already
//!
//! A panic is printed as `panic <message>`.

use std::collections::HashMap;
use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use lean_vm::{AggregateClaims, AggregateProof, OutputClaims, aggregate, lean_da, lean_sphincs, lean_xmss};

#[derive(Default)]
struct Session {
    proofs: Vec<(AggregateClaims, AggregateProof)>,
    xmss: HashMap<u8, (lean_xmss::LeanXmssExpandedSecretKey, lean_xmss::LeanXmssPublicKey)>,
}

type Pairs = Vec<(u8, u8)>;

fn pairs(s: &str) -> Result<Pairs, String> {
    if s == "-" {
        return Ok(Vec::new());
    }
    s.split(',')
        .map(|pair| {
            let (k, m) = pair.split_once(':').ok_or("not a claim")?;
            Ok((k.parse().map_err(|_| "not a signer")?, m.parse().map_err(|_| "not a message")?))
        })
        .collect()
}

fn blob(s: &str) -> Result<Option<lean_da::BlobMatrix>, String> {
    if s == "-" {
        return Ok(None);
    }
    let seed: u128 = s.parse().map_err(|_| "not a blob")?;
    let blob: lean_da::Blob = std::array::from_fn(|i| i as u128 ^ seed);
    Ok(Some(lean_da::BlobMatrix::build(&[blob]).map_err(|e| e.to_string())?))
}

impl Session {
    fn xmss_key(&mut self, k: u8) -> &(lean_xmss::LeanXmssExpandedSecretKey, lean_xmss::LeanXmssPublicKey) {
        self.xmss.entry(k).or_insert_with(|| lean_xmss::key_gen(&[k; lean_xmss::SECRET_KEY_LEN]))
    }

    fn claims(&mut self, sphincs: &Pairs, xmss: &Pairs, da: &str, sorted: bool) -> Result<AggregateClaims, String> {
        let mut claims = AggregateClaims {
            lean_sphincs: sphincs
                .iter()
                .map(|&(k, m)| (lean_sphincs::key_gen(&[k; 32]), [m; 32]))
                .collect(),
            lean_xmss: xmss.iter().map(|&(k, m)| (self.xmss_key(k).1, [m; 32])).collect(),
            da_commitment: blob(da)?.map(|matrix| matrix.commitment()),
        };
        if sorted {
            claims.lean_sphincs.sort();
            claims.lean_sphincs.dedup();
            claims.lean_xmss.sort();
            claims.lean_xmss.dedup();
        }
        Ok(claims)
    }

    fn run(&mut self, line: &[&str]) -> Result<String, String> {
        Ok(match line {
            ["node", children, sphincs, xmss, da] => {
                let children: Vec<(AggregateClaims, AggregateProof)> = if *children == "-" {
                    Vec::new()
                } else {
                    children
                        .split(',')
                        .map(|n| {
                            let n: usize = n.parse().map_err(|_| "not a proof")?;
                            self.proofs.get(n).cloned().ok_or("no such proof".to_string())
                        })
                        .collect::<Result<_, String>>()?
                };
                let raw_sphincs = pairs(sphincs)?
                    .into_iter()
                    .map(|(k, m)| (lean_sphincs::key_gen(&[k; 32]), [m; 32], lean_sphincs::sign(&[k; 32], &[m; 32])))
                    .collect();
                let mut raw_xmss = Vec::new();
                for (k, m) in pairs(xmss)? {
                    let (secret, public) = self.xmss_key(k);
                    raw_xmss.push((*public, [m; 32], lean_xmss::sign(secret, &[m; 32], m as u32)));
                }
                let matrix = blob(da)?;
                match aggregate(&children, raw_xmss, raw_sphincs, matrix.as_ref(), OutputClaims::All, 2) {
                    Ok(node) => {
                        self.proofs.push(node);
                        format!("ok {}", self.proofs.len() - 1)
                    }
                    Err(error) => format!("error {error:?}"),
                }
            }
            ["forged", claim] => {
                let [(k, m)] = pairs(claim)?[..] else {
                    return Err("one claim".into());
                };
                let signature = lean_sphincs::sign(&[k; 32], &[m.wrapping_add(1); 32]);
                let raw = vec![(lean_sphincs::key_gen(&[k; 32]), [m; 32], signature)];
                match aggregate(&[], Vec::new(), raw, None, OutputClaims::All, 2) {
                    Ok((claims, proof)) => format!("ok verifies={}", proof.verify(&claims)),
                    Err(error) => format!("error {error:?}"),
                }
            }
            ["altered", scheme, what, k, m, position, byte] => {
                let (k, m): (u8, u8) = (k.parse().map_err(|_| "not a signer")?, m.parse().map_err(|_| "not a message")?);
                let position: usize = position.parse().map_err(|_| "not a position")?;
                let byte: u8 = byte.parse().map_err(|_| "not a byte")?;
                let outcome = |result: Result<(AggregateClaims, AggregateProof), lean_vm::AggregateError>| match result {
                    Ok((claims, proof)) => format!("ok verifies={}", proof.verify(&claims)),
                    Err(error) => format!("error {error:?}"),
                };
                // Change one byte of the part named; `None` if it was that byte already.
                let change = |part: &str, bytes: &mut [u8]| -> Option<()> {
                    if part != *what {
                        return Some(());
                    }
                    let position = position % bytes.len();
                    if bytes[position] == byte {
                        return None;
                    }
                    bytes[position] = byte;
                    Some(())
                };
                let mut message = [m; 32];
                match *scheme {
                    "s" => {
                        let mut key = lean_sphincs::key_gen(&[k; 32]).to_bytes();
                        let mut signature = lean_sphincs::sign(&[k; 32], &message).to_bytes();
                        if change("sig", &mut signature).and(change("msg", &mut message)).and(change("key", &mut key)).is_none() {
                            return Ok("same".into());
                        }
                        let public = lean_sphincs::LeanSphincsPublicKey::from_bytes(&key);
                        let signature = lean_sphincs::LeanSphincsSignature::from_bytes(&signature);
                        let native = lean_sphincs::verify(&public, &message, &signature);
                        let raw = vec![(public, message, signature)];
                        format!("native={native} aggregate={}", outcome(aggregate(&[], Vec::new(), raw, None, OutputClaims::All, 2)))
                    }
                    "x" => {
                        let (secret, public) = self.xmss_key(k);
                        let mut key = public.to_bytes();
                        let mut signature = lean_xmss::sign(secret, &message, m as u32).to_bytes();
                        if change("sig", &mut signature).and(change("msg", &mut message)).and(change("key", &mut key)).is_none() {
                            return Ok("same".into());
                        }
                        let public = lean_xmss::LeanXmssPublicKey::from_bytes(&key);
                        let signature = lean_xmss::LeanXmssSignature::from_bytes(&signature);
                        let native = lean_xmss::verify(&public, &message, &signature);
                        let raw = vec![(public, message, signature)];
                        format!("native={native} aggregate={}", outcome(aggregate(&[], raw, Vec::new(), None, OutputClaims::All, 2)))
                    }
                    _ => return Err("no such scheme".into()),
                }
            }
            ["badchild", n, sphincs, xmss, da] => {
                let claims = self.claims(&pairs(sphincs)?, &pairs(xmss)?, da, true)?;
                let n: usize = n.parse().map_err(|_| "not a proof")?;
                let proof = self.proofs.get(n).ok_or("no such proof")?.1.clone();
                match aggregate(&[(claims, proof)], Vec::new(), Vec::new(), None, OutputClaims::All, 2) {
                    Ok((claims, proof)) => format!("ok verifies={}", proof.verify(&claims)),
                    Err(error) => format!("error {error:?}"),
                }
            }
            ["verify", n, sphincs, xmss, da, order] => {
                let claims = self.claims(&pairs(sphincs)?, &pairs(xmss)?, da, *order == "sorted")?;
                let n: usize = n.parse().map_err(|_| "not a proof")?;
                self.proofs.get(n).ok_or("no such proof")?.1.verify(&claims).to_string()
            }
            ["bytes", n] => {
                let n: usize = n.parse().map_err(|_| "not a proof")?;
                let (claims, proof) = self.proofs.get(n).ok_or("no such proof")?;
                match AggregateProof::from_bytes(&proof.to_bytes()) {
                    Some(decoded) => (decoded.verify(claims) && decoded.to_bytes() == proof.to_bytes()).to_string(),
                    None => "none".into(),
                }
            }
            ["tamper", n, position, byte] => {
                let n: usize = n.parse().map_err(|_| "not a proof")?;
                let (claims, proof) = self.proofs.get(n).ok_or("no such proof")?;
                let mut bytes = proof.to_bytes();
                let position = position.parse::<usize>().map_err(|_| "not a position")? % bytes.len();
                let byte: u8 = byte.parse().map_err(|_| "not a byte")?;
                if bytes[position] == byte {
                    return Ok("same".into());
                }
                bytes[position] = byte;
                match AggregateProof::from_bytes(&bytes) {
                    Some(decoded) => decoded.verify(claims).to_string(),
                    None => "none".into(),
                }
            }
            _ => return Err(format!("unknown command: {}", line.join(" "))),
        })
    }
}

fn main() {
    // Panics are reported on the result line, not on standard error.
    std::panic::set_hook(Box::new(|_| {}));
    lean_vm::setup();
    let mut session = Session::default();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("read standard input");
        if line.is_empty() {
            continue;
        }
        let words: Vec<&str> = line.split('\t').collect();
        let result = match catch_unwind(AssertUnwindSafe(|| session.run(&words))) {
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
