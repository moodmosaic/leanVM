//! `leanvm-scheme-property`: the two signature schemes, one command per line of standard input,
//! its words separated by tabs, and one result line for each, so that `lake exe scheme-property`
//! (cli/SchemeProperty.lean) can compare them with the statement's schemes.
//!
//! Bytes are lowercase hexadecimal. A key seed and a message are 32 bytes.
//!
//!     skeygen SEED             leanSPHINCS: the public key
//!     ssign SEED MESSAGE       the signature
//!     sverify KEY MESSAGE SIG  `true` or `false`
//!     xkeygen SEED             leanXMSS: the public key; the expanded secret key is kept
//!     xprepare LEAF            build and cache the bottom tree of a leaf, in the kept key
//!     xsign MESSAGE LEAF       the signature at a leaf, with the kept key
//!     xverify KEY MESSAGE SIG  `true` or `false`
//!
//! A key or a signature of another length than its own is `length`. A panic is printed as
//! `panic <message>`.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

fn bytes(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd hexadecimal".into());
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| "not hexadecimal".to_string()))
        .collect()
}

fn fixed<const N: usize>(s: &str) -> Result<[u8; N], String> {
    bytes(s)?.try_into().map_err(|_| "length".to_string())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn run(key: &mut Option<lean_xmss::LeanXmssExpandedSecretKey>, line: &[&str]) -> Result<String, String> {
    Ok(match line {
        ["skeygen", seed] => hex(&lean_sphincs::key_gen(&fixed(seed)?).to_bytes()),
        ["ssign", seed, message] => hex(&lean_sphincs::sign(&fixed(seed)?, &fixed(message)?).to_bytes()),
        ["sverify", public, message, signature] => {
            let public = lean_sphincs::LeanSphincsPublicKey::from_bytes(&fixed(public)?);
            let signature = lean_sphincs::LeanSphincsSignature::from_bytes(&fixed(signature)?);
            lean_sphincs::verify(&public, &fixed(message)?, &signature).to_string()
        }
        ["xkeygen", seed] => {
            let (secret, public) = lean_xmss::key_gen(&fixed(seed)?);
            *key = Some(secret);
            hex(&public.to_bytes())
        }
        ["xprepare", leaf] => {
            key.as_ref().ok_or("no key")?.prepare(leaf.parse().map_err(|_| "not a leaf")?);
            "ok".into()
        }
        ["xsign", message, leaf] => {
            let leaf = leaf.parse().map_err(|_| "not a leaf")?;
            hex(&lean_xmss::sign(key.as_ref().ok_or("no key")?, &fixed(message)?, leaf).to_bytes())
        }
        ["xverify", public, message, signature] => {
            let public = lean_xmss::LeanXmssPublicKey::from_bytes(&fixed(public)?);
            let signature = lean_xmss::LeanXmssSignature::from_bytes(&fixed(signature)?);
            lean_xmss::verify(&public, &fixed(message)?, &signature).to_string()
        }
        _ => return Err(format!("unknown command: {}", line.join(" "))),
    })
}

fn main() {
    // Panics are reported on the result line, not on standard error.
    std::panic::set_hook(Box::new(|_| {}));
    let mut key = None;
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("read standard input");
        if line.is_empty() {
            continue;
        }
        let words: Vec<&str> = line.split('\t').collect();
        let result = match catch_unwind(AssertUnwindSafe(|| run(&mut key, &words))) {
            Ok(Ok(result)) => result,
            Ok(Err(error)) => error,
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
