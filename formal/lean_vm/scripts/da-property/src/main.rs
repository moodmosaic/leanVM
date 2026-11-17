//! `leanvm-da-property`: LeanDA's encoding, commitment and cell openings, one command per line of
//! standard input, its words separated by tabs, and one result line for each, so that
//! `lake exe da-property` (cli/DaProperty.lean) can check them against the statement's.
//!
//!     build SEED LIMIT N       encode and commit to N blobs, kept; blob `i`'s symbol `s` is
//!                              `symbol(SEED, i, s)` below LIMIT and zero from it on; the commitment
//!     row I FILE               write codeword I, sixteen little-endian bytes a symbol, to FILE
//!     cell I J                 cell J of blob I and its Merkle path, hexadecimal
//!     verify ROOT N I J CELL PATH    `verify_cell`: `true` or `false`
//!
//! A panic is printed as `panic <message>`.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use lean_da::{BLOB_SYMBOLS, Blob, BlobMatrix, CELL_SYMBOLS, MERKLE_PATH_LEN, verify_cell};

/// Word `k` of blob `blob` of seed `seed`: any fixed mixing will do, the Lean driver has the same.
fn word(seed: u64, blob: u64, k: u64) -> u64 {
    seed.wrapping_add(blob.wrapping_mul(0x1_0000_01B3)).wrapping_add(k).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(23) ^ k
}

fn number(s: &str) -> Result<u64, String> {
    s.parse().map_err(|_| format!("not a number: {s}"))
}

fn bytes(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd hexadecimal".into());
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| "not hexadecimal".to_string()))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn run(matrix: &mut Option<BlobMatrix>, line: &[&str]) -> Result<String, String> {
    Ok(match line {
        ["build", seed, limit, n] => {
            let (seed, limit, n) = (number(seed)?, number(limit)? as usize, number(n)?);
            let blobs: Vec<Blob> = (0..n)
                .map(|blob| {
                    std::array::from_fn(|s| {
                        if s < limit {
                            (word(seed, blob, 2 * s as u64) as u128) | ((word(seed, blob, 2 * s as u64 + 1) as u128) << 64)
                        } else {
                            0
                        }
                    })
                })
                .collect();
            debug_assert_eq!(blobs.first().map_or(BLOB_SYMBOLS, |b| b.len()), BLOB_SYMBOLS);
            match BlobMatrix::build(&blobs) {
                Ok(built) => {
                    let root = hex(&built.commitment());
                    *matrix = Some(built);
                    root
                }
                Err(error) => format!("refused {error}"),
            }
        }
        ["row", i, file] => {
            let matrix = matrix.as_ref().ok_or("no matrix")?;
            let row = matrix.row(number(i)? as usize).ok_or("no such row")?;
            let out: Vec<u8> = row.iter().flat_map(|symbol| symbol.to_le_bytes()).collect();
            std::fs::write(file, out).map_err(|e| format!("{file}: {e}"))?;
            "ok".into()
        }
        ["cell", i, j] => {
            let matrix = matrix.as_ref().ok_or("no matrix")?;
            let (i, j) = (number(i)? as usize, number(j)? as usize);
            let cell = matrix.cell(i, j).ok_or("no such cell")?;
            let path = matrix.merkle_path_for_cell(i, j).ok_or("no such path")?;
            let cell: Vec<u8> = cell.iter().flat_map(|symbol| symbol.to_le_bytes()).collect();
            format!("{} {}", hex(&cell), hex(path.as_flattened()))
        }
        ["verify", root, n, i, j, cell, path] => {
            let root: [u8; 32] = bytes(root)?.try_into().map_err(|_| "length")?;
            let cell = bytes(cell)?;
            let path = bytes(path)?;
            if cell.len() != 16 * CELL_SYMBOLS || path.len() != 32 * MERKLE_PATH_LEN {
                return Ok("length".into());
            }
            let cell: [u128; CELL_SYMBOLS] =
                std::array::from_fn(|s| u128::from_le_bytes(cell[16 * s..16 * s + 16].try_into().unwrap()));
            let path: [[u8; 32]; MERKLE_PATH_LEN] =
                std::array::from_fn(|k| path[32 * k..32 * k + 32].try_into().unwrap());
            verify_cell(&root, number(n)? as usize, number(i)? as usize, number(j)? as usize, &cell, &path).to_string()
        }
        _ => return Err(format!("unknown command: {}", line.join(" "))),
    })
}

fn main() {
    // Panics are reported on the result line, not on standard error.
    std::panic::set_hook(Box::new(|_| {}));
    let mut matrix = None;
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("read standard input");
        if line.is_empty() {
            continue;
        }
        let words: Vec<&str> = line.split('\t').collect();
        let result = match catch_unwind(AssertUnwindSafe(|| run(&mut matrix, &words))) {
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
