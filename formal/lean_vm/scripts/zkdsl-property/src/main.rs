//! `leanvm-zkdsl-property`: a zkDSL program through the compiler and a prover, one command per line
//! of standard input, its words separated by tabs, and one result line for each, so that
//! `lake exe zkdsl-property` (cli/ZkdslProperty.lean) can check programs it generates.
//!
//!     exec T SOURCE p0c0 p0c1 p1c0 p1c1     parse, compile and execute
//!     prove T SOURCE p0c0 p0c1 p1c0 p1c1    then prove and verify
//!
//! `T` is the prover tree, `s` (stable) or `x` (experimental); `SOURCE` a file; the last four words
//! the two public-input words' limbs, decimal. The result is `ok` (after `prove`, followed by the
//! hexadecimal Keccak-256 of the proof's wire bytes), or the stage that refused and why:
//! `parse-error`, `compile-panic`, `execute-error`, `prove-error`, `verify-error`, `panic`.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

fn word(s: &str) -> Result<u64, String> {
    s.parse().map_err(|_| format!("not a word: {s}"))
}

fn message(payload: Box<dyn std::any::Any + Send>) -> String {
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "a panic without a message".into())
        .replace('\n', " ")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// One prover tree's `exec` and `prove`.
macro_rules! tree {
    ($name:ident, $core:ident, $primitives:ident) => {
        fn $name(prove: bool, program: &isa::Program, input: [u64; 4]) -> String {
            use $core::cpu;
            use $primitives::field::F128;
            let public = [F128::new(input[0], input[1]), F128::new(input[2], input[3])];
            if !prove {
                return match cpu::execute(program, &[], public) {
                    Ok(_) => "ok".into(),
                    Err(error) => format!("execute-error {error:?}").replace('\n', " "),
                };
            }
            let proof = match cpu::prove(program, &[], public, $core::pcs::TEST_LOG_INV_RATE) {
                Ok((proof, _)) => proof,
                Err(error) => return format!("prove-error {error:?}").replace('\n', " "),
            };
            match cpu::verify(program, &public, &proof) {
                Ok(_) => format!("ok {}", hex(&keccak256::hash(&proof.to_bytes()))),
                Err(error) => format!("verify-error {error:?}").replace('\n', " "),
            }
        }
    };
}

tree!(stable, stable_lean_vm_core, stable_primitives);
tree!(experimental, experimental_lean_vm_core, experimental_primitives);

fn run(line: &[&str]) -> Result<String, String> {
    let [op, tree, source, p0, p1, p2, p3] = line else {
        return Err(format!("unknown command: {}", line.join(" ")));
    };
    let prove = match *op {
        "exec" => false,
        "prove" => true,
        _ => return Err(format!("unknown command: {op}")),
    };
    let input = [word(p0)?, word(p1)?, word(p2)?, word(p3)?];
    let text = std::fs::read_to_string(source).map_err(|e| format!("{source}: {e}"))?;
    let ast = match catch_unwind(AssertUnwindSafe(|| zkdsl_compiler::parse(&text))) {
        Ok(Ok(ast)) => ast,
        Ok(Err(error)) => return Ok(format!("parse-error {error}").replace('\n', " ")),
        Err(payload) => return Ok(format!("parse-panic {}", message(payload))),
    };
    let program = match catch_unwind(AssertUnwindSafe(|| isa::Program::from(zkdsl_compiler::compile(&ast)))) {
        Ok(program) => program,
        Err(payload) => return Ok(format!("compile-panic {}", message(payload))),
    };
    let outcome = catch_unwind(AssertUnwindSafe(|| match *tree {
        "s" => Ok(stable(prove, &program, input)),
        "x" => Ok(experimental(prove, &program, input)),
        _ => Err(format!("no tree {tree}")),
    }));
    match outcome {
        Ok(result) => result,
        Err(payload) => Ok(format!("panic {}", message(payload))),
    }
}

fn main() {
    // Panics are reported on the result line, not on standard error.
    std::panic::set_hook(Box::new(|_| {}));
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("read standard input");
        if line.is_empty() {
            continue;
        }
        let words: Vec<&str> = line.split('\t').collect();
        let result = run(&words).unwrap_or_else(|error| format!("error {error}"));
        writeln!(out, "{result}").expect("write standard output");
        out.flush().expect("flush standard output");
    }
}
