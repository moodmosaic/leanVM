# Findings of the property tests

What the generated-input tests (lean-hedgehog) found in the Rust, with how to see each again. The
tests are `formal/lean_vm/tests/LeanVMTests/Property/` (Lean alone) and three drivers that run the
Rust beside the Lean definitions, each with a Rust harness on a line protocol:

| driver | harness | what it compares |
| --- | --- | --- |
| `lake exe wire-property` | `scripts/wire-diff` | the wire encoding, Lean and Rust, on generated proofs and mutations |
| `lake exe rust-property` | `scripts/rust-property` | fields, multilinear helpers, Keccak, the streamed hasher, the prover's sponge |
| `lake exe zkdsl-property` | `scripts/zkdsl-property`, `scripts/rust-verifier-cli` | the zkDSL compiler and both provers on generated programs; the Lean and the Rust verifier on their proofs |
| `lake exe scheme-property` | `scripts/scheme-property` | leanSPHINCS and leanXMSS, the Rust against the statement's, and the leanXMSS signer's cache |
| `lake exe da-property` | `scripts/da-property` | LeanDA's codewords, commitments and cell openings against the statement's |
| `lake exe agg-property` | `scripts/agg-property` | the aggregation through the public API: which claims a proof verifies for, bad children, altered signatures |

To build and run one, from `formal/lean_vm` (lean-hedgehog beside leanVM, see `lakefile.toml`):

```sh
cargo build --release --manifest-path scripts/rust-property/Cargo.toml
lake build rust-property
lake exe rust-property                                   # 100 cases of each check
lake exe rust-property scripts/rust-property/target/release/leanvm-rust-property 3000
```

A failing check prints the smallest input found, what each side answered, and a line
`recheck SIZE ⟨A, B⟩`: the size and seed of that one case. Every run draws a fresh seed, so a
finding below gives the check to run and the input to expect, not a seed.

## 1. `mle_eval_par` of the experimental tree panics below three variables (not reachable)

- **Where**: `crates/experimental_prover/primitives/src/multilinear.rs`, `mle_eval_par`:
  `assert!(low_vars >= 3 && table.len().is_multiple_of(1 << low_vars))`.
- **What**: on a table shorter than `2^n` at a point of `n < 3` coordinates it panics. The stable
  tree's `mle_eval_par` returns the value (zero for the empty table), and both doc comments say only
  that a shorter table "is zero past its end, which must be a whole number of rows".
- **See it**: `lake exe rust-property`; the check "mle_eval_par of an empty table of fewer than
  three variables" fails on its first case, shrunk to the empty point:

  ```
  ✗ mle_eval_par of an empty table of fewer than three variables failed after 1 test and 1 shrink.
      forAll
      tree s
      tree x
      === failed
        lhs: "panic assertion failed: low_vars >= 3 && table.len().is_multiple_of(1 << low_vars)"
        rhs: "0 0"
  ```

  or by hand: `printf 'mle\tx\t0\t0\n' | scripts/rust-property/target/release/leanvm-rust-property`
  (the stable tree, `mle\ts\t0\t0`, prints `0 0`).
- **Is it a bug in a proof?** No, as far as reading shows. The three callers in the experimental
  tree never pass such a table: `lean_vm_core/src/leaf.rs` (two calls) passes columns of exactly
  `2^kappa` words, which take the early return to `mle_eval`, and `pcs/src/ood.rs` passes a point of
  at least 16 coordinates. The smallest programs (one instruction, two memory cells, every table
  empty) prove and verify on the experimental prover.
- **Worth doing**: say the precondition in the doc comment, or make the two trees agree. Low
  priority.

## What agreed, and at how many cases

No disagreement but the one above, at these counts (2026-11-17, x86-64 with AVX-512):

| check | cases |
| --- | --- |
| wire encoding, Lean and Rust, random sequences of mutations | 100,000 sequences |
| fields `K`, `E` in the verifier and both prover trees; batched products | 3,000 each |
| `eq_eval`, `eq_table`, `poly_eval`, `mle_eval`, `mle_eval_par`, powers, indices, `fold`, `dot` | 3,000 each |
| Keccak-f[1600] one and many states, Keccak-256 at once and batched | 3,000 each |
| streamed `Hasher`, prover's `FiatShamirState` with grind (state machines) | 3,000 sequences each |
| leanSPHINCS: signs what verifies; verdicts on altered inputs | 300 each |
| leanXMSS: verdicts on altered inputs; the signer over 12 bottom trees | 300; 31 sequences |
| LeanDA: codewords, commitments, openings altered or not | 20; 6; 20 |
| zkDSL programs: published words, refusal of another input, same proof in both trees | 10,000 programs |
| zkDSL programs with a statement that cannot hold | 10,000 programs |
| the Lean and the Rust verifier on generated programs' proofs, altered or not | 301 proofs |
| aggregation: own claims and no others, bytes, bad children, forged signatures | 150 sequences |

Not covered: the vector kernels by themselves (`lanes`, `f128x8`, `x4`, `x8`, `bit_fold`), `pcs` and
`keccak_gkr` except through whole proofs, `OutputClaims::Only`, hints and a few zkDSL constructs
(`StackBuf` parameters and returns, recursion, `keccak_cells` with `state=` and `final=`,
`keccak` with `cap=` and `pad_tail=`), and a guest given a witness no honest prover builds: the
drivers reach the guest only through `aggregate`, whose hints come from the crates' own code.
