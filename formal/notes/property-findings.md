# Findings of the property tests

What the generated-input tests (lean-hedgehog) found in the Rust, with how to see each again. The
tests are `formal/lean_vm/tests/LeanVMTests/Property/` (Lean alone) and three drivers that run the
Rust beside the Lean definitions, each with a Rust harness on a line protocol:

| driver | harness | what it compares |
| --- | --- | --- |
| `lake exe wire-property` | `scripts/wire-diff` | the wire encoding, Lean and Rust, on generated proofs and mutations |
| `lake exe rust-property` | `scripts/rust-property` | fields, multilinear helpers, Keccak, the streamed hasher, the prover's sponge |
| `lake exe zkdsl-property` | `scripts/zkdsl-property` | the zkDSL compiler and both provers on generated programs |

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
