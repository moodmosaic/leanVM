# Findings of the property tests

What the generated-input tests (lean-hedgehog) found in the Rust, with how to see each again. The
tests are `formal/lean_vm/tests/LeanVMTests/Property/` (Lean alone) and eight drivers that run the
Rust beside the Lean definitions, each with a Rust harness on a line protocol:

| driver | harness | what it compares |
| --- | --- | --- |
| `lake exe wire-property` | `scripts/wire-diff` | the wire encoding, Lean and Rust, on generated proofs and mutations |
| `lake exe rust-property` | `scripts/rust-property` | fields, multilinear helpers, Keccak, the streamed hasher, the prover's sponge |
| `lake exe zkdsl-property` | `scripts/zkdsl-property`, `scripts/rust-verifier-cli` | the zkDSL compiler and both provers on generated programs; the Lean and the Rust verifier on their proofs |
| `lake exe scheme-property` | `scripts/scheme-property` | leanSPHINCS and leanXMSS, the Rust against the statement's, and the leanXMSS signer's cache |
| `lake exe da-property` | `scripts/da-property` | LeanDA's codewords, commitments and cell openings against the statement's |
| `lake exe agg-property` | `scripts/agg-property` | the aggregation through the public API: which claims a proof verifies for, bad children, altered signatures |
| `lake exe guest-property` | `scripts/guest-property` | the recursion guest on honest witnesses with one hint word changed |
| `lake exe kernel-property` | `scripts/kernel-property` | the vector kernels: the experimental `x8` and `f128x8`, the bit folds, the stable lanes, the word products, the byte operations |

To build and run one, from `formal/lean_vm`:

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

## 2. Hint words the guest never reads, and a flag read only as zero or not (no bug found)

### 2b. Two words changed at once (no bug found)

- **Where**: the recursion guest (`guests/lean_ethereum.py`), hints of a node with children.
- **What**: changing two words of two hints at once, the guest accepts the pair only when each word
alone is free; a read word stays read, and two free words stay free. `cli/GuestProperty.lean` now
runs a `two words changed together` check (a `change2` line in `scripts/guest-property`, two words
set at once): a pair the guest accepts while one word alone is refused would be a tampering check a
second change bypasses, and that never happened (read words stay read, whatever the other change).
The honest witness's free words are independent, not constrained only together.
- **See it**: `lake exe guest-property`; the new check runs beside the one-word one, 1000 cases a
kind and passing. By hand, `capture parent`, then `change2 0 0 0 16 1 0 1 0 0 1` (a no-op `meta`
word plus a free `merkle_caps` word) answers `accepted`, and `change2 15 0 0 15 0 2 1 0 1 0` (a read
`merkle_children` word plus a free one) `refused`.
- **Is it a bug?** No. The guest's refusal is per-word and not bypassed by a second change, and two
free words together stay free (no pair constrained only together was found). A free word is the
same witness written otherwise, and a proof exists for the same claims either way.
- **Worth doing**: nothing required.

- **Where**: `guests/lean_ethereum.py`, the hints of a node with children.
- **What**: with one word of one hint changed, the guest refuses, except in words it never reads,
  where it accepts any value: the tail of `stream` past a child's proof; the half of each
  `merkle_children` pair on the path's own side (`walk_window` hashes the running node with the
  other half); the `merkle_caps` nodes under a node `merkle_cap_active` leaves inactive, and node
  0's two words; flags 0 and 1 of `merkle_cap_active`; and the pull side's slots of
  `block_group_order` ("pull's slots go unread"). And an active cap node's flag may be any nonzero
  `K` word, since it is only compared with zero.
- **See it**: `lake exe guest-property`; `cli/GuestProperty.lean` states each of these as the rule
  it checks in place of refusal, so the run passes, and any other accepted word fails it. By hand,
  after `capture parent`, `flip 17 0 2 1` (a flag from 1 to 3) answers `accepted` and `flip 17 0 2 0`
  (to 0) `refused`; the stream numbers are the order `capture` prints.
- **Is it a bug?** Not that reading shows. An unread word constrains nothing because nothing
  depends on it, and a nonzero flag is the same witness written otherwise: a proof exists for the
  same claims either way. In the signature and blob nodes no changed word is accepted at all
  (4,000 changes of each kind, and before that every word of the leanSPHINCS and leanXMSS nodes'
  hints, fourteen changes each). One word at a time does not find two hints that are free only
  together, and a run `cpu::execute` refuses is not thereby one no trace exists for.
- **Worth doing**: nothing required. Pinning the flag to 1 would make the witness canonical.

## 3. Vector kernels and `mle_eval_par` on non-multiple-of-8 lengths (no reachable bug)

- **Where**: `mle_eval_par` in both prover trees (`crates/stable_prover/.../multilinear.rs` and
  `crates/experimental_prover/.../multilinear.rs`), and the x4/x8/f128x8 kernels behind it.
- **What**: the mle property only generates table lengths `kept * 2 ^ min point 10`, always a
  multiple of 8, so a non-multiple-of-8 table was untested. By hand both trees **panic** on such a
  length: the experimental `assert!(low_vars >= 3 && table.len().is_multiple_of(1 << low_vars))` and
  the stable `assert!(table.len().is_multiple_of(low.len()))`. A multiple-of-8 but non-power-of-two
  row count (e.g. 3072 = 3 * 1024) evaluates the same in both trees. The kernels themselves are
  called only on whole 4- or 8-lane groups, never a partial one: `leaf.rs` asserts a width a
  multiple of 8, and `gkr.rs` pads a short run with `F128::ONE` (the fold's identity).
- **Is it a bug?** No reachable one. A non-multiple-of-8 table is refused by both trees, and the
  callers (leaf columns of `2^kappa`, ood points of at least 16 coordinates) never pass one.
- **See it**: `printf 'mle\tx\t1\t100\t1 0 ...' | leanvm-rust-property` (13 coordinates) prints
  `panic` for both `x` and `s`; `mle\tx\t1\t2048\t...` and `3072` print the same value.
- **Worth doing**: nothing required; say the precondition in the stable tree's doc comment as the
  experimental's does.

## 4. `pcs` and `keccak_gkr` (no bug found beyond whole proofs)

- **What**: these are only exercised through whole proofs at the guest's sizes, but the Lean
  verifier recomputes Keccak-f and the multilinear evaluations, so a wrong `keccak_gkr` or `pcs`
  would make a proof the verifier rejects. The whole-proof drivers (zkdsl-property, agg-property,
  guest-property) all pass, so the sizes in use are correct. `keccak_gkr` also carries its own
  unit tests (`crates/experimental_prover/keccak_gkr/src/tests.rs`) over many shapes and batch
  sizes, and `gkr.rs` pads a short row run to the fold's identity rather than dropping it.
- **Is it a bug?** No evidence. A size a whole proof never uses could still hide one, but the
  guest's sizes are the production ones and they verify.
- **Worth doing**: a direct differential of `keccak_gkr` against the Lean Keccak at unusual
  depths/batches would close the gap, but it needs an exposed harness.

## What agreed, and at how many cases

No disagreement but the first finding's, at these counts (2026-11-17, x86-64 with AVX-512):

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
| zkDSL programs with the later kinds: multi-block `keccak_cells`, `cap=`, `pad_tail=`, `StackBuf` calls, hints, recursion | 400 programs |
| the Lean and the Rust verifier on generated programs' proofs, altered or not | 301 proofs |
| aggregation: own claims and no others, bytes, tampering, bad children, forged signatures | 300 sequences |
| aggregation asked to prove only part of its claims (`OutputClaims::Only`) | 500 sequences |
| a signature, message or key with one byte changed, given to `aggregate` | 300 |
| the guest on a witness with one hint word changed, five kinds of node | 4,000 each |
| the guest on two words changed at once, five kinds of node | 1,000 each |
| the vector kernels: `x8`, `f128x8`, the bit folds, the stable lanes, the word products, the byte operations | 1,000 each |

Not covered: a direct differential of `pcs`/`keccak_gkr` at unusual depths and batches (4 above),
the experimental `x4` arm, which this machine does not compile (it needs AVX2 without AVX-512),
and a prover that does not run `cpu::execute` at all. The vector kernels are now covered by
`lake exe kernel-property` against the Lean definitions on this machine's arms (the AVX-512 `x8`
and `f128x8`, the GFNI bit folds, the stable lanes, the word products, the byte operations);
the non-multiple-of-8 lengths are probed (3 above: both trees refuse them). The first draft's
oracles were wrong in five places, each caught by a failing run and fixed: the interleave's
second half, the bit fold's byte index, a shift that wraps at 64, the bit transpose's byte order,
and a `bcols` line that sent short rows to a full-block fold. `OutputClaims::Only` is covered by `cli/AggProperty.lean`'s `AggregateOnly` (the first draft's
model was wrong in three places, each caught by a failing run and fixed), witnesses changed in
more than one word by `cli/GuestProperty.lean`'s two-word check (2b above), and the zkDSL
constructs the generator once lacked (hints with witness streams, `StackBuf` parameters and
returns, recursion, `keccak_cells` with `state=` and `final=0`, `keccak` with `cap=` and
`pad_tail=`) are now kinds 29..34 of `cli/ZkdslProperty.lean`, run by `lake exe zkdsl-property`.
The harness's `exec`, `prove` and `export` lines take the prover's witness stream beside the
public input: a name, an entry's length and its limbs, the groups in pop order, a name's groups
its successive entries; a hinted value the program pins and the prover gives wrongly is refused.
