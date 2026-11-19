import Hedgehog
import LeanVM.Wire.Encoding
import LeanVM.Cli.Common

/-!
# The wire encoding, the Lean and the Rust, on generated proofs

`scripts/wire-diff.py` runs the Lean transcription of the proof's wire encoding (`lake exe
wire-diff`) and the Rust (`scripts/wire-diff`, `leanvm-rust-wire`) on the same bytes: the honest
proofs of the fixtures and a fixed list of mutations of each. This driver does the same on proofs it
generates and on sequences of mutations it generates, and when the two disagree it shrinks the
sequence to the fewest and smallest steps that still do.

It is a state machine test with effects (lean-hedgehog, `Hedgehog.Command`, in `IO`). The system
under test is the two batch processes and the files they read and write; the model is the bytes
under test and `Proof.fromBytes` and `Proof.toBytes` evaluated in this process. Each step changes
the bytes and then requires that

* the Lean and the Rust give the same verdict on them, `none` or `some`;
* that verdict is this process's own, so the driver's file handling adds or loses nothing;
* when they decode, both write the same proof, and each re-encodes it to the bytes it was given
  (the one encoding).

A step is a command, a type of its own: a new kind of mutation is a new command and edits no other.

    lake build wire-diff wire-property
    cargo build --release --manifest-path scripts/wire-diff/Cargo.toml
    lake exe wire-property                # one step of each kind, in the order given
    MADHOUSE=1 lake exe wire-property     # 100 random sequences of steps
    MADHOUSE=1 lake exe wire-property scripts/wire-diff/target/release/leanvm-rust-wire 100000
-/

open Hedgehog LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Cli

namespace WireProperty

/-! ## The two processes -/

/-- A batch process: one command line in, one result line out. -/
structure Driver where
  stdin : IO.FS.Handle
  stdout : IO.FS.Handle

/-- Start `path --batch`. -/
def Driver.start (path : String) : IO Driver := do
  let child ← IO.Process.spawn
    { cmd := path, args := #["--batch"], stdin := .piped, stdout := .piped, stderr := .inherit }
  pure ⟨child.stdin, child.stdout⟩

/-- Send a command, its words separated by tabs, and read its result line. -/
def Driver.ask (driver : Driver) (words : List String) : IO String := do
  driver.stdin.putStrLn ("\t".intercalate words)
  driver.stdin.flush
  let line ← driver.stdout.getLine
  if line.isEmpty then throw (IO.userError "the process gave no answer")
  pure (String.ofList (line.toList.filter (· ≠ '\n')))

/-- What a step works with: the two processes and a directory for their files. -/
structure Context where
  lean : Driver
  rust : Driver
  dir : System.FilePath

/-- The model: the bytes under test. -/
structure Session where
  bytes : List UInt8 := []
  deriving Inhabited

/-! ## The model's side -/

/-- Keccak-f[1600] in `Id`, the permutation decoding hashes with. -/
def permutation (state : KeccakState) : Id KeccakState := pure (keccakF1600 state)

/-- The plain rendering of a proof, as `wire-diff` writes it. -/
def plain (proof : Proof) : List UInt8 :=
  LeanVM.Prover.u32Bytes proof.stream.length ++ proof.stream.flatMap E.toBytes ++
    phasesBytes proof.openings

/-- The bytes of a list, as a file's. -/
def toArray (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-! ## What every step requires -/

/-- The two processes and the model agree on `bytes`. -/
def agree (ctx : Context) (bytes : List UInt8) : TestT IO Unit := do
  let wire := (ctx.dir / "wire.bin").toString
  let leanPlain := (ctx.dir / "lean.plain").toString
  let rustPlain := (ctx.dir / "rust.plain").toString
  evalIO (IO.FS.writeBinFile wire (toArray bytes))
  let lean ← evalIO (ctx.lean.ask ["decode", wire, leanPlain])
  let rust ← evalIO (ctx.rust.ask ["decode", wire, rustPlain])
  annotate s!"Lean: {lean}; Rust: {rust}"
  lean === rust
  match Proof.fromBytes (m := Id) permutation bytes with
  | none => lean === "none"
  | some proof =>
    lean === "some reencode-ok"
    let fromLean ← evalIO (IO.FS.readBinFile leanPlain)
    let fromRust ← evalIO (IO.FS.readBinFile rustPlain)
    ensure (fromLean.toList == plain proof) "the Lean process wrote another proof than the model's"
    ensure (fromRust.toList == plain proof) "the Rust process wrote another proof than the model's"

/-! ## Generators -/

/-- A 64-bit word: small ones often, any one otherwise. -/
def genLane : Gen UInt64 :=
  Gen.choice [Gen.integral (.exponential 0 (UInt64.ofNat (2 ^ 64 - 1))),
    Gen.integral (.constant 0 (UInt64.ofNat (2 ^ 64 - 1)))]

def genK : Gen K := K.ofLane <$> genLane

def genE : Gen E := Gen.zipWith E.ofLimbs genK genK

/-- The levels of a Merkle tree over Keccak-256, leaves first, up to `height`. -/
def levels (leaves : List Digest) : ℕ → List (List Digest)
  | 0 => [leaves]
  | height + 1 =>
    let parents := (List.range (leaves.length / 2)).map fun i ↦
      keccak256 (digestBytes (leaves.getD (2 * i) default) ++
        digestBytes (leaves.getD (2 * i + 1) default))
    leaves :: levels parents height

/-- The paths one tree over `rows` opens at `queries`. -/
def openPhase (rows : List (List K)) (height : ℕ) (queries : List ℕ) : List Opening :=
  let tree := levels (rows.map fun row ↦ keccak256 (row.flatMap K.toBytes)) height
  queries.map fun q ↦
    ⟨q, rows.getD q [], (List.range height).map fun level ↦
      (tree.getD level []).getD ((q >>> level) ^^^ 1) default⟩

/-- A phase: a tree of height at most 4 over rows of at most 4 words, opened at 1 to 5 positions,
some of them perhaps the same. -/
def genPhase : Gen (List Opening) := do
  let height ← Gen.nat (.linear 0 4)
  let width ← Gen.nat (.linear 0 4)
  let rows ← Gen.list (.singleton (2 ^ height)) (Gen.list (.singleton width) genK)
  let queries ← Gen.list (.linear 1 5) (Gen.nat (.constant 0 (2 ^ height - 1)))
  pure (openPhase rows height queries)

/-- An honest proof: a short stream and at most 3 phases. -/
def genProof : Gen Proof :=
  Gen.zipWith Proof.mk (Gen.list (.linear 0 4) genE) (Gen.list (.linear 0 3) genPhase)

/-! ## The steps -/

/-- Start from an honest proof's encoding. -/
structure Honest where
  ctx : Context
  proof : Proof

instance : Command Honest Session Context IO where
  apply _ c _ := do
    let bytes := c.proof.toBytes
    agree c.ctx bytes
    -- An honest proof decodes to itself (`LeanVM.Wire.roundTrip`, here on the compiled code).
    (Proof.fromBytes (m := Id) permutation bytes).map plain === some (plain c.proof)
    pure ⟨bytes⟩
  label c := s!"HONEST({c.proof.stream.length} scalars, {c.proof.openings.map (·.length)} paths)"
  build ctx := Honest.mk ctx <$> genProof

/-- Flip one bit. -/
structure Flip where
  ctx : Context
  position : ℕ
  bit : ℕ

instance : Command Flip Session Context IO where
  check _ _ s := !s.bytes.isEmpty
  apply _ c s := do
    let i := c.position % s.bytes.length
    let bytes := s.bytes.set i (s.bytes.getD i 0 ^^^ (1 <<< UInt8.ofNat c.bit))
    agree c.ctx bytes
    pure ⟨bytes⟩
  label c := s!"FLIP({c.position}, {c.bit})"
  build ctx := Flip.mk ctx <$> Gen.nat (.linear 0 4096) <*> Gen.nat (.constant 0 7)

/-- Keep only the first bytes. -/
structure Cut where
  ctx : Context
  kept : ℕ

instance : Command Cut Session Context IO where
  check _ _ s := !s.bytes.isEmpty
  apply _ c s := do
    let bytes := s.bytes.take (c.kept % s.bytes.length)
    agree c.ctx bytes
    pure ⟨bytes⟩
  label c := s!"CUT({c.kept})"
  build ctx := Cut.mk ctx <$> Gen.nat (.linear 0 4096)

/-- Add bytes at the end. -/
structure Append where
  ctx : Context
  extra : List UInt8

instance : Command Append Session Context IO where
  apply _ c s := do
    let bytes := s.bytes ++ c.extra
    agree c.ctx bytes
    pure ⟨bytes⟩
  label c := s!"APPEND({c.extra})"
  build ctx := Append.mk ctx <$> Gen.list (.linear 1 40) (Gen.integral (.constant 0 255))

/-- Write a little-endian 32-bit word over four bytes: a count or a size made wrong. -/
structure Overwrite where
  ctx : Context
  position : ℕ
  word : ℕ

instance : Command Overwrite Session Context IO where
  check _ _ s := s.bytes.length ≥ 4
  apply _ c s := do
    let i := c.position % (s.bytes.length - 3)
    let bytes := s.bytes.take i ++ LeanVM.Prover.u32Bytes c.word ++ s.bytes.drop (i + 4)
    agree c.ctx bytes
    pure ⟨bytes⟩
  label c := s!"OVERWRITE({c.position}, {c.word})"
  build ctx := Overwrite.mk ctx <$> Gen.nat (.linear 0 4096)
    <*> Gen.choice [Gen.nat (.linear 0 300), Gen.nat (.exponential 0 (2 ^ 32 - 1))]

/-- Encode again what the bytes decode to, in both processes: the one encoding. -/
structure Reencode where
  ctx : Context

instance : Command Reencode Session Context IO where
  check _ _ s := (Proof.fromBytes (m := Id) permutation s.bytes).isSome
  apply _ c s := do
    let ctx := c.ctx
    match Proof.fromBytes (m := Id) permutation s.bytes with
    | none => pure s
    | some proof =>
      let input := (ctx.dir / "proof.plain").toString
      let leanWire := (ctx.dir / "lean.wire").toString
      let rustWire := (ctx.dir / "rust.wire").toString
      evalIO (IO.FS.writeBinFile input (toArray (plain proof)))
      (← evalIO (ctx.lean.ask ["encode", input, leanWire])) === "encoded roundtrip-ok"
      (← evalIO (ctx.rust.ask ["encode", input, rustWire])) === "encoded roundtrip-ok"
      ensure ((← evalIO (IO.FS.readBinFile leanWire)).toList == s.bytes)
        "the Lean process encoded to other bytes"
      ensure ((← evalIO (IO.FS.readBinFile rustWire)).toList == s.bytes)
        "the Rust process encoded to other bytes"
      pure s
  label _ := "REENCODE"
  build ctx := pure ⟨ctx⟩

/-- The scenario: in the order given, an honest proof, its re-encoding, then one mutation of each
kind; in madhouse mode, random sequences of these. -/
def wire (mode : Mode) (ctx : Context) : Property IO :=
  scenario mode ctx [Command.gen Honest, Command.gen Reencode, Command.gen Flip,
    Command.gen Overwrite, Command.gen Append, Command.gen Cut, Command.gen Reencode]

end WireProperty

/-- The driver: the Rust binary's path may be given, and after it the number of sequences;
`MADHOUSE=1` selects random sequences. -/
def main (args : List String) : IO UInt32 := do
  let rust := args.head?.getD "scripts/wire-diff/target/release/leanvm-rust-wire"
  let tests := (args[1]?.bind String.toNat?)
  let ctx : WireProperty.Context :=
    { lean := ← WireProperty.Driver.start ".lake/build/bin/wire-diff"
      rust := ← WireProperty.Driver.start rust
      dir := ← IO.FS.createTempDir }
  let mode ← Mode.fromEnv
  let ok ← checkGroup s!"wire encoding, Lean and Rust ({repr mode})"
    [("the two agree on every step",
      let property := WireProperty.wire mode ctx
      tests.elim property property.withTests)]
  IO.FS.removeDirAll ctx.dir
  return if ok then 0 else 1
