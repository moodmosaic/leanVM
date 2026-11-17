import LeanVMTests.Property.Gen

/-!
# The drivers' readers, one after another

A file of a driver is a sequence of values, each read where the one before it ended. The properties
of `LeanVMTests.Property.Readers` read one value; here a scenario writes several, of different
kinds, and after each write reads the new value back from where it starts, in the middle of what was
written before. A reader that lost its place, or that needed fewer bytes than it took, fails here and
not there.

This is model-based testing with commands as types (`Hedgehog.Command`): the model is the bytes
written so far, and each kind of value is a command of its own, with its generator, its encoding and
its reader together. A driver that gains a reader gains a command, in its own place, and no existing
one changes; that is why this style and not a single type of transitions, which suits a fixed set
such as the six instructions or the sponge's four operations.

`scenario .deterministic` writes one value of each kind in the order given; `scenario .madhouse`
writes random sequences of them, and a failure shrinks to the fewest and smallest values that show
it.
-/

namespace LeanVMTests.Property.Stream

open Hedgehog LeanVM.Parameters LeanVM.Cli LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

/-- The model: the bytes written so far. -/
structure Written where
  bytes : List UInt8 := []
  deriving Inhabited

/-- Write `x` after what is written and read it back from there: the reader gives `x` and stops at
the new end, and it refuses the same bytes with the last one missing. -/
def put {α β : Type} [BEq β] [Repr β] (encode : α → List UInt8) (read : Read α) (view : α → β)
    (x : α) (written : Written) : TestT Id Written := do
  let start := written.bytes.length
  let bytes := written.bytes ++ encode x
  (read (toByteArray bytes) start).map (fun r ↦ (view r.1, r.2)) === some (view x, bytes.length)
  ensure ((read (toByteArray bytes.dropLast) start).isNone) "a value cut short was read"
  pure ⟨bytes⟩

/-- A `u32` count. -/
structure Count where
  value : ℕ

instance : Command Count Written Unit Id where
  apply c := put LeanVM.Prover.u32Bytes (readLE 4) id c.value
  label c := s!"COUNT({c.value})"
  build _ := Count.mk <$> Gen.nat (.exponential 0 (2 ^ 32 - 1))

/-- A `K` word. -/
structure Word where
  value : K

instance : Command Word Written Unit Id where
  apply c := put K.toBytes readK id c.value
  label c := s!"WORD({c.value.lane})"
  build _ := Word.mk <$> genK

/-- A digest. -/
structure Hash where
  value : Digest

instance : Command Hash Written Unit Id where
  apply c := put digestBytes readDigest id c.value
  label c := s!"DIGEST({c.value.toList})"
  build _ := Hash.mk <$> genDigest

/-- A counted list of `K` words, as a leaf is written. -/
structure Words where
  values : List K

instance : Command Words Written Unit Id where
  apply c := put (fun ws ↦ LeanVM.Prover.u32Bytes ws.length ++ ws.flatMap K.toBytes)
    (readCounted readK) id c.values
  label c := s!"WORDS({c.values.map (·.lane)})"
  build _ := Words.mk <$> Gen.list (.linear 0 5) genK

/-- A proof's openings. -/
structure Phases where
  openings : List (List Opening)

instance : Command Phases Written Unit Id where
  apply c := put phasesBytes readPhases view c.openings
  label c := s!"PHASES({reprStr (view c.openings)})"
  build _ := Phases.mk <$> genPhases

/-- Values of every kind, each read back where it was written. -/
def stream (mode : Mode) : Property Id :=
  scenario mode () [Command.gen Count, Command.gen Word, Command.gen Hash, Command.gen Words,
    Command.gen Phases]

#eval check (stream .deterministic) "one value of each kind" (seed := some (.ofNat 0))
#eval check (stream .madhouse) "values in random sequences" (seed := some (.ofNat 0))

end LeanVMTests.Property.Stream
