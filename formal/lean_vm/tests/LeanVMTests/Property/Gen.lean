import Hedgehog
import LeanVM.Cli.Common
import LeanVM.Protocol.Verifier.Load

/-!
# Generators for the property tests

The property tests (`LeanVMTests.Property.*`) check, on generated inputs, what no theorem states:
the readers and decoders of the command-line drivers and of the verifier's files. Each generator
carries its shrinks (lean-hedgehog), so a failure is reported on a small input: a word shrinks to
`0`, a list to fewer and smaller elements.

A property is checked while its file compiles, `#eval check p name (seed := some (.ofNat 0))`: a
property that fails is an error, with its counterexample, and the fixed seed makes every build
check the same cases.
-/

namespace LeanVMTests.Property

open Hedgehog LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

/-- A 64-bit word: small ones often, any one otherwise; it shrinks to `0`. -/
def genLane : Gen UInt64 :=
  Gen.choice [Gen.integral (.exponential 0 (UInt64.ofNat (2 ^ 64 - 1))),
    Gen.integral (.constant 0 (UInt64.ofNat (2 ^ 64 - 1)))]

/-- A `K` word. -/
def genK : Gen K := K.ofLane <$> genLane

/-- An `E` scalar, of two limbs. -/
def genE : Gen E := Gen.zipWith E.ofLimbs genK genK

/-- A digest, of four lanes. -/
def genDigest : Gen Digest :=
  Gen.zipWith (fun (a, b) (c, d) ↦ #v[a, b, c, d]) (Gen.zip genLane genLane)
    (Gen.zip genLane genLane)

/-- A byte. -/
def genByte : Gen UInt8 := Gen.integral (.constant 0 255)

/-- Some bytes, at most `most`. -/
def genBytes (most : ℕ := 96) : Gen (List UInt8) := Gen.list (.linear 0 most) genByte

/-- A Merkle path: a position below `2^64`, as the plain rendering stores it, a short leaf and a
short path. -/
def genOpening : Gen Opening := do
  let leafIndex ← Gen.nat (.exponential 0 (2 ^ 64 - 1))
  let leaf ← Gen.list (.linear 0 5) genK
  let path ← Gen.list (.linear 0 5) genDigest
  pure ⟨leafIndex, leaf, path⟩

/-- A proof's openings: a few phases of a few paths. -/
def genPhases : Gen (List (List Opening)) :=
  Gen.list (.linear 0 4) (Gen.list (.linear 0 4) genOpening)

/-- An opening as its fields, which compare and print (`Opening` does neither). -/
def Opening.view (o : Opening) : ℕ × List K × List Digest := (o.leafIndex, o.leaf, o.path)

/-- Openings as their fields. -/
def view (openings : List (List Opening)) : List (List (ℕ × List K × List Digest)) :=
  openings.map (·.map Opening.view)

/-- The bytes of a list, as the readers take them. -/
def toByteArray (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

end LeanVMTests.Property
