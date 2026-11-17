import LeanVMTests.Property.Gen

/-!
# The drivers' readers (`LeanVM.Cli.Common`)

`readPhases` reads what `phasesBytes` writes, the plain rendering of a proof's openings that
`leanvm-verify` reads and `leanvm-prove` writes. No proof imports that module, and no test read it
back before these. Here: the round trip, at offset zero and after other bytes; that a rendering cut
short is refused; and the hexadecimal digits and bit vectors of the test cases.
-/

namespace LeanVMTests.Property.Readers

open Hedgehog LeanVM.Parameters LeanVM.Cli LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

/-- Openings are read back from their rendering, and the reader stops at its end. -/
def phasesRoundTrip : Property Id := property do
  let openings ← forAllWith (reprStr ∘ view) genPhases
  let bytes := phasesBytes openings
  (readPhases (toByteArray bytes) 0).map (fun r ↦ (view r.1, r.2))
    === some (view openings, bytes.length)

/-- The same after any bytes: a reader starts where it is told to. -/
def phasesAtAnOffset : Property Id := property do
  let before ← forAll (genBytes 24)
  let openings ← forAllWith (reprStr ∘ view) genPhases
  let bytes := before ++ phasesBytes openings
  (readPhases (toByteArray bytes) before.length).map (fun r ↦ (view r.1, r.2))
    === some (view openings, bytes.length)

/-- A rendering cut short anywhere is refused. -/
def phasesCutShort : Property Id := property do
  let openings ← forAllWith (reprStr ∘ view) genPhases
  let bytes := phasesBytes openings
  let kept ← forAll (Gen.nat (.linear 0 (bytes.length - 1)))
  ensure ((readPhases (toByteArray (bytes.take kept)) 0).isNone)

/-- A little-endian word is the lane `wordBytes` wrote, wherever it starts. -/
def wordRoundTrip : Property Id := property do
  let before ← forAll (genBytes 24)
  let w ← forAll genLane
  readLE 8 (toByteArray (before ++ wordBytes w)) before.length
    === some (w.toNat, before.length + 8)

/-- A count is the number `u32Bytes` wrote, below `2^32`. -/
def countRoundTrip : Property Id := property do
  let n ← forAll (Gen.nat (.exponential 0 (2 ^ 32 - 1)))
  readLE 4 (toByteArray (LeanVM.Prover.u32Bytes n)) 0 === some (n, 4)

/-- No reader reads past the end: a word needs all of its bytes. -/
def wordNeedsItsBytes : Property Id := property do
  let bytes ← forAll (genBytes 24)
  let size ← forAll (Gen.nat (.linear 0 16))
  let offset ← forAll (Gen.nat (.linear 0 32))
  (readLE size (toByteArray bytes) offset).isSome === decide (offset + size ≤ bytes.length)

/-- A hexadecimal digit has its value, in either case; no other character has one. -/
def hexDigits : Property Id := property do
  let n ← forAll (Gen.nat (.constant 0 15))
  let digit := (Nat.toDigits 16 n).headD '?'
  hexDigit? digit === some n
  hexDigit? digit.toUpper === some n
  let c ← forAll Gen.unicode
  ensure ((hexDigit? c).isSome == "0123456789abcdefABCDEF".contains c)

/-- Bit `i` of `bitsLE` is bit `i % 8` of byte `i / 8`, and bits past the bytes are zero. -/
def bitsOfBytes : Property Id := property do
  let bytes ← forAll (Gen.list (.linear 0 12) (Gen.nat (.constant 0 255)))
  let width ← forAll (Gen.nat (.linear 0 128))
  let bits := bitsLE width bytes
  ensure ((List.range width).all fun i ↦ bits.getLsbD i == (bytes.getD (i / 8) 0).testBit (i % 8))

#eval check phasesRoundTrip "openings are read back" (seed := some (.ofNat 0))
#eval check phasesAtAnOffset "openings are read back at an offset" (seed := some (.ofNat 0))
#eval check phasesCutShort "openings cut short are refused" (seed := some (.ofNat 0))
#eval check wordRoundTrip "a word is read back" (seed := some (.ofNat 0))
#eval check countRoundTrip "a count is read back" (seed := some (.ofNat 0))
#eval check wordNeedsItsBytes "a word needs its bytes" (seed := some (.ofNat 0))
#eval check hexDigits "hexadecimal digits" (seed := some (.ofNat 0))
#eval check bitsOfBytes "bits of bytes" (seed := some (.ofNat 0))

end LeanVMTests.Property.Readers
