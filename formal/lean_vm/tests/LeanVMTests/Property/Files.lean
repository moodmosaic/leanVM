import LeanVMTests.Property.Gen

/-!
# The verifier's files (`LeanVM.Protocol.Verifier`)

`leanvm-verify` decodes `bytecode.bin`, `public_input.bin` and `stream.bin` with `decodeWords`,
`decodeDigest` and `decodeScalars`. `LeanVM.Protocol.Verifier.Load` proves that what decodes
re-encodes to the same bytes; the other direction, that what is encoded decodes to itself, is checked
here, with what the decoders refuse. The last property compares the two little-endian readers of the
tree, the files' on lists and the drivers' on byte arrays, which are written independently.
-/

namespace LeanVMTests.Property.Files

open Hedgehog LeanVM.Parameters LeanVM.Cli LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

/-- A stream decodes to the scalars it encodes. -/
def scalarsRoundTrip : Property Id := property do
  let scalars ← forAll (Gen.list (.linear 0 12) genE)
  decodeScalars (encodeScalars scalars) === some scalars

/-- A bytecode decodes to the words it encodes. -/
def wordsRoundTrip : Property Id := property do
  let words ← forAll (Gen.list (.linear 0 24) genK)
  decodeWords (words.flatMap K.toBytes) === some words

/-- A public input decodes to the digest it encodes. -/
def digestRoundTrip : Property Id := property do
  let digest ← forAll genDigest
  decodeDigest (digestBytes digest) === some digest

/-- Bytes are a bytecode exactly when they are whole words, and then they are its encoding. -/
def wordsAreWholeWords : Property Id := property do
  let bytes ← forAll (genBytes 64)
  match decodeWords bytes with
  | some words =>
    bytes.length % 8 === 0
    words.flatMap K.toBytes === bytes
  | none => ensure (bytes.length % 8 != 0)

/-- Bytes are a stream exactly when they are whole scalars, and then they are its encoding. -/
def scalarsAreWholeScalars : Property Id := property do
  let bytes ← forAll (genBytes 96)
  match decodeScalars bytes with
  | some scalars =>
    bytes.length % 16 === 0
    encodeScalars scalars === bytes
  | none => ensure (bytes.length % 16 != 0)

/-- Only 32 bytes are a public input. -/
def digestIsThirtyTwoBytes : Property Id := property do
  let bytes ← forAll (genBytes 64)
  (decodeDigest bytes).isSome === (bytes.length == 32)

/-- The files' readers and the drivers' agree on a word and on a digest, on any bytes. -/
def readersAgree : Property Id := property do
  let bytes ← forAll (Gen.list (.linear 32 64) genByte)
  readK (toByteArray bytes) 0 === some (kOfBytes bytes, 8)
  readDigest (toByteArray bytes) 0 === some (digestOfBytes bytes, 32)

#eval check scalarsRoundTrip "a stream is decoded back" (seed := some (.ofNat 0))
#eval check wordsRoundTrip "a bytecode is decoded back" (seed := some (.ofNat 0))
#eval check digestRoundTrip "a public input is decoded back" (seed := some (.ofNat 0))
#eval check wordsAreWholeWords "a bytecode is whole words" (seed := some (.ofNat 0))
#eval check scalarsAreWholeScalars "a stream is whole scalars" (seed := some (.ofNat 0))
#eval check digestIsThirtyTwoBytes "a public input is 32 bytes" (seed := some (.ofNat 0))
#eval check readersAgree "the two readers agree" (seed := some (.ofNat 0))

end LeanVMTests.Property.Files
