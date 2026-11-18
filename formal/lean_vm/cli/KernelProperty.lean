import Hedgehog
import Statement.LeanVmVerifier

/-!
# The vector kernels against the Lean definitions, on generated inputs

The prover trees carry their field arithmetic in eight-lane vector kernels: the experimental
tree's `x8` (the coefficient layout, in the leaf and the GKR message) and `f128x8` (the plane
layout, in the stack opening), its GFNI bit folds, and the stable tree's `lanes`, with the
carry-less word products and the byte operations every Keccak round uses. Each kernel has a
portable body the tests hold the vector arms to, bit for bit; this driver holds the arms this
machine compiles (the first check says which) to the Lean definitions of the fields and of the
bit-level operations, on generated inputs.

    cargo build --release --manifest-path scripts/kernel-property/Cargo.toml
    lake build kernel-property
    lake exe kernel-property
    lake exe kernel-property scripts/kernel-property/target/release/leanvm-kernel-property 3000
-/

open Hedgehog LeanVM.Parameters

namespace KernelProperty

/-! ## The process -/

/-- The Rust process: one command line in, one result line out. -/
structure Driver where
  stdin : IO.FS.Handle
  stdout : IO.FS.Handle

/-- Start the process. -/
def Driver.start (path : String) : IO Driver := do
  let child ← IO.Process.spawn
    { cmd := path, stdin := .piped, stdout := .piped, stderr := .inherit }
  pure ⟨child.stdin, child.stdout⟩

/-- Send a command, its words separated by tabs, and read its result line. -/
def Driver.ask (driver : Driver) (words : List String) : TestT IO String := evalIO do
  driver.stdin.putStrLn ("\t".intercalate words)
  driver.stdin.flush
  let line ← driver.stdout.getLine
  if line.isEmpty then throw (IO.userError "the process gave no answer")
  pure (String.ofList (line.toList.filter (· ≠ '\n')))

/-! ## Words on the line -/

/-- A lane, in decimal. -/
def lane (w : UInt64) : String := toString w.toNat

/-- Lanes, as a result line has them. -/
def lanes (ws : List UInt64) : String := " ".intercalate (ws.map lane)

/-- A `K` word's lane. -/
def kWord (a : K) : String := lane a.lane

/-- An `E` scalar's two limbs. -/
def eWords (x : E) : List String := [kWord (x.limb 0), kWord (x.limb 1)]

/-- An `E` word, as one line has it. -/
def line (x : E) : String := " ".intercalate (eWords x)

/-- `E` words, as one line has them. -/
def scalars (zs : List E) : String := " ".intercalate (zs.flatMap eWords)

/-- Bytes, one decimal word each. -/
def bytes (bs : List UInt8) : List String := bs.map fun b ↦ toString b.toNat

/-! ## Generators -/

/-- A 64-bit word: small ones often, any one otherwise; it shrinks to `0`. -/
def genLane : Gen UInt64 :=
  Gen.choice [Gen.integral (.exponential 0 (UInt64.ofNat (2 ^ 64 - 1))),
    Gen.integral (.constant 0 (UInt64.ofNat (2 ^ 64 - 1)))]

/-- A word below `2^32`, the field map's images. -/
def genLane32 : Gen UInt64 :=
  Gen.choice [Gen.integral (.exponential 0 (UInt64.ofNat (2 ^ 32 - 1))),
    Gen.integral (.constant 0 (UInt64.ofNat (2 ^ 32 - 1)))]

def genK : Gen K := K.ofLane <$> genLane

def genE : Gen E := Gen.zipWith E.ofLimbs genK genK

def genByte : Gen UInt8 := Gen.integral (.constant 0 255)

/-- Eight `E`s. -/
def gen8E : Gen (List E) := Gen.list (.singleton 8) genE

/-- Eight `K`s. -/
def gen8K : Gen (List K) := Gen.list (.singleton 8) genK

/-- Eight words. -/
def gen8W : Gen (List UInt64) := Gen.list (.singleton 8) genLane

/-- A row of eight bytes. -/
def genRow : Gen (List UInt8) := Gen.list (.singleton 8) genByte

/-- `n` rows. -/
def genRows (n : ℕ) : Gen (List (List UInt8)) := Gen.list (.singleton n) genRow

/-! ## The oracles, in the Lean definitions -/

/-- The carry-less product of two 64-bit polynomials: bit `i + j` of the `128`-bit result is
`a_i · b_j`, the answer as low then high. -/
def clmul (a b : UInt64) : UInt64 × UInt64 :=
  let lo := (List.range 64).filter (fun i ↦ a.toNat.testBit i)
    |>.foldl (fun acc i ↦ acc ^^^ (b <<< i.toUInt64)) 0
  let hi := (List.range 64).filter (fun i ↦ i > 0 ∧ a.toNat.testBit i)
    |>.foldl (fun acc i ↦ acc ^^^ (b >>> (64 - i).toUInt64)) 0
  (lo, hi)

/-- The set bits of a word's low eight, as indices. -/
def lowBits (b : UInt64) : List ℕ :=
  (List.range 8).filter (fun s ↦ b.toNat.testBit s)

/-- A byte through a GF(2)-linear map: the images of its set bits, added. -/
def byteImage (images : List UInt64) (b : UInt64) : UInt64 :=
  lowBits b |>.foldl (fun acc s ↦ acc ^^^ images[s]!) 0

/-- A sixteen-bit field through a GF(2)-linear map to `32` bits. -/
def fieldImage (images : List UInt64) (v : UInt64) : UInt64 :=
  (List.range 16).filter (fun s ↦ v.toNat.testBit s) |>.foldl (fun acc s ↦ acc ^^^ images[s]!) 0

/-- `x`'s `n`-th byte, `n < 8`. -/
def byteOf (w : UInt64) (n : ℕ) : UInt64 := (w >>> (8 * n).toUInt64) &&& 255

/-- The bit transpose: word `w`'s bit `8·c + k` is `x[k]`'s bit `8·w + c`, the 8 by 64 matrix
transposed, byte `n`'s bit `k` to byte `k`'s bit `n`. -/
def transposeBits (x : List UInt64) : List UInt64 :=
  (List.range 8).map fun w ↦
    (List.range 8).foldl (fun acc c ↦
      acc ^^^ (List.range 8
        |>.filter (fun k ↦ (x[k]! >>> (8 * w + c).toUInt64).toNat.testBit 0)
        |>.foldl (fun a k ↦ a ^^^ ((1 : UInt64) <<< (8 * c + k).toUInt64)) 0)) 0

/-- The word transpose of eight rows of eight, in row-major order. -/
def transposeWords (rows : List (List UInt64)) : List UInt64 :=
  (List.range 8).flatMap fun c ↦ rows.map (·[c]!)

/-- The byte transpose of sixteen rows of eight words: word `n`'s byte `b` is row `b`'s byte
`n`, the word as low then high. -/
def transposeBytes (rows : List (List UInt64)) : List (UInt64 × UInt64) :=
  (List.range 64).map fun n ↦
    let byteB (b : ℕ) : UInt64 := byteOf ((rows[b]!)[n / 8]!) (n % 8)
    let half (lo : Bool) : UInt64 :=
      (List.range 8).map (fun b' ↦
        ((byteB ((if lo then 0 else 8) + b')).toNat * 256 ^ b').toUInt64)
        |>.foldl (fun a b ↦ a ^^^ b) 0
    (half true, half false)

/-- The row's bits through the fold's weights: `⊕ { w[8·j+s] : bit `s` of byte `j` is set }`. -/
def foldRow (w : List E) (row : List UInt8) : E :=
  (List.range row.length).foldl (fun acc j ↦
    let b := row[j]!
    acc + (lowBits b.toUInt64).foldl (fun a s ↦ a + w[8 * j + s]!) (0 : E)) (0 : E)

/-- Sixty-four rows folded, the rows past the input as the empty row, which folds to zero. -/
def foldRows (w : List E) (rows : List (List UInt8)) : List E :=
  (List.range 64).map fun p ↦ foldRow w (rows.getD p [])

/-- The rows of a column block, `cols[j][p]` byte `j` of row `p`. -/
def colsToRows (cols : List (List UInt8)) : List (List UInt8) :=
  (List.range 64).map fun p ↦ cols.map (·[p]!)

/-- The eight lane-wise products. -/
def products (a b : List E) : List E := List.zipWith (· * ·) a b

/-- The sum of eight `E`s. -/
def sum8 (xs : List E) : E := xs.foldl (· + ·) (0 : E)

/-- The eight mixed products `c[i] · k[i]`. -/
def mixed (c : List E) (k : List K) : List E := List.zipWith (fun c k ↦ c * ofK k) c k

/-- `a + r · (a + b)`, lane by lane. -/
def foldPairs (a b : List E) (r : E) : List E :=
  List.zipWith (fun x0 x1 ↦ x0 + r * (x0 + x1)) a b

/-- `a + r · a`, lane by lane. -/
def foldLones (a : List E) (r : E) : List E :=
  a.map fun x ↦ x + (r * x)

/-- The lanes of `a` and `b` interleaved, `a0 b0 a1 b1 …`, the last four lanes in the second
word's half. -/
def interleaveOut (a b : List E) : List E :=
  (List.range 8).foldl (fun acc i ↦ acc ++ [a[i]!, b[i]!]) []

/-- The even lanes of `a` then of `b`, and the odd ones: `p8eo` and `x8de` agree on the order. -/
def evenOddOut (a b : List E) : List E :=
  (List.range 4).map (fun i ↦ a[2 * i]!)
    ++ (List.range 4).map (fun i ↦ b[2 * i]!)
    ++ (List.range 4).map (fun i ↦ a[2 * i + 1]!)
    ++ (List.range 4).map (fun i ↦ b[2 * i + 1]!)

/-! ## The checks -/

/-- The experimental `x8`, coefficient layout: the products, their sum, the mixed products, the
shuffles; and the arms the binary compiled, which must be this machine's wide ones. -/
def x8 (rust : Driver) : Property IO := propertyM do
  let a ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let b ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let c ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let k ← forAllWith (reprStr ∘ List.map kWord) gen8K
  pure do
    let ab := a.flatMap eWords
    let bb := b.flatMap eWords
    (← rust.ask ["caps"]) === "x8 p8-avx512 gfni"
    (← rust.ask (["x8mul"] ++ ab ++ bb)) === scalars (products a b)
    (← rust.ask (["x8sum"] ++ ab ++ bb)) === line (sum8 (products a b))
    (← rust.ask (["x8mix"] ++ (c.flatMap eWords) ++ (k.map kWord))) === scalars (mixed c k)
    (← rust.ask (["x8ie"] ++ ab ++ bb)) === scalars (interleaveOut a b)
    (← rust.ask (["x8de"] ++ ab ++ bb)) === scalars (evenOddOut a b)

/-- The experimental `f128x8`, plane layout: the products reduced whole and per lane, the even
and odd lanes, the mixed products, the folds. -/
def p8 (rust : Driver) : Property IO := propertyM do
  let a ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let b ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let c ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let d ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let k ← forAllWith (reprStr ∘ List.map kWord) gen8K
  let r ← forAllWith (reprStr ∘ eWords) genE
  pure do
    let ab := a.flatMap eWords
    let bb := b.flatMap eWords
    let absum := a.zipWith (· + ·) b
    (← rust.ask (["p8mul"] ++ ab ++ bb)) === scalars (products a b)
    (← rust.ask (["p8sum"] ++ ab ++ bb)) === line (sum8 (products a b))
    (← rust.ask (["p8lanes"] ++ ab ++ bb)) === scalars (products a b)
    (← rust.ask (["p8eo"] ++ ab ++ bb)) === scalars (evenOddOut a b)
    (← rust.ask (["p8base"] ++ (c.flatMap eWords) ++ (k.map kWord))) === scalars (mixed c k)
    (← rust.ask (["p8bspl"] ++ eWords r ++ (k.map kWord)))
      === scalars (k.map fun k ↦ r * ofK k)
    (← rust.ask (["p8xor"] ++ (c.flatMap eWords) ++ (d.flatMap eWords)))
      === scalars (c.zipWith (· + ·) d)
    (← rust.ask (["p8fp"] ++ ab ++ bb ++ eWords r)) === scalars (foldPairs a b r)
    (← rust.ask (["p8fl"] ++ ab ++ eWords r)) === scalars (foldLones a r)
    (← rust.ask (["p8mt"] ++ ab ++ bb ++ (c.flatMap eWords) ++ (d.flatMap eWords)))
      === scalars [sum8 (products a c), sum8 (products absum (c.zipWith (· + ·) d))]
    (← rust.ask (["p8ml"] ++ ab ++ (c.flatMap eWords))) === scalars [sum8 (products a c)]

/-- The experimental bit folds: the rows' folded words, the rows past the input zero, and the
same rows given as columns. -/
def bitfolds (rust : Driver) : Property IO := propertyM do
  let w ← forAllWith (reprStr ∘ List.flatMap eWords) (Gen.list (.singleton 64) genE)
  let n ← forAll (Gen.choice [Gen.nat (.linear 1 3), Gen.nat (.constant 1 64)])
  let rows ← forAllWith (reprStr ∘ List.flatMap bytes) (genRows n)
  pure do
    let ws := w.flatMap eWords
    let rs := rows.flatMap bytes
    (← rust.ask (["bfold"] ++ ws ++ rs)) === scalars (foldRows w rows) ++ " 1"
    let cols := (List.range 8).map fun j ↦
      (List.range 64).map fun p ↦ (rows.getD p []).getD j 0
    (← rust.ask (["bcols"] ++ ws ++ (cols.flatMap bytes)))
      === scalars (foldRows w (colsToRows cols))

/-- The stable lanes: the products, their sum, the mixed products. -/
def slanes (rust : Driver) : Property IO := propertyM do
  let a ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let b ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let c ← forAllWith (reprStr ∘ List.flatMap eWords) gen8E
  let k ← forAllWith (reprStr ∘ List.map kWord) gen8K
  pure do
    let ab := a.flatMap eWords
    let bb := b.flatMap eWords
    (← rust.ask (["s8mul"] ++ ab ++ bb)) === scalars (products a b)
    (← rust.ask (["s8sum"] ++ ab ++ bb)) === line (sum8 (products a b))
    (← rust.ask (["s8base"] ++ (c.flatMap eWords) ++ (k.map kWord))) === scalars (mixed c k)

/-- The carry-less products of words: the low halves of eight, the sum of the eight whole, and
one at a time. -/
def clmuls (rust : Driver) : Property IO := propertyM do
  let p ← forAllWith (reprStr ∘ List.map lane) gen8W
  let q ← forAllWith (reprStr ∘ List.map lane) gen8W
  let u ← forAll genLane
  let v ← forAll genLane
  pure do
    let pw := p.map lane
    let qw := q.map lane
    let lo := p.zipWith (fun a b ↦ (clmul a b).1) q
    let hi := p.zipWith (fun a b ↦ (clmul a b).2) q
    (← rust.ask (["clmul"] ++ pw ++ qw)) === lanes lo
    (← rust.ask (["wide"] ++ pw ++ qw))
      === lanes [lo.foldl (fun a b ↦ a ^^^ b) 0, hi.foldl (fun a b ↦ a ^^^ b) 0]
    (← rust.ask (["mwide", lane u, lane v])) === lanes ((clmul u v).1 :: (clmul u v).2 :: [])

/-- A byte as a word. -/
def genByteW : Gen UInt64 := Gen.integral (.constant 0 255)

/-- The byte operations: the byte and field maps, the three transposes. -/
def byteops (rust : Driver) : Property IO := propertyM do
  let images ← forAllWith (reprStr ∘ List.map lane) (Gen.list (.singleton 8) genByteW)
  let x ← forAllWith (reprStr ∘ List.map lane) gen8W
  let fimages ← forAllWith (reprStr ∘ List.map lane) (Gen.list (.singleton 16) genLane32)
  let rows ← forAllWith (reprStr ∘ List.flatMap (List.map lane)) (Gen.list (.singleton 8) gen8W)
  let trows ← forAllWith (reprStr ∘ List.flatMap (List.map lane)) (Gen.list (.singleton 16) gen8W)
  pure do
    (← rust.ask (["mapb"] ++ (images.map lane) ++ (x.map lane)))
      === lanes (x.map fun w ↦
        (List.range 8).map (fun n ↦
          (byteImage images (byteOf w n)).toNat * 256 ^ n |>.toUInt64)
          |>.foldl (fun a b ↦ a ^^^ b) 0)
    (← rust.ask (["mapf"] ++ (fimages.map lane) ++ (x.map lane)))
      === lanes ((List.range 4).flatMap fun plane ↦
        x.map fun w ↦ fieldImage fimages ((w >>> (16 * plane).toUInt64) &&& 65535))
    (← rust.ask (["tbits"] ++ (x.map lane))) === lanes (transposeBits x)
    (← rust.ask (["twords"] ++ rows.flatMap (List.map lane))) === lanes (transposeWords rows)
    let tb := (transposeBytes trows).flatMap (fun (lo, hi) ↦ lo :: hi :: [])
    (← rust.ask (["tbytes"] ++ trows.flatMap (List.map lane))) === lanes tb

end KernelProperty

/-! ## The run -/

def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/kernel-property/target/release/leanvm-kernel-property"
  let rust ← KernelProperty.Driver.start path
  let cases (p : Property IO) : Property IO := (args[1]?.bind String.toNat?).elim p p.withTests
  let ok ← checkGroup "the vector kernels against the Lean definitions" [
    ("the experimental x8, coefficient layout", cases (KernelProperty.x8 rust)),
    ("the experimental f128x8, plane layout", cases (KernelProperty.p8 rust)),
    ("the experimental bit folds", cases (KernelProperty.bitfolds rust)),
    ("the stable lanes", cases (KernelProperty.slanes rust)),
    ("the carry-less word products", cases (KernelProperty.clmuls rust)),
    ("the byte operations", cases (KernelProperty.byteops rust))]
  return if ok then 0 else 1
