import Hedgehog
import Statement.LeanDa

/-!
# LeanDA, the Rust against the statement's, on generated blobs

The Rust (`scripts/da-property`, `leanvm-da-property`: `lean_da::BlobMatrix` and `verify_cell`)
encodes and commits to blobs this driver generates (lean-hedgehog), and then

* **a codeword is a codeword**: it starts with the payload (`encodeRow` is systematic), and it is
  orthogonal to the dual codeword `L(x) = ∏_j (1 + z^(2^j) Ŵ_j(x))` of a generated challenge `z`
  (`dualCodewordAt`, `membershipCheck`), which only the values of a polynomial of degree below
  `2^13` are for more than a few `z`. The normalized subspace polynomials `Ŵ_j` are computed here
  from their recurrence, `W_0 = x`, `W_(j+1) = W_j (W_j + W_j(e_j))`, `Ŵ_j = W_j / W_j(e_j)`;
* **the commitment is the statement's** (`commitCells` over Keccak-f[1600]) of the Rust's rows;
* **a cell's opening verifies**, by `verify_cell` and by the statement's `verifyCellWith`; and with
  the commitment, the cell, the path, the indices or the number of blobs altered, the two verdicts
  are the same.

    cargo build --release --manifest-path scripts/da-property/Cargo.toml
    lake build da-property
    lake exe da-property             # 20 cases of each; a commitment hashes megabytes in Lean
-/

open Hedgehog LeanVM.Parameters LeanVM.Semantics LeanDa

namespace DaProperty

/-! ## The process -/

structure Driver where
  stdin : IO.FS.Handle
  stdout : IO.FS.Handle

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

/-! ## Symbols and bytes -/

/-- Word `k` of blob `blob` of seed `seed`, as `word` of the Rust harness. -/
def mix (seed blob k : UInt64) : UInt64 :=
  let w := (seed + blob * 0x1000001B3 + k) * 0x9E3779B97F4A7C15
  ((w <<< 23) ||| (w >>> 41)) ^^^ k

/-- Symbol `s` of blob `blob`: two words below `limit`, zero from it on. -/
def symbol (seed : UInt64) (limit blob s : ℕ) : E :=
  if s < limit then
    E.ofLimbs (K.ofLane (mix seed (UInt64.ofNat blob) (UInt64.ofNat (2 * s))))
      (K.ofLane (mix seed (UInt64.ofNat blob) (UInt64.ofNat (2 * s + 1))))
  else 0

/-- The little-endian lane at an offset. -/
def laneAt (bytes : ByteArray) (offset : ℕ) : UInt64 :=
  (List.range 8).foldr (fun k acc ↦ acc * 256 + (bytes.get! (offset + k)).toUInt64) 0

/-- The symbols of bytes, sixteen a symbol: limb `0`, then limb `1`. -/
def symbolsOf (bytes : ByteArray) : Array E :=
  Array.ofFn (n := bytes.size / 16) fun i ↦
    E.ofLimbs (K.ofLane (laneAt bytes (16 * i.val))) (K.ofLane (laneAt bytes (16 * i.val + 8)))

def hexDigit (c : Char) : ℕ :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- The bytes of a hexadecimal string. -/
def unhex (s : String) : ByteArray :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (16 * hexDigit a + hexDigit b) :: go rest
    | _ => []
  ⟨(go s.toList).toArray⟩

def hex (bytes : ByteArray) : String :=
  String.join (bytes.toList.map fun b ↦
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length = 1 then '0' :: digits else digits))

/-- 32 bytes as the statement's digest. -/
def digestOf (bytes : ByteArray) (offset : ℕ := 0) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 ↦ bytes.get! (offset + i.val)

/-! ## The membership test -/

/-- `Ŵ_j(point b)` for `j < 13` and `b < 2^14`. -/
def subspaceTables : Array (Array K) := Id.run do
  let mut w : Array K := Array.ofFn (n := 2 ^ 14) fun b ↦ K.ofBits b.val
  let mut tables := #[]
  for j in [0:13] do
    let atBasis := w[2 ^ j]!
    tables := tables.push (w.map (· * atBasis⁻¹))
    w := w.map fun v ↦ v * (v + atBasis)
  pure tables

/-- Whether a row is orthogonal to the dual codeword of `z`. -/
def member (tables : Array (Array K)) (z : E) (row : Array E) : Bool :=
  let powers := (List.range 13).foldl (fun zs _ ↦ zs.push (zs.back! * zs.back!)) #[z]
  let sum := (List.range (2 ^ 14)).foldl (fun acc b ↦
    let weight := (List.range 13).foldl
      (fun weight j ↦ weight * (1 + powers[j]! * ofK ((tables[j]!)[b]!))) (1 : E)
    acc + weight * row[b]!) (0 : E)
  sum == 0

/-! ## Generators -/

def genLane : Gen UInt64 :=
  Gen.choice [Gen.integral (.exponential 0 (UInt64.ofNat (2 ^ 64 - 1))),
    Gen.integral (.constant 0 (UInt64.ofNat (2 ^ 64 - 1)))]

def genE : Gen E := Gen.zipWith (fun a b ↦ E.ofLimbs (K.ofLane a) (K.ofLane b)) genLane genLane

/-- How much of a blob is not zero: none of it, a few symbols, or all. -/
def genLimit : Gen ℕ :=
  Gen.choice [Gen.nat (.constant 0 3), Gen.nat (.linear 0 8192), pure 8192]

/-- The rows of the kept matrix, read from the files the Rust writes. -/
def rows (rust : Driver) (dir : System.FilePath) (count : ℕ) : TestT IO (Array (Array E)) := do
  let mut out := #[]
  for i in [0:count] do
    let file := (dir / s!"row{i}.bin").toString
    (← rust.ask ["row", toString i, file]) === "ok"
    out := out.push (symbolsOf (← evalIO (IO.FS.readBinFile file)))
  pure out

/-! ## The properties -/

/-- A codeword starts with its payload and passes the membership test. -/
def codewords (rust : Driver) (tables : Array (Array K)) (dir : System.FilePath) :
    Property IO := propertyM do
  let seed ← forAll genLane
  let limit ← forAll genLimit
  let count ← forAll (Gen.nat (.constant 1 3))
  let z ← forAll genE
  pure do
    let root ← rust.ask ["build", toString seed.toNat, toString limit, toString count]
    ensure (root.length == 64) s!"no commitment: {root}"
    for (row, i) in (← rows rust dir count).zipIdx do
      annotate s!"row {i}"
      row.size === 2 ^ 14
      ensure ((List.range (2 ^ 13)).all fun s ↦ row[s]! == symbol seed limit i s)
        "the codeword does not start with its payload"
      ensure (member tables z row) "the codeword fails the membership test"

/-- The commitment is the statement's, of the Rust's rows. -/
def commitments (rust : Driver) (dir : System.FilePath) : Property IO := propertyM do
  let seed ← forAll genLane
  let limit ← forAll genLimit
  let count ← forAll (Gen.nat (.constant 1 2))
  pure do
    let root ← rust.ask ["build", toString seed.toNat, toString limit, toString count]
    let rows ← rows rust dir count
    let cells : Fin (rows.size * 128) → Cell :=
      fun p s ↦ (rows[p.val / 128]!)[128 * (p.val % 128) + s.val]!
    let digest := commitCells keccakF1600 cells
    hex ⟨digest.toArray⟩ === root

/-- What of an opening is altered. -/
inductive Alteration where
  | root (position : ℕ) (byte : UInt8)
  | cell (position : ℕ) (byte : UInt8)
  | path (position : ℕ) (byte : UInt8)
  | blobs (count : ℕ)
  | blob (index : ℕ)
  | column (index : ℕ)
  deriving Repr

def genAlteration : Gen Alteration := do
  let byte ← Gen.integral (.constant 0 255)
  Gen.choice [.root <$> Gen.nat (.constant 0 31) <*> pure byte,
    .cell <$> Gen.nat (.constant 0 2047) <*> pure byte,
    .path <$> Gen.nat (.constant 0 383) <*> pure byte,
    .blobs <$> Gen.nat (.constant 0 40), .blob <$> Gen.nat (.constant 0 40),
    .column <$> Gen.choice [Gen.nat (.constant 0 127), Gen.nat (.constant 128 300)]]

/-- The statement's verdict on an opening, with the crate's refusals of what the statement's types
leave out: more blobs than `maxRows`, a blob or a column out of range, a cell or a path of another
length. -/
def verdict (root : ByteArray) (count blob column : ℕ) (cell path : ByteArray) : Bool :=
  if h : count ≤ maxRows ∧ blob < count ∧ column < 128 ∧ root.size = 32 ∧ cell.size = 2048
      ∧ path.size = 384 then
    let symbols := symbolsOf cell
    Id.run (verifyCellWith (fun s ↦ pure (keccakF1600 s)) count (digestOf root)
      ⟨128 * blob + column, by omega⟩ (fun s ↦ symbols[s.val]!)
      ⟨(List.range 12).map fun k ↦ digestOf path (32 * k)⟩)
  else false

/-- A cell's opening verifies by both, and altered the two verdicts are the same. -/
def openings (rust : Driver) : Property IO := propertyM do
  let seed ← forAll genLane
  let limit ← forAll genLimit
  let count ← forAll (Gen.nat (.constant 1 4))
  let blob ← forAll (Gen.nat (.constant 0 (count - 1)))
  let column ← forAll (Gen.nat (.constant 0 127))
  let alterations ← forAll (Gen.list (.linear 1 2) genAlteration)
  pure do
    let root := unhex (← rust.ask ["build", toString seed.toNat, toString limit, toString count])
    let opening ← rust.ask ["cell", toString blob, toString column]
    let (cell, path) := match opening.splitOn " " with
      | [cell, path] => (unhex cell, unhex path)
      | _ => (ByteArray.empty, ByteArray.empty)
    let ask (root : ByteArray) (count blob column : ℕ) (cell path : ByteArray) :=
      rust.ask ["verify", hex root, toString count, toString blob, toString column, hex cell,
        hex path]
    (← ask root count blob column cell path) === "true"
    ensure (verdict root count blob column cell path) "the statement refuses the Rust's opening"
    let (root, count, blob, column, cell, path) := alterations.foldl
      (fun (root, count, blob, column, cell, path) alteration ↦
        match alteration with
        | .root position byte => (root.set! position byte, count, blob, column, cell, path)
        | .cell position byte => (root, count, blob, column, cell.set! position byte, path)
        | .path position byte => (root, count, blob, column, cell, path.set! position byte)
        | .blobs n => (root, n, blob, column, cell, path)
        | .blob i => (root, count, i, column, cell, path)
        | .column j => (root, count, blob, j, cell, path))
      (root, count, blob, column, cell, path)
    (← ask root count blob column cell path)
      === toString (verdict root count blob column cell path)

end DaProperty

/-- The driver: the Rust binary's path may be given, and after it the number of cases of each (a
quarter of it for the commitments, which hash megabytes). -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/da-property/target/release/leanvm-da-property"
  let rust ← DaProperty.Driver.start path
  let count := (args[1]?.bind String.toNat?).getD 20
  let dir ← IO.FS.createTempDir
  let tables := DaProperty.subspaceTables
  let ok ← checkGroup "LeanDA, the Rust against the statement's" [
    ("a codeword starts with its payload and is a codeword",
      (DaProperty.codewords rust tables dir).withTests count),
    ("the commitment is the statement's",
      (DaProperty.commitments rust dir).withTests (count / 4 + 1)),
    ("an opening's verdict is the statement's, altered or not",
      (DaProperty.openings rust).withTests count)]
  IO.FS.removeDirAll dir
  return if ok then 0 else 1
