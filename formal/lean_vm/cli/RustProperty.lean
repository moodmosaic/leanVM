import Hedgehog
import Statement.LeanVmVerifier

/-!
# The Rust primitives against the Lean definitions, on generated inputs

The Lean definitions of the fields, of Keccak and of the Fiat-Shamir sponge (`Statement/`) are what
the theorems are about. The Rust has each of them several times: the field in the verifier and in
both prover trees, with batched and vector kernels in the experimental one; Keccak-f[1600] one state
at a time and many; Keccak-256 at once, batched and streamed; the sponge in the verifier and, written
differently, in the prover. This driver runs the Rust ones (`scripts/rust-property`,
`leanvm-rust-property`, one command per line) on inputs it generates and requires the Lean
definition's answer of each, and it shrinks a disagreement to a small input (lean-hedgehog).

The stateless ones are properties. The two with state are state machine tests in `IO`, the system
under test the Rust process: the streamed hasher against the bytes absorbed so far, and the prover's
sponge against the statement's (`Sponge`, `absorb`, `squeeze`, `absorbNonce`), which is run beside it
on Keccak-f[1600]. Their operations are fixed, so they are one type of transitions each.

    cargo build --release --manifest-path scripts/rust-property/Cargo.toml
    lake build rust-property
    lake exe rust-property            # 100 cases of each
    lake exe rust-property scripts/rust-property/target/release/leanvm-rust-property 100000
-/

open Hedgehog LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

namespace RustProperty

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

/-! ## Words and bytes on the line -/

/-- A lane, in decimal. -/
def lane (w : UInt64) : String := toString w.toNat

/-- Lanes, as a result line has them. -/
def lanes (ws : List UInt64) : String := " ".intercalate (ws.map lane)

/-- A `K` word's lane. -/
def kWord (a : K) : String := lane a.lane

/-- An `E` scalar's two limbs. -/
def eWords (x : E) : List String := [kWord (x.limb 0), kWord (x.limb 1)]

/-- Bytes in hexadecimal, `-` for none. -/
def hex (bytes : List UInt8) : String :=
  if bytes.isEmpty then "-"
  else String.join (bytes.map fun b ↦
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length = 1 then '0' :: digits else digits))

/-! ## Generators -/

/-- A 64-bit word: small ones often, any one otherwise; it shrinks to `0`. -/
def genLane : Gen UInt64 :=
  Gen.choice [Gen.integral (.exponential 0 (UInt64.ofNat (2 ^ 64 - 1))),
    Gen.integral (.constant 0 (UInt64.ofNat (2 ^ 64 - 1)))]

def genK : Gen K := K.ofLane <$> genLane

def genE : Gen E := Gen.zipWith E.ofLimbs genK genK

def genByte : Gen UInt8 := Gen.integral (.constant 0 255)

/-- A Keccak state. -/
def genState : Gen KeccakState :=
  (fun ws ↦ Vector.ofFn fun i : Fin 25 ↦ ws.getD i.val 0) <$> Gen.list (.singleton 25) genLane

/-- A length around a multiple of the rate, where a sponge changes blocks, or any short one. -/
def genLength (most : ℕ) : Gen ℕ :=
  Gen.choice [Gen.nat (.linear 0 most), (fun blocks delta ↦ 136 * blocks + 133 + delta)
    <$> Gen.nat (.constant 0 2) <*> Gen.nat (.constant 0 6)]

/-- Bytes of such a length. -/
def genBytes (most : ℕ := 300) : Gen (List UInt8) := do
  let n ← genLength most
  Gen.list (.singleton n) genByte

/-! ## The fields -/

/-- `x ^ n` by squaring, on the Lean product. -/
def power {α : Type} [Mul α] (one x : α) (n : ℕ) : α :=
  (List.range n.size).foldr (fun i acc ↦ if n.testBit i then acc * acc * x else acc * acc) one

/-- The implementations of the field: the verifier's, the stable prover's, the experimental one's. -/
def implementations : List String := ["v", "s", "x"]

/-- `K`: product, square and inverse in each implementation, and powers in the provers'. -/
def fieldK (rust : Driver) : Property IO := propertyM do
  let a ← forAllWith kWord genK
  let b ← forAllWith kWord genK
  let n ← forAll genLane
  pure do
    for imp in implementations do
      annotate s!"implementation {imp}"
      (← rust.ask ["kmul", imp, kWord a, kWord b]) === kWord (a * b)
      (← rust.ask ["ksq", imp, kWord a]) === kWord (a * a)
      (← rust.ask ["kinv", imp, kWord a]) === kWord a⁻¹
    for imp in ["s", "x"] do
      annotate s!"implementation {imp}"
      (← rust.ask ["kpow", imp, kWord a, lane n]) === kWord (power 1 a n.toNat)

/-- `E`: product, square, inverse and product by a `K` word in each implementation, and the
verifier's powers. -/
def fieldE (rust : Driver) : Property IO := propertyM do
  let x ← forAllWith (reprStr ∘ eWords) genE
  let y ← forAllWith (reprStr ∘ eWords) genE
  let k ← forAllWith kWord genK
  let n ← forAll genLane
  pure do
    let line (z : E) := " ".intercalate (eWords z)
    for imp in implementations do
      annotate s!"implementation {imp}"
      (← rust.ask (["emul", imp] ++ eWords x ++ eWords y)) === line (x * y)
      (← rust.ask (["esq", imp] ++ eWords x)) === line (x * x)
      (← rust.ask (["einv", imp] ++ eWords x)) === line x⁻¹
      (← rust.ask (["emulk", imp] ++ eWords x ++ [kWord k])) === line (x * ofK k)
    (← rust.ask (["epow"] ++ eWords x ++ [lane n])) === line (power 1 x n.toNat)

/-- The experimental tree's two and four products at once are the products. -/
def fieldBatches (rust : Driver) : Property IO := propertyM do
  let xs ← forAllWith (reprStr ∘ List.map eWords) (Gen.list (.singleton 4) genE)
  let ys ← forAllWith (reprStr ∘ List.map eWords) (Gen.list (.singleton 4) genE)
  pure do
    let line (zs : List E) := " ".intercalate (zs.flatMap eWords)
    let products := List.zipWith (· * ·) xs ys
    (← rust.ask (["emul4"] ++ xs.flatMap eWords ++ ys.flatMap eWords)) === line products
    (← rust.ask (["emul2"] ++ (xs.take 2).flatMap eWords ++ (ys.take 2).flatMap eWords))
      === line (products.take 2)

/-! ## The multilinear helpers of the two prover trees -/

/-- The prover trees: the stable one and the experimental one. -/
def trees : List String := ["s", "x"]

/-- Scalars on a line. -/
def scalars (zs : List E) : String := " ".intercalate (zs.flatMap eWords)

/-- Word `i` of the table of seed `seed`, as `table_word` of the Rust harness. -/
def tableWord (seed i : UInt64) : UInt64 :=
  let w := (seed + i) * 0x9E3779B97F4A7C15
  ((w <<< 23) ||| (w >>> 41)) ^^^ i

/-- `eq_eval`, `eq_table` and `poly_eval` are the verifier's `eqEval`, `eqKernel` and `polyEval`. -/
def equalityAndPolynomials (rust : Driver) : Property IO := propertyM do
  let r ← forAllWith scalars (Gen.list (.linear 0 7) genE)
  let x ← forAllWith scalars (Gen.list (.singleton r.length) genE)
  let coefficients ← forAllWith scalars (Gen.list (.linear 0 12) genE)
  let point ← forAllWith (scalars ∘ List.singleton) genE
  pure do
    for tree in trees do
      annotate s!"tree {tree}"
      (← rust.ask (["eqeval", tree, toString r.length] ++ (r ++ x).flatMap eWords))
        === scalars [eqEval r x]
      (← rust.ask (["eqtable", tree] ++ r.flatMap eWords)) === scalars (eqKernel r)
      (← rust.ask (["polyeval", tree] ++ eWords point ++ coefficients.flatMap eWords))
        === scalars [polyEval coefficients point]

/-- A large `eq_table`, built in parallel as a tensor product, is the serial one. -/
def equalityTableInParallel (rust : Driver) : Property IO := propertyM do
  let r ← forAllWith scalars (Gen.list (.constant 15 17) genE)
  pure do
    for tree in trees do
      annotate s!"tree {tree}"
      (← rust.ask (["eqbig", tree] ++ r.flatMap eWords)) === "same"

/-- The table of seed `seed` cut at `length`, zero after, as the verifier's `multilinearEval` takes
it. -/
def tableOf (seed : UInt64) (length count : ℕ) : List E :=
  (List.range (2 ^ count)).map fun i ↦
    if i < length then ofK (K.ofLane (tableWord seed (UInt64.ofNat i))) else 0

/-- `mle_eval`, and `mle_eval_par` on a table cut to whole rows, are the verifier's
`multilinearEval` of the table, zero after its end. A cut table has at least three variables here;
`multilinearExtensionOfAShortTable` is the rest. -/
def multilinearExtension (rust : Driver) : Property IO := propertyM do
  let point ← forAllWith scalars (Gen.list (.linear 0 13) genE)
  let rows := 2 ^ (point.length - 10)
  let kept ← forAll (if point.length < 3 then pure rows
    else Gen.frequency [(2, pure rows), (1, Gen.nat (.constant 0 rows))])
  let seed ← forAll genLane
  let length := kept * 2 ^ min point.length 10
  pure do
    for tree in trees do
      annotate s!"tree {tree}"
      (← rust.ask (["mle", tree, lane seed, toString length] ++ point.flatMap eWords))
        === scalars [multilinearEval (tableOf seed length point.length) point]

/-- `mle_eval_par` on an empty table of fewer than three variables: zero, as the table "is zero past
its end".

**It fails on the experimental tree**, which asserts `low_vars >= 3` there and panics, where the
stable tree returns zero: the two trees differ outside what either documents. Whether a prover
reaches it (a column cut to no row, at a point of fewer than three coordinates) is for the Rust's
authors to say. -/
def multilinearExtensionOfAShortTable (rust : Driver) : Property IO := propertyM do
  let point ← forAllWith scalars (Gen.list (.constant 0 2) genE)
  pure do
    for tree in trees do
      annotate s!"tree {tree}"
      (← rust.ask (["mle", tree, "0", "0"] ++ point.flatMap eWords)) === scalars [0]

/-- `powers`, `g_powers`, `g_pow`, `index_mle`, `mul_by_g` and `div_by_g`. -/
def powersAndIndices (rust : Driver) : Property IO := propertyM do
  let x ← forAllWith (scalars ∘ List.singleton) genE
  let count ← forAll (Gen.nat (.linear 0 40))
  let exponent ← forAll (Gen.nat (.exponential 0 (2 ^ 40)))
  let zeta ← forAllWith scalars (Gen.list (.linear 0 12) genE)
  let a ← forAllWith kWord genK
  pure do
    for tree in trees do
      annotate s!"tree {tree}"
      (← rust.ask (["powers", tree, toString count] ++ eWords x)) === scalars (powers x count)
      (← rust.ask ["gpowers", tree, toString count])
        === " ".intercalate ((List.range count).map fun i ↦ kWord (power 1 g i))
      (← rust.ask ["gpow", tree, toString exponent]) === kWord (power 1 g exponent)
      (← rust.ask (["indexmle", tree] ++ zeta.flatMap eWords)) === scalars [indexMle zeta]
      (← rust.ask ["mulg", tree, kWord a]) === kWord (g * a)
      (← rust.ask ["divg", tree, kWord a]) === kWord (a * g⁻¹)

/-- The stable tree's `fold` binds the lowest variable of rows, and its `dot` is the verifier's. -/
def foldAndDot (rust : Driver) : Property IO := propertyM do
  let width ← forAll (Gen.nat (.constant 1 3))
  let pairs ← forAll (Gen.nat (.linear 0 4))
  let table ← forAllWith scalars (Gen.list (.singleton (2 * width * pairs)) genE)
  let t ← forAllWith (scalars ∘ List.singleton) genE
  let left ← forAllWith scalars (Gen.list (.linear 0 20) genE)
  let right ← forAllWith scalars (Gen.list (.singleton left.length) genE)
  pure do
    let folded := (List.range pairs).flatMap fun p ↦ (List.range width).map fun j ↦
      let lo := table.getD (2 * width * p + j) 0
      let hi := table.getD (2 * width * p + width + j) 0
      lo + t * (lo + hi)
    (← rust.ask (["fold", toString width] ++ eWords t ++ table.flatMap eWords)) === scalars folded
    (← rust.ask ("dot" :: (left ++ right).flatMap eWords)) === scalars [dot left right]

/-! ## Keccak -/

/-- Keccak-f[1600], one state. -/
def permutation (rust : Driver) : Property IO := propertyM do
  let state ← forAllWith (lanes ∘ Vector.toList) genState
  pure do
    (← rust.ask ("keccakf" :: state.toList.map lane)) === lanes (keccakF1600 state).toList

/-- Keccak-f[1600], many states at once: whole vectors of them and the rest. -/
def permutationMany (rust : Driver) : Property IO := propertyM do
  let states ← forAllWith (reprStr ∘ List.map (lanes ∘ Vector.toList))
    (Gen.list (.linear 0 20) genState)
  pure do
    (← rust.ask ("keccakfmany" :: states.flatMap fun s ↦ s.toList.map lane))
      === lanes (states.flatMap fun s ↦ (keccakF1600 s).toList)

/-- Keccak-256 of a byte string. -/
def hash (rust : Driver) : Property IO := propertyM do
  let data ← forAll (genBytes 300)
  pure do
    (← rust.ask ["hash", hex data]) === hex (digestBytes (keccak256 data))

/-- Keccak-256 of many inputs of one length at once. -/
def hashMany (rust : Driver) : Property IO := propertyM do
  let length ← forAll (genLength 200)
  let count ← forAll (Gen.nat (.linear 0 20))
  let inputs ← forAll (Gen.list (.singleton count) (Gen.list (.singleton length) genByte))
  pure do
    if length ≠ 0 then
      (← rust.ask ["hashmany", toString length, hex inputs.flatten])
        === hex (inputs.flatMap fun input ↦ digestBytes (keccak256 input))

/-! ## The streamed hasher, a state machine -/

/-- What a hasher is asked. -/
inductive Hashing where
  /-- Absorb more bytes. -/
  | update (bytes : List UInt8)
  /-- Read the digest of what was absorbed; more may follow. -/
  | finish
  deriving Repr

/-- The hasher against the bytes absorbed so far: its digest is their Keccak-256, whatever pieces
they came in. -/
def hasher (rust : Driver) : StateMachine (List UInt8) Hashing Unit IO where
  initState := pure []
  transitions _ := Gen.frequency [(3, .update <$> genBytes 200), (1, pure .finish)]
  apply absorbed
    | .update bytes => absorbed ++ bytes
    | .finish => absorbed
  initSut _ := do
    rust.stdin.putStrLn "hnew"
    rust.stdin.flush
    let _ ← rust.stdout.getLine
  applySut _ absorbed
    | .update bytes => do (← rust.ask ["hupdate", hex bytes]) === "ok"
    | .finish => do (← rust.ask ["hfinal"]) === hex (digestBytes (keccak256 absorbed))

/-! ## The prover's sponge, a state machine -/

/-- What a sponge is asked. -/
inductive Asking where
  /-- Absorb a scalar. -/
  | observe (c0 c1 : UInt64)
  /-- Squeeze a challenge. -/
  | sample
  /-- Grind `bits` bits of proof of work. -/
  | grind (bits : ℕ)
  deriving Repr

/-- The model the sequences are generated from: the seeds, and whether a grind's challenge waits (the
Rust asserts that nothing is absorbed then). -/
structure Seeded where
  iv : List UInt64
  publicInput : List UInt64
  ground : Bool := false
  deriving Repr

/-- Keccak-f[1600] in `Id`. -/
def keccak (state : KeccakState) : Id KeccakState := pure (keccakF1600 state)

/-- A nonce as the scalar the Rust absorbs: the nonce in limb `0`. -/
def nonceScalar (nonce : ℕ) : E := E.ofLimbs (K.ofLane (UInt64.ofNat nonce)) 0

/-- Whether the low `bits` bits of a lane are zero. -/
def lowBitsZero (bits : ℕ) (w : UInt64) : Bool := w.toNat % 2 ^ bits == 0

/-- The prover's sponge against the statement's, run beside it: the same challenges, and a grind's
nonce is the least whose proof of work has its low bits zero. -/
def sponge (rust : Driver) : StateMachine Seeded Asking Sponge IO where
  initState := (fun iv publicInput ↦ { iv, publicInput })
    <$> Gen.list (.singleton 4) genLane <*> Gen.list (.singleton 4) genLane
  transitions s :=
    if s.ground then pure .sample
    else Gen.frequency [(4, .observe <$> genLane <*> genLane), (3, pure .sample),
      (1, .grind <$> Gen.nat (.constant 0 6))]
  preconditions s
    | .sample => true
    | _ => !s.ground
  apply s
    | .observe _ _ => s
    | .sample => { s with ground := false }
    | .grind bits => { s with ground := bits != 0 }
  initSut s := do
    rust.stdin.putStrLn ("\t".intercalate ("snew" :: (s.iv ++ s.publicInput).map lane))
    rust.stdin.flush
    let _ ← rust.stdout.getLine
    let digest (ws : List UInt64) : Digest := Vector.ofFn fun i : Fin 4 ↦ ws.getD i.val 0
    pure ⟨keccakF1600 (seedInput (digest s.iv) (digest s.publicInput)), [], none⟩
  applySut model _
    | .observe c0 c1 => do
      (← rust.ask ["sobserve", lane c0, lane c1]) === "ok"
      pure (absorb keccak model (E.ofLimbs (K.ofLane c0) (K.ofLane c1)) dsObserve)
    | .sample => do
      let (challenge, model) := squeeze keccak model
      (← rust.ask ["ssample"]) === " ".intercalate (eWords challenge)
      pure model
    | .grind bits => do
      let answer ← rust.ask ["sgrind", toString bits]
      if bits = 0 then
        answer === "none"
        pure model
      else
        match answer.toNat? with
        | none => failWith s!"no nonce: {answer}"
        | some nonce =>
          let work (n : ℕ) : UInt64 := (absorbNonce keccak model (nonceScalar n)).1
          ensure (lowBitsZero bits (work nonce)) "the nonce's proof of work is not zero"
          ensure ((List.range nonce).all fun n ↦ !lowBitsZero bits (work n))
            "a smaller nonce passes"
          pure (absorbNonce keccak model (nonceScalar nonce)).2

end RustProperty

/-- The driver: the Rust binary's path may be given, and after it the number of cases of each. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/rust-property/target/release/leanvm-rust-property"
  let rust ← RustProperty.Driver.start path
  let cases (p : Property IO) : Property IO := (args[1]?.bind String.toNat?).elim p p.withTests
  let ok ← checkGroup "the Rust primitives against the Lean definitions" [
    ("K in the verifier and both provers", cases (RustProperty.fieldK rust)),
    ("E in the verifier and both provers", cases (RustProperty.fieldE rust)),
    ("E products two and four at once", cases (RustProperty.fieldBatches rust)),
    ("eq_eval, eq_table and poly_eval of both trees", cases (RustProperty.equalityAndPolynomials rust)),
    ("eq_table in parallel", cases (RustProperty.equalityTableInParallel rust)),
    ("mle_eval and mle_eval_par of both trees", cases (RustProperty.multilinearExtension rust)),
    ("mle_eval_par of an empty table of fewer than three variables",
      cases (RustProperty.multilinearExtensionOfAShortTable rust)),
    ("powers and indices of both trees", cases (RustProperty.powersAndIndices rust)),
    ("the stable tree's fold and dot", cases (RustProperty.foldAndDot rust)),
    ("Keccak-f[1600]", cases (RustProperty.permutation rust)),
    ("Keccak-f[1600], many states", cases (RustProperty.permutationMany rust)),
    ("Keccak-256", cases (RustProperty.hash rust)),
    ("Keccak-256, many inputs", cases (RustProperty.hashMany rust)),
    ("the streamed hasher", cases ((RustProperty.hasher rust).property (.linear 1 30))),
    ("the prover's sponge", cases ((RustProperty.sponge rust).property (.linear 1 40)))]
  return if ok then 0 else 1
