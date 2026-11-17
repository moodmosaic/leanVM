import Hedgehog
import Statement.Field

/-!
# The zkDSL compiler and the provers on generated programs

A generated zkDSL program computes two words from literals by field arithmetic, through helper
functions, inlined functions, unrolled loops, runtime loops over a heap buffer, branches and
assertions, and publishes them. While it writes the program this driver computes the same two words
with the Lean field (`Statement/Field.lean`), which the theorems are about. Then the Rust
(`scripts/zkdsl-property`, `leanvm-zkdsl-property`: `zkdsl_compiler::parse` and `compile`, and
`cpu::execute`, `prove` and `verify` of either prover tree) must

* execute the program on those two words as its public input, in both trees;
* refuse to execute it on any other public input, since a published word is an assertion;
* prove it and verify the proof, in both trees, and the two proofs must be the same bytes.

A program the compiler mistranslates, or constant arithmetic the compiler folds wrongly, or an
instruction a prover executes wrongly, publishes other words than the Lean ones and fails the first;
a published word that is not enforced fails the second. A failure is shrunk to a small program
(lean-hedgehog), printed with the words expected.

    cargo build --release --manifest-path scripts/zkdsl-property/Cargo.toml
    lake build zkdsl-property
    lake exe zkdsl-property           # 100 programs
    lake exe zkdsl-property scripts/zkdsl-property/target/release/leanvm-zkdsl-property 20000
-/

open Hedgehog LeanVM.Parameters

namespace ZkdslProperty

/-! ## The process -/

/-- The Rust process: one command line in, one result line out. -/
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

/-! ## Words -/

/-- The word an integer literal below `2^128` denotes: its low 64 bits in limb `0`. -/
def word (n : ℕ) : E := E.ofLimbs (K.ofBits (n % 2 ^ 64)) (K.ofBits (n / 2 ^ 64))

/-- The literal of a word. -/
def literal (x : E) : ℕ := (x.limb 0).lane.toNat + 2 ^ 64 * (x.limb 1).lane.toNat

/-- A word's two limbs, as the Rust harness takes a public-input word. -/
def limbs (x : E) : List String := [toString (x.limb 0).lane.toNat, toString (x.limb 1).lane.toNat]

/-- `x ^ n` by squaring. -/
def power (x : E) (n : ℕ) : E :=
  (List.range n.size).foldr (fun i acc ↦ if n.testBit i then acc * acc * x else acc * acc) 1

/-! ## Helper functions: an expression of two parameters -/

/-- The body of a generated helper. -/
inductive Body where
  | a
  | b
  | lit (n : ℕ)
  | add (x y : Body)
  | mul (x y : Body)

def Body.eval (a b : E) : Body → E
  | .a => a
  | .b => b
  | .lit n => word n
  | .add x y => x.eval a b + y.eval a b
  | .mul x y => x.eval a b * y.eval a b

def Body.text : Body → String
  | .a => "a"
  | .b => "b"
  | .lit n => toString n
  | .add x y => s!"({x.text} + {y.text})"
  | .mul x y => s!"({x.text} * {y.text})"

/-- A literal: a digit, a `K` word, or any word. -/
def genLiteral : Gen ℕ :=
  Gen.choice [Gen.nat (.constant 0 9), Gen.nat (.exponential 0 (2 ^ 64 - 1)),
    Gen.nat (.exponential 0 (2 ^ 128 - 1))]

def genBody : ℕ → Gen Body
  | 0 => Gen.choice [pure .a, pure .b, .lit <$> genLiteral]
  | depth + 1 => Gen.choice [pure .a, pure .b, .lit <$> genLiteral,
      .add <$> genBody depth <*> genBody depth, .mul <$> genBody depth <*> genBody depth]

/-! ## The program, written and evaluated together -/

/-- What is known while `main` is written: its lines, the names bound with their words and whether
each is a runtime cell (the result of a call or of a heap read) and not a folded constant, the heap
cells used, and the names used. -/
structure Scope where
  lines : Array String := #[]
  names : Array (String × E × Bool) := #[]
  cells : ℕ := 0
  fresh : ℕ := 0

def Scope.bind (s : Scope) (line : String) (value : E) (runtime : Bool) : Scope :=
  { s with lines := s.lines.push line, fresh := s.fresh + 1,
           names := s.names.push (s!"v{s.fresh}", value, runtime) }

/-- A name bound so far. -/
def genName (s : Scope) : Gen (String × E × Bool) := do
  let i ← Gen.nat (.constant 0 (s.names.size - 1))
  pure (s.names.getD i ("v0", 0, false))

/-- An operand: a name, or a literal. -/
def genOperand (s : Scope) : Gen (String × E) :=
  Gen.frequency [(3, (fun x ↦ (x.1, x.2.1)) <$> genName s),
    (1, (fun n ↦ (toString n, word n)) <$> genLiteral)]

/-- The helpers of a program: the plain ones, each called in a frame of its own, and the inlined
ones. -/
structure Helpers where
  plain : List Body
  inlined : List Body

/-- One more statement of `main`. -/
def genStatement (helpers : Helpers) (s : Scope) : Gen Scope := do
  let v := s!"v{s.fresh}"
  let (a, x) ← genOperand s
  let (b, y) ← genOperand s
  let kind ← Gen.nat (.constant 0 11)
  match kind with
  | 0 => do
    let n ← genLiteral
    pure (s.bind s!"    {v} = {n}" (word n) false)
  | 1 => pure (s.bind s!"    {v} = {a} + {b}" (x + y) false)
  | 2 => pure (s.bind s!"    {v} = {a} * {b}" (x * y) false)
  | 3 =>
    if y = 0 then pure (s.bind s!"    {v} = {a} + {b}" (x + y) false)
    else pure (s.bind s!"    {v} = {a} / {b}" (x * y⁻¹) true)
  | 4 => pure (s.bind s!"    {v} = same({a})" x true)
  | 5 => do
    let i ← Gen.nat (.constant 0 (helpers.plain.length - 1))
    match helpers.plain[i]? with
    | some body => pure (s.bind s!"    {v} = f{i}({a}, {b})" (body.eval x y) true)
    | none => pure (s.bind s!"    {v} = same({a})" x true)
  | 6 => do
    let i ← Gen.nat (.constant 0 (helpers.inlined.length - 1))
    match helpers.inlined[i]? with
    | some body => pure (s.bind s!"    {v} = g{i}({a}, {b})" (body.eval x y) true)
    | none => pure (s.bind s!"    {v} = same({a})" x true)
  | 7 => do
    -- An unrolled loop: the name is bound again by every copy of the body.
    let count ← Gen.nat (.constant 0 4)
    let value := (List.range count).foldl (fun acc _ ↦ acc * x + y) x
    let s := s.bind s!"    {v} = same({a})" value true
    let lines := (s.lines.push s!"    for i{s.fresh} in unroll(0, {count}):").push
      s!"        {v} = {v} * {a} + {b}"
    pure { s with lines }
  | 8 => do
    -- A runtime loop over a heap buffer: cell `i + 1` from cell `i`.
    let count ← Gen.nat (.constant 1 5)
    let value := (List.range count).foldl (fun acc _ ↦ acc * x + y) x
    let h := s!"h{s.fresh}"
    let lines := s.lines ++ #[s!"    {h} = HeapBuf({count + 1})", s!"    {h}[1] = {a}",
      s!"    for i{s.fresh} in mul_range(1, GEN ** {count}):",
      s!"        {h}[i{s.fresh} * GEN] = {h}[i{s.fresh}] * {a} + {b}"]
    pure ({ s with lines }.bind s!"    {v} = {h}[GEN ** {count}]" value true)
  | 9 => do
    -- A branch on two words whose sum is in `K`; each side writes the cell the join reads.
    if (x + y).limb 1 ≠ 0 then pure (s.bind s!"    {v} = {a} + {b}" (x + y) false)
    else
      let (c, z) ← genOperand s
      let (d, w) ← genOperand s
      let equal ← Gen.bool
      let taken := if (x == y) == equal then z else w
      let test := if equal then "==" else "!="
      let lines := s.lines ++ #[s!"    if same({a}) {test} same({b}):",
        s!"        r[GEN ** {s.cells}] = {c}", "    else:", s!"        r[GEN ** {s.cells}] = {d}"]
      pure ({ s with lines, cells := s.cells + 1 }.bind s!"    {v} = r[GEN ** {s.cells}]"
        taken true)
  | 10 => do
    -- An assertion that holds, of the kind the two words allow.
    let test := if x == y then "==" else "!="
    pure { s with lines := s.lines.push s!"    assert same({a}) {test} same({b})" }
  | _ => do
    let exponent ← Gen.nat (.constant 0 6)
    pure (s.bind s!"    {v} = same({a}) ** {exponent}" (power x exponent) true)

/-- A program: its source, and the two words it publishes. -/
structure Program where
  source : String
  published : E × E

/-- The most heap cells the branches of a program use. -/
def branchCells : ℕ := 16

def genProgram : Gen Program := do
  let plain ← Gen.list (.linear 1 2) (genBody 2)
  let inlined ← Gen.list (.linear 1 2) (genBody 2)
  let first ← genLiteral
  let start : Scope := ({} : Scope).bind s!"    v0 = {first}" (word first) false
  let count ← Gen.nat (.linear 1 14)
  let scope ← (List.range count).foldlM (fun s _ ↦
    if s.cells < branchCells then genStatement ⟨plain, inlined⟩ s else pure s) start
  let (a, x, _) ← genName scope
  let (b, y, _) ← genName scope
  let functions (prefix_ : String) (decorator : List String) (bodies : List Body) :=
    bodies.zipIdx.flatMap fun (body, i) ↦
      decorator ++ [s!"def {prefix_}{i}(a, b):", s!"    return {body.text}", ""]
  let lines := ["from snark_lib import *", "", "def same(a):", "    return a", ""]
    ++ functions "f" [] plain ++ functions "g" ["@inline"] inlined
    ++ ["def main():", s!"    r = HeapBuf({branchCells})"] ++ scope.lines.toList
    ++ ["    p = GEN ** 0", s!"    p[1] = {a}", s!"    p[GEN] = {b}", "    return", ""]
  pure ⟨"\n".intercalate lines, (x, y)⟩

/-! ## The property -/

/-- The program runs on the words the Lean field gives it, on no others, and both trees prove it
with the same bytes. -/
def compiles (rust : Driver) (dir : System.FilePath) : Property IO := propertyM do
  let program ← forAllWith (fun p ↦
    s!"{p.source}\n# publishes {literal p.published.1}, {literal p.published.2}") genProgram
  let wrong ← forAll (Gen.nat (.exponential 1 (2 ^ 128 - 1)))
  let second ← forAll Gen.bool
  pure do
    let path := (dir / "program.py").toString
    evalIO (IO.FS.writeFile path program.source)
    let (x, y) := program.published
    let input := limbs x ++ limbs y
    let other := if second then limbs x ++ limbs (y + word wrong) else limbs (x + word wrong) ++ limbs y
    for tree in ["s", "x"] do
      annotate s!"tree {tree}"
      (← rust.ask (["exec", tree, path] ++ input)) === "ok"
      let refused ← rust.ask (["exec", tree, path] ++ other)
      ensure (refused.startsWith "execute-error") s!"another public input: {refused}"
    let stable ← rust.ask (["prove", "s", path] ++ input)
    let experimental ← rust.ask (["prove", "x", path] ++ input)
    ensure (stable.startsWith "ok ") s!"the stable prover: {stable}"
    experimental === stable

end ZkdslProperty

/-- The driver: the Rust binary's path may be given, and after it the number of programs. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/zkdsl-property/target/release/leanvm-zkdsl-property"
  let rust ← ZkdslProperty.Driver.start path
  let dir ← IO.FS.createTempDir
  let property := ZkdslProperty.compiles rust dir
  let ok ← checkGroup "the zkDSL compiler and the provers on generated programs"
    [("a program publishes what the Lean field computes",
      (args[1]?.bind String.toNat?).elim property property.withTests)]
  IO.FS.removeDirAll dir
  return if ok then 0 else 1
