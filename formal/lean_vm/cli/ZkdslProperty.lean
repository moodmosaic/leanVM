import Hedgehog
import Statement.Field
import Statement.Keccak
import Statement.LeanIsa

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

A fifth as many programs are also proved and given to the two verifiers, the statement's compiled
(`lake exe leanvm-verify`) and the Rust (`scripts/rust-verifier-cli`): both must accept the proof,
and on the proof, the public input or the bytecode altered they must give the same verdict.

A program the compiler mistranslates, or constant arithmetic the compiler folds wrongly, or an
instruction a prover executes wrongly, publishes other words than the Lean ones and fails the first;
a published word that is not enforced fails the second. A failure is shrunk to a small program
(lean-hedgehog), printed with the words expected.

    cargo build --release --manifest-path scripts/zkdsl-property/Cargo.toml
    lake build zkdsl-property
    lake build leanvm-verify && cargo build --release --manifest-path scripts/rust-verifier-cli/Cargo.toml
    lake exe zkdsl-property           # 100 programs; a fifth as many through the two verifiers
    lake exe zkdsl-property scripts/zkdsl-property/target/release/leanvm-zkdsl-property 20000
-/

open Hedgehog LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

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

/-- The two cells of the Keccak-256 digest of some cells' first `length` bytes: a cell is two
lanes, sixteen bytes. -/
def digestCells (cells : List E) (length : ℕ) : E × E :=
  let digest := keccak256 ((cells.flatMap E.toBytes).take length)
  (E.ofLimbs (K.ofLane digest[0]) (K.ofLane digest[1]),
    E.ofLimbs (K.ofLane digest[2]) (K.ofLane digest[3]))

/-- The address of index `i`, `g^i`, as a word. -/
def address (i : ℕ) : E := power (ofK g) i

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
  /-- The prover's witness streams a `hint_witness` program pops, a name's entries in pop order. -/
  witness : List (String × List (List E)) := []

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

/-- The prover's witness stream as the harness takes it: a name, an entry's length, and the
entry's limbs, the groups in the order the entries are popped, a name's groups its successive
entries. -/
def witnessWords (w : List (String × List (List E))) : List String :=
  w.flatMap fun (name, entries) => entries.flatMap fun values =>
    [name, toString values.length] ++ values.flatMap limbs

/-- The thirteen input cells of a `keccak(.., cap=)` step: the four message cells, four zeros,
and the five capacity cells, the first in cell eight, whose high limb holds no lane. -/
def duplexCells (message capacity : List E) : List E := message ++ [0, 0, 0, 0] ++ capacity

/-- The step's output cells, in the even layout: the first of them the challenge the guest reads. -/
def duplexOut (cells : List E) : List E :=
  let state : LeanVM.Semantics.KeccakState :=
    LeanVM.Semantics.stateOfCells (fun c => cells.getD c.val 0) false
  (List.finRange 13).map fun c =>
    LeanVM.Semantics.cellsOfState (LeanVM.Semantics.keccakF1600 state) false c

/-- One more statement of `main`. -/
def genStatement (helpers : Helpers) (s : Scope) : Gen Scope := do
  let v := s!"v{s.fresh}"
  let (a, x) ← genOperand s
  let (b, y) ← genOperand s
  let kind ← Gen.nat (.constant 0 34)
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
  | 11 => do
    let exponent ← Gen.nat (.constant 0 6)
    pure (s.bind s!"    {v} = same({a}) ** {exponent}" (power x exponent) true)
  | 12 => do
    -- One `KECCAK`: the hash of four cells' first 64, 48, 32 or 16 bytes; a cell past them is `0`.
    let (c, z) ← genOperand s
    let (d, w) ← genOperand s
    let kept ← Gen.nat (.constant 1 4)
    let words := (List.zip [a, b, c, d] [x, y, z, w]).zipIdx.map fun ((name, value), i) ↦
      if i < kept then (name, value) else ("0", 0)
    let name (i : ℕ) := (words.getD i ("0", 0)).1
    let (d0, d1) := digestCells (words.map (·.2)) (16 * kept)
    let k := s!"k{s.fresh}"
    let length := if kept = 4 then "" else s!", len={16 * kept}"
    let lines := s.lines ++ #[s!"    {k} = StackBuf(2)",
      s!"    keccak([{name 0}, {name 1}], [{name 2}, {name 3}], {k}{length})"]
    let s := { s with lines }.bind s!"    {v} = {k}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {k}[1]" d1 true)
  | 13 => do
    -- `keccak_cells`: the hash of a run of cells, of several blocks, ending anywhere in its last
    -- cell, whose bytes after the end are zero.
    let count ← Gen.nat (.linear 1 20)
    let last ← Gen.nat (.constant 1 16)
    let cells ← Gen.list (.singleton count) (genOperand s)
    let tail ← Gen.nat (.exponential 0 (2 ^ (8 * last) - 1))
    let cells := if last = 16 then cells else cells.take (count - 1) ++ [(toString tail, word tail)]
    let length := 16 * (count - 1) + last
    let (d0, d1) := digestCells (cells.map (·.2)) length
    let (run, k) := (s!"s{s.fresh}", s!"k{s.fresh}")
    let lines := s.lines ++ #[s!"    {run} = StackBuf({count})"]
      ++ (cells.zipIdx.map fun ((name, _), i) ↦ s!"    {run}[{i}] = {name}").toArray
      ++ #[s!"    {k} = StackBuf(2)",
        s!"    keccak_cells({run}, {k}{if last = 16 then "" else s!", len={length}"})"]
    let s := { s with lines }.bind s!"    {v} = {k}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {k}[1]" d1 true)
  | 14 => do
    -- A range check in the exponent, of a power below its bound.
    let bound ← Gen.nat (.linear 1 40)
    let exponent ← Gen.nat (.constant 0 (bound - 1))
    let s := s.bind s!"    {v} = same(GEN ** {exponent})" (address exponent) true
    pure { s with lines := s.lines.push s!"    assert log({v}) < {bound}" }
  | 15 => do
    -- A dispatch on the log of a power: arm `j` is `pick(a, j)`.
    let arms ← Gen.nat (.constant 1 6)
    let taken ← Gen.nat (.constant 0 (arms - 1))
    let m := s!"m{s.fresh}"
    let lines := s.lines.push s!"    {m} = same(GEN ** {taken})"
    pure ({ s with lines }.bind
      s!"    {v} = match(log({m}), range(0, {arms}), lambda j: pick({a}, j))"
      (x * word taken + word taken) true)
  | 16 => do
    let run := s!"s{s.fresh}"
    let lines := s.lines ++ #[s!"    {run} = StackBuf(3)", s!"    {run}[0] = {a}",
      s!"    {run}[1] = {b}", s!"    {run}[2] = {run}[0] * {run}[1] + {run}[0]"]
    pure ({ s with lines }.bind s!"    {v} = {run}[2]" (x * y + x) true)
  | 17 =>
    -- Two `K` words packed into one, their membership asserted.
    if x.limb 1 ≠ 0 ∨ y.limb 1 ≠ 0 then pure (s.bind s!"    {v} = {a} * {b}" (x * y) false)
    else pure (s.bind s!"    {v} = pack64x2(same({a}), same({b}))"
      (E.ofLimbs (x.limb 0) (y.limb 0)) true)
  | 18 => do
    -- A function of two results.
    let s := s.bind s!"    {v}, v{s.fresh + 1} = two({a}, {b})" (x + y) true
    pure { s with fresh := s.fresh + 1, names := s.names.push (s!"v{s.fresh}", x * y, true) }
  | 19 => do
    -- A chain of three branches.
    let (c, z) ← genOperand s
    let (d, w) ← genOperand s
    if (x + y).limb 1 ≠ 0 ∨ (z + w).limb 1 ≠ 0 then
      pure (s.bind s!"    {v} = {a} * {b}" (x * y) false)
    else
      let taken := if x == y then x else if z != w then z else w
      let cell := s!"r[GEN ** {s.cells}]"
      let lines := s.lines ++ #[s!"    if same({a}) == same({b}):", s!"        {cell} = {a}",
        s!"    elif same({c}) != same({d}):", s!"        {cell} = {c}", "    else:",
        s!"        {cell} = {d}"]
      pure ({ s with lines, cells := s.cells + 1 }.bind s!"    {v} = {cell}" taken true)
  | 20 => do
    -- A runtime loop whose bound is a runtime power, its log bounded first.
    let count ← Gen.nat (.constant 0 5)
    let value := (List.range count).foldl (fun acc _ ↦ acc * x + y) x
    let (h, n, i) := (s!"h{s.fresh}", s!"n{s.fresh}", s!"i{s.fresh}")
    let lines := s.lines ++ #[s!"    {n} = same(GEN ** {count})", s!"    assert log({n}) < 16",
      s!"    {h} = HeapBuf({count + 1})", s!"    {h}[1] = {a}",
      s!"    for {i} in mul_range(1, {n}):", s!"        {h}[{i} * GEN] = {h}[{i}] * {a} + {b}"]
    pure ({ s with lines }.bind s!"    {v} = {h}[GEN ** {count}]" value true)
  | 21 => do
    -- A runtime loop left early: the cell after the last one written is still free.
    let count ← Gen.nat (.constant 1 5)
    let stop ← Gen.nat (.constant 0 count)
    let (c, z) ← genOperand s
    let value (k : ℕ) := (List.range k).foldl (fun acc _ ↦ acc * x + y) x
    let (h, i) := (s!"h{s.fresh}", s!"i{s.fresh}")
    let free := if stop < count ∧ value (stop + 1) ≠ z then
      #[s!"    {h}[GEN ** {stop + 1}] = {c}"] else #[]
    let lines := s.lines ++ #[s!"    {h} = HeapBuf({count + 2})", s!"    {h}[1] = {a}",
      s!"    for {i} in mul_range(1, GEN ** {count}):", s!"        if {i} == GEN ** {stop}:",
      "            return", s!"        {h}[{i} * GEN] = {h}[{i}] * {a} + {b}"] ++ free
    pure ({ s with lines }.bind s!"    {v} = {h}[GEN ** {stop}]" (value stop) true)
  | 22 => do
    -- Compound assignment, in an unrolled loop.
    let count ← Gen.nat (.constant 0 3)
    let value := (List.range count).foldl (fun acc _ ↦ (acc + y) * x) x
    let s := s.bind s!"    {v} = same({a})" value true
    pure { s with lines := s.lines ++ #[s!"    for i{s.fresh} in unroll(0, {count}):",
      s!"        {v} += {b}", s!"        {v} *= {a}"] }
  | 23 => do
    -- A global constant and an element of a constant array, as values.
    let index ← Gen.nat (.constant 0 2)
    pure (s.bind s!"    {v} = same({a}) * TABLE[{index}] + SIZE"
      (x * word ([5, 7, 2 ^ 64 + 11].getD index 0) + word 3) true)
  | 24 => do
    -- Integer arithmetic asked for in a value position.
    let m ← Gen.nat (.constant 0 9)
    let n ← Gen.nat (.constant 0 9)
    pure (s.bind s!"    {v} = same({a}) + const({m} * {n} + {m})" (x + word (m * n + m)) true)
  | 25 => do
    -- A hash of heap slices.
    let (c, z) ← genOperand s
    let (d, w) ← genOperand s
    let (d0, d1) := digestCells [x, y, z, w] 64
    let (h, k) := (s!"h{s.fresh}", s!"k{s.fresh}")
    let lines := s.lines ++ #[s!"    {h} = HeapBuf(4)", s!"    {h}[1] = {a}", s!"    {h}[GEN] = {b}",
      s!"    {h}[GEN ** 2] = {c}", s!"    {h}[GEN ** 3] = {d}", s!"    {k} = StackBuf(2)",
      s!"    keccak({h}[0:2], {h}[2:4], {k})"]
    let s := { s with lines }.bind s!"    {v} = {k}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {k}[1]" d1 true)
  | 26 => do
    -- A hash of two slices of a stack run into a third.
    let (c, z) ← genOperand s
    let (d, w) ← genOperand s
    let (d0, d1) := digestCells [x, y, z, w] 64
    let t := s!"t{s.fresh}"
    let lines := s.lines ++ #[s!"    {t} = StackBuf(6)", s!"    {t}[0] = {a}", s!"    {t}[1] = {b}",
      s!"    {t}[2] = {c}", s!"    {t}[3] = {d}", s!"    keccak({t}[0:2], {t}[2:4], {t}[4:6])"]
    let s := { s with lines }.bind s!"    {v} = {t}[4]" d0 true
    pure (s.bind s!"    v{s.fresh} = {t}[5]" d1 true)
  | 27 => do
    -- A hash of 128 bytes: four words and a tail of four cells.
    let words ← Gen.list (.singleton 6) (genOperand s)
    let cells := [(a, x), (b, y)] ++ words
    let (d0, d1) := digestCells (cells.map (·.2)) 128
    let name (i : ℕ) := (cells.getD i ("0", 0)).1
    let (t, k) := (s!"t{s.fresh}", s!"k{s.fresh}")
    let lines := s.lines ++ #[s!"    {t} = StackBuf(4)", s!"    {t}[0] = {name 4}",
      s!"    {t}[1] = {name 5}", s!"    {t}[2] = {name 6}", s!"    {t}[3] = {name 7}",
      s!"    {k} = StackBuf(2)",
      s!"    keccak([{name 0}, {name 1}], [{name 2}, {name 3}], {k}, tail={t}[0:4])"]
    let s := { s with lines }.bind s!"    {v} = {k}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {k}[1]" d1 true)
  | 29 => do
    -- A hash of two block pairs, zero-padded to whole blocks, continued from its state: 17 cells
    -- absorbed with `final=0`, two more into the digest of 304 bytes.
    let cells ← Gen.list (.singleton 19) (genOperand s)
    let (n17, _) := cells.getD 17 ("0", 0)
    let (n18, _) := cells.getD 18 ("0", 0)
    let (d0, d1) := digestCells (cells.map (·.2)) 304
    let (pair, st, k) := (s!"s{s.fresh}", s!"t{s.fresh}", s!"k{s.fresh}")
    let lines := s.lines ++ #[s!"    {pair} = StackBuf(17)"]
      ++ (cells.take 17 |>.zipIdx.map fun ((name, _), i) => s!"    {pair}[{i}] = {name}").toArray
      ++ #[s!"    {st} = StackBuf(13)", s!"    keccak_cells({pair}, {st}, final=0)",
        s!"    {k} = StackBuf(2)", s!"    keccak_cells([{n17}, {n18}], {k}, state={st})"]
    let s := { s with lines }.bind s!"    {v} = {k}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {k}[1]" d1 true)
  | 30 => do
    -- A hash read in place: the message's last cell and the padding's, the tail's cells past
    -- `len` left unwritten and set to the padding by the compiler.
    let (c, z) ← genOperand s
    let (k0, x0) ← genOperand s
    let (k1, x1) ← genOperand s
    let (d0, d1) := digestCells [x, y, z, x0, x1] 80
    let (kids, k) := (s!"k{s.fresh}", s!"h{s.fresh}")
    let lines := s.lines ++ #[s!"    {kids} = StackBuf(5)", s!"    {kids}[0] = {k0}",
      s!"    {kids}[1] = {k1}", s!"    {k} = StackBuf(2)",
      s!"    keccak([{a}, {b}], [{c}, {kids}[0]], {k}, tail={kids}[1:5], len=80, pad_tail=1)"]
    let s := { s with lines }.bind s!"    {v} = {k}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {k}[1]" d1 true)
  | 31 => do
    -- Two duplex steps: the transcript's capacity carried between them, the challenge each step's
    -- first cell.
    let (s0, w0) ← genOperand s
    let (s1, w1) ← genOperand s
    let (s2, w2) ← genOperand s
    let (s3, w3) ← genOperand s
    let (s4, w4) ← genOperand s
    let (p0, v0) ← genOperand s
    let (p1, v1) ← genOperand s
    let out1 := duplexOut (duplexCells [v0, v1, 0, 0] [w0, w1, w2, w3, w4])
    let out2 := duplexOut (duplexCells [0, 0, 0, 0] (out1.drop 8))
    let (d0, d1) := (out1.getD 0 0, out2.getD 0 0)
    let (seed, rate, sp, nxt) := (s!"s{s.fresh}", s!"t{s.fresh}", s!"u{s.fresh}", s!"w{s.fresh}")
    let lines := s.lines ++ #[s!"    {seed} = [{s0}, {s1}, {s2}, {s3}, {s4}]",
      s!"    {rate} = StackBuf(2)", s!"    {rate}[0] = {p0}", s!"    {rate}[1] = {p1}",
      s!"    {sp} = StackBuf(13)", s!"    keccak({rate}[0:2], [0, 0], {sp}, cap={seed})",
      s!"    {nxt} = StackBuf(13)", s!"    keccak([0, 0], [0, 0], {nxt}, cap={sp})"]
    let s := { s with lines }.bind s!"    {v} = {sp}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {nxt}[0]" d1 true)
  | 32 => do
    -- A run of cells through a call: in through a `StackBuf` parameter, out through a `StackBuf`
    -- return, and the product of its cells through a scalar return.
    let (b0, x0) ← genOperand s
    let (b1, x1) ← genOperand s
    let (b, r) := (s!"b{s.fresh}", s!"r{s.fresh}")
    let lines := s.lines ++ #[s!"    {b} = StackBuf(2)", s!"    {b}[0] = {b0}",
      s!"    {b}[1] = {b1}", s!"    {r} = swap({b})"]
    let s := { s with lines }.bind s!"    {v} = {r}[0]" x1 true
    let s := s.bind s!"    v{s.fresh} = {r}[1]" x0 true
    pure (s.bind s!"    v{s.fresh} = dot({b})" (x0 * x1) true)
  | 33 => do
    -- Prover-supplied values: two entries of a stream the program pins by asserts, a heap slice
    -- of another, and the first stream's second entry in a fourth cell.
    let w0 ← genLiteral
    let w1 ← genLiteral
    let w2 ← genLiteral
    let w3 ← genLiteral
    let w4 ← genLiteral
    let w5 ← genLiteral
    let (sb, hb, q) := (s!"h{s.fresh}", s!"q{s.fresh}", String.singleton '"')
    let lines := s.lines ++ #[s!"    {sb} = StackBuf(2)", s!"    hint_witness({sb}, {q}r{q})",
      s!"    assert {sb}[0] == {literal (word w0)}",
      s!"    assert {sb}[1] == {literal (word w1)}",
      s!"    {hb} = HeapBuf(4)", s!"    hint_witness({hb}[0:3], {q}h{q})",
      s!"    assert {hb}[1] == {literal (word w2)}",
      s!"    assert {hb}[GEN] == {literal (word w3)}",
      s!"    assert {hb}[GEN ** 2] == {literal (word w4)}",
      s!"    hint_witness({hb}[3:4], {q}r{q})",
      s!"    assert {hb}[GEN ** 3] == {literal (word w5)}"]
    let s := { s with lines }.bind s!"    {v} = {sb}[0]" (word w0) true
    let s := s.bind s!"    v{s.fresh} = {hb}[GEN ** 2]" (word w4) true
    pure { s with witness := s.witness ++
      [("r", [[word w0, word w1], [word w5]]), ("h", [[word w2, word w3, word w4]])] }
  | 34 => do
    -- A function that calls itself at runtime, a g-power counting down by division: one frame
    -- per call.
    let count ← Gen.nat (.constant 1 6)
    let (x0, i0) ← genOperand s
    let (a0, m0) ← genOperand s
    let (c0, b0) ← genOperand s
    let value := (List.range count).foldl (fun acc _ => acc * m0 + b0) i0
    pure (s.bind s!"    {v} = rec(GEN ** {count}, {x0}, {a0}, {c0})" value true)
  | _ => do
    -- `keccak_cells` of words named in a list, read where they lie.
    let words ← Gen.list (.linear 1 12) (genOperand s)
    let (d0, d1) := digestCells (words.map (·.2)) (16 * words.length)
    let k := s!"k{s.fresh}"
    let lines := s.lines ++ #[s!"    {k} = StackBuf(2)",
      s!"    keccak_cells([{", ".intercalate (words.map (·.1))}], {k})"]
    let s := { s with lines }.bind s!"    {v} = {k}[0]" d0 true
    pure (s.bind s!"    v{s.fresh} = {k}[1]" d1 true)

/-- A statement that cannot hold, which an execution must refuse. -/
def genFalse (s : Scope) : Gen (Array String) := do
  let (a, x) ← genOperand s
  let (b, y) ← genOperand s
  let kind ← Gen.nat (.constant 0 3)
  let test := if x == y then "!=" else "=="
  match kind with
  | 0 => pure #[s!"    assert same({a}) {test} same({b})"]
  | 1 => do
    let bound ← Gen.nat (.linear 1 30)
    let over ← Gen.nat (.constant 0 5)
    pure #[s!"    assert log(same(GEN ** {bound + over})) < {bound}"]
  | 2 =>
    -- Two stores of different words into one cell.
    if x == y then pure #[s!"    assert same({a}) {test} same({b})"]
    else pure #[s!"    r[GEN ** {16}] = {a}", s!"    r[GEN ** {16}] = {b}"]
  | _ => do
    -- A hash into a cell that already holds another word.
    let (d0, _) := digestCells [x, y, x, y] 64
    pure #["    wrong = StackBuf(2)", s!"    wrong[0] = {literal (d0 + 1)}",
      s!"    keccak([{a}, {b}], [{a}, {b}], wrong)"]

/-- A program: its source, the two words it publishes, and the witness streams its
`hint_witness` calls pop, a name's entries in pop order. -/
structure Program where
  source : String
  published : E × E
  witness : List (String × List (List E)) := []

/-- The most heap cells the branches of a program use. -/
def branchCells : ℕ := 16

/-- A program; with `refused`, one whose last statement before it publishes cannot hold. -/
def genProgramThat (refused : Bool) : Gen Program := do
  let plain ← Gen.list (.linear 1 2) (genBody 2)
  let inlined ← Gen.list (.linear 1 2) (genBody 2)
  let first ← genLiteral
  let start : Scope := ({} : Scope).bind s!"    v0 = {first}" (word first) false
  let count ← Gen.nat (.linear 1 14)
  let scope ← (List.range count).foldlM (fun s _ ↦
    if s.cells < branchCells then genStatement ⟨plain, inlined⟩ s else pure s) start
  let false_ ← if refused then genFalse scope else pure #[]
  let (a, x, _) ← genName scope
  let (b, y, _) ← genName scope
  let functions (prefix_ : String) (decorator : List String) (bodies : List Body) :=
    bodies.zipIdx.flatMap fun (body, i) ↦
      decorator ++ [s!"def {prefix_}{i}(a, b):", s!"    return {body.text}", ""]
  let lines := ["from snark_lib import *", "", "SIZE = 3", "TABLE = [5, 7, 18446744073709551627]",
      "", "def same(a):", "    return a", "", "def two(a, b):", "    return a + b, a * b", "",
      "def pick(a, k: Const):", "    return a * k + k", "",
      "@inline", "def pack64x2(a, b):", "    assert_in_k(a, b)",
      "    return a + 18446744073709551616 * b", "",
      "def swap(s: StackBuf(2)):", "    t = StackBuf(2)", "    t[0] = s[1]", "    t[1] = s[0]",
      "    return t", "", "def dot(s: StackBuf(2)):", "    return s[0] * s[1]", "",
      "def rec(i, acc, a, b):", "    if i == GEN ** 0:", "        return acc",
      "    return rec(i / (GEN ** 1), acc * a + b, a, b)", ""]
    ++ functions "f" [] plain ++ functions "g" ["@inline"] inlined
    ++ ["def main():", s!"    r = HeapBuf({branchCells + 1})"] ++ scope.lines.toList
    ++ false_.toList
    ++ ["    p = GEN ** 0", s!"    p[1] = {a}", s!"    p[GEN] = {b}", "    return", ""]
  pure ⟨"\n".intercalate lines, (x, y), scope.witness⟩

def genProgram : Gen Program := genProgramThat false

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
      (← rust.ask (["exec", tree, path] ++ input ++ witnessWords program.witness)) === "ok"
      let refused ← rust.ask (["exec", tree, path] ++ other ++ witnessWords program.witness)
      ensure (refused.startsWith "execute-error") s!"another public input: {refused}"
    -- A hinted value the prover gives wrongly is refused: the entry is the program's own.
    match program.witness with
    | (name, entries) :: _ =>
      match entries with
      | entry :: _ =>
        match entry with
        | value :: rest =>
          let values := (value + word wrong) :: rest
          let tampered := program.witness.map fun (n, es) =>
            if n == name then (n, values :: es.tail) else (n, es)
          let refused ← rust.ask (["exec", "s", path] ++ input ++ witnessWords tampered)
          ensure (refused.startsWith "execute-error") s!"a wrong witness: {refused}"
        | [] => pure ()
      | [] => pure ()
    | [] => pure ()
    let stable ← rust.ask (["prove", "s", path] ++ input ++ witnessWords program.witness)
    let experimental ← rust.ask (["prove", "x", path] ++ input ++ witnessWords program.witness)
    ensure (stable.startsWith "ok ") s!"the stable prover: {stable}"
    experimental === stable

/-- A program with a statement that cannot hold is refused by both trees, on the words it would
publish. -/
def refuses (rust : Driver) (dir : System.FilePath) : Property IO := propertyM do
  let program ← forAllWith (fun p ↦ s!"{p.source}\n# witness {repr p.witness}") (genProgramThat true)
  pure do
    let path := (dir / "refused.py").toString
    evalIO (IO.FS.writeFile path program.source)
    let (x, y) := program.published
    for tree in ["s", "x"] do
      let outcome ← rust.ask (["exec", tree, path] ++ limbs x ++ limbs y ++ witnessWords program.witness)
      annotate s!"tree {tree}: {outcome}"
      ensure (outcome.startsWith "execute-error" || outcome.startsWith "panic")
        "a statement that cannot hold was executed"

/-! ## The two verifiers on the proofs of generated programs -/

/-- Where a proof's files are altered, and to what. -/
inductive File where
  | wire
  | publicInput
  | bytecode
  deriving Repr, BEq

structure Alteration where
  file : File
  /-- A position, reduced modulo the file's length. -/
  position : ℕ
  byte : UInt8
  deriving Repr

/-- An alteration: mostly of the proof, near its start, where the scalars are, or anywhere. -/
def genAlteration : Gen Alteration := do
  let file ← Gen.frequency [(6, pure .wire), (1, pure .publicInput), (1, pure .bytecode)]
  let position ← Gen.choice [Gen.nat (.linear 0 4000), Gen.nat (.exponential 0 (2 ^ 24))]
  pure ⟨file, position, ← Gen.integral (.constant 0 255)⟩

/-- The file's bytes altered. -/
def alter (alterations : List Alteration) (file : File) (bytes : ByteArray) : ByteArray :=
  alterations.foldl (fun bytes a ↦
    if a.file == file && bytes.size ≠ 0 then bytes.set! (a.position % bytes.size) a.byte else bytes)
    bytes

/-- The Lean verifier's verdict on a wire proof's files (`lake exe leanvm-verify`). -/
def leanAccepts (bytecode publicInput wire : String) : IO Bool := do
  let out ← IO.Process.output
    { cmd := ".lake/build/bin/leanvm-verify", args := #[bytecode, publicInput, wire] }
  pure (out.exitCode == 0)

/-- The proof of a generated program is accepted by the statement's verifier, compiled, and by the
Rust one; and on the proof, the public input or the bytecode altered, the two give the same
verdict. The Lean verifier is the one proved sound: a proof it refuses and the Rust accepts is what
no theorem covers. -/
def verifiers (rust verifier : Driver) (dir : System.FilePath) : Property IO := propertyM do
  let program ← forAllWith (fun p ↦
    s!"{p.source}\n# publishes {literal p.published.1}, {literal p.published.2}") genProgram
  let alterations ← forAll (Gen.list (.linear 1 3) genAlteration)
  pure do
    let file (name : String) : String := (dir / name).toString
    evalIO (IO.FS.writeFile (file "verified.py") program.source)
    let (x, y) := program.published
    let exported ← rust.ask
      (["export", "s", file "verified.py"] ++ limbs x ++ limbs y ++ [dir.toString]
        ++ witnessWords program.witness)
    ensure (exported.startsWith "ok ") s!"the stable prover: {exported}"
    let honest := [file "bytecode.bin", file "public_input.bin", file "proof.wire"]
    (← verifier.ask honest) === "accept"
    ensure (← evalIO (leanAccepts (file "bytecode.bin") (file "public_input.bin") (file "proof.wire")))
      "the Lean verifier refuses the Rust prover's proof"
    for (name, target) in [("bytecode.bin", File.bytecode), ("public_input.bin", .publicInput),
        ("proof.wire", .wire)] do
      let bytes ← evalIO (IO.FS.readBinFile (file name))
      evalIO (IO.FS.writeBinFile (file ("altered-" ++ name)) (alter alterations target bytes))
    let altered := ["altered-bytecode.bin", "altered-public_input.bin", "altered-proof.wire"].map file
    let rustVerdict ← verifier.ask altered
    annotate s!"the Rust verifier, altered: {rustVerdict}"
    let leanVerdict ← evalIO (leanAccepts (altered.getD 0 "") (altered.getD 1 "") (altered.getD 2 ""))
    (rustVerdict == "accept") === leanVerdict

end ZkdslProperty

/-- The driver: the Rust binary's path may be given, and after it the number of programs. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/zkdsl-property/target/release/leanvm-zkdsl-property"
  let rust ← ZkdslProperty.Driver.start path
  let verifier ← do
    let child ← IO.Process.spawn
      { cmd := "scripts/rust-verifier-cli/target/release/leanvm-rust-verify", args := #["--batch"],
        stdin := .piped, stdout := .piped, stderr := .inherit }
    pure (⟨child.stdin, child.stdout⟩ : ZkdslProperty.Driver)
  let count := (args[1]?.bind String.toNat?).getD 100
  let dir ← IO.FS.createTempDir
  let cases (p : Property IO) : Property IO := (args[1]?.bind String.toNat?).elim p p.withTests
  let ok ← checkGroup "the zkDSL compiler and the provers on generated programs"
    [("a program publishes what the Lean field computes",
      cases (ZkdslProperty.compiles rust dir)),
     ("a statement that cannot hold is refused", cases (ZkdslProperty.refuses rust dir)),
     ("the Lean and the Rust verifier agree on its proof, altered or not",
      (ZkdslProperty.verifiers rust verifier dir).withTests (count / 5 + 1))]
  IO.FS.removeDirAll dir
  return if ok then 0 else 1
