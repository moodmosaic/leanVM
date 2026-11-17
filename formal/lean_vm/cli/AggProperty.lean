import Hedgehog

/-!
# The aggregation: which claims a proof verifies for

Soundness across recursion levels is not proved (`formal/README.md`), and what binds a proof to its
claims is Rust: the claim lists' digests, the DA digest and the statement's digest
(`crates/aggregation`). This driver builds trees of aggregated leanSPHINCS and leanXMSS signatures
and blobs through the public API (`scripts/agg-property`, `leanvm-agg-property`: `lean_vm::aggregate`
and `AggregateProof::verify`) and requires, of every proof it made,

* it verifies for its own claims: the union of its children's and its own signatures' claims, and
  its own blob's root, or else the first child's that has one;
* it verifies for no other claims: one dropped, one added, another blob's root or none;
* its claims in an order that is not the sorted one are refused;
* its bytes decode to a proof that verifies, and with any byte changed they do not;
* a signature of another message is refused before any proof is made;
* offered as a child with other claims than its own, it makes no parent: this is what carries a
  claim from one level of the recursion to the next;
* asked to prove only some of its covered claims (`OutputClaims::Only`), it verifies for exactly
  those, not for the covered ones it left out, not for a part of the declared ones, and it
  refuses a claim its inputs do not cover;
* a signature with one byte changed, in any region of it, is aggregated only if the crate's own
  `verify` accepts it: what the aggregation does not check before proving, the guest must refuse.

It is a state machine test with effects (lean-hedgehog, `Hedgehog.Command`, in `IO`): the system
under test is the Rust process and the proofs it keeps, the model the claims each proof should
have. Each step is a command, a type of its own.

    cargo build --release --manifest-path scripts/agg-property/Cargo.toml
    lake build agg-property
    lake exe agg-property               # one step of each kind, in the order given
    MADHOUSE=1 lake exe agg-property    # 100 random sequences, minutes: an aggregation takes about
                                        # a second, and sequences reach their full length only as
                                        # the cases' size grows, so fewer cases stay short
    MADHOUSE=1 lake exe agg-property scripts/agg-property/target/release/leanvm-agg-property 500
-/

open Hedgehog

namespace AggProperty

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

/-! ## The model -/

/-- A claim: a signer and a message, small numbers the harness expands. -/
abbrev Claim := Nat × Nat

/-- What a proof should prove: its claims, without repeats, and its blob. `id` is the harness's
number of the proof. -/
structure Node where
  id : Nat
  sphincs : List Claim
  xmss : List Claim
  blob : Option Nat
  deriving Repr, BEq

/-- The proofs made so far. -/
structure Tree where
  nodes : Array Node := #[]
  deriving Inhabited

/-- Claims as the harness reads them. -/
def claims (cs : List Claim) : String :=
  if cs.isEmpty then "-" else ",".intercalate (cs.map fun (k, m) ↦ s!"{k}:{m}")

def blob (b : Option Nat) : String := (b.map toString).getD "-"

/-- Two lists as sets. -/
def sameClaims (a b : List Claim) : Bool := a.all b.contains && b.all a.contains

/-- The node a tree's position names: positions wrap. -/
def Tree.pick (tree : Tree) (position : Nat) : Option Node :=
  tree.nodes[position % tree.nodes.size]?

/-- Whether proof `node` verifies for the claims given, sorted by the harness. -/
def verifies (rust : Driver) (node : Node) (sphincs xmss : List Claim) (b : Option Nat) :
    TestT IO String :=
  rust.ask ["verify", toString node.id, claims sphincs, claims xmss, blob b, "sorted"]

/-! ## Generators -/

def genSphincs : Gen Claim := Gen.zip (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 3))

/-- Two leanXMSS signers at most: a key takes seconds to make. -/
def genXmss : Gen Claim := Gen.zip (Gen.nat (.constant 0 1)) (Gen.nat (.constant 0 3))

def genBlob : Gen (Option Nat) := Gen.frequency [(2, pure none), (1, some <$> Gen.nat (.constant 0 2))]

/-! ## The steps -/

/-- Aggregate some proofs, some signatures and perhaps a blob. -/
structure Aggregate where
  rust : Driver
  children : List Nat
  sphincs : List Claim
  xmss : List Claim
  blob : Option Nat

instance : Command Aggregate Tree Driver IO where
  apply c tree := do
    let children := (c.children.filterMap tree.pick).eraseDups
    let answer ← c.rust.ask ["node",
      if children.isEmpty then "-" else ",".intercalate (children.map (toString ·.id)),
      claims c.sphincs, claims c.xmss, blob c.blob]
    if children.isEmpty && c.sphincs.isEmpty && c.xmss.isEmpty && c.blob.isNone then
      ensure (answer.startsWith "error") s!"a proof of nothing: {answer}"
      pure tree
    else
      match (answer.dropPrefix? "ok ").bind (·.toNat?) with
      | none => failWith s!"no proof: {answer}"
      | some id =>
        let node : Node :=
          { id
            sphincs := (children.flatMap (·.sphincs) ++ c.sphincs).eraseDups
            xmss := (children.flatMap (·.xmss) ++ c.xmss).eraseDups
            blob := c.blob <|> children.findSome? (·.blob) }
        -- A new proof verifies for what the model says it proves.
        (← verifies c.rust node node.sphincs node.xmss node.blob) === "true"
        pure { nodes := tree.nodes.push node }
  label c := s!"AGGREGATE(children {c.children}, sphincs {claims c.sphincs}, \
    xmss {claims c.xmss}, blob {blob c.blob})"
  build rust := Aggregate.mk rust <$> Gen.list (.linear 0 3) (Gen.nat (.constant 0 7))
    <*> Gen.list (.linear 0 3) genSphincs
    <*> Gen.frequency [(4, pure []), (1, Gen.list (.constant 1 2) genXmss)] <*> genBlob

/-! ## `OutputClaims::Only`: a node that proves less than it covers -/

/-- Which of a node's covered claims it declares. -/
inductive DeclareMode where
  /-- Every covered claim, as `node` does. -/
  | all
  /-- A random subset of them, perhaps none, and a DA root or none. -/
  | subset (da : Bool)
  /-- The covered claims of one scheme, plus one more the inputs do not cover. -/
  | foreign (scheme : Bool) (claim : Claim)
  /-- A subset, reordered and with repeats. -/
  | messy
  /-- No blob of its own, and a declared DA root no child has. -/
  | badDa (seed : Nat)
  deriving Repr

/-- Aggregate some proofs, some signatures and perhaps a blob, and declare which of the covered
claims the node proves. The returned proof must verify for exactly the declared claims, and for
no other: not for the covered ones it did not declare, not for a part of the declared ones. -/
structure AggregateOnly where
  rust : Driver
  children : List Nat
  sphincs : List Claim
  xmss : List Claim
  blob : Option Nat
  mode : DeclareMode
  /-- Which of the covered claims `subset` and `messy` keep, by position. -/
  keepS : List Bool
  keepX : List Bool
  /-- `messy`: positions in the kept list, to repeat. -/
  repeats : List Nat

/-- The claims a node covers: its children's and its own signatures', without repeats, and its
DA root: its own blob, or the first child's that has one. -/
def coveredOf (children : List Node) (sphincs xmss : List Claim) (blob : Option Nat) :
    List Claim × List Claim × Option Nat :=
  ((children.flatMap (·.sphincs) ++ sphincs).eraseDups,
    (children.flatMap (·.xmss) ++ xmss).eraseDups,
    blob <|> children.findSome? (·.blob))

/-- The covered claims a node keeps where its `keep` list says so. -/
def kept (l : List Claim) (keep : List Bool) : List Claim :=
  (l.zip (keep.take l.length)).filterMap (fun (c, k) ↦ if k then some c else none)

/-- What the node declares, and whether the aggregation should make it. -/
def AggregateOnly.declared (c : AggregateOnly) (tree : Tree) :
    List Claim × List Claim × Option Nat × Bool :=
  let children := (c.children.filterMap tree.pick).eraseDups
  let (coveredS, coveredX, coveredDa) := coveredOf children c.sphincs c.xmss c.blob
  match c.mode with
  | .all => (coveredS, coveredX, coveredDa,
      coveredS.length > 0 ∨ coveredX.length > 0 ∨ coveredDa.isSome)
  | .subset da =>
    let (s, x) := (kept coveredS c.keepS, kept coveredX c.keepX)
    let da' := c.blob <|> if da then coveredDa else none
    (s, x, da', s.length > 0 ∨ x.length > 0 ∨ da'.isSome)
  | .foreign scheme claim =>
    let (s, x) := if scheme then (claim :: coveredS, coveredX) else (coveredS, claim :: coveredX)
    -- The injected claim is foreign only if the covered set lacks it; else it is
    -- the `all` case and must aggregate.
    let covered := if scheme then coveredS.contains claim else coveredX.contains claim
    (s, x, coveredDa, covered)
  | .messy =>
    let (s, x) := (kept coveredS c.keepS, kept coveredX c.keepX)
    let withRepeats (l : List Claim) := l ++ (c.repeats.filterMap (fun i ↦ l[i]?)).eraseDups
    let (s, x) := (withRepeats s, withRepeats x)
    let da' := c.blob <|> coveredDa
    (s, x, da', s.length > 0 ∨ x.length > 0 ∨ da'.isSome)
  | .badDa seed =>
    -- A declared DA root: its own blob's, or a child's, or else an error. `seed` is
    -- a child's when it is `some seed` in some child's blob.
    (coveredS, coveredX, some seed,
      if c.blob.isSome then c.blob == some seed else children.any (·.blob == some seed))

/-- `claims N`'s answer, `s=k:m,...;x=k:m,...;sorted=B`: the two lists and their order. -/
def parseClaims (s : String) : List Claim × List Claim × Bool :=
  let parts := s.splitOn ";"
  let body (i : Nat) : String :=
    match (parts[i]?.getD "").splitOn "=" with
    | [_name, body] => body
    | _ => ""
  let list (i : Nat) : List Claim :=
    (body i).splitOn "," |>.filter (· ≠ "") |>.map fun p =>
      match p.splitOn ":" with
      | [k, m] => (k.toNat?.getD 65535, m.toNat?.getD 65535)
      | _ => (65535, 65535)
  (list 0, list 1, (parts[2]?.getD "") == "sorted=true")

instance : Command AggregateOnly Tree Driver IO where
  apply c tree := do
    let children := (c.children.filterMap tree.pick).eraseDups
    let (coveredS, coveredX, coveredDa) := coveredOf children c.sphincs c.xmss c.blob
    let (declS, declX, declDa, expectOk) := c.declared tree
    let answer ← c.rust.ask ["node-only",
      if children.isEmpty then "-" else ",".intercalate (children.map (toString ·.id)),
      claims c.sphincs, claims c.xmss, blob c.blob, claims declS, claims declX, blob declDa]
    unless expectOk do
      ensure (answer.startsWith "error") s!"a node of undeclared claims was made: {answer}"
    if not expectOk then pure tree else
    match (answer.dropPrefix? "ok ").bind (·.toNat?) with
    | none => failWith s!"no proof: {answer}"
    | some id =>
      let node : Node := { id, sphincs := declS.eraseDups, xmss := declX.eraseDups, blob := declDa }
      -- The API's own report: the declared claims, in a strictly sorted order.
      let (rs, rx, sorted) := parseClaims (← c.rust.ask ["claims", toString id])
      ensure sorted "the API returned its claims out of order"
      ensure (sameClaims rs node.sphincs) s!"returned sphincs claims {rs}: expected {node.sphincs}"
      ensure (sameClaims rx node.xmss) s!"returned xmss claims {rx}: expected {node.xmss}"
      -- It verifies for what the model says it proves.
      (← verifies c.rust node node.sphincs node.xmss node.blob) === "true"
      -- It verifies for the covered claims only if those are what it declared.
      let coveredSame := sameClaims coveredS node.sphincs && sameClaims coveredX node.xmss
          && coveredDa == node.blob
      (← verifies c.rust node coveredS coveredX coveredDa) === toString coveredSame
      -- It verifies for no strict part of its claims: one dropped, where one exists.
      if node.sphincs.length + node.xmss.length > 0 then
        let (s, x) := if node.sphincs.length > 0
          then (node.sphincs.tail, node.xmss)
          else (node.sphincs, node.xmss.tail)
        (← verifies c.rust node s x node.blob) === "false"
      pure { nodes := tree.nodes.push node }
  label c := s!"AGGREGATE-ONLY({repr c.mode}, children {c.children}, sphincs {claims c.sphincs}, \
    xmss {claims c.xmss}, blob {blob c.blob})"
  build rust := do
    let mode ← Gen.frequency [
      (3, pure DeclareMode.all),
      (4, .subset <$> Gen.bool),
      (2, DeclareMode.foreign <$> Gen.bool <*> genSphincs),
      (2, pure DeclareMode.messy),
      (1, .badDa <$> Gen.nat (.constant 0 9))]
    pure ⟨rust, ← Gen.list (.linear 0 3) (Gen.nat (.constant 0 7)),
      ← Gen.list (.linear 0 3) genSphincs,
      ← Gen.frequency [(4, pure []), (1, Gen.list (.constant 1 2) genXmss)],
      ← genBlob, mode, ← Gen.list (.constant 16 16) Gen.bool, ← Gen.list (.constant 16 16) Gen.bool,
      ← Gen.list (.constant 4 4) (Gen.nat (.constant 0 7))⟩


/-- How a proof's claims are altered. -/
inductive Alteration where
  | dropSphincs (position : Nat)
  | addSphincs (claim : Claim)
  | dropXmss (position : Nat)
  | addXmss (claim : Claim)
  | setBlob (blob : Option Nat)
  /-- The two lists exchanged: a leanXMSS claim offered as a leanSPHINCS one. -/
  | exchange
  deriving Repr

/-- Verify a proof for other claims than its own. -/
structure VerifyOther where
  rust : Driver
  node : Nat
  alteration : Alteration

instance : Command VerifyOther Tree Driver IO where
  check _ tree := tree.nodes.size != 0
  apply c tree := do
    match tree.pick c.node with
    | none => pure tree
    | some node =>
      let (sphincs, xmss, b) := match c.alteration with
        | .dropSphincs i => (node.sphincs.eraseIdx (i % (node.sphincs.length + 1)), node.xmss, node.blob)
        | .addSphincs claim => ((claim :: node.sphincs).eraseDups, node.xmss, node.blob)
        | .dropXmss i => (node.sphincs, node.xmss.eraseIdx (i % (node.xmss.length + 1)), node.blob)
        | .addXmss claim => (node.sphincs, (claim :: node.xmss).eraseDups, node.blob)
        | .setBlob b => (node.sphincs, node.xmss, b)
        | .exchange => (node.xmss.filter (·.1 ≤ 3), node.sphincs.filter (·.1 ≤ 1), node.blob)
      let same := sameClaims sphincs node.sphincs && sameClaims xmss node.xmss && b == node.blob
      -- The two schemes' keys of one signer number differ, so exchanged lists are other claims
      -- unless both are empty.
      let same := match c.alteration with
        | .exchange => node.sphincs.isEmpty && node.xmss.isEmpty
        | _ => same
      (← verifies c.rust node sphincs xmss b) === toString same
      pure tree
  label c := s!"VERIFY-OTHER({c.node}, {reprStr c.alteration})"
  build rust := VerifyOther.mk rust <$> Gen.nat (.constant 0 7) <*> Gen.choice [
    .dropSphincs <$> Gen.nat (.constant 0 5), .addSphincs <$> genSphincs,
    .dropXmss <$> Gen.nat (.constant 0 3), .addXmss <$> genXmss, .setBlob <$> genBlob,
    pure .exchange]

/-- Aggregate a proof as a child with other claims than its own: the parent must not be made. -/
structure BadChild where
  rust : Driver
  node : Nat
  alteration : Alteration

/-- A node's claims altered, and whether they are still its own. -/
def altered (node : Node) : Alteration → List Claim × List Claim × Option Nat × Bool
  | .dropSphincs i =>
    let sphincs := node.sphincs.eraseIdx (i % (node.sphincs.length + 1))
    (sphincs, node.xmss, node.blob, sameClaims sphincs node.sphincs)
  | .addSphincs claim =>
    ((claim :: node.sphincs).eraseDups, node.xmss, node.blob, node.sphincs.contains claim)
  | .dropXmss i =>
    let xmss := node.xmss.eraseIdx (i % (node.xmss.length + 1))
    (node.sphincs, xmss, node.blob, sameClaims xmss node.xmss)
  | .addXmss claim =>
    (node.sphincs, (claim :: node.xmss).eraseDups, node.blob, node.xmss.contains claim)
  | .setBlob b => (node.sphincs, node.xmss, b, b == node.blob)
  | .exchange => (node.xmss.filter (·.1 ≤ 3), node.sphincs.filter (·.1 ≤ 1), node.blob,
      node.sphincs.isEmpty && node.xmss.isEmpty)

instance : Command BadChild Tree Driver IO where
  check _ tree := tree.nodes.size != 0
  apply c tree := do
    match tree.pick c.node with
    | none => pure tree
    | some node =>
      let (sphincs, xmss, b, same) := altered node c.alteration
      let answer ← c.rust.ask ["badchild", toString node.id, claims sphincs, claims xmss, blob b]
      annotate s!"a child with other claims: {answer}"
      if same then answer === "ok verifies=true"
      else
        ensure (answer.startsWith "error")
          "a parent was made of a child with claims it does not prove"
      pure tree
  label c := s!"BAD-CHILD({c.node}, {reprStr c.alteration})"
  build rust := BadChild.mk rust <$> Gen.nat (.constant 0 7) <*> Gen.choice [
    .dropSphincs <$> Gen.nat (.constant 0 5), .addSphincs <$> genSphincs,
    .dropXmss <$> Gen.nat (.constant 0 3), .addXmss <$> genXmss, .setBlob <$> genBlob,
    pure .exchange]

/-- Verify a proof for its own claims in two opposite orders: at most one is sorted. -/
structure VerifyUnsorted where
  rust : Driver
  node : Nat

instance : Command VerifyUnsorted Tree Driver IO where
  check _ tree := tree.nodes.size != 0
  apply c tree := do
    match tree.pick c.node with
    | none => pure tree
    | some node =>
      let ask (sphincs : List Claim) := c.rust.ask ["verify", toString node.id, claims sphincs,
        claims node.xmss, blob node.blob, "given"]
      let forward ← ask node.sphincs
      let backward ← ask node.sphincs.reverse
      annotate s!"as given: {forward}; reversed: {backward}"
      if node.sphincs.length ≥ 2 then
        ensure (forward != "true" || backward != "true") "two orders of one list both verify"
      pure tree
  label c := s!"VERIFY-UNSORTED({c.node})"
  build rust := VerifyUnsorted.mk rust <$> Gen.nat (.constant 0 7)

/-- A proof through its bytes. -/
structure Bytes where
  rust : Driver
  node : Nat

instance : Command Bytes Tree Driver IO where
  check _ tree := tree.nodes.size != 0
  apply c tree := do
    match tree.pick c.node with
    | none => pure tree
    | some node =>
      (← c.rust.ask ["bytes", toString node.id]) === "true"
      pure tree
  label c := s!"BYTES({c.node})"
  build rust := Bytes.mk rust <$> Gen.nat (.constant 0 7)

/-- A proof with one byte changed. -/
structure Tamper where
  rust : Driver
  node : Nat
  position : Nat
  byte : Nat

instance : Command Tamper Tree Driver IO where
  check _ tree := tree.nodes.size != 0
  apply c tree := do
    match tree.pick c.node with
    | none => pure tree
    | some node =>
      let answer ← c.rust.ask ["tamper", toString node.id, toString c.position, toString c.byte]
      ensure (answer != "true") "a proof with a byte changed verifies"
      ensure (["false", "none", "same"].contains answer) s!"a changed proof: {answer}"
      pure tree
  label c := s!"TAMPER({c.node}, {c.position}, {c.byte})"
  build rust := Tamper.mk rust <$> Gen.nat (.constant 0 7)
    <*> Gen.choice [Gen.nat (.linear 0 2000), Gen.nat (.exponential 0 (2 ^ 22))]
    <*> Gen.nat (.constant 0 255)

/-- A signature of another message than its claim's. -/
structure Forged where
  rust : Driver
  claim : Claim

instance : Command Forged Tree Driver IO where
  apply c tree := do
    let answer ← c.rust.ask ["forged", claims [c.claim]]
    ensure (answer.startsWith "error") s!"a forged signature was aggregated: {answer}"
    pure tree
  label c := s!"FORGED({claims [c.claim]})"
  build rust := Forged.mk rust <$> genSphincs

/-- The scenario: in the order given, two proofs, a third over both, and each kind of question;
in madhouse mode, random sequences of these. -/
def aggregation (mode : Mode) (rust : Driver) : Property IO :=
  scenario mode rust [Command.gen Aggregate, Command.gen Aggregate, Command.gen Aggregate,
    Command.gen VerifyOther, Command.gen AggregateOnly, Command.gen VerifyUnsorted,
    Command.gen Bytes, Command.gen Tamper, Command.gen Forged, Command.gen VerifyOther,
    Command.gen BadChild, Command.gen AggregateOnly]

/-! ## Altered signatures, given to the aggregation -/

/-- A leanSPHINCS signature's regions, each a start and a length: the randomizer, the FORS
openings, and each layer's counter, chain values and path. -/
def sphincsRegions : List (Nat × Nat) :=
  [(0, 16), (16, 24 * 176)] ++ (List.range 3).flatMap fun layer ↦
    let start := 16 + 24 * 176 + 1156 * layer
    [(start, 4), (start + 4, 1024), (start + 1028, 128)]

/-- A leanXMSS signature's regions: the leaf index, and each layer's randomizer, chain values and
path. -/
def xmssRegions : List (Nat × Nat) :=
  (0, 4) :: (List.range 2).flatMap fun layer ↦
    let start := 4 + 1200 * layer
    [(start, 16), (start + 16, 928), (start + 944, 256)]

/-- A signature, its message and its key, one byte of one of them changed, are aggregated exactly
when the crate's own `verify` accepts them. The aggregation checks little before proving
(`AggregateError::InvalidSignature`); the rest is the guest's to refuse, inside the proof
(`ProvingFailed`). A changed signature that `verify`
refuses and that is aggregated all the same would be a claim proved without a signature. -/
def alteredSignatures (rust : Driver) : Property IO := propertyM do
  let xmss ← forAll (Gen.frequency [(4, pure false), (1, pure true)])
  let signer ← forAll (Gen.nat (.constant 0 (if xmss then 1 else 3)))
  let message ← forAll (Gen.nat (.constant 0 3))
  let what ← forAll (Gen.frequency [(6, pure "sig"), (1, pure "msg"), (1, pure "key")])
  let (start, length) ← forAll (if what == "sig"
    then Gen.element (if xmss then xmssRegions else sphincsRegions) else pure (0, 32))
  let offset ← forAll (Gen.nat (.constant 0 (length - 1)))
  let byte ← forAll (Gen.nat (.constant 0 255))
  pure do
    let answer ← rust.ask ["altered", if xmss then "x" else "s", what, toString signer,
      toString message, toString (start + offset), toString byte]
    annotate answer
    if answer != "same" then
      if answer.startsWith "native=false " then
        ensure ((answer.splitOn "aggregate=error").length == 2)
          "a signature the crate refuses was aggregated"
      else
        answer === "native=true aggregate=ok verifies=true"

end AggProperty

/-- The driver: the Rust binary's path may be given, and after it the number of sequences;
`MADHOUSE=1` selects random sequences. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/agg-property/target/release/leanvm-agg-property"
  let rust ← AggProperty.Driver.start path
  let mode ← Mode.fromEnv
  let property := AggProperty.aggregation mode rust
  let count := (args[1]?.bind String.toNat?).getD (if mode == .madhouse then 100 else 1)
  let ok ← checkGroup s!"the aggregation's claims ({repr mode})"
    [("a proof verifies for its own claims and no others", property.withTests count),
     ("an altered signature is aggregated only if it verifies",
      (AggProperty.alteredSignatures rust).withTests (if mode == .madhouse then count else 20))]
  return if ok then 0 else 1
