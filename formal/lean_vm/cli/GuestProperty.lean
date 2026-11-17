import Hedgehog

/-!
# The recursion guest on witnesses changed one hint at a time

The guest (`guests/lean_ethereum.py`) reads its witness through `hint_witness`, in some fifty
streams, and what it reads is the prover's to choose: a hint is sound only if the guest then
constrains it. This driver takes the witness of an honest aggregation, changes one word of one hint
(a bit flipped, or the word replaced), runs the guest again on the same public input, and requires
that it **refuses** (`scripts/guest-property`, `leanvm-guest-property`, which captures the witness
through the public `isa::Prover` interface and runs `cpu::execute`). A changed hint the guest
accepts is a value the prover is free to choose; whether that matters is then a question about
that hint.

Some words are never read, and the guest accepts any value there. They are named here, each with
the rule the driver checks in place of refusal, so that a new accepted word is a failure:

* `stream`, a child's proof: the buffer holds `STREAM_CAP` words and a proof is shorter, so its
  tail is unread. An accepted word's successors are accepted too, and word 0 never is.
* `merkle_children`, four words a level, the two children of a path's node: `walk_window` hashes
  the running node with the child on the other side and never reads its own side. Of the two
  halves of a level at most one is accepted.
* `merkle_caps`, node `k` at words `2k`, `2k + 1`: there is no node 0, and the children of a node
  that `merkle_cap_active` leaves inactive are not hashed (`verify_merkle_cap`). An accepted word
  past the first two has its node's sibling accepted too.
* `merkle_cap_active`: no node 0, and the root is always hashed, so flags 0 and 1 are unread. Any
  other flag is read as zero or not zero (`if flags[GEN ** node] != 0`), so an active node's flag
  may be any nonzero `K` word: the same witness written otherwise. An accepted flag past the first
  two is one that zero is refused for.
* `block_group_order`: "pull's slots go unread", the groups of the second side, words 9 to 17 at
  this configuration.

It is not a proof of anything: one word at a time finds a hint left free, not two hints that are
only constrained together, and a run the interpreter refuses is not thereby one no trace exists
for.

    cargo build --release --manifest-path scripts/guest-property/Cargo.toml
    lake build guest-property
    lake exe guest-property            # 300 changes of each kind of node
    lake exe guest-property scripts/guest-property/target/release/leanvm-guest-property 5000
-/

open Hedgehog

namespace GuestProperty

structure Driver where
  stdin : IO.FS.Handle
  stdout : IO.FS.Handle

def Driver.start (path : String) : IO Driver := do
  let child ← IO.Process.spawn
    { cmd := path, stdin := .piped, stdout := .piped, stderr := .inherit }
  pure ⟨child.stdin, child.stdout⟩

/-- Send a command, its words separated by tabs, and read its result line. -/
def Driver.send (driver : Driver) (words : List String) : IO String := do
  driver.stdin.putStrLn ("\t".intercalate words)
  driver.stdin.flush
  let line ← driver.stdout.getLine
  if line.isEmpty then throw (IO.userError "the process gave no answer")
  pure (String.ofList (line.toList.filter (· ≠ '\n')))

/-- A hint stream of the captured witness: its name, its entries, and its longest entry's words. -/
structure Stream where
  name : String
  entries : Nat
  words : Nat
  deriving Repr

/-- The streams `capture` printed. -/
def streamsOf (line : String) : List Stream :=
  (line.splitOn " ").filterMap fun s ↦
    match s.splitOn ":" with
    | [name, entries, words] => some ⟨name, entries.toNat?.getD 0, words.toNat?.getD 0⟩
    | _ => none

/-- A change of one word: a bit flipped, or the word replaced. -/
inductive Change where
  | flip (bit : Nat)
  | set (c0 c1 : Nat)
  deriving Repr

def genChange : Gen Change :=
  Gen.choice [.flip <$> Gen.nat (.constant 0 127),
    .set <$> Gen.element [0, 1, 2] <*> Gen.element [0, 1],
    .set <$> Gen.nat (.exponential 0 (2 ^ 64 - 1)) <*> Gen.nat (.exponential 0 (2 ^ 64 - 1))]

/-- A replacement of a word, the only kind `change2` carries. -/
def genSet : Gen Change := .set <$> Gen.element [0, 1, 2] <*> Gen.element [0, 1]

/-- The verdict on one word changed: `same` counts as not a change. -/
def verdict (rust : Driver) (stream entry word : Nat) (change : Change) : TestT IO String := do
  let position := [toString stream, toString entry, toString word]
  evalIO <| rust.send <| match change with
    | .flip bit => ["flip"] ++ position ++ [toString bit]
    | .set c0 c1 => ["change"] ++ position ++ [toString c0, toString c1]

/-- Whether the guest accepts the witness with one word changed (`same` counts as refused: nothing
was changed, and so does a word past the entry's end). -/
def accepts (rust : Driver) (stream entry word : Nat) (change : Change) : TestT IO Bool := do
  let position := [toString stream, toString entry, toString word]
  let answer ← evalIO <| rust.send <| match change with
    | .flip bit => ["flip"] ++ position ++ [toString bit]
    | .set c0 c1 => ["change"] ++ position ++ [toString c0, toString c1]
  -- Entries of one stream differ in length: a word past an entry's end is no change.
  if answer == "error no such word" then pure false
  else if answer.startsWith "error" || answer.startsWith "panic" then failWith answer
  else pure (answer == "accepted")

/-- One word of one hint changed: the guest refuses, or the word is one it never reads. -/
def hints (rust : Driver) (streams : List Stream) : Property IO := propertyM do
  let index ← forAll (Gen.nat (.constant 0 (streams.length - 1)))
  let stream := streams.getD index ⟨"", 1, 1⟩
  let entry ← forAll (Gen.nat (.constant 0 (stream.entries - 1)))
  let word ← forAll (Gen.nat (.constant 0 (stream.words - 1)))
  let change ← forAll genChange
  pure do
    annotate s!"stream {stream.name}"
    if ← accepts rust index entry word change then
      let also (w : Nat) := accepts rust index entry w change
      match stream.name with
      | "stream" =>
        ensure (word != 0 && (← also (word + 1 - (word + 1) / stream.words))
          && (← also (stream.words - 1))) "a word of a child's proof is free, and not in its tail"
      | "merkle_children" =>
        let other := if word % 4 < 2 then word + 2 else word - 2
        ensure (!(← also other)) "both children of a level are free"
      | "merkle_caps" =>
        if word ≥ 2 then
          let sibling := if (word / 2) % 2 == 0 then word + 2 else word - 2
          ensure (← also sibling) "a cap node is free and its sibling is not"
      | "merkle_cap_active" =>
        if word ≥ 2 then
          ensure (!(← accepts rust index entry word (.set 0 0))) "a flag of a cap node is free"
      | "block_group_order" => ensure (9 ≤ word && word ≤ 17) "a group's rank is free"
      | _ => failWith "the guest accepts a changed hint"

/-- Two words of two hints changed at once: the guest accepts the pair only if each word alone is
free. A pair accepted while one word alone is refused would be a tampering check a second change
bypasses; a pair refused while both words alone are free is a pair constrained only together, which
is sound and worth recording, not a failure. -/
def twoWords (rust : Driver) (streams : List Stream) : Property IO := propertyM do
  let i1 ← forAll (Gen.nat (.constant 0 (streams.length - 1)))
  let i2 ← forAll (Gen.nat (.constant 0 (streams.length - 1)))
  let s1 := streams.getD i1 ⟨"", 1, 1⟩
  let s2 := streams.getD i2 ⟨"", 1, 1⟩
  let e1 ← forAll (Gen.nat (.constant 0 (s1.entries - 1)))
  let e2 ← forAll (Gen.nat (.constant 0 (s2.entries - 1)))
  let w1 ← forAll (Gen.nat (.constant 0 (s1.words - 1)))
  let w2 ← forAll (Gen.nat (.constant 0 (s2.words - 1)))
  let c1 ← forAll genSet
  let c2 ← forAll genSet
  pure do
    annotate s!"stream {s1.name} and {s2.name}"
    let pair := match c1 with
      | .set c0 c1 => match c2 with
        | .set d0 d1 =>
          ["change2"] ++ [toString i1, toString e1, toString w1, toString i2, toString e2, toString w2]
            ++ [toString c0, toString c1, toString d0, toString d1]
        | .flip _ => [""]
      | .flip _ => [""]
    let answer ← evalIO (rust.send pair)
    -- Entries of a stream differ in length: a word past an entry's end is no change.
    if answer == "error no such word" || answer == "error no such entry" || answer == "error no such stream" then pure ()
    else if answer.startsWith "error" || answer.startsWith "panic" then failWith answer
    else if answer == "same" then pure ()
    else if answer == "accepted" then
      -- A pair accepted is sound only if each word alone is free; a word refused alone that a
      -- second change frees would be a tampering check a second change bypasses.
      let v1 ← verdict rust i1 e1 w1 c1
      let v2 ← verdict rust i2 e2 w2 c2
      if v1 == "same" || v2 == "same" then
        -- One word was not changed: the pair is a one-word change, covered elsewhere.
        pure ()
      else
        ensure (!v1.startsWith "refused") "a word refused alone is freed by a second change"
        ensure (!v2.startsWith "refused") "a word refused alone is freed by a second change"
    else
      -- Refused. A pair refused while both words alone are free is two hints constrained
      -- together: sound, and worth recording, not a failure.
      pure ()

end GuestProperty

/-- The driver: the Rust binary's path may be given, and after it the number of changes for each
kind of node. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/guest-property/target/release/leanvm-guest-property"
  let count := (args[1]?.bind String.toNat?).getD 300
  let mut ok := true
  -- A process a kind: a capture replaces the one before it.
  for kind in ["sphincs", "xmss", "blob", "both", "parent"] do
    let rust ← GuestProperty.Driver.start path
    let streams := GuestProperty.streamsOf (← rust.send ["capture", kind])
    if streams.isEmpty then
      IO.println s!"no witness for {kind}"
      ok := false
    else
      ok := (← checkGroup s!"the guest on a changed witness: {kind}"
        [(s!"a changed hint is refused, of {streams.length} streams",
          (GuestProperty.hints rust streams).withTests count),
         (s!"two words changed together, of {streams.length} streams",
          (GuestProperty.twoWords rust streams).withTests count)]) && ok
  return if ok then 0 else 1
