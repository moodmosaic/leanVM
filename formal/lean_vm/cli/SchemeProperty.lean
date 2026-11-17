import Hedgehog
import Statement.LeanSphincs
import Statement.LeanXmss
import Statement.Fast.Schemes
import Statement.Fast.Keccak
import LeanVM.Cli.Common

/-!
# The signature schemes, the Rust and the statement's, on generated inputs

`scheme-vectors` runs the statement's leanSPHINCS and leanXMSS on EthLib's test vectors. This driver
generates the inputs (lean-hedgehog): keys, messages, and signatures altered a few bytes at a time,
in the regions a signature is made of. The Rust (`scripts/scheme-property`,
`leanvm-scheme-property`: `lean_sphincs` and `lean_xmss`) signs, and then

* a signature the Rust made verifies, by the Rust and by the statement's `verifyWithKeccak`;
* on an altered key, message or signature the two verdicts are the same: a signature the Rust
  accepts and the statement refuses would be a forgery the theorems do not cover.

The leanXMSS signer keeps state, the bottom trees it used last (`MAX_CACHED_BOTTOM_TREES`), so it
is a state machine test in `IO`: sequences of `prepare` and `sign` over more trees than the cache
holds, where a signature must verify whatever the cache held and be the same each time it is asked.

    cargo build --release --manifest-path scripts/scheme-property/Cargo.toml
    lake build scheme-property
    lake exe scheme-property          # 20 cases of each; a leanXMSS bottom tree takes seconds
    lake exe scheme-property scripts/scheme-property/target/release/leanvm-scheme-property 200
-/

open Hedgehog HashSig LeanVM.Cli

namespace SchemeProperty

/-! ## The process -/

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

def Driver.ask (driver : Driver) (words : List String) : TestT IO String :=
  evalIO (driver.send words)

/-! ## Bytes -/

/-- Bytes in hexadecimal. -/
def hex (bytes : List ℕ) : String :=
  String.join (bytes.map fun b ↦
    let digits := Nat.toDigits 16 b
    String.ofList (if digits.length = 1 then '0' :: digits else digits))

/-- The bytes of a hexadecimal string. -/
def unhex (s : String) : List ℕ :=
  let rec go : List Char → List ℕ
    | a :: b :: rest => (16 * (hexDigit? a).getD 0 + (hexDigit? b).getD 0) :: go rest
    | _ => []
  go s.toList

/-- The 16 bytes at offset `o`, as `scheme-vectors` reads a digest. -/
def digestAt (bytes : List ℕ) (o : ℕ) : Digest := bitsLE 128 ((bytes.drop o).take 16)

/-- A leanXMSS public key: the root, then the parameter. -/
def xmssPublicKeyOf (bytes : List ℕ) : PublicKey := ⟨digestAt bytes 0, digestAt bytes 16⟩

/-- A leanSPHINCS public key: `PK.seed`, then `PK.root`. -/
def sphincsPublicKeyOf (bytes : List ℕ) : Sphincs.PublicKey :=
  ⟨digestAt bytes 0, digestAt bytes 16⟩

/-- A leanSPHINCS signature, as `scheme-vectors` reads it: the randomizer, 24 FORS openings of a
secret and 10 path nodes, then three layers, each a 4-byte big-endian counter, 64 chain values and
its tree's siblings. -/
def sphincsSignatureOf (bytes : List ℕ) : Sphincs.Signature :=
  let layerStart (layer : Sphincs.Layer) : ℕ := 16 + 24 * 176 + 1156 * layer.val
  ⟨digestAt bytes 0,
    fun tree ↦ ⟨digestAt bytes (16 + 176 * tree.val),
      fun level ↦ digestAt bytes (16 + 176 * tree.val + 16 + 16 * level.val)⟩,
    fun layer ↦ ⟨bitsLE 32 ((bytes.drop (layerStart layer)).take 4).reverse,
      fun chain ↦ digestAt bytes (layerStart layer + 4 + 16 * chain.val),
      fun level ↦ digestAt bytes (layerStart layer + 4 + 1024 + 16 * level.val)⟩⟩

/-- A leanXMSS signature: the 4-byte leaf index, then the bottom and top layers, each a randomizer,
58 chain values and 16 siblings. -/
def xmssSignatureOf (bytes : List ℕ) : LeanXmss.Signature :=
  let layerStart (layer : LeanXmss.Layer) : ℕ := 4 + 1200 * layer.val
  ⟨(bitsLE 32 (bytes.take 4)).toFin,
    fun layer ↦ ⟨digestAt bytes (layerStart layer),
      fun chain ↦ digestAt bytes (layerStart layer + 16 + 16 * chain.val),
      fun level ↦ digestAt bytes (layerStart layer + 16 + 928 + 16 * level.val)⟩⟩

/-- The statement's leanSPHINCS verdict on bytes. -/
def sphincsVerdict (key message signature : List ℕ) : Bool :=
  Sphincs.verifyWithKeccak (sphincsPublicKeyOf key) (bitsLE 256 message)
    (sphincsSignatureOf signature)

/-- The statement's leanXMSS verdict on bytes. -/
def xmssVerdict (key message signature : List ℕ) : Bool :=
  LeanXmss.verifyWithKeccak (xmssPublicKeyOf key) (bitsLE 256 message) (xmssSignatureOf signature)

/-! ## Generators -/

def genByte : Gen ℕ := Gen.nat (.constant 0 255)

/-- A seed or a message: 32 bytes. -/
def gen32 : Gen (List ℕ) := Gen.list (.singleton 32) genByte

/-- Where a signature, a key or a message is altered, and to what. -/
inductive Target where
  | key
  | message
  | signature
  deriving Repr, BEq

structure Alteration where
  target : Target
  position : ℕ
  byte : ℕ
  deriving Repr

/-- An alteration: of the key, of the message, or of the signature in one of its `regions`, each a
start and a length, so that short regions (an index, a counter) are altered as often as long ones. -/
def genAlteration (regions : List (ℕ × ℕ)) : Gen Alteration := do
  let target ← Gen.frequency [(1, pure .key), (1, pure .message), (6, pure .signature)]
  let position ← match target with
    | .signature => do
      let (start, length) ← Gen.element regions
      (start + ·) <$> Gen.nat (.constant 0 (length - 1))
    | _ => Gen.nat (.constant 0 31)
  pure ⟨target, position, ← genByte⟩

/-- The bytes altered. -/
def alter (alterations : List Alteration) (target : Target) (bytes : List ℕ) : List ℕ :=
  alterations.foldl (fun bytes a ↦ if a.target == target then bytes.set a.position a.byte else bytes)
    bytes

/-- A leanSPHINCS signature's regions: the randomizer, the FORS openings, and each layer's counter,
chain values and path. -/
def sphincsRegions : List (ℕ × ℕ) :=
  [(0, 16), (16, 24 * 176)] ++ (List.range 3).flatMap fun layer ↦
    let start := 16 + 24 * 176 + 1156 * layer
    [(start, 4), (start + 4, 1024), (start + 1028, 128)]

/-- A leanXMSS signature's regions: the leaf index, and each layer's randomizer, chain values and
path. -/
def xmssRegions : List (ℕ × ℕ) :=
  (0, 4) :: (List.range 2).flatMap fun layer ↦
    let start := 4 + 1200 * layer
    [(start, 16), (start + 16, 928), (start + 944, 256)]

/-! ## leanSPHINCS -/

/-- A signature the Rust makes verifies, by the Rust and by the statement. -/
def sphincsSigns (rust : Driver) : Property IO := propertyM do
  let seed ← forAllWith hex gen32
  let message ← forAllWith hex gen32
  pure do
    let key ← rust.ask ["skeygen", hex seed]
    let signature ← rust.ask ["ssign", hex seed, hex message]
    (← rust.ask ["sverify", key, hex message, signature]) === "true"
    ensure (sphincsVerdict (unhex key) message (unhex signature))
      "the statement refuses the Rust's signature"

/-- On an altered key, message or signature the Rust's verdict is the statement's. -/
def sphincsVerdicts (rust : Driver) : Property IO := propertyM do
  let seed ← forAllWith hex gen32
  let message ← forAllWith hex gen32
  let alterations ← forAll (Gen.list (.linear 1 3) (genAlteration sphincsRegions))
  pure do
    let key := alter alterations .key (unhex (← rust.ask ["skeygen", hex seed]))
    let signature :=
      alter alterations .signature (unhex (← rust.ask ["ssign", hex seed, hex message]))
    let message := alter alterations .message message
    (← rust.ask ["sverify", hex key, hex message, hex signature])
      === toString (sphincsVerdict key message signature)

/-! ## leanXMSS -/

/-- What a leanXMSS signer is asked. -/
inductive Signing where
  /-- Build and cache the bottom tree of a leaf. -/
  | prepare (leaf : ℕ)
  /-- Sign a message at a leaf. -/
  | sign (message : List ℕ) (leaf : ℕ)
  deriving Repr

/-- A leaf in one of twelve bottom trees, more than the signer caches. -/
def genLeaf : Gen ℕ := (fun tree offset ↦ 2 ^ 16 * tree + offset)
  <$> Gen.nat (.constant 0 11) <*> Gen.nat (.constant 0 2)

/-- The signer against what it signed before: a signature verifies, by the Rust and by the
statement, whatever the cache held, and is the same each time. The model counts nothing; what was
signed is kept beside the process. -/
def xmssSigner (rust : Driver) (key : String) :
    StateMachine Unit Signing (List ((List ℕ × ℕ) × String)) IO where
  initState := pure ()
  transitions _ := Gen.frequency [(1, .prepare <$> genLeaf),
    (3, .sign <$> Gen.list (.singleton 32) (Gen.nat (.constant 0 3)) <*> genLeaf)]
  apply _ _ := ()
  initSut _ := pure []
  applySut signed _
    | .prepare leaf => do
      (← rust.ask ["xprepare", toString leaf]) === "ok"
      pure signed
    | .sign message leaf => do
      let signature ← rust.ask ["xsign", hex message, toString leaf]
      (← rust.ask ["xverify", key, hex message, signature]) === "true"
      ensure (xmssVerdict (unhex key) message (unhex signature))
        "the statement refuses the Rust's signature"
      match signed.lookup (message, leaf) with
      | some before => ensure (before == signature) "another signature than before"
      | none => pure ()
      pure (((message, leaf), signature) :: signed)

/-- On an altered key, message or signature the Rust's verdict is the statement's. -/
def xmssVerdicts (rust : Driver) (key : String) : Property IO := propertyM do
  let message ← forAllWith hex gen32
  let leaf ← forAll (Gen.nat (.constant 0 9))
  let alterations ← forAll (Gen.list (.linear 1 3) (genAlteration xmssRegions))
  pure do
    let signature :=
      alter alterations .signature (unhex (← rust.ask ["xsign", hex message, toString leaf]))
    let key := alter alterations .key (unhex key)
    let message := alter alterations .message message
    (← rust.ask ["xverify", hex key, hex message, hex signature])
      === toString (xmssVerdict key message signature)

end SchemeProperty

/-- The driver: the Rust binary's path may be given, and after it the number of cases of each (a
tenth of it for the leanXMSS signer, whose trees take seconds). -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scripts/scheme-property/target/release/leanvm-scheme-property"
  let rust ← SchemeProperty.Driver.start path
  let count := (args[1]?.bind String.toNat?).getD 20
  let seed ← Gen.sample SchemeProperty.gen32
  let key ← rust.send ["xkeygen", SchemeProperty.hex seed]
  IO.println s!"leanXMSS key seed {SchemeProperty.hex seed}"
  let ok ← checkGroup "the signature schemes, the Rust and the statement's" [
    ("leanSPHINCS signs what verifies", (SchemeProperty.sphincsSigns rust).withTests count),
    ("leanSPHINCS verdicts on altered inputs",
      (SchemeProperty.sphincsVerdicts rust).withTests count),
    ("leanXMSS verdicts on altered inputs",
      (SchemeProperty.xmssVerdicts rust key).withTests count),
    ("the leanXMSS signer and its cache",
      ((SchemeProperty.xmssSigner rust key).property (.linear 1 12)).withTests (count / 10 + 1))]
  return if ok then 0 else 1
