import LeanVMTests.Property.Gen

/-!
# The duplex sponge against a model of its queue

The Fiat-Shamir sponge (`Statement/Field.lean`) queues up to four scalars, permutes when a fifth
arrives or a challenge is squeezed, and after a grind keeps a challenge for the next squeeze. The
model here knows none of the lanes: it counts the scalars waiting, the permutations made, and whether
a ground challenge waits. Random sequences of the sponge's operations are run on the sponge, over a
permutation that only counts its calls, and on the model, and after each operation the two must agree.
The number of permutations is what the Rust transcript and the cost statements depend on.

This is model-based testing with transitions as one type (`Hedgehog.StateMachine`): the sponge has
three operations, fixed by the specification, so they are the constructors of one type and Lean
checks that the model and the run each handle all of them. `LeanVMTests.Property.Stream` is the other
style, for a set that grows.

The Rust asserts that nothing is absorbed while a ground challenge waits; the model's precondition
says the same, and shrinking keeps to it.
-/

namespace LeanVMTests.Property.Sponge

open Hedgehog LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

/-- The sponge's operations. -/
inductive Operation where
  /-- Absorb a scalar the prover sent. -/
  | absorb (x : E)
  /-- Squeeze a challenge. -/
  | squeeze
  /-- Absorb a grinding nonce and permute at once. -/
  | grind (nonce : E)
  deriving Repr

/-- The model: how many scalars wait, how many permutations were made, and whether a grind's
challenge waits. -/
structure Queue where
  waiting : ℕ := 0
  permutations : ℕ := 0
  ground : Bool := false
  deriving Repr

/-- The model after an absorption: a full queue is permuted first. -/
def Queue.absorb (q : Queue) : Queue :=
  if q.waiting = 4 then { q with waiting := 1, permutations := q.permutations + 1 }
  else { q with waiting := q.waiting + 1 }

/-- A permutation that only counts its calls; the sponge's queue does not depend on what it does to
the state. -/
def countingPermutation (state : KeccakState) : StateM ℕ KeccakState := do
  modify (· + 1)
  pure (state.map (· + 1))

/-- The sponge and the calls of its permutation so far. -/
abbrev Run := Sponge × ℕ

def machine : StateMachine Queue Operation Run Id where
  initState := pure {}
  transitions q :=
    if q.ground then pure .squeeze
    else Gen.choice [.absorb <$> genE, pure .squeeze, .grind <$> genE]
  preconditions q
    | .squeeze => true
    | _ => !q.ground
  apply q
    | .absorb _ => q.absorb
    | .squeeze =>
      if q.ground then { q with ground := false }
      else { q with waiting := 0, permutations := q.permutations + 1 }
    | .grind _ =>
      { q.absorb with waiting := 0, permutations := q.absorb.permutations + 1, ground := true }
  initSut _ := pure (⟨Vector.replicate 25 0, [], none⟩, 0)
  applySut run _
    | .absorb x => pure ((absorb countingPermutation run.1 x dsObserve).run run.2)
    | .squeeze => do
      let ((challenge, sponge), calls) := (squeeze countingPermutation run.1).run run.2
      -- A ground challenge is the one squeezed; otherwise it is read from the new state.
      challenge === (run.1.ground.getD (challengeOf sponge.state))
      pure (sponge, calls)
    | .grind nonce =>
      let ((_, sponge), calls) := (absorbNonce countingPermutation run.1 nonce).run run.2
      pure (sponge, calls)
  invariants run q := do
    run.1.pending.length === q.waiting
    ensure (run.1.pending.length ≤ rateScalars) "more scalars wait than the rate holds"
    run.1.ground.isSome === q.ground
    run.2 === q.permutations

#eval check (machine.property (.linear 1 60)) "the sponge agrees with its queue"
  (seed := some (.ofNat 0))

end LeanVMTests.Property.Sponge
