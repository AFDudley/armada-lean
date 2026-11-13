/-
  Probe for rule PE2 (calls), `docs/pool-executable.md`. It elaborates only when PE2
  holds. Run it from the repo root, after `lake build`:

    python3 scripts/oracles/lean_probe.py scripts/oracles/pool_exec/PE2.lean

  The interface it fixes: `Pool.Call` is an inductive type with exactly four
  constructors, each with exactly the calldata arguments below, in this order. No argument
  is a circuit witness. The proof is a `Term`: the model holds no Groth16 proof objects,
  and a proof is calldata, a symbolic message like every other value a caller sends.
  * `shield (token : Token) (x : Nat) (npk : Term)`: the token, the gross amount and the
    note key.
  * `transact {N M : Nat} (caller : Term) (pub : TransactPublic N M) (bp : BoundParams)
    (proof : Term) (unshieldToken : Option Token)
    (records : List (Term × CommitmentPreimage)) (openings : List (Term × OwnedOpening))`.
  * `transactOwned {N M : Nat} (caller : Term) (pub : TransactOwnedPublic N M)
    (bp : BoundParams) (proof : Term) (records : List (Term × CommitmentPreimage))
    (openings : List (Term × OwnedOpening))`: the same, with no unshield.
  * `setFeeRatio (caller : Term) (r : FeeRatio)`: the fee-admin setter,
    the caller and the new fee rate.
-/
import ArmadaLean

-- Every armada-lean declaration is under the root namespace `ArmadaLean`.
open ArmadaLean

-- An unknown name in a binder must be an error, not a new variable.
set_option autoImplicit false

/-- A shield call: the token, the gross amount and the note key, and nothing else. -/
example (token : Token) (x : Nat) (npk : Term) : Pool.Call :=
  .shield token x npk

/-- A transact call: the caller, the public inputs, the bound parameters, the proof, the
    token of the unshield if there is one, the disclosed records and the published
    openings, and nothing else. -/
example {N M : Nat} (caller : Term) (pub : TransactPublic N M) (bp : BoundParams)
    (proof : Term) (unshieldToken : Option Token) (records : List (Term × CommitmentPreimage))
    (openings : List (Term × OwnedOpening)) : Pool.Call :=
  .transact caller pub bp proof unshieldToken records openings

/-- An owned transact call: the same as a transact call, with no unshield. -/
example {N M : Nat} (caller : Term) (pub : TransactOwnedPublic N M) (bp : BoundParams)
    (proof : Term) (records : List (Term × CommitmentPreimage))
    (openings : List (Term × OwnedOpening)) : Pool.Call :=
  .transactOwned caller pub bp proof records openings

/-- A fee-admin setter call: the caller and the new fee rate, and nothing else. -/
example (caller : Term) (r : FeeRatio) : Pool.Call :=
  .setFeeRatio caller r

/-- Exactly four constructors: a fifth makes this match incomplete. -/
example (c : Pool.Call) : Fin 4 :=
  match c with
  | .shield .. => 0
  | .transact .. => 1
  | .transactOwned .. => 2
  | .setFeeRatio .. => 3

/-! ### Axioms

`lean_probe.py` reports each `#print axioms` line. The check after them fails the probe
when a main declaration depends on an axiom other than Lean's three core axioms and the
model's three declared primitives (PE6: no new axiom; `sorryAx` is not allowed). -/

#print axioms Pool.Call

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound,
    ``EdDSAVerify, ``VerifyAccepts, ``VerifyOwnedAccepts]
  for d in [``Pool.Call] do
    for a in (← collectAxioms d) do
      unless allowed.contains a do
        throwError m!"{d} depends on the axiom {a}, which is not allowed"
