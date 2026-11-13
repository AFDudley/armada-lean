/-
  Probe for rule PE3 (executable operation), `docs/pool-executable.md`. It elaborates only
  when PE3 holds. Run it from the repo root, after `lake build`:

    python3 scripts/oracles/lean_probe.py scripts/oracles/pool_exec/PE3.lean

  The interface it fixes (it uses `Pool.ContractState`, PE1, and `Pool.Call`, PE2):
  * `Pool.Verifier`: a structure with exactly two fields, the proof check of each circuit
    (`PrivacyPool.verify` and `PrivacyPool.verifyOwned`):
    `transact : ∀ {N M : Nat}, TransactPublic N M → Term → Bool` and
    `owned : ∀ {N M : Nat}, TransactOwnedPublic N M → Term → Bool`.
  * `Pool.Verifier.Realizes (verify : Pool.Verifier)`: a structure with exactly two fields,
    `transact : ∀ {N M : Nat} (pub : TransactPublic N M),
      VerifyAccepts pub ↔ ∃ proof, verify.transact pub proof = true` and the same `owned`
    field over `VerifyOwnedAccepts`. It restates the doc comment of `VerifyAccepts`
    (`ArmadaLean/PoolSafety.lean`) with `verify` as `PrivacyPool.verify`. PE4 and PE5 take
    it as a hypothesis; `Pool.apply` does not read it.
  * `Pool.apply (verify : Pool.Verifier) : Pool.ContractState → Pool.Call →
    Option Pool.ContractState`, computable.
  * One precondition and one effect per call, in `Pool.ContractState`. The precondition
    takes the state and every argument of the call. The effect takes the same arguments,
    with the last call argument as a subtype value that carries the precondition (the form
    of `ArmadaLean/Nitro/Adjudicator.lean`, "One precondition and one effect per
    operation"). A precondition of a transact call also takes `verify`.
    `ShieldPre`/`shieldEffect`, `TransactPre`/`transactEffect`,
    `TransactOwnedPre`/`transactOwnedEffect`, `SetFeeRatioPre`/`setFeeRatioEffect`, each
    precondition `Decidable`.
  * The equations `Pool.apply_shield_equation`, `Pool.apply_transact_equation`,
    `Pool.apply_transactOwned_equation` and `Pool.apply_setFeeRatio_equation`, each with the arguments `verify`, the state and
    the call arguments, in that order.
-/
import ArmadaLean

-- Every armada-lean declaration is under the root namespace `ArmadaLean`.
open ArmadaLean

-- An unknown name in a binder must be an error, not a new variable.
set_option autoImplicit false

/-! ### The verifier -/

/-- `Pool.Verifier` has exactly the two proof checks, in this order. -/
example (t : ∀ {N M : Nat}, TransactPublic N M → Term → Bool)
    (o : ∀ {N M : Nat}, TransactOwnedPublic N M → Term → Bool) :
    let v : Pool.Verifier := ⟨t, o⟩
    (∀ {N M : Nat} (pub : TransactPublic N M) (proof : Term),
        v.transact pub proof = t pub proof) ∧
      (∀ {N M : Nat} (pub : TransactOwnedPublic N M) (proof : Term),
        v.owned pub proof = o pub proof) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- `Pool.Verifier.Realizes` holds exactly when `verify` accepts some proof for a public
    input of each circuit iff the model's trusted verifier accepts that input. -/
example (verify : Pool.Verifier)
    (t : ∀ {N M : Nat} (pub : TransactPublic N M),
      VerifyAccepts pub ↔ ∃ proof, verify.transact pub proof = true)
    (o : ∀ {N M : Nat} (pub : TransactOwnedPublic N M),
      VerifyOwnedAccepts pub ↔ ∃ proof, verify.owned pub proof = true) :
    verify.Realizes :=
  ⟨t, o⟩

example (verify : Pool.Verifier) (h : verify.Realizes) {N M : Nat} (pub : TransactPublic N M) :
    VerifyAccepts pub ↔ ∃ proof, verify.transact pub proof = true :=
  h.transact pub

example (verify : Pool.Verifier) (h : verify.Realizes) {N M : Nat}
    (pub : TransactOwnedPublic N M) :
    VerifyOwnedAccepts pub ↔ ∃ proof, verify.owned pub proof = true :=
  h.owned pub

/-! ### The operation -/

/-- The type: `Pool.apply` reads only the verifier, its state and its call. -/
example : Pool.Verifier → Pool.ContractState → Pool.Call → Option Pool.ContractState :=
  Pool.apply

/- `Pool.apply` runs. On the contract state at deployment with a fee rate of 1 %, and with
    a verifier that accepts every proof, a shield of 1000 grows the custody of its token by
    the note value 990 and the treasury fees of the token by the fee 10. Another token does
    not change. `#guard` evaluates compiled code, so a noncomputable `Pool.apply` fails
    here. -/
#guard
  let r : FeeRatio := ⟨1, 100, by decide, by decide, by decide⟩
  let v : Pool.Verifier := ⟨fun _ _ => true, fun _ _ => true⟩
  let tok : Token := ⟨.val 1⟩
  (Pool.apply v (genesis r (.val 3) (.val 4)).contract (.shield tok 1000 (.val 7))).map
      (fun t => (t.held tok, t.treasuryFees tok, t.held ⟨.val 2⟩)) == some (990, 10, 0)

/- A shield of 0 fails (`hValue` of `Step.shield`). -/
#guard
  let r : FeeRatio := ⟨1, 100, by decide, by decide, by decide⟩
  let v : Pool.Verifier := ⟨fun _ _ => true, fun _ _ => true⟩
  (Pool.apply v (genesis r (.val 3) (.val 4)).contract (.shield ⟨.val 1⟩ 0 (.val 7))).isNone

/- The fee admin `.val 3` sets the fee rate to 0.5 %: the result has the new rate and the
    same custody. -/
#guard
  let r : FeeRatio := ⟨1, 100, by decide, by decide, by decide⟩
  let r' : FeeRatio := ⟨1, 200, by decide, by decide, by decide⟩
  let v : Pool.Verifier := ⟨fun _ _ => true, fun _ _ => true⟩
  (Pool.apply v (genesis r (.val 3) (.val 4)).contract (.setFeeRatio (.val 3) r')).map
      (fun t => (t.feeRatio.num, t.feeRatio.den, t.feeAdmin == .val 3, t.held ⟨.val 1⟩)) ==
    some (1, 200, true, 0)

/- Another caller fails (item (b)). -/
#guard
  let r : FeeRatio := ⟨1, 100, by decide, by decide, by decide⟩
  let r' : FeeRatio := ⟨1, 200, by decide, by decide, by decide⟩
  let v : Pool.Verifier := ⟨fun _ _ => true, fun _ _ => true⟩
  (Pool.apply v (genesis r (.val 3) (.val 4)).contract (.setFeeRatio (.val 4) r')).isNone

/-! ### One equation per call -/

/-- The shield equation. -/
example (verify : Pool.Verifier) (s : Pool.ContractState) (token : Token) (x : Nat)
    (npk : Term) :
    Pool.apply verify s (.shield token x npk) =
      if h : s.ShieldPre token x npk then some (s.shieldEffect token x ⟨npk, h⟩) else none :=
  Pool.apply_shield_equation verify s token x npk

/-- The transact equation. -/
example (verify : Pool.Verifier) (s : Pool.ContractState) {N M : Nat} (caller : Term)
    (pub : TransactPublic N M) (bp : BoundParams) (proof : Term) (unshieldToken : Option Token)
    (records : List (Term × CommitmentPreimage)) (openings : List (Term × OwnedOpening)) :
    Pool.apply verify s (.transact caller pub bp proof unshieldToken records openings) =
      if h : s.TransactPre verify caller pub bp proof unshieldToken records openings then
        some (s.transactEffect verify caller pub bp proof unshieldToken records ⟨openings, h⟩)
      else none :=
  Pool.apply_transact_equation verify s caller pub bp proof unshieldToken records openings

/-- The owned transact equation. -/
example (verify : Pool.Verifier) (s : Pool.ContractState) {N M : Nat} (caller : Term)
    (pub : TransactOwnedPublic N M) (bp : BoundParams) (proof : Term)
    (records : List (Term × CommitmentPreimage)) (openings : List (Term × OwnedOpening)) :
    Pool.apply verify s (.transactOwned caller pub bp proof records openings) =
      if h : s.TransactOwnedPre verify caller pub bp proof records openings then
        some (s.transactOwnedEffect verify caller pub bp proof records ⟨openings, h⟩)
      else none :=
  Pool.apply_transactOwned_equation verify s caller pub bp proof records openings

/-- The fee-admin setter equation. -/
example (verify : Pool.Verifier) (s : Pool.ContractState) (caller : Term) (r : FeeRatio) :
    Pool.apply verify s (.setFeeRatio caller r) =
      if h : s.SetFeeRatioPre caller r then some (s.setFeeRatioEffect caller ⟨r, h⟩)
      else none :=
  Pool.apply_setFeeRatio_equation verify s caller r

/-! ### Axioms

`lean_probe.py` reports each `#print axioms` line. The check after them fails the probe
when a main declaration depends on an axiom other than Lean's three core axioms and the
model's three declared primitives (PE6: no new axiom; `sorryAx` is not allowed). -/

#print axioms Pool.apply
#print axioms Pool.apply_shield_equation
#print axioms Pool.apply_transact_equation
#print axioms Pool.apply_transactOwned_equation
#print axioms Pool.apply_setFeeRatio_equation

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound,
    ``EdDSAVerify, ``VerifyAccepts, ``VerifyOwnedAccepts]
  for d in [``Pool.apply, ``Pool.apply_shield_equation, ``Pool.apply_transact_equation,
      ``Pool.apply_transactOwned_equation, ``Pool.apply_setFeeRatio_equation] do
    for a in (← collectAxioms d) do
      unless allowed.contains a do
        throwError m!"{d} depends on the axiom {a}, which is not allowed"
