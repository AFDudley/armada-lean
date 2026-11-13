/-
  Probe for rule PE5 (backward refinement), `docs/pool-executable.md`. It elaborates only
  when PE5 holds. Run it from the repo root, after `lake build`:

    python3 scripts/oracles/lean_probe.py scripts/oracles/pool_exec/PE5.lean

  The interface it fixes (it uses PE1-PE3): the two structures `TransactProofSoundness`
  and `OwnedProofSoundness`, each with exactly one field `sound`, and the theorem
  `Pool.apply_backward_refinement`, with the statement below and its arguments in this
  order.

  The hypothesis of PE5, "every public input that `verify` accepts has a witness that
  satisfies the circuit", is the soundness of the trusted verifier: the verifier stays
  trusted. `Step.transact` and `Step.transactOwned` take it today as their hypotheses
  `Constrained w pub` and `OwnedConstrained w pub`. The two soundness structures state it
  over `VerifyAccepts` and `VerifyOwnedAccepts`, the converse of `TransactProofCompleteness`
  and `OwnedProofCompleteness`. `Pool.Verifier.Realizes verify` (PE3) carries it to
  `verify`.
-/
import ArmadaLean

-- Every armada-lean declaration is under the root namespace `ArmadaLean`.
open ArmadaLean

-- An unknown name in a binder must be an error, not a new variable.
set_option autoImplicit false

/-! ### The soundness hypotheses -/

/-- `TransactProofSoundness` is exactly: every public input that the trusted verifier
    accepts has a witness that satisfies `Transact.circom`. -/
example (sound : ∀ {N M : Nat} {pub : TransactPublic N M},
      VerifyAccepts pub → ∃ w : TransactWitness N M, Constrained w pub) :
    TransactProofSoundness :=
  ⟨sound⟩

example (h : TransactProofSoundness) {N M : Nat} {pub : TransactPublic N M}
    (hv : VerifyAccepts pub) : ∃ w : TransactWitness N M, Constrained w pub :=
  h.sound hv

/-- `OwnedProofSoundness` is exactly: every public input that the trusted owned verifier
    accepts has a witness that satisfies `TransactOwned.circom`. -/
example (sound : ∀ {N M : Nat} {pub : TransactOwnedPublic N M},
      VerifyOwnedAccepts pub → ∃ w : TransactOwnedWitness N M, OwnedConstrained w pub) :
    OwnedProofSoundness :=
  ⟨sound⟩

example (h : OwnedProofSoundness) {N M : Nat} {pub : TransactOwnedPublic N M}
    (hv : VerifyOwnedAccepts pub) : ∃ w : TransactOwnedWitness N M, OwnedConstrained w pub :=
  h.sound hv

/-! ### The theorem -/

/-- PE5: for every reachable state, a call that `Pool.apply` accepts is the contract image
    of some step from that state. -/
example (verify : Pool.Verifier) (hReal : verify.Realizes)
    (hTS : TransactProofSoundness) (hOS : OwnedProofSoundness)
    (s : ReachableState Pool.machine) {c : Pool.Call} {t : Pool.ContractState}
    (h : Pool.apply verify s.state.contract c = some t) :
    ∃ s' : PoolState, Step s.state s' ∧ s'.contract = t :=
  Pool.apply_backward_refinement verify hReal hTS hOS s h

/-! ### Axioms

`lean_probe.py` reports each `#print axioms` line. The check after them fails the probe
when a main declaration depends on an axiom other than Lean's three core axioms and the
model's three declared primitives (PE6: no new axiom; `sorryAx` is not allowed). -/

#print axioms Pool.apply_backward_refinement

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound,
    ``EdDSAVerify, ``VerifyAccepts, ``VerifyOwnedAccepts]
  for d in [``Pool.apply_backward_refinement] do
    for a in (← collectAxioms d) do
      unless allowed.contains a do
        throwError m!"{d} depends on the axiom {a}, which is not allowed"
