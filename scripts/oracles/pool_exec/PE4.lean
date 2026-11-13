/-
  Probe for rule PE4 (forward refinement), `docs/pool-executable.md`. It elaborates only
  when PE4 holds. Run it from the repo root, after `lake build`:

    python3 scripts/oracles/lean_probe.py scripts/oracles/pool_exec/PE4.lean

  The interface it fixes (it uses PE1-PE3): the theorem `Pool.apply_forward_refinement`,
  with the statement below and its arguments in this order.

  The hypothesis of PE4, "`verify` accepts every proof for public inputs that a witness
  satisfies", is the completeness of the trusted verifier. It is the two existing
  structures `TransactProofCompleteness` (`ArmadaLean/PoolSafety.lean`) and
  `OwnedProofCompleteness` (`ArmadaLean/PoolOwned.lean`), over `VerifyAccepts` and
  `VerifyOwnedAccepts`, with `Pool.Verifier.Realizes verify` (PE3), which says that
  `verify` accepts some proof exactly when the trusted verifier accepts the input.
-/
import ArmadaLean

-- Every armada-lean declaration is under the root namespace `ArmadaLean`.
open ArmadaLean

-- An unknown name in a binder must be an error, not a new variable.
set_option autoImplicit false

/-- PE4: for every reachable state and every step from it, some call makes `Pool.apply`
    give the contract state of the step's result. -/
example (verify : Pool.Verifier) (hReal : verify.Realizes)
    (hT : TransactProofCompleteness) (hO : OwnedProofCompleteness)
    (s : ReachableState Pool.machine) {s' : PoolState} (h : Step s.state s') :
    ∃ c : Pool.Call, Pool.apply verify s.state.contract c = some s'.contract :=
  Pool.apply_forward_refinement verify hReal hT hO s h

/-! ### Axioms

`lean_probe.py` reports each `#print axioms` line. The check after them fails the probe
when a main declaration depends on an axiom other than Lean's three core axioms and the
model's three declared primitives (PE6: no new axiom; `sorryAx` is not allowed). -/

#print axioms Pool.apply_forward_refinement

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound,
    ``EdDSAVerify, ``VerifyAccepts, ``VerifyOwnedAccepts]
  for d in [``Pool.apply_forward_refinement] do
    for a in (← collectAxioms d) do
      unless allowed.contains a do
        throwError m!"{d} depends on the axiom {a}, which is not allowed"
