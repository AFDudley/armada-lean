/-
  ArmadaLean.PoolMachine — the pool as a `Machine` (`ArmadaLean.Machine`).
  ("Generic state: `Machine` and `System`"):
  `docs/process.md:130` requires a step to start "built by real steps from
  genesis". `PoolSafety.lean`'s four can-happen theorems take this file's
  `Pool.machine.Reachable s` as a hypothesis, so this file is imported
  before `PoolSafety.lean`, not after it.
-/
import ArmadaLean.Machine
import ArmadaLean.Pool

namespace ArmadaLean

/-- The pool as a `Machine`: an initial state is `genesis r feeAdmin treasury` for some
    fee rate `r`, fee admin `feeAdmin` and treasury address `treasury` (`genesis`, one
    genesis state per deployment, not a single state); a step is `Step`. -/
def Pool.machine : Machine PoolState where
  init := fun s => ∃ r feeAdmin treasury, s = genesis r feeAdmin treasury
  step := Step

/-- `Pool.machine`'s `Machine.Reachable` is exactly `Pool.lean`'s own
    `Reachable`: both are some `genesis r feeAdmin treasury`, closed under `Step`. -/
theorem Pool.machine_reachable_iff {s : PoolState} : Pool.machine.Reachable s ↔ Reachable s := by
  constructor
  · rintro ⟨s₀, ⟨r, a, t, rfl⟩, hsteps⟩
    induction hsteps with
    | refl => exact Reachable.genesis r a t
    | tail _ hstep ih => exact Reachable.step ih hstep
  · intro hr
    induction hr with
    | genesis r a t => exact ⟨genesis r a t, ⟨r, a, t, rfl⟩, Relation.ReflTransGen.refl⟩
    | step _ hstep ih =>
      obtain ⟨s₀, hinit, hsteps⟩ := ih
      exact ⟨s₀, hinit, hsteps.tail hstep⟩

end ArmadaLean
