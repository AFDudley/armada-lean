/-
  ArmadaLean.PoolMachine — the pool as a `Machine` (`ArmadaLean.Machine`).
  Operator ruling 2026-10-29 ("Generic state: `Machine` and `System`"):
  `docs/process.md:130` requires a step to start "built by real steps from
  genesis". `PoolSafety.lean`'s four can-happen theorems take this file's
  `Pool.machine.Reachable s` as a hypothesis, so this file is imported
  before `PoolSafety.lean`, not after it.
-/
import ArmadaLean.Machine
import ArmadaLean.Pool

/-- The pool as a `Machine`: an initial state is `genesis r` for some fee
    rate `r` (`genesis`, `Pool.lean:968`, one genesis state per fee rate,
    not a single state); a step is `Step` (`Pool.lean:1037`). -/
def Pool.machine : Machine PoolState where
  init := fun s => ∃ r, s = genesis r
  step := Step

/-- `Pool.machine`'s `Machine.Reachable` is exactly `Pool.lean`'s own
    `Reachable` (`Pool.lean:1146`): both are some `genesis r`, closed under
    `Step`. -/
theorem Pool.machine_reachable_iff {s : PoolState} : Pool.machine.Reachable s ↔ Reachable s := by
  constructor
  · rintro ⟨s₀, ⟨r, rfl⟩, hsteps⟩
    induction hsteps with
    | refl => exact Reachable.genesis r
    | tail _ hstep ih => exact Reachable.step ih hstep
  · intro hr
    induction hr with
    | genesis r => exact ⟨genesis r, ⟨r, rfl⟩, Relation.ReflTransGen.refl⟩
    | step _ hstep ih =>
      obtain ⟨s₀, hinit, hsteps⟩ := ih
      exact ⟨s₀, hinit, hsteps.tail hstep⟩
