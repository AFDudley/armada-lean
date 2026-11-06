/-
  ArmadaLean.Types.Reachable — the reachable states of a machine, as a type.

  Operator decision 2026-10-31: reachability is a type, not a hypothesis. A
  statement over the reachable states of a machine `M` takes one binder
  `(s : ReachableState M)`. It does not take a state `s` and a separate
  hypothesis `M.Reachable s`. A statement that is true of every state takes the
  raw state type, and its spec entry says "Every state" with its reason
  (`docs/spec-module-design.md`).

  This module starts the typed library of
  `armada-laconic/docs/lean/typed-library.md` (§3 rules 2-3, §4 `Reachable.lean`).
  It is generic: it imports only `ArmadaLean.Machine`. The Nitro forms
  (`Nitro.ReachableNetwork`, `Nitro.ReachableParticipant`) are abbreviations in
  `ArmadaLean/Nitro/Reachable.lean`, directly after the machines they name.

  API (`typed-library.md` §3 rule 2): the coercion to the carrier
  (`ReachableState.state`), the evidence (`ReachableState.reachable`), the
  constructor from a reachability proof (`ReachableState.mk'`), and `@[simp]`
  lemmas for the projections. `Machine.Reachable` is not decidable, so the type
  has no decidable smart constructor `ofX?`.
-/
import ArmadaLean.Machine

namespace ArmadaLean

/-- The states of `M` that some history reaches: a state together with the proof
    `M.Reachable s` (`Machine.Reachable`, `ArmadaLean/Machine.lean`). -/
def ReachableState {S : Type} (M : Machine S) : Type := {s : S // M.Reachable s}

namespace ReachableState

variable {S : Type} {M : Machine S}

/-- The state. -/
@[reducible] def state (s : ReachableState M) : S := Subtype.val s

/-- The state is reachable. -/
theorem reachable (s : ReachableState M) : M.Reachable s.state := Subtype.property s

/-- A reachable state from a state and its reachability proof. -/
def mk' (s : S) (h : M.Reachable s) : ReachableState M := ⟨s, h⟩

/-- The coercion to the carrier is `state`. -/
instance : CoeOut (ReachableState M) S := ⟨state⟩

@[simp] theorem state_mk' (s : S) (h : M.Reachable s) : (mk' s h).state = s := rfl

@[simp] theorem state_mk (s : S) (h : M.Reachable s) :
    state (⟨s, h⟩ : ReachableState M) = s := rfl

@[simp] theorem coe_eq_state (s : ReachableState M) : ((s : S)) = s.state := rfl

/-- Two reachable states are equal when their states are equal. -/
@[ext] theorem ext {s t : ReachableState M} (h : s.state = t.state) : s = t :=
  Subtype.ext h

/-- One more step of `M` keeps the state reachable (`Machine.Reachable.tail`). -/
def step (s : ReachableState M) {s' : S} (h : M.step s.state s') : ReachableState M :=
  ⟨s', s.reachable.tail h⟩

@[simp] theorem state_step (s : ReachableState M) {s' : S} (h : M.step s.state s') :
    (s.step h).state = s' := rfl

end ReachableState

end ArmadaLean
