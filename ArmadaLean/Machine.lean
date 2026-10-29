/-
  A generic reactive component and its reachable states. Operator ruling
  2026-10-29 (`armada-laconic/labbook/2026-10-29-nitro-reachability-ruling.md`,
  "Generic state: `Machine` and `System`"): reachability is defined once,
  generically. A `Machine` is one reactive component (motif #13; Abrial
  2010, Event-B `MACHINE`): states, initial states, one step relation.
  `Machine.Reachable` and one invariant principle (`Machine.invariant`)
  serve every machine (`docs/process.md` Stratum 2, and 4.4 on parallel
  inductions). A `System` is a composition of machines; its reachable
  states are those of the composed machine. No composition operator lives
  here: `Machine.interleave` (independent machines, no shared state) was
  the wrong shape for the Nitro network game, whose participants share one
  chain (coordinator finding 2026-10-29); `ArmadaLean/Nitro/Reachable.lean`
  states that machine directly, over one `Network` type with one `chain`
  field.
-/
import Mathlib.Logic.Relation

/-- One reactive component: a predicate on initial states and a step
    relation between states (Event-B `MACHINE`). -/
structure Machine (S : Type) where
  init : S → Prop
  step : S → S → Prop

/-- The states `M` can reach: some initial state, followed by zero or more
    steps (`Relation.ReflTransGen`). -/
def Machine.Reachable {S : Type} (M : Machine S) (s : S) : Prop :=
  ∃ s₀, M.init s₀ ∧ Relation.ReflTransGen M.step s₀ s

/-- **Invariant induction**, the one proof rule `Machine.Reachable` needs:
    a property true of every initial state and preserved by every step is
    true of every reachable state. -/
theorem Machine.invariant {S : Type} (M : Machine S) {P : S → Prop}
    (h0 : ∀ s, M.init s → P s) (hs : ∀ s s', P s → M.step s s' → P s') :
    ∀ s, M.Reachable s → P s := by
  intro s hr
  obtain ⟨s₀, hinit, hsteps⟩ := hr
  have hP0 : P s₀ := h0 s₀ hinit
  induction hsteps with
  | refl => exact hP0
  | tail _ hstep ih => exact hs _ _ ih hstep
