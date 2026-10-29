/-
  A generic reactive component and its reachable states. Operator ruling
  2026-10-29 (`armada-laconic/labbook/2026-10-29-nitro-reachability-ruling.md`,
  "Generic state: `Machine` and `System`"): reachability is defined once,
  generically. A `Machine` is one reactive component (motif #13; Abrial
  2010, Event-B `MACHINE`): states, initial states, one step relation.
  `Machine.Reachable` and one invariant principle (`Machine.invariant`)
  serve every machine (`docs/process.md` Stratum 2, and 4.4 on parallel
  inductions). A `System` is a composition of machines; its reachable
  states are those of the composed machine. `Machine.interleave` below is
  the one composition this draft needs: independent machines with no
  shared state, each stepping on its own turn.
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

/-- Compose a family of machines, one per index `i : I`, with no shared
    state: the joint state is the dependent product `∀ i, S i`, a step
    picks one index and lets that component machine step, and every other
    component's state is unchanged. -/
def Machine.interleave {I : Type} {S : I → Type} (M : ∀ i, Machine (S i)) :
    Machine (∀ i, S i) where
  init := fun s => ∀ i, (M i).init (s i)
  step := fun s s' => ∃ i, (M i).step (s i) (s' i) ∧ ∀ j, j ≠ i → s j = s' j

/-- A reachable state of the composed machine projects to a reachable state
    of each component machine: either a step touched component `i`
    (extend `i`'s own reachability by that step) or it did not (`i`'s state
    is unchanged, `hother`). -/
theorem Machine.interleave_reachable_component {I : Type} {S : I → Type}
    (M : ∀ i, Machine (S i)) {s : ∀ i, S i} (h : (Machine.interleave M).Reachable s) (i : I) :
    (M i).Reachable (s i) := by
  obtain ⟨s₀, hinit, hsteps⟩ := h
  refine ⟨s₀ i, hinit i, ?_⟩
  induction hsteps with
  | refl => exact Relation.ReflTransGen.refl
  | @tail s1 s2 _ hstep ih =>
    obtain ⟨j, hj, hother⟩ := hstep
    by_cases hji : j = i
    · subst hji
      exact ih.tail hj
    · have heq : s1 i = s2 i := hother i (Ne.symm hji)
      rw [← heq]
      exact ih
