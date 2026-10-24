/-
  ArmadaLean.Adjudicator.Reachability — every state any sequence of calls
  by any caller can reach, from the deployment state.

  Phase 1 brief: "A safety statement holds at every state reachable from
  deployment by any sequence of calls by any caller, so state it over that
  reachable set, not over one step from a chosen state." Nitro-2019-219.pdf
  §3.3: "There is no restriction on who can trigger the operations" — this
  file's closure does not distinguish CALLERS, matching that quote; it
  does track each call's `Actor` (`Operations.lean`), because `.sign`/
  `.signNote` restrict who may take THOSE two steps (same file's module
  comment), and a reachability argument needs to see which actor each step
  in a witnessing sequence used. `Reachable` is anchored at `State.lean`'s
  `genesis`, the deployment state — not an arbitrary starting state a
  theorem could leave unconstrained.

  `AppliesAll`/`Reachable` carry the same `SignatureAssumptions`/`appRel`
  parameters `Step` does, since they are built from `Step`.
-/
import ArmadaLean.Adjudicator.Operations

namespace ArmadaLean.Adjudicator

/-- `s` steps to `s'` through the exact sequence of `(actor, call)` pairs,
    in order (the "unimpeded... any operation... before time t + Δ" world
    of Nitro-2019-219.pdf §4.3 assumption 1, with no step skipped or
    reordered). Each pair names who actually took that step — unconstrained
    for most calls, restricted to the key holder for `.sign`/`.signNote`
    (`Operations.lean`'s `Step`). -/
def AppliesAll (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (s : AdjudicatorState) : List (Actor × Call) → AdjudicatorState → Prop
  | [], s' => s' = s
  | (actor, call) :: rest, s' =>
      ∃ mid, Step sig appRel actor s call mid ∧ AppliesAll sig appRel mid rest s'

/-- Every state reachable from deployment (`genesis assets self pool0`) by
    SOME sequence of `(actor, call)` steps by SOME (unrestricted) set of
    callers, under assumptions `sig`/`appRel`. The reflexive-transitive
    closure of `Step`, stated through `AppliesAll` so a witnessing call
    sequence is always at hand for the liveness theorems in
    `Safety.lean`. -/
def Reachable (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (deployed s : AdjudicatorState) : Prop :=
  ∃ calls : List (Actor × Call), AppliesAll sig appRel deployed calls s

theorem reachable_refl (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (deployed : AdjudicatorState) : Reachable sig appRel deployed deployed :=
  ⟨[], rfl⟩

/-- `AppliesAll` composes along list append. -/
theorem appliesAll_append {sig : SignatureAssumptions}
    {appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop}
    {s mid s' : AdjudicatorState} {calls1 calls2 : List (Actor × Call)}
    (h1 : AppliesAll sig appRel s calls1 mid)
    (h2 : AppliesAll sig appRel mid calls2 s') :
    AppliesAll sig appRel s (calls1 ++ calls2) s' := by
  induction calls1 generalizing s with
  | nil =>
    have hmid : mid = s := h1
    subst hmid
    simpa using h2
  | cons c cs ih =>
    obtain ⟨m, hc, hrest⟩ := h1
    exact ⟨m, hc, ih hrest⟩

theorem reachable_step {sig : SignatureAssumptions}
    {appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop}
    {deployed s s' : AdjudicatorState} {actor : Actor} {call : Call}
    (h : Reachable sig appRel deployed s)
    (hstep : Step sig appRel actor s call s') :
    Reachable sig appRel deployed s' := by
  obtain ⟨calls, happ⟩ := h
  exact ⟨calls ++ [(actor, call)], appliesAll_append happ ⟨s', hstep, rfl⟩⟩

end ArmadaLean.Adjudicator
