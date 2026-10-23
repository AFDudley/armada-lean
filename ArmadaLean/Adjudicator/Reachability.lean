/-
  ArmadaLean.Adjudicator.Reachability — every state any sequence of calls
  by any caller can reach.

  Phase 1 brief: "A safety statement holds at every state reachable from
  deployment by any sequence of calls by any caller, so state it over that
  reachable set, not over one step from a chosen state." Nitro-2019-219.pdf
  §3.3: "There is no restriction on who can trigger the operations" — this
  file's closure does not distinguish callers, matching that quote and
  `Operations.lean`'s `Step` (which already carries no caller-identity
  field beyond what each call's own data supplies).
-/
import ArmadaLean.Adjudicator.Operations

namespace ArmadaLean.Adjudicator

/-- `s` steps to `s'` through the exact call sequence `calls`, in order
    (the "unimpeded... any operation... before time t + Δ" world of
    Nitro-2019-219.pdf §4.3 assumption 1, with no step skipped or
    reordered). -/
def AppliesAll (s : AdjudicatorState) : List Call → AdjudicatorState → Prop
  | [], s' => s' = s
  | call :: rest, s' => ∃ mid, Step s call mid ∧ AppliesAll mid rest s'

/-- Every state reachable from `s0` by SOME sequence of calls by SOME
    (unrestricted) set of callers. The reflexive-transitive closure of
    `Step`, stated through `AppliesAll` so a witnessing call sequence is
    always at hand for the liveness theorems in `Safety.lean`. -/
def Reachable (s0 s : AdjudicatorState) : Prop :=
  ∃ calls : List Call, AppliesAll s0 calls s

theorem reachable_refl (s0 : AdjudicatorState) : Reachable s0 s0 :=
  ⟨[], rfl⟩

/-- `AppliesAll` composes along list append. -/
theorem appliesAll_append {s mid s' : AdjudicatorState} {calls1 calls2 : List Call}
    (h1 : AppliesAll s calls1 mid) (h2 : AppliesAll mid calls2 s') :
    AppliesAll s (calls1 ++ calls2) s' := by
  induction calls1 generalizing s with
  | nil =>
    have hmid : mid = s := h1
    subst hmid
    simpa using h2
  | cons c cs ih =>
    obtain ⟨m, hc, hrest⟩ := h1
    exact ⟨m, hc, ih hrest⟩

theorem reachable_step {s0 s s' : AdjudicatorState} {call : Call}
    (h : Reachable s0 s) (hstep : Step s call s') : Reachable s0 s' := by
  obtain ⟨calls, happ⟩ := h
  exact ⟨calls ++ [call], appliesAll_append happ ⟨s', hstep, rfl⟩⟩

end ArmadaLean.Adjudicator
