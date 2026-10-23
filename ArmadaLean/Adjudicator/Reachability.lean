/-
  ArmadaLean.Adjudicator.Reachability — every state any sequence of calls
  by any caller can reach, from the deployment state.

  Phase 1 brief: "A safety statement holds at every state reachable from
  deployment by any sequence of calls by any caller, so state it over that
  reachable set, not over one step from a chosen state." Nitro-2019-219.pdf
  §3.3: "There is no restriction on who can trigger the operations" — this
  file's closure does not distinguish callers, matching that quote and
  `Operations.lean`'s `Step` (which already carries no caller-identity
  field beyond what each call's own data supplies). `Reachable` is anchored
  at `State.lean`'s `genesis`, the deployment state — not an arbitrary
  starting state a theorem could leave unconstrained (coordinator
  correction, this session).

  `AppliesAll`/`Reachable` carry the same `SignatureAssumptions`/
  `ProofAssumptions` parameters `Step` does, since they are built from
  `Step`.
-/
import ArmadaLean.Adjudicator.Operations

namespace ArmadaLean.Adjudicator

/-- `s` steps to `s'` through the exact call sequence `calls`, in order
    (the "unimpeded... any operation... before time t + Δ" world of
    Nitro-2019-219.pdf §4.3 assumption 1, with no step skipped or
    reordered). -/
def AppliesAll (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s : AdjudicatorState) : List Call → AdjudicatorState → Prop
  | [], s' => s' = s
  | call :: rest, s' => ∃ mid, Step sig proofA s call mid ∧ AppliesAll sig proofA mid rest s'

/-- Every state reachable from deployment (`genesis assets self`) by SOME
    sequence of calls by SOME (unrestricted) set of callers, under
    assumptions `sig`/`proofA`. The reflexive-transitive closure of `Step`,
    stated through `AppliesAll` so a witnessing call sequence is always at
    hand for the liveness theorems in `Safety.lean`. -/
def Reachable (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (deployed s : AdjudicatorState) : Prop :=
  ∃ calls : List Call, AppliesAll sig proofA deployed calls s

theorem reachable_refl (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (deployed : AdjudicatorState) : Reachable sig proofA deployed deployed :=
  ⟨[], rfl⟩

/-- `AppliesAll` composes along list append. -/
theorem appliesAll_append {sig : SignatureAssumptions} {proofA : ProofAssumptions}
    {s mid s' : AdjudicatorState} {calls1 calls2 : List Call}
    (h1 : AppliesAll sig proofA s calls1 mid) (h2 : AppliesAll sig proofA mid calls2 s') :
    AppliesAll sig proofA s (calls1 ++ calls2) s' := by
  induction calls1 generalizing s with
  | nil =>
    have hmid : mid = s := h1
    subst hmid
    simpa using h2
  | cons c cs ih =>
    obtain ⟨m, hc, hrest⟩ := h1
    exact ⟨m, hc, ih hrest⟩

theorem reachable_step {sig : SignatureAssumptions} {proofA : ProofAssumptions}
    {deployed s s' : AdjudicatorState} {call : Call}
    (h : Reachable sig proofA deployed s) (hstep : Step sig proofA s call s') :
    Reachable sig proofA deployed s' := by
  obtain ⟨calls, happ⟩ := h
  exact ⟨calls ++ [call], appliesAll_append happ ⟨s', hstep, rfl⟩⟩

end ArmadaLean.Adjudicator
