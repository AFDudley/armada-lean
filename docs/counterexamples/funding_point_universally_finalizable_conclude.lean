/-
  Counterexample to `funding_point_universally_finalizable` (Liveness.lean),
  Nitro-23 (Nitro:635-636): a final setup state with
  another outcome.

  The earlier rule `HonestSend.noAlternative` forbade two states of one
  channel at one turn below the funding point. It did not forbid a final
  state. `AtFundingPoint` bounds the turn number of a sent state, not its
  `isFinal` flag. So a participant that kept that rule could still sign a
  final state below the funding point, at a turn where another participant
  is the mover, and the claim failed on the honest network of that time.
  Design decision 2026-11-01: `HonestSend.noConflict` replaces
  `noAlternative`. The honest participant signs no two states of one
  channel at one slot with two outcomes, and every setup turn is one slot.
  So below the funding point, every state that it signs on a channel, final
  or not, carries the setup outcome (ForceMove:1112-1114, ForceMove:1208;
  `State.signSlot_setup`). So `nF` is not reachable on the
  honest network `Nitro.network` (`nF_not_honest`), and the library theorem
  holds. This file shows that the claim fails without the rule, on the
  unrestricted network `Nitro.networkUnrestricted`.

  The network `nF` starts at genesis and has three sends on the
  two-participant channel `c2 = [p0, q0]` (`c2.n = 2`):
  * `p0` sends `sA0` (turn 0, outcome `Ωg`, not final).
  * `q0` sends `sA1` (turn 1, outcome `Ωg`, not final).
  * `p0` sends `sF1` (turn 1, outcome `Ωb ≠ Ωg`, final).
  Every participant holds the turn-0 and turn-1 states with outcome `Ωg`,
  so `AtFundingPoint` holds for `Ωg`. Every other hypothesis holds, with
  `vtAll` and the canonical threats `Ts apps1`.

  In `p0`'s game, `q0` is the adversary. Before the first call of `p0`
  lands, the adversary calls `conclude` with `⟨sF1, [p0, q0]⟩`. This is a
  conclusion proof (`ConclusionProof`): `sF1` is final and both participants
  sign it. The `p0` signature is not forged, because `p0` sent `sF1`. The
  channel then finalizes with `Ωb`, and the outcome of finalization never
  changes (`UnbeatableIn.finalized_eq_of_steps`). So `Ωg` is not
  finalizable for `p0` (`not_finalizable`).

  go-nitro's unanimous `conclude` checks no transition; ForceMove:1208
  requires the resolution to match on a setup-to-CONCLUDE transition. The
  rule is therefore a rule of the honest signer.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/funding_point_universally_finalizable_conclude.lean`.
-/
import ArmadaLean.Nitro.NonVacuity

namespace ArmadaLean.Nitro.Counterexample.FundingPointConclude

open ArmadaLean.Nitro ArmadaLean.Nitro.NonVacuity

/-! ## The states and the network -/

def o2 : Allocation Nat := [alloc d1 1]
/-- The outcome every participant holds at the funding point. -/
def Ωg : Outcome Nat := .allocation o1
/-- The outcome of the final state `p0` signs at turn 1. -/
def Ωb : Outcome Nat := .allocation o2

theorem Ωb_ne_Ωg : Ωb ≠ Ωg := by decide

def sA0 : State Nat := ⟨c2, 0, Ωg, false, .opaque 0⟩
def sA1 : State Nat := ⟨c2, 1, Ωg, false, .opaque 0⟩
/-- `p0`'s final state at turn 1, the turn of `q0`. -/
def sF1 : State Nat := ⟨c2, 1, Ωb, true, .opaque 0⟩

def n0 : Network Nat := ⟨g0, fun _ => [], fun _ => [], noDeposits⟩
def nA : Network Nat := n0.applyHonest p0 (.send sA0)
def nB : Network Nat := nA.applyHonest q0 (.send sA1)
/-- `p0` sends a final state at turn 1. -/
def nF : Network Nat := nB.applyHonest p0 (.send sF1)

theorem voucher_gate (n : Network Nat) (st : State Nat) (hst : st.voucher? = none) :
    ∀ r : Reaction Nat, HonestMove.send st = .react r → ∀ st' ∈ r.sends, n.VoucherSendable st' := by
  intro r hr st' hst'
  injection hr with hr; subst hr
  simp only [List.mem_singleton] at hst'; subst hst'
  intro v hv; rw [hst] at hv; cases hv

/-! Reachability steps on the unrestricted network `Nitro.networkUnrestricted` (an honest
    move needs only feasible calls, `HonestMove.CallsFeasible`). -/

theorem networkU_reachable_init (apps : Apps Nat) (Ts : Threats Nat apps) (w : Participant → Coins) :
    (Nitro.networkUnrestricted apps Ts).Reachable
      (⟨Adjudicator.genesis, fun _ => [], fun _ => [], w⟩ : Network Nat) :=
  ⟨_, ⟨rfl, rfl, rfl⟩, .refl⟩

theorem networkU_reachable_honest {apps : Apps Nat} {Ts : Threats Nat apps} {n : Network Nat}
    (h : (Nitro.networkUnrestricted apps Ts).Reachable n) (p : Participant) (m : HonestMove Nat)
    (hm : m.CallsFeasible (n.view p))
    (hvgate : ∀ r : Reaction Nat, m = .react r → ∀ st ∈ r.sends, n.VoucherSendable st) :
    (Nitro.networkUnrestricted apps Ts).Reachable (Network.applyHonest n p m) :=
  h.tail ⟨p, Or.inl ⟨m, hm, hvgate, rfl⟩⟩

/-- `nF` is reachable on the unrestricted network: it has no signing rule, only
    the voucher gate. -/
theorem nF_reach : (Nitro.networkUnrestricted apps1 (Ts apps1)).Reachable nF :=
  networkU_reachable_honest
    (networkU_reachable_honest
      (networkU_reachable_honest (networkU_reachable_init apps1 (Ts apps1) noDeposits) p0 (.send sA0)
        (by simp) (voucher_gate _ _ rfl))
      q0 (.send sA1) (by simp) (voucher_gate _ _ rfl))
    p0 (.send sF1) (by simp) (voucher_gate _ _ rfl)

theorem nF_views_p0 : nF.views p0 = ⟨g0, [⟨sA1, [q0]⟩], [⟨sF1, [p0]⟩, ⟨sA0, [p0]⟩]⟩ := by
  simp [nF, nB, nA, n0, Network.views, Network.view, Network.applyHonest, HonestMove.send,
    State.recipients, sA0, sA1, sF1, c2, p0, q0]

theorem nF_views_q0 : nF.views q0 = ⟨g0, [⟨sF1, [p0]⟩, ⟨sA0, [p0]⟩], [⟨sA1, [q0]⟩]⟩ := by
  simp [nF, nB, nA, n0, Network.views, Network.view, Network.applyHonest, HonestMove.send,
    State.recipients, sA0, sA1, sF1, c2, p0, q0]

theorem nF_views_chain (r : Participant) : (nF.views r).chain = g0 := rfl

/-! ## Every hypothesis of the theorem holds -/

theorem atFundingPoint : AtFundingPoint nF.views c2 Ωg := by
  refine ⟨?_, ?_⟩
  · intro r hr k hk
    have hr' : r = p0 ∨ r = q0 := by simpa [c2] using hr
    have hk' : k = 0 ∨ k = 1 := by
      have : k < 2 := by simpa [FixedPart.n, c2] using hk
      omega
    rcases hk' with rfl | rfl
    · refine ⟨⟨sA0, [p0]⟩, ?_, rfl, rfl, rfl, rfl, ⟨p0, by decide, by decide⟩⟩
      rcases hr' with rfl | rfl
      · rw [nF_views_p0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
      · rw [nF_views_q0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
    · refine ⟨⟨sA1, [q0]⟩, ?_, rfl, rfl, rfl, rfl, ⟨q0, by decide, by decide⟩⟩
      rcases hr' with rfl | rfl
      · rw [nF_views_p0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
      · rw [nF_views_q0]; exact holds_intro _ _ (by decide) (fun _ h => by cases h)
  · intro r hr ss hss _
    have hr' : r = p0 ∨ r = q0 := by simpa [c2] using hr
    rcases hr' with rfl | rfl
    · rw [nF_views_p0] at hss
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
      rcases hss with rfl | rfl <;> decide
    · rw [nF_views_q0] at hss
      simp only [List.mem_singleton] at hss; subst hss; decide

/-! ## The adversary concludes with `p0`'s final state -/

/-- `p0`'s adversary: the canonical threat of `NonVacuity.lean`. -/
abbrev T : Threat Nat p0 := (Ts apps1).T p0

def net0 : NetworkState Nat p0 := ⟨g0, [⟨sA1, [q0]⟩], [⟨sF1, [p0]⟩, ⟨sA0, [p0]⟩]⟩

theorem net0_eq : nF.views p0 = net0 := nF_views_p0

/-- The conclusion proof: `sF1` with the signatures of `p0` and `q0`. -/
def ssF : SignedState Nat := ⟨sF1, [p0, q0]⟩
def concludeOp : Op Nat := .conclude c2 ssF

def s1 : Adjudicator Nat := g0.setStatus c2 (.finalized 1 Ωb Ωb)

theorem g0_conclude : g0.apply apps1 q0 concludeOp = some s1 := by
  simp only [concludeOp, Adjudicator.apply, Adjudicator.conclude]
  rw [if_pos (by decide)]
  rfl

/-- The adversary may conclude: the caller is `q0`, and `p0` sent `sF1`. -/
theorem conclude_feasible : T.feasible net0 (.chain q0 concludeOp) := by
  refine ⟨by decide, fun ss hss => ?_⟩
  simp only [concludeOp, Op.proofStates, List.mem_singleton] at hss
  subst hss
  exact unforged_intro _ _ (fun _ => ⟨⟨sF1, [p0]⟩, by simp [net0], rfl⟩) (fun _ h => by cases h)

def net1 : NetworkState Nat p0 := net0.applyAdv apps1 (.chain q0 concludeOp)

theorem net1_chain : net1.chain = s1 := by
  have h : net0.chain.apply apps1 q0 concludeOp = some s1 := g0_conclude
  simp only [net1, NetworkState.applyAdv_chain_some apps1 h]

theorem net1_finalized : net1.chain.finalizedWith c2.address = some Ωb := by
  rw [net1_chain]
  simp [s1, FixedPart.address_eq, ChannelStatus.finalizedWith]

/-- `Ωg` is not finalizable for `p0` at the funding point. -/
theorem not_finalizable : ¬ Finalizable apps1 T c2 Ωg (nF.views p0) := by
  rw [net0_eq]
  intro h
  have hS : OtherSteps apps1 T net0 net1 :=
    .tail .refl conclude_feasible (by intro dt h; cases h) (by intro o h; cases h)
  have hnow : net1.chain.now = net0.chain.now := by rw [net1_chain]; rfl
  exact Ωb_ne_Ωg (UnbeatableIn.finalized_eq_of_steps h hS hnow net1_finalized)

/-! ## The counterexample -/

/-- Every hypothesis of `funding_point_universally_finalizable` holds for
    `apps1`, `Ts apps1`, `nF`, `c2`, `Ωg` and `vtAll`, with `nF` reachable on
    the unrestricted network, and the conclusion fails: `Ωg` is not
    finalizable for `p0`. -/
theorem funding_point_universally_finalizable_false :
    ¬ ∀ (apps : Apps Nat) (Ts : Threats Nat apps) (v : Views Nat) (n : Network Nat)
        (_hr : (Nitro.networkUnrestricted apps Ts).Reachable n) (_hvn : v = n.views) (c : FixedPart)
        (Ω : Outcome Nat) (vt : State Nat → State Nat → Bool)
        (_hc : apps c.appDef = forceMoveRules vt) (_hsetup : SetupPhaseKeepsOutcome vt c)
        (_hvt : SetupPhaseAccepted vt c) (_hn : 0 < c.n) (_h : AtFundingPoint v c Ω)
        (_hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0),
        UniversallyFinalizable apps Ts v c Ω := by
  intro h
  have hU := h apps1 (Ts apps1) nF.views nF nF_reach rfl c2 Ωg vtAll rfl
    (fun s1 s2 h _ _ => by simpa [vtAll] using h)
    (fun s1 s2 _ _ _ _ ho _ => by simp [vtAll, ho])
    (by decide) atFundingPoint
    (fun r => by rw [nF_views_chain]; exact ⟨rfl, rfl⟩)
  exact not_finalizable (hU p0 (by simp [c2]))

/-- The own-violation: `p0` signed two setup states of `c2` with two outcomes
    (`sA0` with `Ωg`, the final `sF1` with `Ωb`), against
    `HonestSend.noConflict` (one slot for every setup turn, `State.signSlot_setup`). -/
theorem p0_breaks_noConflict {sup : State Nat → Prop} :
    ¬ ∀ s ∈ (nF.views p0).sent, HonestSend (nF.views p0).sent (nF.views p0).HoldsPrefund sup s.state := by
  intro h
  have h_eq := (h ⟨sF1, [p0]⟩ (by simp [nF_views_p0])).outcome_eq ⟨sA0, [p0]⟩
    (by simp [nF_views_p0]) (by decide) (State.signSlot_setup ⟨by decide, by decide⟩)
  exact Ωb_ne_Ωg h_eq.symm

/-- `nF` is not reachable on the honest network: there, every view satisfies the
    signing rules (`Nitro.participant_sent_honest`,
    `Nitro.network_views_participant_reachable`). -/
theorem nF_not_honest : ¬ (Nitro.network apps1 (Ts apps1)).Reachable nF := fun h =>
  p0_breaks_noConflict
    (Nitro.participant_sent_honest ⟨_, Nitro.network_views_participant_reachable ⟨nF, h⟩ p0⟩)

end ArmadaLean.Nitro.Counterexample.FundingPointConclude

#print axioms ArmadaLean.Nitro.Counterexample.FundingPointConclude.funding_point_universally_finalizable_false
#print axioms ArmadaLean.Nitro.Counterexample.FundingPointConclude.nF_not_honest
