/-
  Failure test for `Spec.single_enabled_is_finalizable` (Liveness.lean,
  Nitro-24, Nitro:657-658: "if a participant has only enabled a single
  outcome, that outcome must be finalizable for them"), from branch
  `draft/prove-single-enabled-is-finalizable` (`75f8578`), on the trunk types
  (`Nitro.ReachableParticipant`, `TimedChannel`, the honest machine
  `Nitro.participant`).

  The app `appsΩ` supports a candidate when the candidate's outcome is `Ω0`
  and every participant signed some state of the proof. The proof does not
  bound the candidate's turn number.

  `appsΩ` is a compliant app: the adjudicator accepts it. It is not a
  ForceMove app, and it must fail Nitro-24. Design decision 2026-11-01: an
  app that lets old signatures support a higher turn must explicitly fail
  `finalizable_or_two_enabled` and `single_enabled_is_finalizable`. This file
  proves:
  * `appsΩ_not_supportWindow`: `appsΩ` fails `Rules.SupportWindow`, the
    premise `happ` of both statements (ForceMove:744-778, 1340-1354,
    1379-1381). Signatures at turn 1 support a candidate at turn 7.
  * `single_enabled_is_finalizable_false` and
    `finalizable_or_two_enabled_false`: both statements with the premise
    deleted from the library on 2026-11-01 (`OldPremise`, every participant signed
    some state of the proof) are false. `appsΩ` carries `OldPremise`
    (`appsΩ_oldPremise`).

  At `net1`, `p0` received `stAt 1` signed by `q0`, and then `p0` sent
  `stF`, a final state at the setup turn 1 with the same outcome `Ω0`
  (ForceMove:887-888, the graceful end, with the resolution kept,
  ForceMove:986-987). The send is honest (`send_feasible`), so `net1` is
  reachable on the honest machine (`net1_reachable`). `p0` holds the proof
  `P = [stF by p0, stAt 1 by q0]`, which supports every candidate with the
  outcome `Ω0`, `stF` included (`hsupp_net1`).
  * `Ω0` is enabled (`enabled`): in the first round, after `p0`'s calls
    land, the adversary concludes `c0` with `stF` signed by `p0` and `q0`.
  * `Ω0` is the only enabled outcome (`prevents_other`): every supported
    state and every conclusion proof of `c0` has the outcome `Ω0`, so `p0`
    prevents every other outcome by waiting.
  * `Ω0` is not finalizable (`not_finalizable`): after each of `p0`'s
    reactions the adversary checkpoints `c0` with `P` at the next turn, and
    an open channel never finalizes. `p0` cannot conclude: `q0` signed no
    final state.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/single_enabled_is_finalizable_stall.lean`.
  The theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Spec.Nitro.Liveness

namespace ArmadaLean.Nitro.CounterexampleSingleEnabled

open ArmadaLean.Nitro

def p0 : Participant := ⟨0⟩
def q0 : Participant := ⟨1⟩

def Ω0 : Outcome Unit := .allocation []

/-- Rules that support a candidate with the outcome `Ω0` when each
    participant signed some state of the proof. -/
def appsΩ : Apps Unit := fun _ =>
  ⟨fun c proof cand => decide (cand.outcome = Ω0) &&
    c.participants.all (fun q => proof.any (fun ss => decide (q ∈ ss.signers)))⟩

/-- The app premise deleted from the
    library on 2026-11-01: every participant signed some state of the proof.
    It does not bound the turn that a signature supports. -/
def OldPremise (r : Rules Unit) : Prop :=
  ∀ c proof candidate, r.supports c proof candidate = true →
    ∀ q ∈ c.participants, ∃ ss ∈ proof, q ∈ ss.signers

theorem appsΩ_oldPremise (a : AppId) : OldPremise (appsΩ a) := by
  intro c proof cand h q hq
  simp only [appsΩ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
  exact h.2 q hq

theorem appsΩ_outcome {a : AppId} {c : FixedPart} {proof : SupportProof Unit} {cand : State Unit}
    (h : (appsΩ a).supports c proof cand = true) : cand.outcome = Ω0 := by
  simp only [appsΩ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- A virtual channel: no transfer and no reclaim writes its status. -/
def c0 : FixedPart :=
  { participants := [p0, q0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 6, kind := .virtual }

/-- The state of `c0` at turn `k`. -/
def stAt (k : Nat) : State Unit :=
  { channel := c0, turnNum := k, outcome := Ω0, isFinal := false, appData := .opaque 0 }

/-- A final state of `c0` with the outcome `Ω0`, at turn 1, a setup turn
    (`HonestSend.movesFrom` binds only the turns from `c0.n` on). -/
def stF : State Unit :=
  { channel := c0, turnNum := 1, outcome := Ω0, isFinal := true, appData := .opaque 0 }

def ssF : SignedState Unit := ⟨stF, [p0]⟩
def ssQ : SignedState Unit := ⟨stAt 1, [q0]⟩

/-- The conclusion proof the adversary submits. -/
def ssC : SignedState Unit := ⟨stF, [p0, q0]⟩

/-- One signature of each participant. -/
def P : SupportProof Unit := [ssF, ssQ]

theorem supports_P_stAt (k : Nat) : (appsΩ c0.appDef).supports c0 P (stAt k) = true := rfl

theorem supports_P_stF : (appsΩ c0.appDef).supports c0 P stF = true := rfl

/-- `appsΩ` fails `Rules.SupportWindow`: `P` holds signatures at turn 1,
    and it supports `stAt 7`. -/
theorem appsΩ_not_supportWindow : ¬ (appsΩ c0.appDef).SupportWindow := by
  intro h
  obtain ⟨ss, hss, -, -, -, hlt⟩ := h c0 P (stAt 7) (supports_P_stAt _) p0 (by simp [c0])
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl <;> simp [ssF, ssQ, stF, stAt, c0, FixedPart.n] at hlt

/-- The adversary: any call by another participant that forges no
    signature of `p0`, any unforged delivery, any tick. -/
def T0 : Threat Unit p0 where
  feasible net m := match m with
    | .chain caller op => caller ≠ p0 ∧ ∀ ss ∈ op.proofStates, net.Unforged ss
    | .deliver ss => net.Unforged ss
    | .tick _ => True
    | .land _ => True
  ε := 2
  ε_pos := Nat.two_pos

theorem A0 : Assumptions appsΩ p0 T0 where
  unforgeable := fun _ _ _ h => h.2
  unforgeableDeliver := fun _ _ h => h
  notHonest := fun _ _ _ h => h.1
  capable := fun _ _ _ h1 h2 => ⟨h1, h2⟩
  capableDeliver := fun _ _ h => h
  capableTick := fun _ _ => trivial
  clockRuns := le_refl 2

theorem p0_ne_q0 : p0 ≠ q0 := by decide

/-- `p0` received `q0`'s signature on `stAt 1`, then sent `stF`. -/
def net1 : NetworkState Unit p0 := ⟨Adjudicator.genesis, [ssQ], [ssF]⟩

theorem unforged_ssQ (n : NetworkState Unit p0) : n.Unforged ssQ :=
  ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0, fun v hv => by simp [ssQ, stAt, State.voucher?] at hv⟩

/-- A state with `stF` that `p0` signed is unforged where `p0` sent `stF`. -/
theorem unforged_stF {n : NetworkState Unit p0} (hs : ∃ s ∈ n.sent, s.state = stF)
    {ss : SignedState Unit} (hss : ss.state = stF) : n.Unforged ss := by
  refine ⟨fun _ => ?_, fun v hv => by simp [hss, stF, State.voucher?] at hv⟩
  obtain ⟨s, hs, hst⟩ := hs
  exact ⟨s, hs, hst.trans hss.symm⟩

/-- The send of `stF` after `p0` received `ssQ` satisfies `HonestSend`: one
    setup state, an empty allocation. -/
theorem send_feasible :
    (HonestMove.send stF).Feasible appsΩ (⟨Adjudicator.genesis, [ssQ], []⟩ : NetworkState Unit p0) :=
  (HonestMove.Feasible_send _ _ _).mpr
    ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide), fun h => absurd h (by decide), by decide, by decide⟩

theorem net1_reachable : (Nitro.participant appsΩ T0).Reachable net1 := by
  refine ⟨⟨Adjudicator.genesis, [], []⟩, rfl, ?_⟩
  refine .tail (.tail .refl ?_) (Or.inl ⟨.send stF, send_feasible, rfl⟩)
  exact Or.inr (Or.inr (Or.inl ⟨.deliver ssQ, unforged_ssQ _, fun op h => (by cases h), rfl⟩))

theorem statusOf_genesis : (Adjudicator.genesis (E := Unit)).statusOf c0 = .open 0 := rfl

theorem c0_not_ledger : c0.kind ≠ .ledger := by decide

/-- One successful operation, from a status of `c0` that is not finalized,
    keeps the status, opens it, or starts a fresh challenge. -/
theorem step_status {caller : Participant} {op : Op Unit} {s s' : Adjudicator Unit}
    (h : s.apply appsΩ caller op = some s')
    (hnc : ∀ ss, op = .conclude c0 ss → ¬ ConclusionProof c0 ss) :
    s'.statusOf c0 = s.statusOf c0 ∨ (∃ k, s'.statusOf c0 = .open k) ∨
      (∃ k st, s'.statusOf c0 = .challenged k ⟨st, s.now + c0.challengeDuration⟩) := by
  by_cases ht : Op.targets op c0
  · cases op with
    | deposit a e x => simp [Op.targets] at ht
    | tick dt => simp [Op.targets] at ht
    | transfer a b =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hk, -⟩ := Adjudicator.transfer_some h
      exact absurd hk c0_not_ledger
    | reclaim l v =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := Adjudicator.reclaim_some h
      exact absurd hk c0_not_ledger
    | challenge c' proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
      exact Or.inr (Or.inr ⟨cand.turnNum, cand, by simp⟩)
    | checkpoint c' proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
      exact Or.inr (Or.inl ⟨cand.turnNum, by simp⟩)
    | conclude c' ss =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hcp⟩, -⟩ := Adjudicator.conclude_some h
      exact absurd hcp (hnc ss rfl)
  · exact Or.inl (statusOf_apply_of_not_targets h ht)

/-- A conclusion proof of `c0` carries `q0`'s signature on a final state. -/
theorem no_conclude {ss : SignedState Unit} (hs : q0 ∈ ss.signers → ss.state.isFinal = false) :
    ¬ ConclusionProof c0 ss := by
  rintro ⟨hc, hfin, hall⟩
  rw [hs (hall q0 (by rw [hc]; simp [c0]))] at hfin
  cases hfin

/-! ## Part 1: `Ω0` is not finalizable for `p0`. -/

/-- Every state that `p0` received with `q0`'s signature is not final. -/
def QNF (n : NetworkState Unit p0) : Prop := ∀ r ∈ n.received, q0 ∈ r.signers → r.state.isFinal = false

/-- The status of `c0` has no final outcome now. -/
def NF (s : Adjudicator Unit) : Prop := (s.statusOf c0).finalOutcome s.now = none

/-- `omega` after unfolding the `Time` abbreviation. -/
macro "tomega" : tactic => `(tactic| ((try unfold Time at *); omega))

theorem isOpen_of_nf {s : Adjudicator Unit} (hnf : NF s) : (s.statusOf c0).IsOpen s.now := by
  unfold NF at hnf
  unfold ChannelStatus.IsOpen
  cases hst : s.statusOf c0 with
  | «open» t => simp
  | challenged t ch =>
    rw [hst] at hnf
    simp only [ChannelStatus.finalOutcome_challenged] at hnf
    split at hnf
    · cases hnf
    · rename_i hlt; simp [hlt]
  | finalized t f o => rw [hst] at hnf; simp at hnf

theorem holds_qnf {n : NetworkState Unit p0} (hq : QNF n) {ss : SignedState Unit}
    (hh : n.Holds ss) : q0 ∈ ss.signers → ss.state.isFinal = false := by
  intro hx
  rcases hh.1 q0 hx with ⟨h, -⟩ | ⟨r, hr, hrs, hxr⟩
  · exact absurd h.symm p0_ne_q0
  · rw [← hrs]; exact hq r hr hxr

/-- A call `p0` can issue in this game. -/
def Good (op : Op Unit) : Prop :=
  (∀ dt, op ≠ .tick dt) ∧ ∀ ss ∈ op.proofStates, q0 ∈ ss.signers → ss.state.isFinal = false

theorem good_of_feasible {n : NetworkState Unit p0} (hq : QNF n) {op : Op Unit}
    (h : op.HonestFeasible n) : Good op := by
  refine ⟨?_, ?_⟩
  · intro dt heq; subst heq; exact h
  · intro ss hss
    cases op with
    | deposit => exact absurd h id
    | tick => exact absurd h id
    | transfer => simp [Op.proofStates] at hss
    | reclaim => simp [Op.proofStates] at hss
    | challenge c proof cand => exact holds_qnf hq (h ss hss)
    | checkpoint c proof cand => exact holds_qnf hq (h ss hss)
    | conclude c ss' => exact holds_qnf hq (h ss hss)

theorem nf_of_step {caller : Participant} {op : Op Unit} {s s' : Adjudicator Unit}
    (h : s.apply appsΩ caller op = some s') (hop : ∀ dt, op ≠ .tick dt)
    (hnc : ∀ ss, op = .conclude c0 ss → ¬ ConclusionProof c0 ss) (hnf : NF s) : NF s' := by
  have hnow := Adjudicator.apply_now_eq_of_not_tick hop h
  unfold NF at hnf ⊢
  rw [hnow]
  rcases step_status h hnc with h1 | ⟨k, h1⟩ | ⟨k, st, h1⟩
  · rw [h1]; exact hnf
  · rw [h1]; rfl
  · rw [h1]; simp [c0]

/-- `p0`'s calls land one after the other, the clock does not move, `sent`
    does not change, and the status of `c0` stays not finalized. -/
theorem land_all (t : Time) : ∀ (pending : List (Op Unit)), (∀ op ∈ pending, Good op) →
    ∀ (n : NetworkState Unit p0), NF n.chain → QNF n →
      ∃ n', Threat.RoundSeq appsΩ T0 t pending n n' ∧ NF n'.chain ∧ QNF n' ∧
        n'.chain.now = n.chain.now ∧ n'.sent = n.sent := by
  intro pending
  induction pending with
  | nil => intro _ n hnf hq; exact ⟨n, .nil, hnf, hq, rfl, rfl⟩
  | cons op rest ih =>
    intro hgood n hnf hq
    obtain ⟨hop, hps⟩ := hgood op List.mem_cons_self
    have hrest : ∀ op' ∈ rest, Good op' := fun op' h => hgood op' (List.mem_cons_of_mem op h)
    have key : NF (n.applyAdv appsΩ (.land op)).chain ∧ QNF (n.applyAdv appsΩ (.land op)) ∧
        (n.applyAdv appsΩ (.land op)).chain.now = n.chain.now ∧
        (n.applyAdv appsΩ (.land op)).sent = n.sent := by
      simp only [NetworkState.applyAdv]
      cases happ : n.chain.apply appsΩ p0 op with
      | none => exact ⟨hnf, hq, rfl, rfl⟩
      | some s' =>
        refine ⟨nf_of_step happ hop ?_ hnf, ?_, Adjudicator.apply_now_eq_of_not_tick hop happ, rfl⟩
        · rintro ss rfl
          exact no_conclude (hps ss (by simp [Op.proofStates]))
        · intro r hr hx
          rcases List.mem_append.1 hr with hr | hr
          · exact hps r hr hx
          · exact hq r hr hx
    obtain ⟨hnf1, hq1, hnow1, hs1⟩ := key
    obtain ⟨n', hseq, hnf', hq', hnow', hs'⟩ := ih hrest _ hnf1 hq1
    exact ⟨n', .land (l1 := []) (l2 := rest) rfl hseq, hnf', hq', by rw [hnow', hnow1],
      by rw [hs', hs1]⟩

/-- A run of adversary moves with nothing pending can follow any round. -/
theorem roundSeq_append {t : Time} {pending : List (Op Unit)} {n n1 n2 : NetworkState Unit p0}
    (h1 : Threat.RoundSeq appsΩ T0 t pending n n1) (h2 : Threat.RoundSeq appsΩ T0 t [] n1 n2) :
    Threat.RoundSeq appsΩ T0 t pending n n2 := by
  induction h1 with
  | nil => exact h2
  | land hsplit _ ih => exact .land hsplit (ih h2)
  | tick hfeas hgate _ ih => exact .tick hfeas hgate (ih h2)
  | other hfeas hnotick hnoland _ ih => exact .other hfeas hnotick hnoland (ih h2)

theorem qnf_P : ∀ r ∈ P, q0 ∈ r.signers → r.state.isFinal = false := by
  intro r hr hx
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact absurd (List.mem_singleton.1 hx).symm p0_ne_q0
  · rfl

/-- The invariant of part 1: `c0` is open, `q0` signed no final state that
    `p0` received, and `p0` sent `stF`. -/
def Inv1 (n : NetworkState Unit p0) : Prop :=
  (∃ k, n.chain.statusOf c0 = .open k) ∧ QNF n ∧ ∃ s ∈ n.sent, s.state = stF

/-- The adversary's answer to any move of `p0`: land `p0`'s calls, then
    checkpoint `c0` with `P` at the next turn. -/
theorem round1 (n : NetworkState Unit p0) (hI : Inv1 n) (m : HonestMove Unit)
    (hfeas : m.Feasible appsΩ n) :
    ∃ n', T0.Round appsΩ m n n' ∧ Inv1 (n'.applyHonest m) := by
  obtain ⟨⟨k, hk⟩, hq, hsent⟩ := hI
  have hgood : ∀ op ∈ m.calls, Good op := by
    cases m with
    | react r => intro op hop; exact good_of_feasible hq (hfeas.1 op hop)
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  have hnf : NF n.chain := by unfold NF; rw [hk]; rfl
  obtain ⟨n1, hseq1, hnf1, hq1, hnow1, hs1⟩ := land_all n.chain.now m.calls hgood n hnf hq
  set op : Op Unit := .checkpoint c0 P (stAt ((n1.chain.statusOf c0).turnNumRecord + 1)) with hopdef
  have hopen : (n1.chain.statusOf c0).IsOpen n1.chain.now := isOpen_of_nf hnf1
  have happ : n1.chain.apply appsΩ q0 op =
      some (n1.chain.setStatus c0 (.open ((n1.chain.statusOf c0).turnNumRecord + 1))) := by
    simp only [hopdef, Adjudicator.apply_checkpoint, Adjudicator.checkpoint]
    rw [if_pos ⟨hopen, supports_P_stAt _, rfl, Nat.lt_succ_self _⟩]
    rfl
  set n2 := n1.applyAdv appsΩ (.chain q0 op) with hn2
  have hn2c : n2.chain = n1.chain.setStatus c0 (.open ((n1.chain.statusOf c0).turnNumRecord + 1)) := by
    simp only [hn2, NetworkState.applyAdv, happ]
  have hn2r : n2.received = P ++ n1.received := by
    simp only [hn2, NetworkState.applyAdv, happ]
    rfl
  have hn2s : n2.sent = n.sent := by
    rw [← hs1]; simp only [hn2, NetworkState.applyAdv, happ]
  have hfeasq : T0.feasible n1 (.chain q0 op) := by
    refine ⟨fun h => p0_ne_q0 h.symm, ?_⟩
    intro ss hss
    simp only [hopdef, Op.proofStates, P, List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact unforged_stF (by rw [hs1]; exact hsent) rfl
    · exact unforged_ssQ n1
  have hseq : Threat.RoundSeq appsΩ T0 n.chain.now m.calls n n2 :=
    roundSeq_append hseq1 (.other hfeasq (by intro dt h; cases h) (by intro o h; cases h) .nil)
  refine ⟨n2, ⟨hseq, ?_⟩, ?_⟩
  · rw [hn2c, Adjudicator.setStatus_now, hnow1]
    exact Nat.lt_add_of_pos_right T0.ε_pos
  · have hq2 : QNF n2 := by
      intro r hr hx
      rw [hn2r] at hr
      rcases List.mem_append.1 hr with hr | hr
      · exact qnf_P r hr hx
      · exact hq1 r hr hx
    obtain ⟨s, hs, hst⟩ := hsent
    cases m with
    | react r =>
      refine ⟨⟨(n1.chain.statusOf c0).turnNumRecord + 1, ?_⟩, hq2, s, ?_, hst⟩
      · simp only [NetworkState.applyHonest]; rw [hn2c]; simp
      · simp only [NetworkState.applyHonest]; rw [hn2s]; exact List.mem_append_right _ hs
    | wait dt =>
      refine ⟨⟨(n1.chain.statusOf c0).turnNumRecord + 1, ?_⟩, hq2, s, ?_, hst⟩
      · simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; rw [hn2c]; simp
      · simp only [NetworkState.applyHonest]; rw [hn2s]; exact hs

theorem not_unbeatable (Ω : Outcome Unit) (n : NetworkState Unit p0)
    (h : UnbeatableIn appsΩ T0 (fun _ => True) (fun n => n.Finalized c0 Ω) n) : Inv1 n → False := by
  induction h with
  | done hG =>
    rintro ⟨⟨k, hk⟩, -⟩
    simp [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hk] at hG
  | move m _ hfeas _ ih =>
    intro hI
    obtain ⟨n', hR, hI'⟩ := round1 _ hI m hfeas
    exact ih n' hR hI'

theorem qnf_net1 : QNF net1 := by
  intro r hr _
  simp only [net1, List.mem_singleton] at hr
  subst hr; rfl

theorem not_finalizable (Ω : Outcome Unit) : ¬ Finalizable appsΩ T0 c0 Ω net1 :=
  fun h => not_unbeatable Ω net1 h ⟨⟨0, statusOf_genesis⟩, qnf_net1, ssF, by simp [net1], rfl⟩

/-! ## Part 2: `Ω0` is enabled for `p0`. -/

theorem conclusionProof_ssC : ConclusionProof c0 ssC := by decide

/-- Whatever `p0` plays first, the adversary lands `p0`'s calls and then
    concludes `c0` with `ssC`, in the same round. -/
theorem enabled : Enabled appsΩ T0 c0 Ω0 net1 := by
  rintro ⟨σ, hσ, hprev⟩
  have hfeas := hσ net1
  have hgood : ∀ op ∈ (σ net1).calls, Good op := by
    cases hm : σ net1 with
    | react r =>
      rw [hm] at hfeas
      intro op hop; exact good_of_feasible qnf_net1 (hfeas.1 op hop)
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  have hnf : NF net1.chain := by unfold NF; rw [show net1.chain = Adjudicator.genesis from rfl, statusOf_genesis]; rfl
  obtain ⟨n1, hseq1, hnf1, -, hnow1, hs1⟩ :=
    land_all net1.chain.now (σ net1).calls hgood net1 hnf qnf_net1
  have happ : n1.chain.apply appsΩ q0 (.conclude c0 ssC) =
      some (n1.chain.setStatus c0 (.finalized ssC.state.turnNum ssC.state.outcome ssC.state.outcome)) := by
    simp only [Adjudicator.apply_conclude, Adjudicator.conclude]
    rw [if_pos ⟨isOpen_of_nf hnf1, conclusionProof_ssC⟩]
  set n2 := n1.applyAdv appsΩ (.chain q0 (.conclude c0 ssC)) with hn2
  have hn2c : n2.chain =
      n1.chain.setStatus c0 (.finalized ssC.state.turnNum ssC.state.outcome ssC.state.outcome) := by
    simp only [hn2, NetworkState.applyAdv, happ]
  have hfeasq : T0.feasible n1 (.chain q0 (.conclude c0 ssC)) := by
    refine ⟨fun h => p0_ne_q0 h.symm, ?_⟩
    intro ss hss
    simp only [Op.proofStates, List.mem_singleton] at hss
    subst hss
    exact unforged_stF ⟨ssF, by rw [hs1]; simp [net1], rfl⟩ rfl
  have hseq : Threat.RoundSeq appsΩ T0 net1.chain.now (σ net1).calls net1 n2 :=
    roundSeq_append hseq1 (.other hfeasq (by intro dt h; cases h) (by intro o h; cases h) .nil)
  refine hprev net1 n2 .refl ⟨hseq, ?_⟩ ?_
  · rw [hn2c, Adjudicator.setStatus_now, hnow1]
    exact Nat.lt_add_of_pos_right T0.ε_pos
  · simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hn2c,
      Adjudicator.statusOf_setStatus, if_true]
    rfl

/-! ## Part 3: `p0` prevents every other outcome. -/

/-- Every outcome the status of `c0` can finalize with is `Ω0`. -/
def Shape : ChannelStatus Unit → Prop
  | .open _ => True
  | .challenged _ ch => ch.state.outcome = Ω0
  | .finalized _ f _ => f = Ω0

/-- The invariant of part 3: `p0` sent only `stF`, and `c0` can finalize
    only with `Ω0`. -/
def Inv3 (n : NetworkState Unit p0) : Prop := n.sent = [ssF] ∧ Shape (n.chain.statusOf c0)

/-- An adversary chain call keeps `Inv3`: every supported candidate has the
    outcome `Ω0`, and a conclusion proof carries `p0`'s signature, so its
    state is `stF`. -/
theorem chain_keeps {n : NetworkState Unit p0} {caller : Participant} {op : Op Unit}
    (hfeas : T0.feasible n (.chain caller op)) (hI : Inv3 n) :
    Inv3 (n.applyAdv appsΩ (.chain caller op)) := by
  cases happ : n.chain.apply appsΩ caller op with
  | none => rw [NetworkState.applyAdv_chain_none appsΩ happ]; exact hI
  | some s' =>
    rw [NetworkState.applyAdv_chain_some appsΩ happ]
    refine ⟨hI.1, ?_⟩
    show Shape (s'.statusOf c0)
    by_cases ht : Op.targets op c0
    · cases op with
      | deposit a e x => simp [Op.targets] at ht
      | tick dt => simp [Op.targets] at ht
      | transfer a b =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hk, -⟩ := Adjudicator.transfer_some happ
        exact absurd hk c0_not_ledger
      | reclaim l v =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := Adjudicator.reclaim_some happ
        exact absurd hk c0_not_ledger
      | challenge c' proof cand =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨⟨-, hsupp, -⟩, rfl⟩ := Adjudicator.challenge_some happ
        simp only [Adjudicator.statusOf_setStatus, if_true, Shape]
        exact appsΩ_outcome hsupp
      | checkpoint c' proof cand =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some happ
        simp only [Adjudicator.statusOf_setStatus, if_true, Shape]
      | conclude c' ss =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨⟨-, hc, -, hall⟩, rfl⟩ := Adjudicator.conclude_some happ
        have hp : p0 ∈ ss.signers := hall p0 (by rw [hc]; simp [c0])
        obtain ⟨s, hs, hst⟩ := (hfeas.2 ss (by simp [Op.proofStates])).1 hp
        rw [hI.1, List.mem_singleton] at hs
        subst hs
        simp only [Adjudicator.statusOf_setStatus, if_true, Shape]
        rw [← hst]
        rfl
    · rw [statusOf_apply_of_not_targets happ ht]
      exact hI.2

/-- `Inv3`'s step obligations, for any guard. -/
theorem inv3_step (Guard : NetworkState Unit p0 → Prop) :
    T0.StepInvariant appsΩ Guard Inv3 (fun _ _ => False) where
  land _ hc _ := hc.elim
  deliver _ _ hI := hI
  tick _ _ hI := hI
  chain _ hfeas hI := chain_keeps hfeas hI

/-- `p0` waits, every round. -/
def σw : Strategy Unit p0 := fun _ => .wait 0

theorem round3 {n1 n2 : NetworkState Unit p0} (hI : Inv3 n1) (hR : T0.Round appsΩ (σw n1) n1 n2) :
    Inv3 n2 :=
  Threat.RoundSeq.nil_invariant hR.1 (inv3_step _) hI

theorem run_inv3 {n : NetworkState Unit p0} (h : Run appsΩ T0 σw net1 n) : Inv3 n := by
  induction h with
  | refl => exact ⟨rfl, trivial⟩
  | round _ hR ih => exact round3 ih hR

theorem prevents_other (Ω : Outcome Unit) (hne : Ω ≠ Ω0) :
    Prevents appsΩ T0 (fun n => n.Finalized c0 Ω) net1 := by
  refine ⟨σw, fun _ => trivial, ?_⟩
  intro n1 n2 hrun hR hfin
  have hI := round3 (run_inv3 hrun) hR
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hfin
  have hsh := hI.2
  cases hst : n2.chain.statusOf c0 with
  | «open» k => rw [hst] at hfin; cases hfin
  | challenged k ch =>
    rw [hst] at hfin hsh
    simp only [ChannelStatus.finalizedWith_challenged] at hfin
    split at hfin
    · cases hfin; exact hne hsh
    · cases hfin
  | finalized k f o =>
    rw [hst] at hfin hsh
    cases hfin; exact hne hsh

/-! ## The counterexample. -/

/-- `p0` holds every state of `P`. -/
theorem holds_P : ∀ ss ∈ P, net1.Holds ss := by
  intro ss hss
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · refine ⟨fun x hx => Or.inl ⟨List.mem_singleton.1 hx, ssF, by simp [net1], rfl⟩, ?_⟩
    intro v hv; simp [ssF, stF, State.voucher?] at hv
  · refine ⟨fun x hx => Or.inr ⟨ssQ, by simp [net1], rfl, hx⟩, ?_⟩
    intro v hv; simp [ssQ, stAt, State.voucher?] at hv

/-- `p0` holds `P`, which supports `stF`, the one state `p0` sent. -/
theorem hsupp_net1 : ∀ t ∈ net1.sent, t.state.channel = c0 →
    ∃ proof, (∀ ss ∈ proof, net1.Holds ss) ∧ (appsΩ c0.appDef).supports c0 proof t.state = true := by
  intro t ht _
  simp only [net1, List.mem_singleton] at ht
  subst ht
  exact ⟨P, holds_P, supports_P_stF⟩

/-- `Spec.single_enabled_is_finalizable` with the app premise
    deleted from the library on 2026-11-01 (`OldPremise`) in place of
    `Rules.SupportWindow`. -/
def Old_single_enabled_is_finalizable : Prop :=
  ∀ (apps : Apps Unit) {p : Participant} (T : Threat Unit p)
    (_A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε)
    (_happ : OldPremise (apps (c : FixedPart).appDef))
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) →
      ∃ proof, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof t.state = true)
    (Ω : Outcome Unit) (_hΩ : Enabled apps T (c : FixedPart) Ω net.state)
    (_huniq : ∀ Ω', Enabled apps T (c : FixedPart) Ω' net.state → Ω' = Ω),
    Finalizable apps T (c : FixedPart) Ω net.state

/-- `Spec.finalizable_or_two_enabled` with the app premise of the design
    decision of 2026-10-30 (`OldPremise`) in place of `Rules.SupportWindow`. -/
def Old_finalizable_or_two_enabled : Prop :=
  ∀ (apps : Apps Unit) {p : Participant} (T : Threat Unit p)
    (_A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε)
    (_happ : OldPremise (apps (c : FixedPart).appDef))
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof candidate = true ∧
      candidate.channel = (c : FixedPart)),
    (∃ Ω, Finalizable apps T (c : FixedPart) Ω net.state) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T (c : FixedPart) Ω1 net.state ∧
      Enabled apps T (c : FixedPart) Ω2 net.state)

/-- Every hypothesis of `Old_single_enabled_is_finalizable`, `happ` and
    `hsupp` included, holds for `appsΩ`, `p0`, `T0`, `net1`, `c0` and `Ω0`:
    `Ω0` is the one enabled outcome. Its conclusion fails: `Ω0` is not
    finalizable. -/
theorem single_enabled_is_finalizable_false :
    ¬ Old_single_enabled_is_finalizable := by
  intro h
  refine not_finalizable Ω0 (h appsΩ T0 A0 ⟨net1, net1_reachable⟩ ⟨c0, by decide⟩
    (appsΩ_oldPremise _) (by simp [c0]) hsupp_net1 Ω0 enabled ?_)
  intro Ω' hE
  by_contra hne
  exact hE (prevents_other Ω' hne)

/-- The same instance refutes `Old_finalizable_or_two_enabled`: `net1` has
    no finalizable outcome and one enabled outcome. -/
theorem finalizable_or_two_enabled_false :
    ¬ Old_finalizable_or_two_enabled := by
  intro h
  rcases h appsΩ T0 A0 ⟨net1, net1_reachable⟩ ⟨c0, by decide⟩ (appsΩ_oldPremise _)
      (by simp [c0]) ⟨P, stF, holds_P, supports_P_stF, rfl⟩ with
    ⟨Ω, hΩ⟩ | ⟨Ω1, Ω2, hne, hE1, hE2⟩
  · exact not_finalizable Ω hΩ
  · by_cases h1 : Ω1 = Ω0
    · exact hE2 (prevents_other Ω2 (fun h2 => hne (h1.trans h2.symm)))
    · exact hE1 (prevents_other Ω1 h1)

#print axioms single_enabled_is_finalizable_false
#print axioms finalizable_or_two_enabled_false
#print axioms appsΩ_not_supportWindow

/-! ## `appsΩ` is not desirable

Design decision 2026-11-01: the Nitro-24 claims take `Desirable`. `appsΩ`
fails `AppIR`: at `net1`, `p0` holds `P`, a support of `stAt 2`, with the
channel open, and no outcome ever finalizes (`not_unbeatable_any`). -/

theorem not_unbeatable_any {G : Outcome Unit → Prop} (n : NetworkState Unit p0)
    (h : UnbeatableIn appsΩ T0 (fun _ => True) (fun n => ∃ Ω, n.Finalized c0 Ω ∧ G Ω) n) :
    Inv1 n → False := by
  induction h with
  | done hG =>
    rintro ⟨⟨k, hk⟩, -⟩
    obtain ⟨Ω, hf, -⟩ := hG
    simp [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hk] at hf
  | move m _ hfeas _ ih =>
    intro hI
    obtain ⟨n', hR, hI'⟩ := round1 _ hI m hfeas
    exact ih n' hR hI'

theorem appsΩ_not_desirable (dest : Participant → Unit) : ¬ Desirable appsΩ ⟨0⟩ dest := by
  intro h
  have hH : HoldsShare appsΩ net1 c0 (dest p0) 0 :=
    ⟨P, stAt 2, holds_P, supports_P_stAt 2, rfl, Nat.zero_le _, fun s hs _ => by
      simp only [net1, List.mem_singleton] at hs; subst hs
      exact ⟨by decide, fun _ => Nat.zero_le _⟩, 0, statusOf_genesis, Nat.zero_le _⟩
  exact not_unbeatable_any net1
    (h.ir.takeOut T0 A0 ⟨net1, net1_reachable⟩ ⟨c0, by decide⟩ 0 rfl (by simp [c0]) hH)
    ⟨⟨0, statusOf_genesis⟩, qnf_net1, ssF, by simp [net1], rfl⟩

#print axioms appsΩ_not_desirable

end ArmadaLean.Nitro.CounterexampleSingleEnabled
