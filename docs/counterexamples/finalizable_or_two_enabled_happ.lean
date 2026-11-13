/-
  Failure test for `Spec.finalizable_or_two_enabled` (Liveness.lean,
  Nitro-24, Nitro:653-658). The first version predates the trunk types
  (`dbcafcc`); it was ported to the trunk types

  The app `appsU` supports a candidate when every participant signed some
  state of the proof. The proof does not bound the candidate's turn number.
  So one signature of each participant supports every turn number.

  `appsU` is a compliant app: the adjudicator accepts it. It is not a
  ForceMove app, and it must fail Nitro-24. Design decision 2026-11-01: an
  app that lets old signatures support a higher turn must explicitly fail
  `finalizable_or_two_enabled`. This file proves both halves:
  * `appsU_not_supportWindow`: `appsU` fails `Rules.SupportWindow`, the
    premise `happ` of the statement (ForceMove:744-778, 1340-1354,
    1379-1381). Two turn-0 signatures support a candidate at turn 5.
  * `finalizable_or_two_enabled_happ_false`: the statement with the premise
    of the premise deleted from the library on 2026-11-01 (`OldPremise`, every participant
    signed some state of the proof) is false. `appsU` carries `OldPremise`
    (`appsU_oldPremise`).

  `p0` sent `stAt 0` and received `stAt 0` signed by `q0`. The send satisfies
  every rule of `HonestSend` (`send_feasible`), so `net1` is reachable on the
  honest machine (`net1_reachable`). Each side then holds the proof `P` and
  can reset a running challenge without the other: a checkpoint at the next
  turn number. So:
  * `p0` cannot force any outcome: after each of `p0`'s reactions the
    adversary checkpoints `c0` with `P`, and an open channel never
    finalizes (`not_finalizable`).
  * `p0` prevents every outcome: `p0` checkpoints `c0` with `P` every round,
    so a challenge never reaches its deadline (`prevents`).
  At `net1`, `p0` has no finalizable outcome and no enabled outcome.
  An internal design note on app classes §5 lists `appsU`.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/finalizable_or_two_enabled_happ.lean`.
  Both theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Spec.Nitro.Liveness

namespace ArmadaLean.Nitro.CounterexampleHapp

open ArmadaLean.Nitro

def p0 : Participant := ⟨0⟩
def q0 : Participant := ⟨1⟩

/-- Rules that support every candidate when each participant signed some
    state of the proof. -/
def appsU : Apps Unit := fun _ =>
  ⟨fun c proof _ => c.participants.all (fun q => proof.any (fun ss => decide (q ∈ ss.signers)))⟩

/-- The app premise deleted from the
    library on 2026-11-01: every participant signed some state of the proof.
    It does not bound the turn that a signature supports. -/
def OldPremise (r : Rules Unit) : Prop :=
  ∀ c proof candidate, r.supports c proof candidate = true →
    ∀ q ∈ c.participants, ∃ ss ∈ proof, q ∈ ss.signers

theorem appsU_oldPremise (a : AppId) : OldPremise (appsU a) := by
  intro c proof cand h q hq
  simp only [appsU, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact h q hq

def c0 : FixedPart :=
  { participants := [p0, q0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 6, kind := .ledger }

def Ω0 : Outcome Unit := .allocation []

/-- The state of `c0` at turn `k`. -/
def stAt (k : Nat) : State Unit :=
  { channel := c0, turnNum := k, outcome := Ω0, isFinal := false, appData := .opaque 0 }

def ssP : SignedState Unit := ⟨stAt 0, [p0]⟩
def ssQ : SignedState Unit := ⟨stAt 0, [q0]⟩

/-- One signature of each participant. -/
def P : SupportProof Unit := [ssP, ssQ]

theorem supports_P (cand : State Unit) : (appsU c0.appDef).supports c0 P cand = true := rfl

/-- `appsU` fails `Rules.SupportWindow`: `P` holds two signatures at turn 0,
    and it supports `stAt 5`, five turns above them. -/
theorem appsU_not_supportWindow : ¬ (appsU c0.appDef).SupportWindow := by
  intro h
  obtain ⟨ss, hss, -, -, -, hlt⟩ := h c0 P (stAt 5) (supports_P _) p0 (by simp [c0])
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl <;> simp [ssP, ssQ, stAt, c0, FixedPart.n] at hlt

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

theorem A0 : Assumptions appsU p0 T0 where
  unforgeable := fun _ _ _ h => h.2
  unforgeableDeliver := fun _ _ h => h
  notHonest := fun _ _ _ h => h.1
  capable := fun _ _ _ h1 h2 => ⟨h1, h2⟩
  capableDeliver := fun _ _ h => h
  capableTick := fun _ _ => trivial
  clockRuns := le_refl 2

theorem p0_ne_q0 : p0 ≠ q0 := by decide

/-- `p0` sent `stAt 0` and received `q0`'s signature on it. -/
def net1 : NetworkState Unit p0 := ⟨Adjudicator.genesis, [ssQ], [ssP]⟩

theorem unforged_ssQ (n : NetworkState Unit p0) : n.Unforged ssQ :=
  ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0, fun v hv => by simp [ssQ, stAt, State.voucher?] at hv⟩

/-- The send of `stAt 0` from the empty state satisfies `HonestSend`: one
    state, an empty allocation. -/
theorem send_feasible :
    (HonestMove.send (stAt 0)).Feasible appsU (⟨Adjudicator.genesis, [], []⟩ : NetworkState Unit p0) :=
  (HonestMove.Feasible_send _ _ _).mpr
    ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide), fun h => absurd h (by decide), by decide, by decide⟩

theorem net1_reachable : (Nitro.participant appsU T0).Reachable net1 := by
  refine ⟨⟨Adjudicator.genesis, [], []⟩, rfl, ?_⟩
  refine .tail (.tail .refl (Or.inl ⟨.send (stAt 0), send_feasible, rfl⟩)) ?_
  exact Or.inr (Or.inr (Or.inl ⟨.deliver ssQ, unforged_ssQ _, fun op h => (by cases h), rfl⟩))

theorem statusOf_genesis : (Adjudicator.genesis (E := Unit)).statusOf c0 = .open 0 := rfl

/-- One successful operation, from a status of `c0` that is not finalized,
    keeps the status, opens it, or starts a fresh challenge. -/
theorem step_status {caller : Participant} {op : Op Unit} {s s' : Adjudicator Unit}
    (h : s.apply appsU caller op = some s')
    (hnc : ∀ ss, op = .conclude c0 ss → ¬ ConclusionProof c0 ss)
    (hnf : (s.statusOf c0).finalOutcome s.now = none) :
    s'.statusOf c0 = s.statusOf c0 ∨ (∃ k, s'.statusOf c0 = .open k) ∨
      (∃ k st, s'.statusOf c0 = .challenged k ⟨st, s.now + c0.challengeDuration⟩) := by
  by_cases ht : Op.targets op c0
  · cases op with
    | deposit a e x => simp [Op.targets] at ht
    | tick dt => simp [Op.targets] at ht
    | transfer a b =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨o, -, -, hf, -⟩ := Adjudicator.transfer_some h
      simp [Adjudicator.finalOutcome_channel, FixedPart.address_eq, hnf] at hf
    | reclaim l v =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨oL, -, -, -, -, hL, -⟩ := Adjudicator.reclaim_some h
      simp [Adjudicator.finalOutcome_channel, FixedPart.address_eq, hnf] at hL
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

/-! ## Part 1: no outcome is finalizable for `p0`. -/

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
    (h : s.apply appsU caller op = some s') (hop : ∀ dt, op ≠ .tick dt)
    (hnc : ∀ ss, op = .conclude c0 ss → ¬ ConclusionProof c0 ss) (hnf : NF s) : NF s' := by
  have hnow := Adjudicator.apply_now_eq_of_not_tick hop h
  unfold NF at hnf ⊢
  rw [hnow]
  rcases step_status h hnc hnf with h1 | ⟨k, h1⟩ | ⟨k, st, h1⟩
  · rw [h1]; exact hnf
  · rw [h1]; rfl
  · rw [h1]; simp [c0]

/-- `p0`'s calls land one after the other, the clock does not move, `sent`
    does not change, and the status of `c0` stays not finalized. -/
theorem land_all (t : Time) : ∀ (pending : List (Op Unit)), (∀ op ∈ pending, Good op) →
    ∀ (n : NetworkState Unit p0), NF n.chain → QNF n →
      ∃ n', Threat.RoundSeq appsU T0 t pending n n' ∧ NF n'.chain ∧ QNF n' ∧
        n'.chain.now = n.chain.now ∧ n'.sent = n.sent := by
  intro pending
  induction pending with
  | nil => intro _ n hnf hq; exact ⟨n, .nil, hnf, hq, rfl, rfl⟩
  | cons op rest ih =>
    intro hgood n hnf hq
    obtain ⟨hop, hps⟩ := hgood op List.mem_cons_self
    have hrest : ∀ op' ∈ rest, Good op' := fun op' h => hgood op' (List.mem_cons_of_mem op h)
    have key : NF (n.applyAdv appsU (.land op)).chain ∧ QNF (n.applyAdv appsU (.land op)) ∧
        (n.applyAdv appsU (.land op)).chain.now = n.chain.now ∧
        (n.applyAdv appsU (.land op)).sent = n.sent := by
      simp only [NetworkState.applyAdv]
      cases happ : n.chain.apply appsU p0 op with
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
    (h1 : Threat.RoundSeq appsU T0 t pending n n1) (h2 : Threat.RoundSeq appsU T0 t [] n1 n2) :
    Threat.RoundSeq appsU T0 t pending n n2 := by
  induction h1 with
  | nil => exact h2
  | land hsplit _ ih => exact .land hsplit (ih h2)
  | tick hfeas hgate _ ih => exact .tick hfeas hgate (ih h2)
  | other hfeas hnotick hnoland _ ih => exact .other hfeas hnotick hnoland (ih h2)

/-- The invariant of part 1: `c0` is open, `q0` signed no final state that
    `p0` received, and `p0` sent `stAt 0`. -/
def Inv1 (n : NetworkState Unit p0) : Prop :=
  (∃ k, n.chain.statusOf c0 = .open k) ∧ QNF n ∧ ∃ s ∈ n.sent, s.state = stAt 0

/-- The adversary's answer to any move of `p0`: land `p0`'s calls, then
    checkpoint `c0` with `P` at the next turn. -/
theorem round1 (n : NetworkState Unit p0) (hI : Inv1 n) (m : HonestMove Unit)
    (hfeas : m.Feasible appsU n) :
    ∃ n', T0.Round appsU m n n' ∧ Inv1 (n'.applyHonest m) := by
  obtain ⟨⟨k, hk⟩, hq, hsent⟩ := hI
  have hgood : ∀ op ∈ m.calls, Good op := by
    cases m with
    | react r => intro op hop; exact good_of_feasible hq (hfeas.1 op hop)
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  have hnf : NF n.chain := by unfold NF; rw [hk]; rfl
  obtain ⟨n1, hseq1, hnf1, hq1, hnow1, hs1⟩ := land_all n.chain.now m.calls hgood n hnf hq
  set op : Op Unit := .checkpoint c0 P (stAt ((n1.chain.statusOf c0).turnNumRecord + 1)) with hopdef
  have hopen : (n1.chain.statusOf c0).IsOpen n1.chain.now := isOpen_of_nf hnf1
  have happ : n1.chain.apply appsU q0 op =
      some (n1.chain.setStatus c0 (.open ((n1.chain.statusOf c0).turnNumRecord + 1))) := by
    simp only [hopdef, Adjudicator.apply_checkpoint, Adjudicator.checkpoint]
    rw [if_pos ⟨hopen, supports_P _, rfl, Nat.lt_succ_self _⟩]
    rfl
  set n2 := n1.applyAdv appsU (.chain q0 op) with hn2
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
    · refine ⟨fun _ => by rw [hs1]; exact hsent, fun v hv => by simp [ssP, stAt, State.voucher?] at hv⟩
    · exact unforged_ssQ n1
  have hseq : Threat.RoundSeq appsU T0 n.chain.now m.calls n n2 :=
    roundSeq_append hseq1 (.other hfeasq (by intro dt h; cases h) (by intro o h; cases h) .nil)
  refine ⟨n2, ⟨hseq, ?_⟩, ?_⟩
  · rw [hn2c, Adjudicator.setStatus_now, hnow1]
    exact Nat.lt_add_of_pos_right T0.ε_pos
  · have hq2 : QNF n2 := by
      intro r hr hx
      rw [hn2r] at hr
      rcases List.mem_append.1 hr with hr | hr
      · simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> rfl
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
    (h : UnbeatableIn appsU T0 (fun _ => True) (fun n => n.Finalized c0 Ω) n) : Inv1 n → False := by
  induction h with
  | done hG =>
    rintro ⟨⟨k, hk⟩, -⟩
    simp [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hk] at hG
  | move m _ hfeas _ ih =>
    intro hI
    obtain ⟨n', hR, hI'⟩ := round1 _ hI m hfeas
    exact ih n' hR hI'

theorem not_finalizable (Ω : Outcome Unit) : ¬ Finalizable appsU T0 c0 Ω net1 := by
  refine fun h => not_unbeatable Ω net1 h ⟨⟨0, statusOf_genesis⟩, ?_, ssP, by simp [net1], rfl⟩
  intro r hr _
  simp only [net1, List.mem_singleton] at hr
  subst hr; rfl

/-! ## Part 2: `p0` prevents every outcome. -/

/-- `p0` sent `stAt 0`, received `q0`'s signature on it, and sent no final
    state. -/
def Q (n : NetworkState Unit p0) : Prop :=
  (∃ s ∈ n.sent, s.state = stAt 0) ∧ (∃ r ∈ n.received, r.state = stAt 0 ∧ q0 ∈ r.signers) ∧
    ∀ s ∈ n.sent, s.state.isFinal = false

theorem holdsP_of_Q {n : NetworkState Unit p0} (h : Q n) : ∀ ss ∈ P, n.Holds ss := by
  obtain ⟨⟨s, hs, hst⟩, ⟨r, hr, hrs, hq⟩, -⟩ := h
  intro ss hss
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · refine ⟨fun x hx => Or.inl ⟨List.mem_singleton.1 hx, s, hs, hst⟩, ?_⟩
    intro v hv; simp [ssP, stAt, State.voucher?] at hv
  · refine ⟨fun x hx => Or.inr ⟨r, hr, hrs, by rw [List.mem_singleton.1 hx]; exact hq⟩, ?_⟩
    intro v hv; simp [ssQ, stAt, State.voucher?] at hv

/-- Every adversary move keeps `Q`: `sent` does not change and `received`
    only grows. -/
theorem applyAdv_Q {n : NetworkState Unit p0} (m : AdvMove Unit) (h : Q n) :
    Q (n.applyAdv appsU m) := by
  obtain ⟨h1, ⟨r, hr, h2⟩, h3⟩ := h
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases n.chain.apply appsU caller op with
    | none => exact ⟨h1, ⟨r, hr, h2⟩, h3⟩
    | some s' => exact ⟨h1, ⟨r, List.mem_append_right _ hr, h2⟩, h3⟩
  | deliver ss => exact ⟨h1, ⟨r, List.mem_cons_of_mem _ hr, h2⟩, h3⟩
  | tick dt => exact ⟨h1, ⟨r, hr, h2⟩, h3⟩
  | land op =>
    simp only [NetworkState.applyAdv]
    cases n.chain.apply appsU p0 op with
    | none => exact ⟨h1, ⟨r, hr, h2⟩, h3⟩
    | some s' => exact ⟨h1, ⟨r, List.mem_append_right _ hr, h2⟩, h3⟩

/-- `p0`'s checkpoint of `c0` with `P` at the next turn. -/
def opAt (n : NetworkState Unit p0) : Op Unit :=
  .checkpoint c0 P (stAt ((n.chain.statusOf c0).turnNumRecord + 1))

open Classical in
/-- `p0` checkpoints `c0` with `P` at the next turn, every round in which it
    holds `P`. -/
noncomputable def σ1 : Strategy Unit p0 := fun n => if Q n then .chain (opAt n) else .wait 0

theorem σ1_eq {n : NetworkState Unit p0} (h : Q n) : σ1 n = .chain (opAt n) := if_pos h

theorem σ1_feasible (n : NetworkState Unit p0) : (σ1 n).Feasible appsU n := by
  by_cases h : Q n
  · rw [σ1_eq h, HonestMove.Feasible_chain]
    exact holdsP_of_Q h
  · simp only [σ1, if_neg h]; trivial

theorem applyAdv_now_le (n : NetworkState Unit p0) (m : AdvMove Unit) :
    n.chain.now ≤ (n.applyAdv appsU m).chain.now := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases h : n.chain.apply appsU caller op with
    | none => exact le_rfl
    | some s' => exact Adjudicator.apply_now_le h
  | deliver ss => exact le_rfl
  | tick dt => simp [NetworkState.applyAdv]
  | land op =>
    simp only [NetworkState.applyAdv]
    cases h : n.chain.apply appsU p0 op with
    | none => exact le_rfl
    | some s' => exact Adjudicator.apply_now_le h

theorem roundSeq_now_le {t : Time} {pending : List (Op Unit)} {n n' : NetworkState Unit p0}
    (h : Threat.RoundSeq appsU T0 t pending n n') : n.chain.now ≤ n'.chain.now := by
  induction h with
  | nil => exact le_rfl
  | land _ _ ih => exact le_trans (applyAdv_now_le _ _) ih
  | tick _ _ _ ih => exact le_trans (applyAdv_now_le _ _) ih
  | other _ _ _ _ ih => exact le_trans (applyAdv_now_le _ _) ih

/-- After `p0`'s call landed: `c0` is open, or its challenge started this
    round (deadline at least `t + 6`). -/
def Post (t : Time) (n : NetworkState Unit p0) : Prop :=
  Q n ∧ t ≤ n.chain.now ∧
    ((∃ k, n.chain.statusOf c0 = .open k) ∨
     (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ t + 6 ≤ ch.deadline))

/-- Before `p0`'s call landed: also the challenge from the round's start,
    at a turn at most `r0`, with deadline at least `t + 2`. -/
def Pre (t r0 : Time) (n : NetworkState Unit p0) : Prop :=
  Q n ∧ t ≤ n.chain.now ∧
    ((∃ k, n.chain.statusOf c0 = .open k) ∨
     (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ t + 6 ≤ ch.deadline) ∨
     (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ k ≤ r0 ∧ t + 2 ≤ ch.deadline))

theorem pre_of_post {t r0 : Time} {n : NetworkState Unit p0} (h : Post t n) : Pre t r0 n :=
  ⟨h.1, h.2.1, h.2.2.elim Or.inl (fun h => Or.inr (Or.inl h))⟩

/-- A status of the three `Pre` shapes has no final outcome before `t + 2`. -/
theorem nf_pre {t r0 : Time} {n : NetworkState Unit p0} (h : Pre t r0 n) (hlt : n.chain.now < t + 2) :
    NF n.chain := by
  obtain ⟨-, -, h | ⟨k, ch, hs, hd⟩ | ⟨k, ch, hs, -, hd⟩⟩ := h
  · obtain ⟨k, hs⟩ := h; unfold NF; rw [hs]; rfl
  · unfold NF; rw [hs]; simp only [ChannelStatus.finalOutcome_challenged]
    rw [if_neg (show ¬ ch.deadline ≤ n.chain.now by tomega)]
  · unfold NF; rw [hs]; simp only [ChannelStatus.finalOutcome_challenged]
    rw [if_neg (show ¬ ch.deadline ≤ n.chain.now by tomega)]

/-- An adversary chain call keeps `Pre` (or `Post`): `p0` signed no final
    state, so the adversary cannot conclude `c0`. -/
theorem adv_chain_keeps {t : Time} {n : NetworkState Unit p0} {caller : Participant} {op : Op Unit}
    {s' : Adjudicator Unit} (hfeas : T0.feasible n (.chain caller op))
    (hQ : Q n) (htn : t ≤ n.chain.now) (hnf : NF n.chain)
    (happ : n.chain.apply appsU caller op = some s') :
    s'.statusOf c0 = n.chain.statusOf c0 ∨ (∃ k, s'.statusOf c0 = .open k) ∨
      (∃ k ch, s'.statusOf c0 = .challenged k ch ∧ t + 6 ≤ ch.deadline) := by
  have hnc : ∀ ss, op = .conclude c0 ss → ¬ ConclusionProof c0 ss := by
    rintro ss rfl ⟨hc, hfin, hall⟩
    have hp : p0 ∈ ss.signers := hall p0 (by rw [hc]; simp [c0])
    obtain ⟨s, hs, hst⟩ := (hfeas.2 ss (by simp [Op.proofStates])).1 hp
    have := hQ.2.2 s hs
    rw [hst, hfin] at this
    cases this
  rcases step_status happ hnc hnf with h | h | ⟨k, st, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨k, _, h, by simp [c0]; tomega⟩)

/-- The round invariant. `p0`'s call is its checkpoint at turn `r0 + 1`. -/
theorem round_inv (t r0 : Time) :
    ∀ {pending : List (Op Unit)} {n n' : NetworkState Unit p0},
      Threat.RoundSeq appsU T0 t pending n n' →
      ((pending = [.checkpoint c0 P (stAt (r0 + 1))] ∧ Pre t r0 n) ∨ (pending = [] ∧ Post t n)) →
      n'.chain.now < t + 2 → Post t n' := by
  intro pending n n' h
  induction h with
  | nil =>
    rintro (⟨h, -⟩ | ⟨-, hP⟩) _
    · cases h
    · exact hP
  | @land pending n n' op l1 l2 hsplit hrest ih =>
    rintro (⟨hpend, hP⟩ | ⟨hpend, -⟩) hlt
    · rw [hpend] at hsplit
      have hl : l1 = [] ∧ op = .checkpoint c0 P (stAt (r0 + 1)) ∧ l2 = [] := by
        rcases l1 with _ | ⟨a, l1⟩
        · simp only [List.nil_append, List.cons.injEq] at hsplit
          exact ⟨rfl, hsplit.1.symm, hsplit.2.symm⟩
        · simp at hsplit
      obtain ⟨rfl, rfl, rfl⟩ := hl
      apply ih _ hlt
      right
      refine ⟨rfl, ?_⟩
      have hle1 := applyAdv_now_le n (.land (.checkpoint c0 P (stAt (r0 + 1))))
      have hle2 := roundSeq_now_le hrest
      obtain ⟨hQ, htn, hst⟩ := hP
      have hnf := nf_pre ⟨hQ, htn, hst⟩ (by tomega)
      have hopen : (n.chain.statusOf c0).IsOpen n.chain.now := isOpen_of_nf hnf
      have hQ' := applyAdv_Q (.land (.checkpoint c0 P (stAt (r0 + 1)))) hQ
      have hcases : n.chain.apply appsU p0 (.checkpoint c0 P (stAt (r0 + 1))) = none ∨
          n.chain.apply appsU p0 (.checkpoint c0 P (stAt (r0 + 1))) =
            some (n.chain.setStatus c0 (.open (r0 + 1))) := by
        simp only [Adjudicator.apply_checkpoint, Adjudicator.checkpoint]
        split
        · right; rfl
        · left; rfl
      rcases hcases with happ | happ
      · have hn : n.applyAdv appsU (.land (.checkpoint c0 P (stAt (r0 + 1)))) = n := by
          simp only [NetworkState.applyAdv, happ]
        rw [hn]
        refine ⟨hQ, htn, ?_⟩
        rcases hst with h | h | ⟨k, ch, hs, hk, -⟩
        · exact Or.inl h
        · exact Or.inr h
        · exfalso
          simp only [Adjudicator.apply_checkpoint, Adjudicator.checkpoint] at happ
          rw [if_pos ⟨hopen, supports_P _, rfl, by rw [hs]; simp [stAt]; tomega⟩] at happ
          cases happ
      · simp only [NetworkState.applyAdv, happ] at hQ' ⊢
        exact ⟨hQ', by simp; exact htn, Or.inl ⟨r0 + 1, by simp⟩⟩
    · rw [hpend] at hsplit; simp at hsplit
  | @tick pending n n' dt hfeas hgate hrest ih =>
    intro hP hlt
    apply ih _ hlt
    have keep : ∀ {r0' : Time}, (Pre t r0' n → Pre t r0' (n.applyAdv appsU (.tick dt))) ∧
        (Post t n → Post t (n.applyAdv appsU (.tick dt))) := by
      intro r0'
      constructor
      · rintro ⟨hs, htn, hst⟩
        exact ⟨applyAdv_Q _ hs, by simp [NetworkState.applyAdv]; tomega,
          by simpa [NetworkState.applyAdv] using hst⟩
      · rintro ⟨hs, htn, hst⟩
        exact ⟨applyAdv_Q _ hs, by simp [NetworkState.applyAdv]; tomega,
          by simpa [NetworkState.applyAdv] using hst⟩
    rcases hP with ⟨hp, hP⟩ | ⟨hp, hP⟩
    · exact Or.inl ⟨hp, keep.1 hP⟩
    · exact Or.inr ⟨hp, (keep (r0' := r0)).2 hP⟩
  | @other pending n n' m hfeas hnotick hnoland hrest ih =>
    intro hP hlt
    apply ih _ hlt
    have hle1 := applyAdv_now_le n m
    have hle2 := roundSeq_now_le hrest
    cases m with
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | deliver ss =>
      rcases hP with ⟨hp, hs, htn, hst⟩ | ⟨hp, hs, htn, hst⟩
      · exact Or.inl ⟨hp, applyAdv_Q _ hs, htn, hst⟩
      · exact Or.inr ⟨hp, applyAdv_Q _ hs, htn, hst⟩
    | chain caller op =>
      have hpre : Pre t r0 n := hP.elim (fun h => h.2) (fun h => pre_of_post h.2)
      have hnf := nf_pre hpre (by tomega)
      obtain ⟨hQ, htn, -⟩ := hpre
      have hQ' := applyAdv_Q (.chain caller op) hQ
      revert hle1 hQ'
      simp only [NetworkState.applyAdv]
      cases happ : n.chain.apply appsU caller op with
      | none =>
        intro _ _
        rcases hP with ⟨hp, hP⟩ | ⟨hp, hP⟩
        · exact Or.inl ⟨hp, hP⟩
        · exact Or.inr ⟨hp, hP⟩
      | some s' =>
        intro hle1 hQ'
        have hnow := Adjudicator.apply_now_le happ
        rcases adv_chain_keeps hfeas hQ htn hnf happ with h | h | h
        · rcases hP with ⟨hp, -, -, hst⟩ | ⟨hp, -, -, hst⟩
          · exact Or.inl ⟨hp, hQ', by simp; tomega, by simpa [h] using hst⟩
          · exact Or.inr ⟨hp, hQ', by simp; tomega, by simpa [h] using hst⟩
        · rcases hP with ⟨hp, -⟩ | ⟨hp, -⟩
          · exact Or.inl ⟨hp, hQ', by simp; tomega, Or.inl h⟩
          · exact Or.inr ⟨hp, hQ', by simp; tomega, Or.inl h⟩
        · rcases hP with ⟨hp, -⟩ | ⟨hp, -⟩
          · exact Or.inl ⟨hp, hQ', by simp; tomega, Or.inr (Or.inl h)⟩
          · exact Or.inr ⟨hp, hQ', by simp; tomega, Or.inr h⟩

/-- The invariant at the start of every round of `σ1`. -/
def Inv2 (n : NetworkState Unit p0) : Prop :=
  Q n ∧ ((∃ k, n.chain.statusOf c0 = .open k) ∨
    (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ n.chain.now + 2 ≤ ch.deadline))

theorem round2 {n1 n2 : NetworkState Unit p0} (hI : Inv2 n1) (hR : T0.Round appsU (σ1 n1) n1 n2) :
    Post n1.chain.now n2 ∧ n2.chain.now < n1.chain.now + 2 := by
  rw [σ1_eq hI.1] at hR
  obtain ⟨hseq, hlt⟩ := hR
  have hlt' : n2.chain.now < n1.chain.now + 2 := hlt
  refine ⟨round_inv n1.chain.now (n1.chain.statusOf c0).turnNumRecord hseq ?_ hlt', hlt'⟩
  left
  refine ⟨rfl, hI.1, le_rfl, ?_⟩
  rcases hI.2 with h | ⟨k, ch, hs, hd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨k, ch, hs, by rw [hs]; rfl, hd⟩)

theorem Q_net1 : Q net1 :=
  ⟨⟨ssP, by simp [net1], rfl⟩, ⟨ssQ, by simp [net1], rfl, by simp [ssQ]⟩,
    fun s hs => by simp only [net1, List.mem_singleton] at hs; subst hs; rfl⟩

theorem run_inv {n : NetworkState Unit p0} (h : Run appsU T0 σ1 net1 n) : Inv2 n := by
  induction h with
  | refl => exact ⟨Q_net1, Or.inl ⟨0, statusOf_genesis⟩⟩
  | @round n1 n2 _ hR ih =>
    obtain ⟨⟨hs, -, hst⟩, hlt⟩ := round2 ih hR
    have happ : n2.applyHonest (σ1 n1) = n2 := by
      rw [σ1_eq ih.1]; simp [HonestMove.chain, Reaction.one, NetworkState.applyHonest]
    rw [happ]
    refine ⟨hs, ?_⟩
    rcases hst with h | ⟨k, ch, hc, hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, ch, hc, by tomega⟩

theorem prevents (Ω : Outcome Unit) : Prevents appsU T0 (fun n => n.Finalized c0 Ω) net1 := by
  refine ⟨σ1, σ1_feasible, ?_⟩
  intro n1 n2 hrun hR hfin
  obtain ⟨⟨-, -, hst⟩, hlt⟩ := round2 (run_inv hrun) hR
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hfin
  rcases hst with ⟨k, hk⟩ | ⟨k, ch, hk, hd⟩
  · rw [hk] at hfin; simp at hfin
  · rw [hk] at hfin; simp only [ChannelStatus.finalizedWith_challenged] at hfin
    rw [if_neg (show ¬ ch.deadline ≤ n2.chain.now by tomega)] at hfin; cases hfin

/-! ## The counterexample. -/

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

/-- Every hypothesis of `Old_finalizable_or_two_enabled` holds for `appsU`,
    `p0`, `T0`, `net1`, `c0`, and its conclusion fails: no outcome is
    finalizable and no outcome is enabled. -/
theorem finalizable_or_two_enabled_happ_false : ¬ Old_finalizable_or_two_enabled := by
  intro h
  rcases h appsU T0 A0 ⟨net1, net1_reachable⟩ ⟨c0, by decide⟩ (appsU_oldPremise _)
      (by simp [c0]) ⟨P, stAt 0, holdsP_of_Q Q_net1, supports_P _, rfl⟩ with
    ⟨Ω, hΩ⟩ | ⟨Ω1, -, -, hE, -⟩
  · exact not_finalizable Ω hΩ
  · exact hE (prevents Ω1)

#print axioms finalizable_or_two_enabled_happ_false
#print axioms appsU_not_supportWindow

/-! ## `appsU` is not desirable

Design decision 2026-11-01: the Nitro-24 claims take `Desirable`. `appsU`
fails `AppIR`: at `net1`, `p0` holds `P`, a support of `stAt 0`, with the
channel open, and no outcome ever finalizes (`not_unbeatable_any`). -/

theorem not_unbeatable_any {G : Outcome Unit → Prop} (n : NetworkState Unit p0)
    (h : UnbeatableIn appsU T0 (fun _ => True) (fun n => ∃ Ω, n.Finalized c0 Ω ∧ G Ω) n) :
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

theorem appsU_not_desirable (dest : Participant → Unit) : ¬ Desirable appsU ⟨0⟩ dest := by
  intro h
  have hH : HoldsShare appsU net1 c0 (dest p0) 0 :=
    ⟨P, stAt 0, holdsP_of_Q Q_net1, supports_P _, rfl, Nat.zero_le _, fun s hs _ => by
      simp only [net1, List.mem_singleton] at hs; subst hs
      exact ⟨le_refl _, fun _ => Nat.zero_le _⟩, 0, statusOf_genesis, le_refl _⟩
  refine not_unbeatable_any net1
    (h.ir.takeOut T0 A0 ⟨net1, net1_reachable⟩ ⟨c0, by decide⟩ 0 rfl (by simp [c0]) hH)
    ⟨⟨0, statusOf_genesis⟩, ?_, ssP, by simp [net1], rfl⟩
  intro r hr _
  simp only [net1, List.mem_singleton] at hr
  subst hr; rfl

#print axioms appsU_not_desirable

end ArmadaLean.Nitro.CounterexampleHapp
