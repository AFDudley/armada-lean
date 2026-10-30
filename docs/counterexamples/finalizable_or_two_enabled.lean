/-
  Counterexample to the original, unconstrained `finalizable_or_two_enabled`
  (Liveness.lean), Nitro-24 (Nitro:653-658, pebble `aln-6ca`).

  The app `appsAll` supports every state with every proof. Each side can then
  reset a running challenge without the other: a checkpoint at the next turn
  number. So:
  * `p0` cannot force any outcome: after each of `p0`'s reactions the
    adversary checkpoints `c0`, and an open channel never finalizes
    (`not_finalizable`).
  * `p0` prevents every outcome: `p0` checkpoints `c0` every round, so a
    challenge never reaches its deadline (`prevents`).
  At the initial network state, `p0` has no finalizable outcome and no
  enabled outcome. `finalizable_or_two_enabled_false` refutes the statement
  that drops the `happ : (apps c.appDef).NoUnilateralSupport` hypothesis.

  The paper's claim rests on a premise the model does not state: a channel
  cannot stall forever. Nitro:644-645 (footnote 4): "If a channel does not
  end with a conclusion proof, it ends with an expired on-chain challenge".
  ForceMove:1379-1381: each response increases the turn number, and "this
  prevents the game from stalling indefinitely". Here, the supply of
  supported higher-turn states is unbounded for both sides.

  Operator ruling 2026-10-30: the fix adds `happ` to `finalizable_or_two_enabled`.
  `appsAll_not_noUnilateralSupport` shows why `appsAll` does not refute the
  patched theorem: `appsAll` fails `happ`'s hypothesis. An empty proof
  supports every candidate, so no participant's signature is required.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/finalizable_or_two_enabled.lean`.
  `finalizable_or_two_enabled_false` uses only `propext`,
  `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Nitro.Liveness

namespace ArmadaLean.Nitro.Counterexample

open ArmadaLean.Nitro

def p0 : Participant := ⟨0⟩
def q0 : Participant := ⟨1⟩

/-- Rules that support every state with every proof. -/
def appsAll : Apps Unit := fun _ => ⟨fun _ _ _ => true⟩

def c0 : FixedPart :=
  { participants := [p0, q0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 2, kind := .ledger }

def Ω0 : Outcome Unit := .allocation []

/-- The state of `c0` at turn `k`. -/
def stAt (k : Nat) : State Unit :=
  { channel := c0, turnNum := k, outcome := Ω0, isFinal := false, appData := .opaque 0 }

/-- The adversary: any call by another participant that forges no
    signature of `p0`, any unforged delivery, any tick. -/
def T0 : Threat Unit p0 where
  feasible net m := match m with
    | .chain caller op => caller ≠ p0 ∧ ∀ ss ∈ op.proofStates, net.Unforged ss
    | .deliver ss => net.Unforged ss
    | .tick _ => True
    | .land _ => True
  ε := 1
  ε_pos := Nat.one_pos

theorem A0 : Assumptions appsAll p0 T0 where
  unforgeable := fun _ _ _ h => h.2
  unforgeableDeliver := fun _ _ h => h
  notHonest := fun _ _ _ h => h.1
  capable := fun _ _ _ h1 h2 => ⟨h1, h2⟩
  capableDeliver := fun _ _ h => h
  capableTick := fun _ _ => trivial

def net0 : NetworkState Unit p0 := ⟨Adjudicator.genesis, [], []⟩

theorem p0_ne_q0 : p0 ≠ q0 := by decide

theorem statusOf_genesis : (Adjudicator.genesis (E := Unit)).statusOf c0 = .open 0 := rfl

/-- One successful operation, from a status of `c0` that is not finalized,
    keeps the status, opens it, or starts a fresh challenge. -/
theorem step_status {caller : Participant} {op : Op Unit} {s s' : Adjudicator Unit}
    (h : s.apply appsAll caller op = some s')
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

/-! ## Part 1: no outcome is finalizable for `p0`. -/

/-- Every signer of every received state is `p0`. -/
def POnly (n : NetworkState Unit p0) : Prop := ∀ r ∈ n.received, ∀ x ∈ r.signers, x = p0

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

theorem holds_pOnly {n : NetworkState Unit p0} (hpo : POnly n) {ss : SignedState Unit}
    (hh : n.Holds ss) : ∀ x ∈ ss.signers, x = p0 := by
  intro x hx
  rcases hh.1 x hx with ⟨rfl, -⟩ | ⟨r, hr, -, hxr⟩
  · rfl
  · exact hpo r hr x hxr

/-- A call `p0` can issue in this game. -/
def Good (op : Op Unit) : Prop :=
  (∀ dt, op ≠ .tick dt) ∧ ∀ ss ∈ op.proofStates, ∀ x ∈ ss.signers, x = p0

theorem good_of_feasible {n : NetworkState Unit p0} (hpo : POnly n) {op : Op Unit}
    (h : op.HonestFeasible n) : Good op := by
  refine ⟨?_, ?_⟩
  · intro dt heq; subst heq; exact h
  · intro ss hss
    cases op with
    | deposit => exact absurd h id
    | tick => exact absurd h id
    | transfer => simp [Op.proofStates] at hss
    | reclaim => simp [Op.proofStates] at hss
    | challenge c proof cand => exact holds_pOnly hpo (h ss hss)
    | checkpoint c proof cand => exact holds_pOnly hpo (h ss hss)
    | conclude c ss' => exact holds_pOnly hpo (h ss hss)

theorem nf_of_step {caller : Participant} {op : Op Unit} {s s' : Adjudicator Unit}
    (h : s.apply appsAll caller op = some s') (hop : ∀ dt, op ≠ .tick dt)
    (hnc : ∀ ss, op = .conclude c0 ss → ¬ ConclusionProof c0 ss) (hnf : NF s) : NF s' := by
  have hnow := Adjudicator.apply_now_eq_of_not_tick hop h
  unfold NF at hnf ⊢
  rw [hnow]
  rcases step_status h hnc hnf with h1 | ⟨k, h1⟩ | ⟨k, st, h1⟩
  · rw [h1]; exact hnf
  · rw [h1]; rfl
  · rw [h1]; simp [c0]

theorem no_conclude_of_pOnly {ss : SignedState Unit} (hs : ∀ x ∈ ss.signers, x = p0) :
    ¬ ConclusionProof c0 ss := by
  rintro ⟨hc, -, hall⟩
  have hq : q0 ∈ ss.signers := hall q0 (by rw [hc]; simp [c0])
  exact p0_ne_q0 (hs q0 hq).symm

/-- `p0`'s calls land one after the other, the clock does not move, and the
    status of `c0` stays not finalized. -/
theorem land_all (t : Time) : ∀ (pending : List (Op Unit)), (∀ op ∈ pending, Good op) →
    ∀ (n : NetworkState Unit p0), NF n.chain → POnly n →
      ∃ n', Threat.RoundSeq appsAll T0 t pending n n' ∧ NF n'.chain ∧ POnly n' ∧
        n'.chain.now = n.chain.now := by
  intro pending
  induction pending with
  | nil => intro _ n hnf hpo; exact ⟨n, .nil, hnf, hpo, rfl⟩
  | cons op rest ih =>
    intro hgood n hnf hpo
    obtain ⟨hop, hps⟩ := hgood op List.mem_cons_self
    have hrest : ∀ op' ∈ rest, Good op' := fun op' h => hgood op' (List.mem_cons_of_mem op h)
    have key : NF (n.applyAdv appsAll (.land op)).chain ∧ POnly (n.applyAdv appsAll (.land op)) ∧
        (n.applyAdv appsAll (.land op)).chain.now = n.chain.now := by
      simp only [NetworkState.applyAdv]
      cases happ : n.chain.apply appsAll p0 op with
      | none => exact ⟨hnf, hpo, rfl⟩
      | some s' =>
        refine ⟨nf_of_step happ hop ?_ hnf, ?_, Adjudicator.apply_now_eq_of_not_tick hop happ⟩
        · rintro ss rfl
          exact no_conclude_of_pOnly (hps ss (by simp [Op.proofStates]))
        · intro r hr x hx
          rcases List.mem_append.1 hr with hr | hr
          · exact hps r hr x hx
          · exact hpo r hr x hx
    obtain ⟨hnf1, hpo1, hnow1⟩ := key
    obtain ⟨n', hseq, hnf', hpo', hnow'⟩ := ih hrest _ hnf1 hpo1
    exact ⟨n', .land (l1 := []) (l2 := rest) rfl hseq, hnf', hpo', by rw [hnow', hnow1]⟩

/-- A run of adversary moves with nothing pending can follow any round. -/
theorem roundSeq_append {t : Time} {pending : List (Op Unit)} {n n1 n2 : NetworkState Unit p0}
    (h1 : Threat.RoundSeq appsAll T0 t pending n n1) (h2 : Threat.RoundSeq appsAll T0 t [] n1 n2) :
    Threat.RoundSeq appsAll T0 t pending n n2 := by
  induction h1 with
  | nil => exact h2
  | land hsplit _ ih => exact .land hsplit (ih h2)
  | tick hfeas hgate _ ih => exact .tick hfeas hgate (ih h2)
  | other hfeas hnotick hnoland _ ih => exact .other hfeas hnotick hnoland (ih h2)

/-- The invariant of part 1: `c0` is open and `p0` received only its own
    signatures. -/
def Inv1 (n : NetworkState Unit p0) : Prop := (∃ k, n.chain.statusOf c0 = .open k) ∧ POnly n

/-- The adversary's answer to any move of `p0`: land `p0`'s calls, then
    checkpoint `c0` at the next turn. -/
theorem round1 (n : NetworkState Unit p0) (hI : Inv1 n) (m : HonestMove Unit) (hfeas : m.Feasible n) :
    ∃ n', T0.Round appsAll m n n' ∧ Inv1 (n'.applyHonest m) := by
  obtain ⟨⟨k, hk⟩, hpo⟩ := hI
  have hgood : ∀ op ∈ m.calls, Good op := by
    cases m with
    | react r => intro op hop; exact good_of_feasible hpo (hfeas op hop)
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  have hnf : NF n.chain := by unfold NF; rw [hk]; rfl
  obtain ⟨n1, hseq1, hnf1, hpo1, hnow1⟩ := land_all n.chain.now m.calls hgood n hnf hpo
  set op : Op Unit := .checkpoint c0 [] (stAt ((n1.chain.statusOf c0).turnNumRecord + 1)) with hopdef
  have hopen : (n1.chain.statusOf c0).IsOpen n1.chain.now := isOpen_of_nf hnf1
  have happ : n1.chain.apply appsAll q0 op =
      some (n1.chain.setStatus c0 (.open ((n1.chain.statusOf c0).turnNumRecord + 1))) := by
    simp only [hopdef, Adjudicator.apply_checkpoint, Adjudicator.checkpoint]
    rw [if_pos ⟨hopen, rfl, rfl, Nat.lt_succ_self _⟩]
    rfl
  set n2 := n1.applyAdv appsAll (.chain q0 op) with hn2
  have hn2c : n2.chain = n1.chain.setStatus c0 (.open ((n1.chain.statusOf c0).turnNumRecord + 1)) := by
    simp only [hn2, NetworkState.applyAdv, happ]
  have hn2r : n2.received = n1.received := by
    simp only [hn2, NetworkState.applyAdv, happ]
    simp [hopdef, Op.proofStates]
  have hfeasq : T0.feasible n1 (.chain q0 op) := ⟨fun h => p0_ne_q0 h.symm, by simp [hopdef, Op.proofStates]⟩
  have hseq : Threat.RoundSeq appsAll T0 n.chain.now m.calls n n2 :=
    roundSeq_append hseq1 (.other hfeasq (by intro dt h; cases h) (by intro o h; cases h) .nil)
  refine ⟨n2, ⟨hseq, ?_⟩, ?_⟩
  · rw [hn2c, Adjudicator.setStatus_now, hnow1]
    exact Nat.lt_add_of_pos_right T0.ε_pos
  · have hpo2 : POnly n2 := by intro r hr; rw [hn2r] at hr; exact hpo1 r hr
    cases m with
    | react r =>
      refine ⟨⟨(n1.chain.statusOf c0).turnNumRecord + 1, ?_⟩, ?_⟩
      · simp only [NetworkState.applyHonest]; rw [hn2c]; simp
      · intro r' hr; exact hpo2 r' hr
    | wait dt =>
      refine ⟨⟨(n1.chain.statusOf c0).turnNumRecord + 1, ?_⟩, ?_⟩
      · simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; rw [hn2c]; simp
      · intro r' hr; exact hpo2 r' hr

theorem not_unbeatable (Ω : Outcome Unit) (n : NetworkState Unit p0)
    (h : UnbeatableIn appsAll T0 (fun _ => True) (fun n => n.Finalized c0 Ω) n) : Inv1 n → False := by
  induction h with
  | done hG =>
    rintro ⟨⟨k, hk⟩, -⟩
    simp [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hk] at hG
  | move m _ hfeas _ ih =>
    intro hI
    obtain ⟨n', hR, hI'⟩ := round1 _ hI m hfeas
    exact ih n' hR hI'

theorem not_finalizable (Ω : Outcome Unit) : ¬ Finalizable appsAll T0 c0 Ω net0 :=
  fun h => not_unbeatable Ω net0 h ⟨⟨0, statusOf_genesis⟩, by simp [POnly, net0]⟩

/-! ## Part 2: `p0` prevents every outcome. -/

/-- `p0` checkpoints `c0` at the next turn, every round. -/
def σ0 : Strategy Unit p0 := fun n =>
  .chain (.checkpoint c0 [] (stAt ((n.chain.statusOf c0).turnNumRecord + 1)))

theorem σ0_feasible (n : NetworkState Unit p0) : (σ0 n).Feasible n := by
  simp [σ0, Op.HonestFeasible, Op.proofStates]

theorem applyAdv_now_le (n : NetworkState Unit p0) (m : AdvMove Unit) :
    n.chain.now ≤ (n.applyAdv appsAll m).chain.now := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases h : n.chain.apply appsAll caller op with
    | none => exact le_rfl
    | some s' => exact Adjudicator.apply_now_le h
  | deliver ss => exact le_rfl
  | tick dt => simp [NetworkState.applyAdv]
  | land op =>
    simp only [NetworkState.applyAdv]
    cases h : n.chain.apply appsAll p0 op with
    | none => exact le_rfl
    | some s' => exact Adjudicator.apply_now_le h

theorem roundSeq_now_le {t : Time} {pending : List (Op Unit)} {n n' : NetworkState Unit p0}
    (h : Threat.RoundSeq appsAll T0 t pending n n') : n.chain.now ≤ n'.chain.now := by
  induction h with
  | nil => exact le_rfl
  | land _ _ ih => exact le_trans (applyAdv_now_le _ _) ih
  | tick _ _ _ ih => exact le_trans (applyAdv_now_le _ _) ih
  | other _ _ _ _ ih => exact le_trans (applyAdv_now_le _ _) ih

/-- After `p0`'s call landed: `c0` is open, or its challenge started this
    round (deadline at least `t + 2`). -/
def Post (t : Time) (n : NetworkState Unit p0) : Prop :=
  n.sent = [] ∧ t ≤ n.chain.now ∧
    ((∃ k, n.chain.statusOf c0 = .open k) ∨
     (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ t + 2 ≤ ch.deadline))

/-- Before `p0`'s call landed: also the challenge from the round's start,
    at a turn at most `r0`, with deadline at least `t + 1`. -/
def Pre (t r0 : Time) (n : NetworkState Unit p0) : Prop :=
  n.sent = [] ∧ t ≤ n.chain.now ∧
    ((∃ k, n.chain.statusOf c0 = .open k) ∨
     (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ t + 2 ≤ ch.deadline) ∨
     (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ k ≤ r0 ∧ t + 1 ≤ ch.deadline))

theorem pre_of_post {t r0 : Time} {n : NetworkState Unit p0} (h : Post t n) : Pre t r0 n :=
  ⟨h.1, h.2.1, h.2.2.elim Or.inl (fun h => Or.inr (Or.inl h))⟩

/-- A status of the three `Pre` shapes has no final outcome before `t + 1`. -/
theorem nf_pre {t r0 : Time} {n : NetworkState Unit p0} (h : Pre t r0 n) (hlt : n.chain.now < t + 1) :
    NF n.chain := by
  obtain ⟨-, -, h | ⟨k, ch, hs, hd⟩ | ⟨k, ch, hs, -, hd⟩⟩ := h
  · obtain ⟨k, hs⟩ := h; unfold NF; rw [hs]; rfl
  · unfold NF; rw [hs]; simp only [ChannelStatus.finalOutcome_challenged]
    rw [if_neg (show ¬ ch.deadline ≤ n.chain.now by tomega)]
  · unfold NF; rw [hs]; simp only [ChannelStatus.finalOutcome_challenged]
    rw [if_neg (show ¬ ch.deadline ≤ n.chain.now by tomega)]

/-- An adversary chain call keeps `Pre` (or `Post`): `p0` signed nothing, so
    the adversary cannot conclude `c0`. -/
theorem adv_chain_keeps {t : Time} {n : NetworkState Unit p0} {caller : Participant} {op : Op Unit}
    {s' : Adjudicator Unit} (hfeas : T0.feasible n (.chain caller op))
    (hsent : n.sent = []) (htn : t ≤ n.chain.now) (hnf : NF n.chain)
    (happ : n.chain.apply appsAll caller op = some s') :
    s'.statusOf c0 = n.chain.statusOf c0 ∨ (∃ k, s'.statusOf c0 = .open k) ∨
      (∃ k ch, s'.statusOf c0 = .challenged k ch ∧ t + 2 ≤ ch.deadline) := by
  have hnc : ∀ ss, op = .conclude c0 ss → ¬ ConclusionProof c0 ss := by
    rintro ss rfl ⟨hc, -, hall⟩
    have hp : p0 ∈ ss.signers := hall p0 (by rw [hc]; simp [c0])
    obtain ⟨s, hs, -⟩ := (hfeas.2 ss (by simp [Op.proofStates])).1 hp
    rw [hsent] at hs; cases hs
  rcases step_status happ hnc hnf with h | h | ⟨k, st, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨k, _, h, by simp [c0]; tomega⟩)

/-- The round invariant. `op_p` is `p0`'s checkpoint at turn `r0 + 1`. -/
theorem round_inv (t r0 : Time) :
    ∀ {pending : List (Op Unit)} {n n' : NetworkState Unit p0},
      Threat.RoundSeq appsAll T0 t pending n n' →
      ((pending = [.checkpoint c0 [] (stAt (r0 + 1))] ∧ Pre t r0 n) ∨ (pending = [] ∧ Post t n)) →
      n'.chain.now < t + 1 → Post t n' := by
  intro pending n n' h
  induction h with
  | nil =>
    rintro (⟨h, -⟩ | ⟨-, hP⟩) _
    · cases h
    · exact hP
  | @land pending n n' op l1 l2 hsplit hrest ih =>
    rintro (⟨hpend, hP⟩ | ⟨hpend, -⟩) hlt
    · rw [hpend] at hsplit
      have hl : l1 = [] ∧ op = .checkpoint c0 [] (stAt (r0 + 1)) ∧ l2 = [] := by
        rcases l1 with _ | ⟨a, l1⟩
        · simp only [List.nil_append, List.cons.injEq] at hsplit
          exact ⟨rfl, hsplit.1.symm, hsplit.2.symm⟩
        · simp at hsplit
      obtain ⟨rfl, rfl, rfl⟩ := hl
      apply ih _ hlt
      right
      refine ⟨rfl, ?_⟩
      have hle1 := applyAdv_now_le n (.land (.checkpoint c0 [] (stAt (r0 + 1))))
      have hle2 := roundSeq_now_le hrest
      obtain ⟨hsent, htn, hst⟩ := hP
      have hnf := nf_pre ⟨hsent, htn, hst⟩ (by tomega)
      have hopen : (n.chain.statusOf c0).IsOpen n.chain.now := isOpen_of_nf hnf
      have hcases : n.chain.apply appsAll p0 (.checkpoint c0 [] (stAt (r0 + 1))) = none ∨
          n.chain.apply appsAll p0 (.checkpoint c0 [] (stAt (r0 + 1))) =
            some (n.chain.setStatus c0 (.open (r0 + 1))) := by
        simp only [Adjudicator.apply_checkpoint, Adjudicator.checkpoint]
        split
        · right; rfl
        · left; rfl
      rcases hcases with happ | happ
      · have hn : n.applyAdv appsAll (.land (.checkpoint c0 [] (stAt (r0 + 1)))) = n := by
          simp only [NetworkState.applyAdv, happ]
        rw [hn]
        refine ⟨hsent, htn, ?_⟩
        rcases hst with h | h | ⟨k, ch, hs, hk, -⟩
        · exact Or.inl h
        · exact Or.inr h
        · exfalso
          simp only [Adjudicator.apply_checkpoint, Adjudicator.checkpoint] at happ
          rw [if_pos ⟨hopen, rfl, rfl, by rw [hs]; simp [stAt]; tomega⟩] at happ
          cases happ
      · simp only [NetworkState.applyAdv, happ]
        exact ⟨hsent, by simp; exact htn, Or.inl ⟨r0 + 1, by simp⟩⟩
    · rw [hpend] at hsplit; simp at hsplit
  | @tick pending n n' dt hfeas hgate hrest ih =>
    intro hP hlt
    apply ih _ hlt
    have keep : ∀ {r0' : Time}, (Pre t r0' n → Pre t r0' (n.applyAdv appsAll (.tick dt))) ∧
        (Post t n → Post t (n.applyAdv appsAll (.tick dt))) := by
      intro r0'
      constructor
      · rintro ⟨hs, htn, hst⟩
        exact ⟨hs, by simp [NetworkState.applyAdv]; tomega, by simpa [NetworkState.applyAdv] using hst⟩
      · rintro ⟨hs, htn, hst⟩
        exact ⟨hs, by simp [NetworkState.applyAdv]; tomega, by simpa [NetworkState.applyAdv] using hst⟩
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
      · exact Or.inl ⟨hp, hs, htn, hst⟩
      · exact Or.inr ⟨hp, hs, htn, hst⟩
    | chain caller op =>
      have hpre : Pre t r0 n := hP.elim (fun h => h.2) (fun h => pre_of_post h.2)
      have hnf := nf_pre hpre (by tomega)
      obtain ⟨hsent, htn, -⟩ := hpre
      revert hle1
      simp only [NetworkState.applyAdv]
      cases happ : n.chain.apply appsAll caller op with
      | none =>
        intro _
        rcases hP with ⟨hp, hP⟩ | ⟨hp, hP⟩
        · exact Or.inl ⟨hp, hP⟩
        · exact Or.inr ⟨hp, hP⟩
      | some s' =>
        intro hle1
        have hnow := Adjudicator.apply_now_le happ
        rcases adv_chain_keeps hfeas hsent htn hnf happ with h | h | h
        · rcases hP with ⟨hp, -, -, hst⟩ | ⟨hp, -, -, hst⟩
          · exact Or.inl ⟨hp, hsent, by simp; tomega, by simpa [h] using hst⟩
          · exact Or.inr ⟨hp, hsent, by simp; tomega, by simpa [h] using hst⟩
        · rcases hP with ⟨hp, -⟩ | ⟨hp, -⟩
          · exact Or.inl ⟨hp, hsent, by simp; tomega, Or.inl h⟩
          · exact Or.inr ⟨hp, hsent, by simp; tomega, Or.inl h⟩
        · rcases hP with ⟨hp, -⟩ | ⟨hp, -⟩
          · exact Or.inl ⟨hp, hsent, by simp; tomega, Or.inr (Or.inl h)⟩
          · exact Or.inr ⟨hp, hsent, by simp; tomega, Or.inr h⟩

/-- The invariant at the start of every round of `σ0`. -/
def Inv2 (n : NetworkState Unit p0) : Prop :=
  n.sent = [] ∧ ((∃ k, n.chain.statusOf c0 = .open k) ∨
    (∃ k ch, n.chain.statusOf c0 = .challenged k ch ∧ n.chain.now + 1 ≤ ch.deadline))

theorem round2 {n1 n2 : NetworkState Unit p0} (hI : Inv2 n1) (hR : T0.Round appsAll (σ0 n1) n1 n2) :
    Post n1.chain.now n2 ∧ n2.chain.now < n1.chain.now + 1 := by
  obtain ⟨hseq, hlt⟩ := hR
  have hlt' : n2.chain.now < n1.chain.now + 1 := hlt
  refine ⟨round_inv n1.chain.now (n1.chain.statusOf c0).turnNumRecord hseq ?_ hlt', hlt'⟩
  left
  refine ⟨rfl, hI.1, le_rfl, ?_⟩
  rcases hI.2 with h | ⟨k, ch, hs, hd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨k, ch, hs, by rw [hs]; rfl, hd⟩)

theorem run_inv {n : NetworkState Unit p0} (h : Run appsAll T0 σ0 net0 n) : Inv2 n := by
  induction h with
  | refl => exact ⟨rfl, Or.inl ⟨0, statusOf_genesis⟩⟩
  | @round n1 n2 _ hR ih =>
    obtain ⟨⟨hs, -, hst⟩, hlt⟩ := round2 ih hR
    have happ : n2.applyHonest (σ0 n1) = n2 := by simp [σ0]
    rw [happ]
    refine ⟨hs, ?_⟩
    rcases hst with h | ⟨k, ch, hc, hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, ch, hc, by tomega⟩

theorem prevents (Ω : Outcome Unit) : Prevents appsAll T0 (fun n => n.Finalized c0 Ω) net0 := by
  refine ⟨σ0, σ0_feasible, ?_⟩
  intro n1 n2 hrun hR hfin
  obtain ⟨⟨-, -, hst⟩, hlt⟩ := round2 (run_inv hrun) hR
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hfin
  rcases hst with ⟨k, hk⟩ | ⟨k, ch, hk, hd⟩
  · rw [hk] at hfin; simp at hfin
  · rw [hk] at hfin; simp only [ChannelStatus.finalizedWith_challenged] at hfin
    rw [if_neg (show ¬ ch.deadline ≤ n2.chain.now by tomega)] at hfin; cases hfin

/-! ## The counterexample. -/

/-- Every hypothesis of `finalizable_or_two_enabled` holds for `appsAll`,
    `p0`, `T0`, `net0`, `c0`, and its conclusion fails: no outcome is
    finalizable and no outcome is enabled. -/
theorem finalizable_or_two_enabled_false :
    ¬ ∀ (apps : Apps Unit) (p : Participant) (T : Threat Unit p) (_A : Assumptions apps p T)
        (net : NetworkState Unit p) (_hr : (Nitro.participant apps T).Reachable net)
        (c : FixedPart) (_hp : p ∈ c.participants)
        (_hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.Holds ss) ∧
          (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c)
        (_hdur : 2 * T.ε ≤ c.challengeDuration),
        (∃ Ω, Finalizable apps T c Ω net) ∨
        (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T c Ω1 net ∧ Enabled apps T c Ω2 net) := by
  intro h
  rcases h appsAll p0 T0 A0 net0 ⟨net0, rfl, .refl⟩ c0 (by simp [c0])
      ⟨[], stAt 0, by simp, rfl, rfl⟩ (by decide) with ⟨Ω, hΩ⟩ | ⟨Ω1, -, -, hE, -⟩
  · exact not_finalizable Ω hΩ
  · exact hE (prevents Ω1)

/-- `appsAll` does not carry `Rules.NoUnilateralSupport`: the empty proof
    supports `stAt 0` (`appsAll`'s rule accepts every proof unconditionally),
    but no participant signed the empty proof. Operator ruling 2026-10-30:
    the patched `finalizable_or_two_enabled` needs this hypothesis, and
    `appsAll` does not supply it, so the counterexample above does not
    refute the patched theorem. -/
theorem appsAll_not_noUnilateralSupport :
    ¬ (appsAll (⟨0⟩ : AppId) : Rules Unit).NoUnilateralSupport := by
  intro h
  obtain ⟨ss, hss, -⟩ := h c0 [] (stAt 0) rfl p0 (by simp [c0])
  exact List.not_mem_nil hss

end ArmadaLean.Nitro.Counterexample
