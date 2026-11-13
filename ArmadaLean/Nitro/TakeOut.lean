/-
  The take-out strategy, and the two IR apps: `TakeOut.consensus_IR` and
  `TakeOut.forceMove_IR` prove `AppIR` (`ArmadaLean/Types/App.lean`) for the
  consensus app and for every ForceMove app whose game library takes
  nothing from a non-mover (`NoTakeFromNonMover`). Moved from the IR draft
  of `docs/counterexamples/ir_game_rewrites_share.lean`.

  The strategy (`TakeOut.canTakeOut_of`): challenge an open channel with a
  held support, answer a challenge below the held turn `Th` with the own
  support at `Th`, and wait for a challenge at `Th` or above to end. Every
  support at a turn from `Th` on pays `p` at least its share (the proofs of
  `forceMove_IR` and `consensus_IR`). The support window bounds every turn
  record by `M = Th + n` (`Ctx.turnLt`), so the rank `rk` falls in every
  round. The helpers take their shared premises as structures (`Ctx`, `K`,
  `TI`, `RankBound`), and the strategy itself is one theorem, so that no
  premise repeats across declarations (`docs/lean/type-doctrine.md` rule 1).
-/
import ArmadaLean.Nitro.Liveness
import ArmadaLean.Types.App

namespace ArmadaLean.Nitro.TakeOut

variable {E : Type} [DecidableEq E]

/-- Every state of `proof` that `p` signed is a state in `sent`. -/
def SignedIn (sent : List (SignedState E)) (p : Participant) (proof : SupportProof E) : Prop :=
  ∀ ss ∈ proof, p ∈ ss.signers → ∃ s ∈ sent, s.state = ss.state

/-- The facts of the take-out strategy: `p` signed `sent0` only, every state
    of `c` in it is below the turn bound `M`, every support of `c` with `p`'s
    signatures from `sent0` is below `M` (the support window), `Th < M`, and
    every support of `c` at a turn from `Th` on, and every conclusion proof,
    pays `d` at least `x`. -/
structure Ctx (apps : Apps E) (p : Participant) (c : FixedPart) (d : E) (x Th M : Nat)
    (sent0 : List (SignedState E)) : Prop where
  hp : p ∈ c.participants
  sentTurn : ∀ s ∈ sent0, s.state.channel = c → s.state.turnNum < M
  thLt : Th < M
  turnLt : ∀ proof cand, SignedIn sent0 p proof → (apps c.appDef).supports c proof cand = true →
    cand.turnNum < M
  pay : ∀ proof cand, SignedIn sent0 p proof → (apps c.appDef).supports c proof cand = true →
    cand.channel = c → Th ≤ cand.turnNum → x ≤ share cand.outcome d
  payConc : ∀ ss, ConclusionProof c ss → (∃ s ∈ sent0, s.state = ss.state) →
    x ≤ share ss.state.outcome d

/-- The rank of a status of `c`: it falls at each change of the status. -/
def rk (M : Nat) : ChannelStatus E → Nat
  | .open t => 2 * (M - t) + 2
  | .challenged t _ => 2 * (M - t) + 1
  | .finalized .. => 0


/-- One successful operation, and the status of `c` it leaves. -/
theorem status_cases {apps : Apps E} {s s' : Adjudicator E} {caller : Participant} {op : Op E}
    {c : FixedPart} (h : s.apply apps caller op = some s') :
    s'.statusOf c = s.statusOf c ∨
    (∃ P cand, op = .challenge c P cand ∧ (apps c.appDef).supports c P cand = true ∧
      cand.channel = c ∧
      ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ cand.turnNum) ∨
        (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < cand.turnNum)) ∧
      s'.statusOf c = .challenged cand.turnNum ⟨cand, s.now + c.challengeDuration⟩) ∨
    (∃ P cand, op = .checkpoint c P cand ∧ (apps c.appDef).supports c P cand = true ∧
      cand.channel = c ∧ (s.statusOf c).IsOpen s.now ∧
      (s.statusOf c).turnNumRecord < cand.turnNum ∧ s'.statusOf c = .open cand.turnNum) ∨
    (∃ ss, op = .conclude c ss ∧ ConclusionProof c ss ∧
      s'.statusOf c = .finalized ss.state.turnNum ss.state.outcome ss.state.outcome) ∨
    (∃ o0 o', (s.statusOf c).finalOutcome s.now = some o0 ∧
      s'.statusOf c = (s.statusOf c).withOutcome o') := by
  by_cases ht : Op.targets op c
  · cases op with
    | deposit a e x => (simp? [Op.targets] at ht says simp only [Op.targets] at ht)
    | tick dt => (simp? [Op.targets] at ht says simp only [Op.targets] at ht)
    | transfer a b =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨o, amt, x, hf, -, -, -, -, hst, -⟩ := Adjudicator.transfer_some h
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨.allocation o, .allocation (o.reduceOwed b x), ?_, ?_⟩)))
      · simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hf
      · rw [Adjudicator.statusOf_of_status hst]
        simp only [Adjudicator.statusOf_setStatus, if_true]
    | reclaim l v =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨oL, oV, x, left, right, hL, -, -, -, -, -, rfl, -, -⟩ := Adjudicator.reclaim_some h
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨.allocation oL,
        .allocation (((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address), ?_, ?_⟩)))
      · simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hL
      · simp only [Adjudicator.statusOf_setStatus, if_true]
    | challenge c' P cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hsup, hcc, hmode⟩, rfl⟩ := Adjudicator.challenge_some h
      exact Or.inr (Or.inl ⟨P, cand, rfl, hsup, hcc, hmode,
        by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])⟩)
    | checkpoint c' P cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨hopen, hsup, hcc, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
      exact Or.inr (Or.inr (Or.inl ⟨P, cand, rfl, hsup, hcc, hopen, hlt,
        by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])⟩))
    | conclude c' ss =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hcp⟩, rfl⟩ := Adjudicator.conclude_some h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ss, rfl, hcp,
        by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])⟩)))
  · exact Or.inl (statusOf_apply_of_not_targets h ht)


/-- The invariant inside a round that starts at `n0`. `R` is a lower bound of
    the turn record (or the status is finalized); the rank stays below `Kb`, or
    the status stays `S`. -/
structure K (apps : Apps E) {p : Participant} (c : FixedPart) (d : E) (x Th M : Nat)
    (sent0 : List (SignedState E)) (proof0 : SupportProof E) (n0 : NetworkState E p)
    (R Kb : Nat) (S : ChannelStatus E) (n : NetworkState E p) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = sent0
  now0 : n0.chain.now ≤ n.chain.now
  recv0 : ∀ r ∈ n0.received, r ∈ n.received
  held0 : ∀ ss ∈ proof0, n.Holds ss
  openW : ∀ t, n.chain.statusOf c = .open t → t ≤ Th ∨
    ∃ proof cand, (∀ ss ∈ proof, n.Holds ss) ∧ (apps c.appDef).supports c proof cand = true ∧
      cand.channel = c ∧ t ≤ cand.turnNum
  chPay : ∀ t ch, n.chain.statusOf c = .challenged t ch → Th ≤ t → x ≤ share ch.state.outcome d
  finPay : ∀ t f o, n.chain.statusOf c = .finalized t f o → x ≤ share f d
  recLt : (n.chain.statusOf c).turnNumRecord < M
  lowK : ∀ t ch, n.chain.statusOf c = .challenged t ch → t < Th →
    n.chain.statusOf c = n0.chain.statusOf c ∨ n0.chain.now + c.challengeDuration ≤ ch.deadline
  recR : R ≤ (n.chain.statusOf c).turnNumRecord ∨ ∃ t f o, n.chain.statusOf c = .finalized t f o
  prog : rk M (n.chain.statusOf c) < Kb ∨ n.chain.statusOf c = S


/-- The rank bound of a round: `Kb` is positive, and the rank of the status
    `S` is at most `Kb`. -/
structure RankBound (M : Nat) (S : ChannelStatus E) (Kb : Nat) : Prop where
  pos : 0 < Kb
  le : rk M S ≤ Kb

omit [DecidableEq E] in
theorem rk_step {M : Nat} {Kb : Nat} {S st st' : ChannelStatus E} (hB : RankBound M S Kb)
    (hprev : rk M st < Kb ∨ st = S)
    (hstep : st' = st ∨ rk M st' < rk M st ∨ rk M st' = 0) : rk M st' < Kb ∨ st' = S := by
  rcases hstep with rfl | hlt | h0
  · exact hprev
  · rcases hprev with h | rfl
    · exact Or.inl (lt_trans hlt h)
    · exact Or.inl (lt_of_lt_of_le hlt hB.le)
  · exact Or.inl (by rw [h0]; exact hB.pos)

/-- A step invariant with the side condition `Cond` is one for a sub-round
    of pure adversary play, where no call of `p` lands. -/
theorem _root_.ArmadaLean.Nitro.Threat.StepInvariant.noLand {apps : Apps E} {p : Participant}
    {T : Threat E p} {Guard Inv : NetworkState E p → Prop} {Cond : NetworkState E p → Op E → Prop}
    (h : T.StepInvariant apps Guard Inv Cond) : T.StepInvariant apps Guard Inv (fun _ _ => False) :=
  ⟨fun _ hc _ => hc.elim, h.deliver, h.tick, h.chain⟩

/-- `K` as a step invariant of a sub-round that ends no later than
    `Eend < E0`: each successful operation with unforged proof states keeps
    `K`, whether `p`'s own call lands or the adversary acts. A low challenge
    standing at `n0` ends no sooner than `E0`. -/
theorem K.stepInv {apps : Apps E} {p : Participant} {T : Threat E p} {c : FixedPart} {d : E}
    {x Th M : Nat} {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n0 : NetworkState E p}
    {R Kb : Nat} {S : ChannelStatus E} (C : Ctx apps p c d x Th M sent0) (B : Bounds apps p T)
    {E0 Eend : Time} (hE0 : E0 ≤ n0.chain.now + c.challengeDuration) (hEend : Eend < E0)
    (hlow0 : ∀ t ch, n0.chain.statusOf c = .challenged t ch → t < Th → E0 ≤ ch.deadline)
    (hB : RankBound M S Kb) :
    T.StepInvariant apps (fun n => n.chain.now ≤ Eend)
      (K apps c d x Th M sent0 proof0 n0 R Kb S)
      (fun n op => ∀ ss ∈ op.proofStates, n.Unforged ss) := by
  have step : ∀ {m : NetworkState E p} {caller : Participant} {op : Op E} {s' : Adjudicator E},
      K apps c d x Th M sent0 proof0 n0 R Kb S m → m.chain.now < E0 →
      m.chain.apply apps caller op = some s' → (∀ ss ∈ op.proofStates, m.Unforged ss) →
      K apps c d x Th M sent0 proof0 n0 R Kb S
        { m with chain := s', received := op.proofStates ++ m.received } := by
    intro m caller op s' hK hnow h hU
    have hS : SignedIn sent0 p op.proofStates := fun ss hss hps => by
      obtain ⟨s, hs, hse⟩ := (hU ss hss).1 hps
      exact ⟨s, by rw [← hK.sent]; exact hs, hse⟩
    have hrec : ∀ r ∈ m.received, r ∈ op.proofStates ++ m.received :=
      fun r hr => List.mem_append_right _ hr
    have hheld : ∀ {ss}, m.Holds ss →
        ({ m with chain := s', received := op.proofStates ++ m.received } : NetworkState E p).Holds ss :=
      fun h => NetworkState.Holds.mono (net := m) rfl hrec h
    have hnow' := Adjudicator.apply_now_le h
    -- a low challenge at `m` has not expired
    have hlive : ∀ t ch, m.chain.statusOf c = .challenged t ch → t < Th → m.chain.now < ch.deadline := by
      intro t ch hc ht
      rcases hK.lowK t ch hc ht with h0 | h6
      · exact lt_of_lt_of_le hnow (hlow0 t ch (h0 ▸ hc) ht)
      · exact lt_of_lt_of_le hnow (le_trans hE0 h6)
    have hM : (m.chain.statusOf c).turnNumRecord < M := hK.recLt
    -- the facts that do not read the status
    have hRecU : ∀ r ∈ op.proofStates ++ m.received,
        ({ m with chain := s', received := op.proofStates ++ m.received } : NetworkState E p).Unforged r := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact (hU r hr).of_sent rfl
      · exact (hK.recvU r hr).of_sent rfl
    rcases status_cases (c := c) h with heq | ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩ |
        ⟨P, cand, rfl, hsup, hcc, hopen, hlt, hst⟩ | ⟨ss, rfl, hcp, hst⟩ | ⟨o0, o', hfo, hst⟩
    · -- the status is unchanged
      refine ⟨hRecU, hK.sent, le_trans hK.now0 hnow', fun r hr => hrec r (hK.recv0 r hr), fun ss hss => hheld (hK.held0 ss hss), fun t ht => ?_,
        fun t ch hc => hK.chPay t ch (heq ▸ hc), fun t f o hc => hK.finPay t f o (heq ▸ hc),
        by rw [heq]; exact hK.recLt, fun t ch hc ht => by rw [heq] at hc ⊢; exact hK.lowK t ch hc ht,
        by rw [heq]; exact hK.recR, by rw [heq]; exact hK.prog⟩
      rcases hK.openW t (heq ▸ ht) with h1 | ⟨pr, cd, hH, hsu, hcc, hle⟩
      · exact Or.inl h1
      · exact Or.inr ⟨pr, cd, fun ss hss => hheld (hH ss hss), hsu, hcc, hle⟩
    · -- a challenge
      have hge : (m.chain.statusOf c).turnNumRecord ≤ cand.turnNum := by
        rcases hmode with ⟨-, h⟩ | ⟨-, h⟩
        · exact h
        · exact le_of_lt h
      have hlt' : cand.turnNum < M := C.turnLt _ _ hS hsup
      refine ⟨hRecU, hK.sent, le_trans hK.now0 hnow', fun r hr => hrec r (hK.recv0 r hr), fun ss hss => hheld (hK.held0 ss hss),
        fun t ht => (by rw [hst] at ht; cases ht), fun t ch hc hTh => ?_,
        fun t f o hc => (by rw [hst] at hc; cases hc), by rw [hst]; exact hlt',
        fun t ch hc _ => ?_, ?_, ?_⟩
      · rw [hst] at hc
        obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hc
        exact C.pay P cand hS hsup hcc hTh
      · rw [hst] at hc
        obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hc
        exact Or.inr (Nat.add_le_add_right hK.now0 _)
      · rw [hst]
        rcases hK.recR with h1 | h1
        · exact Or.inl (le_trans h1 hge)
        · obtain ⟨t, f, o, hf⟩ := h1
          rw [Adjudicator.mode_eq, hf] at hmode
          rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
      · refine rk_step hB hK.prog (Or.inr (Or.inl ?_))
        rw [hst]
        rw [Adjudicator.mode_eq] at hmode
        cases hs : m.chain.statusOf c with
        | «open» r =>
          rw [hs] at hmode hM
          rcases hmode with ⟨-, hr⟩ | ⟨hm, -⟩
          · simp only [ChannelStatus.turnNumRecord_open] at hr
            simp only [rk]; omega
          · cases hm
        | challenged r ch' =>
          rw [hs] at hmode hM
          rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
          · simp only [ChannelStatus.mode] at hm; split at hm <;> cases hm
          · simp only [ChannelStatus.turnNumRecord_challenged] at hr hM
            simp only [rk]; omega
        | finalized r f o =>
          rw [hs] at hmode
          rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
    · -- a checkpoint
      have hlt' : cand.turnNum < M := C.turnLt _ _ hS hsup
      have hnotfin : ∀ t f o, m.chain.statusOf c ≠ .finalized t f o := fun t f o hf => by
        rw [hf] at hopen
        exact hopen (by (simp? [ChannelStatus.mode] says simp only [ChannelStatus.mode]))
      refine ⟨hRecU, hK.sent, le_trans hK.now0 hnow', fun r hr => hrec r (hK.recv0 r hr), fun ss hss => hheld (hK.held0 ss hss),
        fun t ht => ?_, fun t ch hc => (by rw [hst] at hc; cases hc),
        fun t f o hc => (by rw [hst] at hc; cases hc), by rw [hst]; exact hlt',
        fun t ch hc => (by rw [hst] at hc; cases hc), ?_, ?_⟩
      · rw [hst] at ht
        obtain rfl := ChannelStatus.open.inj ht
        exact Or.inr ⟨P, cand, fun ss hss => holds_of_mem_received (List.mem_append_left _ hss), hsup,
          hcc, le_refl _⟩
      · rw [hst]
        rcases hK.recR with h1 | ⟨t, f, o, hf⟩
        · exact Or.inl (le_trans h1 (le_of_lt hlt))
        · exact absurd hf (hnotfin t f o)
      · refine rk_step hB hK.prog (Or.inr (Or.inl ?_))
        rw [hst]
        cases hs : m.chain.statusOf c with
        | «open» r =>
          rw [hs] at hlt hM
          simp only [ChannelStatus.turnNumRecord_open] at hlt hM
          simp only [rk]; omega
        | challenged r ch' =>
          rw [hs] at hlt hM
          simp only [ChannelStatus.turnNumRecord_challenged] at hlt hM
          simp only [rk]; omega
        | finalized r f o => exact absurd hs (hnotfin r f o)
    · -- a conclusion
      have hpss : ∃ s ∈ sent0, s.state = ss.state :=
        hS ss (List.mem_singleton_self ss) (hcp.2.2 p (by rw [hcp.1]; exact C.hp))
      have hlt' : ss.state.turnNum < M := by
        obtain ⟨s, hs, hse⟩ := hpss
        have := C.sentTurn s hs (by rw [hse]; exact hcp.1)
        rw [hse] at this
        exact this
      refine ⟨hRecU, hK.sent, le_trans hK.now0 hnow', fun r hr => hrec r (hK.recv0 r hr), fun ss hss => hheld (hK.held0 ss hss),
        fun t ht => (by rw [hst] at ht; cases ht), fun t ch hc => (by rw [hst] at hc; cases hc),
        fun t f o hc => ?_, by rw [hst]; exact hlt', fun t ch hc => (by rw [hst] at hc; cases hc),
        Or.inr ⟨_, _, _, hst⟩, rk_step hB hK.prog (Or.inr (Or.inr (by rw [hst]; rfl)))⟩
      rw [hst] at hc
      obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hc
      exact C.payConc ss hcp hpss
    · -- a payout: the status was already final
      cases hs : m.chain.statusOf c with
      | «open» r =>
        rw [hs] at hfo
        (simp? [ChannelStatus.finalOutcome] at hfo says
          simp only [ChannelStatus.finalOutcome, reduceCtorEq] at hfo)
      | challenged r ch' =>
        rw [hs] at hfo hst hM
        have hexp : ch'.deadline ≤ m.chain.now := by
          simp only [ChannelStatus.finalOutcome] at hfo
          split at hfo
          · assumption
          · cases hfo
        have hr : Th ≤ r := by
          by_contra hlow
          exact absurd hexp (not_le.mpr (hlive r ch' hs (by omega)))
        have hpay := hK.chPay r ch' hs hr
        simp only [ChannelStatus.withOutcome_challenged] at hst
        refine ⟨hRecU, hK.sent, le_trans hK.now0 hnow', fun r hr => hrec r (hK.recv0 r hr), fun ss hss => hheld (hK.held0 ss hss),
          fun t ht => (by rw [hst] at ht; cases ht), fun t ch hc => (by rw [hst] at hc; cases hc),
          fun t f o hc => ?_, by rw [hst]; exact hM, fun t ch hc => (by rw [hst] at hc; cases hc),
          Or.inr ⟨_, _, _, hst⟩, rk_step hB hK.prog (Or.inr (Or.inr (by rw [hst]; rfl)))⟩
        rw [hst] at hc
        obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hc
        exact hpay
      | finalized r f o =>
        rw [hs] at hst hM
        have hpay := hK.finPay r f o hs
        simp only [ChannelStatus.withOutcome_finalized] at hst
        refine ⟨hRecU, hK.sent, le_trans hK.now0 hnow', fun r hr => hrec r (hK.recv0 r hr), fun ss hss => hheld (hK.held0 ss hss),
          fun t ht => (by rw [hst] at ht; cases ht), fun t ch hc => (by rw [hst] at hc; cases hc),
          fun t f' o'' hc => ?_, by rw [hst]; exact hM, fun t ch hc => (by rw [hst] at hc; cases hc),
          Or.inr ⟨_, _, _, hst⟩, rk_step hB hK.prog (Or.inr (Or.inr (by rw [hst]; rfl)))⟩
        rw [hst] at hc
        obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hc
        exact hpay
  refine ⟨fun {n op} hg hU hK => ?_, fun {n ss} _ hfe hK => ?_, fun {n dt} _ _ hK => ?_,
    fun {n caller op} hg hfe hK => ?_⟩
  · cases happ : n.chain.apply apps p op with
    | none => rw [NetworkState.applyAdv_land_none apps happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_land_some apps happ]
      exact step hK (lt_of_le_of_lt hg hEend) happ hU
  · rw [NetworkState.applyAdv_deliver]
    have hrec : ∀ r ∈ n.received, r ∈ ss :: n.received := fun r hr => List.mem_cons_of_mem _ hr
    have hheld : ∀ {x}, n.Holds x → ({ n with received := ss :: n.received } : NetworkState E p).Holds x :=
      fun h => NetworkState.Holds.mono (net := n) rfl hrec h
    refine ⟨fun r hr => ?_, hK.sent, hK.now0, fun r hr => hrec r (hK.recv0 r hr),
      fun x hx => hheld (hK.held0 x hx), fun t ht => ?_, hK.chPay, hK.finPay, hK.recLt, hK.lowK,
      hK.recR, hK.prog⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact (B.unforgeableDeliver n r hfe).of_sent rfl
      · exact (hK.recvU r hr).of_sent rfl
    · rcases hK.openW t ht with h1 | ⟨pr, cd, hH, hsu, hcc, hle⟩
      · exact Or.inl h1
      · exact Or.inr ⟨pr, cd, fun x hx => hheld (hH x hx), hsu, hcc, hle⟩
  · rw [NetworkState.applyAdv_tick]
    refine ⟨fun r hr => (hK.recvU r hr).of_sent rfl, hK.sent,
      le_trans hK.now0 (Nat.le_add_right _ _), hK.recv0,
      fun x hx => NetworkState.Holds.mono (net := n) rfl (fun _ h => h) (hK.held0 x hx), ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;> simp only [Adjudicator.tick_statusOf]
    · intro t ht
      rcases hK.openW t ht with h1 | ⟨pr, cd, hH, hsu, hcc, hle⟩
      · exact Or.inl h1
      · exact Or.inr ⟨pr, cd, fun x hx => NetworkState.Holds.mono (net := n) rfl (fun _ h => h) (hH x hx),
          hsu, hcc, hle⟩
    · exact hK.chPay
    · exact hK.finPay
    · exact hK.recLt
    · exact hK.lowK
    · exact hK.recR
    · exact hK.prog
  · cases happ : n.chain.apply apps caller op with
    | none => rw [NetworkState.applyAdv_chain_none apps happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_chain_some apps happ]
      exact step hK (lt_of_le_of_lt hg hEend) happ (B.unforgeable n caller op hfe)

/-- The invariant at the start of each round. -/
structure TI (apps : Apps E) {p : Participant} (ε : Time) (c : FixedPart) (d : E) (x Th M : Nat)
    (sent0 : List (SignedState E)) (proof0 : SupportProof E) (n : NetworkState E p) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = sent0
  held0 : ∀ ss ∈ proof0, n.Holds ss
  openW : ∀ t, n.chain.statusOf c = .open t → t ≤ Th ∨
    ∃ proof cand, (∀ ss ∈ proof, n.Holds ss) ∧ (apps c.appDef).supports c proof cand = true ∧
      cand.channel = c ∧ t ≤ cand.turnNum
  chPay : ∀ t ch, n.chain.statusOf c = .challenged t ch → Th ≤ t → x ≤ share ch.state.outcome d
  finPay : ∀ t f o, n.chain.statusOf c = .finalized t f o → x ≤ share f d
  recLt : (n.chain.statusOf c).turnNumRecord < M
  chLow : ∀ t ch, n.chain.statusOf c = .challenged t ch → t < Th → n.chain.now + ε ≤ ch.deadline

theorem TI.toK {apps : Apps E} {p : Participant} {ε : Time} {c : FixedPart} {d : E} {x Th M : Nat}
    {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n : NetworkState E p}
    (hI : TI apps ε c d x Th M sent0 proof0 n) :
    K apps c d x Th M sent0 proof0 n (n.chain.statusOf c).turnNumRecord (rk (M) (n.chain.statusOf c))
      (n.chain.statusOf c) n :=
  ⟨hI.recvU, hI.sent, le_refl _, fun _ h => h, hI.held0, hI.openW, hI.chPay, hI.finPay, hI.recLt,
    fun _ _ _ _ => Or.inl rfl, Or.inl (le_refl _), Or.inr rfl⟩

theorem K.reS {apps : Apps E} {p : Participant} {c : FixedPart} {d : E} {x Th M : Nat}
    {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n0 n : NetworkState E p}
    {R R' Kb : Nat} {S S' : ChannelStatus E} (hK : K apps c d x Th M sent0 proof0 n0 R Kb S n)
    (hlt : rk (M) (n.chain.statusOf c) < Kb)
    (hR : R' ≤ (n.chain.statusOf c).turnNumRecord ∨ ∃ t f o, n.chain.statusOf c = .finalized t f o) :
    K apps c d x Th M sent0 proof0 n0 R' Kb S' n :=
  ⟨hK.recvU, hK.sent, hK.now0, hK.recv0, hK.held0, hK.openW, hK.chPay, hK.finPay, hK.recLt, hK.lowK,
    hR, Or.inl hlt⟩


/-- The rank of one successful operation with proof states of `sent0`: the
    status stays, or its rank falls, or it becomes `0`. -/
theorem rank_step {apps : Apps E} {p : Participant} {c : FixedPart} {d : E} {x Th M : Nat}
    {sent0 : List (SignedState E)} (C : Ctx apps p c d x Th M sent0) {s s' : Adjudicator E}
    {caller : Participant} {op : Op E} (h : s.apply apps caller op = some s')
    (hS : SignedIn sent0 p op.proofStates) (hM : (s.statusOf c).turnNumRecord < M) :
    s'.statusOf c = s.statusOf c ∨ rk (M) (s'.statusOf c) < rk (M) (s.statusOf c) ∨
      rk (M) (s'.statusOf c) = 0 := by
  rcases status_cases (c := c) h with heq | ⟨P, cand, rfl, hsup, -, hmode, hst⟩ |
      ⟨P, cand, rfl, hsup, -, hopen, hlt, hst⟩ | ⟨ss, rfl, -, hst⟩ | ⟨o0, o', hfo, hst⟩
  · exact Or.inl heq
  · right; left
    have hlt' : cand.turnNum < M := C.turnLt _ _ hS hsup
    rw [hst]
    rw [Adjudicator.mode_eq] at hmode
    cases hs : s.statusOf c with
    | «open» r =>
      rw [hs] at hmode
      rcases hmode with ⟨-, hr⟩ | ⟨hm, -⟩
      · simp only [ChannelStatus.turnNumRecord_open] at hr
        simp only [rk]; omega
      · cases hm
    | challenged r ch' =>
      rw [hs] at hmode hM
      rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
      · simp only [ChannelStatus.mode] at hm; split at hm <;> cases hm
      · simp only [ChannelStatus.turnNumRecord_challenged] at hr hM
        simp only [rk]; omega
    | finalized r f o =>
      rw [hs] at hmode
      rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
  · right; left
    have hlt' : cand.turnNum < M := C.turnLt _ _ hS hsup
    rw [hst]
    cases hs : s.statusOf c with
    | «open» r =>
      rw [hs] at hlt hM
      simp only [ChannelStatus.turnNumRecord_open] at hlt hM
      simp only [rk]; omega
    | challenged r ch' =>
      rw [hs] at hlt hM
      simp only [ChannelStatus.turnNumRecord_challenged] at hlt hM
      simp only [rk]; omega
    | finalized r f o =>
      rw [hs] at hopen
      exact absurd (by (simp? [ChannelStatus.mode] says simp only [ChannelStatus.mode])) hopen
  · right; right; rw [hst]; rfl
  · right; right
    rw [hst]
    cases s.statusOf c <;> rfl


/-- The goal: `c` is finalized with an outcome that pays `d` at least `x`. -/
def Goal {p : Participant} (c : FixedPart) (d : E) (x : Nat) (n : NetworkState E p) : Prop :=
  ∃ Ω, n.Finalized c Ω ∧ x ≤ share Ω d


/-- `K` at the end of a round from `n`, with a rank below `n`'s, gives `TI`. -/
theorem K.toTI {apps : Apps E} {p : Participant} {ε : Time} {c : FixedPart} {d : E} {x Th M : Nat}
    {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n n1 : NetworkState E p} {R Kb : Nat}
    {S : ChannelStatus E} (hK : K apps c d x Th M sent0 proof0 n R Kb S n1)
    (hdur : 2 * ε ≤ c.challengeDuration) (hbound : n1.chain.now < n.chain.now + ε)
    (hne : n1.chain.statusOf c ≠ n.chain.statusOf c) : TI apps ε c d x Th M sent0 proof0 n1 := by
  refine ⟨hK.recvU, hK.sent, hK.held0, hK.openW, hK.chPay, hK.finPay, hK.recLt, fun t ch hc ht => ?_⟩
  rcases hK.lowK t ch hc ht with h0 | h6
  · exact absurd h0 hne
  · have : n1.chain.now + ε ≤ n.chain.now + 2 * ε := by
      have := Nat.add_le_add_right (le_of_lt hbound) ε
      rw [Nat.add_assoc, ← Nat.two_mul] at this
      exact this
    exact le_trans this (le_trans (Nat.add_le_add_left hdur _) h6)


/-- The round of a challenge by `p`: from a round-start state `n` with `TI`,
    `p` challenges `c` with a support `P` of `cand` that it holds. If the
    status is still `n`'s when the call lands, the call succeeds and lowers
    the rank (`hok`). At the end of the round, the rank is lower and `TI`
    holds again. -/
theorem challenge_round {apps : Apps E} {p : Participant} {T : Threat E p} {c : FixedPart} {d : E}
    {x Th M : Nat} {sent0 : List (SignedState E)} {proof0 : SupportProof E}
    (C : Ctx apps p c d x Th M sent0) (A : Assumptions apps p T)
    (hdur : 2 * T.ε ≤ c.challengeDuration) {n n1 : NetworkState E p}
    (hI : TI apps T.ε c d x Th M sent0 proof0 n) {P : SupportProof E} {cand : State E}
    (hH : ∀ ss ∈ P, n.Holds ss)
    (hok : ∀ s : Adjudicator E, s.statusOf c = n.chain.statusOf c → s.now < n.chain.now + T.ε →
      ∃ s', s.apply apps p (.challenge c P cand) = some s' ∧
        rk M (s'.statusOf c) < rk M (n.chain.statusOf c))
    (hpos : 0 < rk M (n.chain.statusOf c))
    (hround : T.Round apps (HonestMove.chain (.challenge c P cand)) n n1) :
    TI apps T.ε c d x Th M sent0 proof0 n1 ∧
      rk M (n1.chain.statusOf c) < rk M (n.chain.statusOf c) := by
  have hbound : n1.chain.now < n.chain.now + T.ε := hround.2
  have hE0 : n.chain.now + T.ε ≤ n.chain.now + c.challengeDuration :=
    Nat.add_le_add_left (le_trans (Nat.le_mul_of_pos_left T.ε (by decide)) hdur) _
  obtain ⟨na, hA, hB⟩ := Threat.Round.single hround
  have hnaend : na.chain.now ≤ n1.chain.now :=
    le_trans (NetworkState.applyAdv_now_le apps na _) hB.now_le
  have hnow_a : na.chain.now < n.chain.now + T.ε := lt_of_le_of_lt hnaend hbound
  have hKa := Threat.RoundSeq.nil_invariant hA
      (K.stepInv (R := (n.chain.statusOf c).turnNumRecord) C A.toBounds hE0 hnow_a hI.chLow
        ⟨hpos, le_refl _⟩).noLand hI.toK
  have hHa : ∀ ss ∈ P, na.Holds ss := fun ss hss =>
    NetworkState.Holds.mono (by rw [hKa.sent, hI.sent]) hKa.recv0 (hH ss hss)
  have hUa : ∀ ss ∈ (Op.challenge c P cand).proofStates, na.Unforged ss := fun ss hss =>
    (hHa ss hss).unforged hKa.recvU
  have hSa : SignedIn sent0 p (Op.challenge c P cand).proofStates := fun ss hss hps => by
    obtain ⟨s, hs, hse⟩ := (hUa ss hss).1 hps
    exact ⟨s, by rw [← hKa.sent]; exact hs, hse⟩
  -- after the land, the rank is below `n`'s
  have hKL : K apps c d x Th M sent0 proof0 n (n.chain.statusOf c).turnNumRecord
      (rk M (n.chain.statusOf c)) (.finalized 0 cand.outcome cand.outcome)
      (na.applyAdv apps (.land (.challenge c P cand))) := by
    have hK' := (K.stepInv (R := (n.chain.statusOf c).turnNumRecord) C A.toBounds hE0 hnow_a
      hI.chLow ⟨hpos, le_refl _⟩).land (le_refl _) hUa hKa
    have hlt : rk M ((na.applyAdv apps (.land (.challenge c P cand))).chain.statusOf c) <
        rk M (n.chain.statusOf c) := by
      cases happ : na.chain.apply apps p (.challenge c P cand) with
      | none =>
        rw [NetworkState.applyAdv_land_none apps happ]
        rcases hKa.prog with h | h
        · exact h
        · obtain ⟨s', hs', -⟩ := hok na.chain h hnow_a
          rw [happ] at hs'; cases hs'
      | some s' =>
        rw [NetworkState.applyAdv_land_some apps happ]
        show rk M (s'.statusOf c) < rk M (n.chain.statusOf c)
        rcases hKa.prog with h | h
        · rcases rank_step C happ hSa hKa.recLt with heq | hlt | h0
          · rw [heq]; exact h
          · exact lt_trans hlt h
          · rw [h0]; exact hpos
        · obtain ⟨s'', hs'', hlt⟩ := hok na.chain h hnow_a
          rw [happ] at hs''
          obtain rfl := Option.some.inj hs''
          exact hlt
    exact hK'.reS hlt hK'.recR
  have hK1 := Threat.RoundSeq.nil_invariant hB
      (K.stepInv C A.toBounds hE0 hbound hI.chLow ⟨hpos, Nat.zero_le _⟩).noLand hKL
  have hlt1 : rk M (n1.chain.statusOf c) < rk M (n.chain.statusOf c) := by
    rcases hK1.prog with h | h
    · exact h
    · rw [h]; exact hpos
  exact ⟨hK1.toTI hdur hbound (fun h => by rw [h] at hlt1; exact lt_irrefl _ hlt1), hlt1⟩


open Classical in
/-- **The exit strategy** of `p` for `c`, with the held support `proof0` of
    `cand0`: challenge an open `c` with a held support at a turn no lower than
    the recorded one, answer a challenge below the turn of `cand0` with
    `proof0`, and wait for a challenge at that turn or above to end. -/
noncomputable def exitStrategy (apps : Apps E) {p : Participant} (c : FixedPart)
    (proof0 : SupportProof E) (cand0 : State E) : Strategy E p := fun n =>
  match n.chain.statusOf c with
  | .open t =>
    if h : ∃ P cand, (∀ ss ∈ P, n.Holds ss) ∧ (apps c.appDef).supports c P cand = true ∧
        cand.channel = c ∧ t ≤ cand.turnNum then
      .chain (.challenge c h.choose h.choose_spec.choose)
    else .chain (.challenge c proof0 cand0)
  | .challenged t ch =>
    if t < cand0.turnNum then .chain (.challenge c proof0 cand0) else .wait (ch.deadline - n.chain.now)
  | .finalized .. => .wait 1

/-- The held support of the exit strategy: `proof0` supports `cand0`, a
    state of `c` at the turn `Th`. -/
structure Held0 (apps : Apps E) (c : FixedPart) (Th : Nat) (proof0 : SupportProof E)
    (cand0 : State E) : Prop where
  sup : (apps c.appDef).supports c proof0 cand0 = true
  ch : cand0.channel = c
  turn : cand0.turnNum = Th

/-- The exit strategy reaches the goal from every state with `TI`: each
    round lowers the rank `rk` or reaches the goal. -/
theorem exit_by {apps : Apps E} {p : Participant} {T : Threat E p} {c : FixedPart} {d : E}
    {x Th M : Nat} {sent0 : List (SignedState E)} {proof0 : SupportProof E} {cand0 : State E}
    (C : Ctx apps p c d x Th M sent0) (A : Assumptions apps p T)
    (hdur : 2 * T.ε ≤ c.challengeDuration) (H : Held0 apps c Th proof0 cand0) {net : NetworkState E p}
    (hI : TI apps T.ε c d x Th M sent0 proof0 net) :
    UnbeatableBy apps T (exitStrategy apps c proof0 cand0) (Goal c d x) net := by
  obtain ⟨hsup0, hch0, hturn0⟩ := H
  have hp := C.hp
  have challenge_apply : ∀ {s : Adjudicator E} {P : SupportProof E} {cand : State E},
      (apps c.appDef).supports c P cand = true → cand.channel = c →
      ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ cand.turnNum) ∨
        (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < cand.turnNum)) →
      s.apply apps p (.challenge c P cand) =
        some (s.setStatus c (.challenged cand.turnNum ⟨cand, s.now + c.challengeDuration⟩)) := by
    intro s P cand hsup hcc hmode
    show s.challenge apps p c P cand = _
    unfold Adjudicator.challenge
    rw [if_pos ⟨hp, hsup, hcc, hmode⟩]
  have takeout : ∀ μ (n : NetworkState E p), TI apps T.ε c d x Th M sent0 proof0 n →
      rk M (n.chain.statusOf c) ≤ μ → UnbeatableBy apps T (exitStrategy apps c proof0 cand0) (Goal c d x) n := by
    intro μ
    induction μ using Nat.strong_induction_on with
    | _ μ ih =>
    intro n hI hμ
    -- one challenge round, then the induction
    have hround : ∀ {P : SupportProof E} {cand : State E},
        exitStrategy apps c proof0 cand0 n = .chain (.challenge c P cand) → (∀ ss ∈ P, n.Holds ss) →
        (∀ s : Adjudicator E, s.statusOf c = n.chain.statusOf c → s.now < n.chain.now + T.ε →
          ∃ s', s.apply apps p (.challenge c P cand) = some s' ∧
            rk M (s'.statusOf c) < rk M (n.chain.statusOf c)) →
        0 < rk M (n.chain.statusOf c) →
        UnbeatableBy apps T (exitStrategy apps c proof0 cand0) (Goal c d x) n := by
      intro P cand hσ hH hok hpos
      refine .move (by rw [hσ]; exact (HonestMove.Feasible_chain _ _ _).2 hH) fun n1 hr => ?_
      rw [hσ] at hr ⊢
      rw [NetworkState.applyHonest_chain]
      obtain ⟨hI1, hlt⟩ := challenge_round C A hdur hI hH hok hpos hr
      exact ih _ (lt_of_lt_of_le hlt hμ) n1 hI1 (le_refl _)
    cases hs : n.chain.statusOf c with
    | finalized t f o =>
      apply UnbeatableBy.done
      refine ⟨f, ?_, hI.finPay t f o hs⟩
      simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hs,
        ChannelStatus.finalizedWith_finalized]
    | «open» t =>
      have hpos : 0 < rk M (n.chain.statusOf c) := by rw [hs]; simp only [rk]; omega
      have hok : ∀ {P : SupportProof E} {cand : State E}, (apps c.appDef).supports c P cand = true →
          cand.channel = c → t ≤ cand.turnNum →
          ∀ s : Adjudicator E, s.statusOf c = n.chain.statusOf c → s.now < n.chain.now + T.ε →
            ∃ s', s.apply apps p (.challenge c P cand) = some s' ∧
              rk M (s'.statusOf c) < rk M (n.chain.statusOf c) := by
        intro P cand hsup hcc hle s hss _
        rw [hs] at hss ⊢
        refine ⟨_, challenge_apply hsup hcc (Or.inl ⟨by rw [Adjudicator.mode_eq, hss]; rfl,
          by rw [hss]; exact hle⟩), ?_⟩
        simp only [Adjudicator.statusOf_setStatus, if_true, rk]
        omega
      have hex : ∃ P cand, (∀ ss ∈ P, n.Holds ss) ∧ (apps c.appDef).supports c P cand = true ∧
          cand.channel = c ∧ t ≤ cand.turnNum := by
        rcases hI.openW t hs with hle | h
        · exact ⟨proof0, cand0, hI.held0, hsup0, hch0, by rw [hturn0]; exact hle⟩
        · exact h
      obtain ⟨hH, hsup, hcc, hle⟩ := hex.choose_spec.choose_spec
      exact hround (by simp only [exitStrategy, hs, dif_pos hex]) hH (hok hsup hcc hle) hpos
    | challenged t ch =>
      have hpos : 0 < rk M (n.chain.statusOf c) := by rw [hs]; simp only [rk]; omega
      by_cases hlow : t < Th
      · -- answer with the own support at `Th`
        refine hround (P := proof0) (cand := cand0)
          (by simp only [exitStrategy, hs, if_pos (show t < cand0.turnNum by rw [hturn0]; exact hlow)])
          hI.held0 (fun s hss hsnow => ?_) hpos
        rw [hs] at hss ⊢
        have hdl := hI.chLow t ch hs hlow
        have hmode : s.mode c = .challenge := by
          rw [Adjudicator.mode_eq, hss]
          simp only [ChannelStatus.mode, if_neg (not_le.mpr (lt_of_lt_of_le hsnow hdl))]
        refine ⟨_, challenge_apply hsup0 hch0 (Or.inr ⟨hmode, by rw [hss, hturn0]; exact hlow⟩), ?_⟩
        have hThM := C.thLt
        simp only [Adjudicator.statusOf_setStatus, if_true, rk, hturn0]
        omega
      · -- wait for the challenge to end
        have hpay := hI.chPay t ch hs (by omega)
        by_cases hexp : ch.deadline ≤ n.chain.now
        · apply UnbeatableBy.done
          refine ⟨ch.state.outcome, ?_, hpay⟩
          simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hs,
            ChannelStatus.finalizedWith_challenged, if_pos hexp]
        · have hσ : exitStrategy apps c proof0 cand0 n = .wait (ch.deadline - n.chain.now) := by
            simp only [exitStrategy, hs, if_neg (show ¬ t < cand0.turnNum by rw [hturn0]; exact hlow)]
          refine .move (by rw [hσ]; trivial) fun n1 hr => ?_
          rw [hσ] at hr ⊢
          have hbound : n1.chain.now < n.chain.now + T.ε := hr.2
          have hE0 : n.chain.now + T.ε ≤ n.chain.now + c.challengeDuration :=
            Nat.add_le_add_left (le_trans (Nat.le_mul_of_pos_left T.ε (by decide)) hdur) _
          have hK1 := Threat.RoundSeq.nil_invariant hr.1
            (K.stepInv (R := t) C A.toBounds hE0 hbound hI.chLow ⟨hpos, le_refl _⟩).noLand
            (by have := hI.toK; rw [hs] at this ⊢; exact this)
          have hTI : TI apps T.ε c d x Th M sent0 proof0
              (n1.applyHonest (.wait (ch.deadline - n.chain.now))) := by
            refine ⟨fun r hr => (hK1.recvU r hr).of_sent rfl, hK1.sent,
              fun ss hss => NetworkState.Holds.mono (net := n1) rfl (fun _ h => h) (hK1.held0 ss hss),
              ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]
            · intro t' ht'
              rcases hK1.openW t' ht' with h1 | ⟨pr, cd, hH, hsu, hcc, hle⟩
              · exact Or.inl h1
              · exact Or.inr ⟨pr, cd, fun x hx => NetworkState.Holds.mono (net := n1) rfl (fun _ h => h)
                  (hH x hx), hsu, hcc, hle⟩
            · exact hK1.chPay
            · exact hK1.finPay
            · exact hK1.recLt
            · intro t' ch' hc' hlt'
              rcases hK1.recR with h1 | ⟨_, _, _, hf⟩
              · rw [hc'] at h1
                simp only [ChannelStatus.turnNumRecord_challenged] at h1
                omega
              · rw [hf] at hc'; cases hc'
          rcases hK1.prog with hlt | heq
          · refine ih _ (lt_of_lt_of_le ?_ hμ) _ hTI (le_refl _)
            simpa? [NetworkState.applyHonest] using hlt says
              simpa only [NetworkState.applyHonest, Adjudicator.tick_statusOf] using hlt
          · apply UnbeatableBy.done
            refine ⟨ch.state.outcome, ?_, hpay⟩
            have hle : n.chain.now ≤ n1.chain.now := hr.1.now_le
            have key : ∀ a b k : Nat, a ≤ b → k ≤ b + (k - a) := fun a b k h => by omega
            have hge : ch.deadline ≤ n1.chain.now + (ch.deadline - n.chain.now) := key _ _ _ hle
            simp only [NetworkState.applyHonest, NetworkState.Finalized, FixedPart.address_eq,
              Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, heq, hs, Adjudicator.tick_now,
              ChannelStatus.finalizedWith_challenged, if_pos hge]

  exact takeout _ net hI (le_refl _)

/-- An app whose supports from the held turn on pay `p` at least `x` lets `p`
    take out `x`. **The take-out strategy:** from a state with `TI`, `p`
    challenges an open `c` with a support it holds, answers a challenge below
    `Th` with its own support at `Th`, and waits for a challenge at `Th` or
    above to end. Each round lowers the rank `rk` or reaches the goal. -/
theorem canTakeOut_of {apps : Apps E} {p : Participant} {T : Threat E p}
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T) (c : TimedChannel T.ε)
    {d : E} {x : Coins} (hp : p ∈ (c : FixedPart).participants)
    (hsw : (apps (c : FixedPart).appDef).SupportWindow)
    (hpay : ∀ Th proof cand, SentBelow net.state.sent c d x Th → SignedIn net.state.sent p proof →
      (apps (c : FixedPart).appDef).supports c proof cand = true → Th ≤ cand.turnNum →
      x ≤ share cand.outcome d)
    (hH : HoldsShare apps net.state c d x) : CanTakeOut apps T c d x net.state := by
  have hU0 := Nitro.participant_received_unforged A.toBounds net
  obtain ⟨proof0, cand0, hH0, hsup0, hch0, -, hB, t0, hst, hle⟩ := hH
  obtain ⟨net, hr⟩ := net
  obtain ⟨c, hdur⟩ := c
  replace hdur : 2 * T.ε ≤ c.challengeDuration := hdur
  dsimp only at hp hsw hpay hH0 hsup0 hch0 hB hst hU0 ⊢
  obtain ⟨Th, hturn0⟩ : ∃ Th, cand0.turnNum = Th := ⟨_, rfl⟩
  rw [hturn0] at hB hle
  obtain ⟨sent0, hs0⟩ : ∃ sent0, net.sent = sent0 := ⟨_, rfl⟩
  rw [hs0] at hB hpay
  have hn : 0 < c.n := List.length_pos_of_mem hp
  obtain ⟨M, hM⟩ : ∃ M, Th + c.n = M := ⟨_, rfl⟩
  have C : Ctx apps p c d x Th M sent0 := by
    refine ⟨hp, fun s hs hc => by have := (hB s hs hc).1; omega, by omega, fun proof cand hS h => ?_,
      fun pr cd hS hsu _ hTh => hpay _ pr cd hB hS hsu hTh, fun ss hcp hs => ?_⟩
    · obtain ⟨ss, hss, hps, hch, -, hlt⟩ := hsw c proof cand h p hp
      obtain ⟨s, hs, hse⟩ := hS ss hss hps
      have := (hB s hs (by rw [hse]; exact hch)).1
      rw [hse] at this
      omega
    · obtain ⟨s, hs, hse⟩ := hs
      have := (hB s hs (by rw [hse]; exact hcp.1)).2 (Or.inr (by rw [hse]; exact hcp.2.1))
      rwa [hse] at this
  have hI : TI apps T.ε c d x Th M sent0 proof0 net := by
    refine ⟨hU0, hs0, hH0, fun t' ht' => (by rw [hst] at ht'; cases ht'; exact Or.inl hle),
      fun _ _ h => (by rw [hst] at h; cases h), fun _ _ _ h => (by rw [hst] at h; cases h),
      (by rw [hst]; simp only [ChannelStatus.turnNumRecord_open]; omega),
      fun _ _ h => (by rw [hst] at h; cases h)⟩
  exact (exit_by C A hdur ⟨hsup0, hch0, hturn0⟩ hI).sound.2 _ fun _ _ h => h

/-- `p`'s position for the exit strategy: `p` holds a support of `cand`, a
    state of `c` at a turn no lower than the turn the chain records, and a
    running challenge of `c` ends no sooner than `ε` from now. -/
structure ExitReady (apps : Apps E) {p : Participant} (T : Threat E p) (net : NetworkState E p)
    (c : FixedPart) (proof : SupportProof E) (cand : State E) : Prop where
  held : ∀ ss ∈ proof, net.Holds ss
  supports : (apps c.appDef).supports c proof cand = true
  channel : cand.channel = c
  record : (net.chain.statusOf c).turnNumRecord ≤ cand.turnNum
  pending : net.DeadlineAfter c T.ε

/-- The ForceMove rules and the consensus rules meet `Rules.SupportWindow`. -/
theorem supportWindow_of_rules {apps : Apps E} {a : AppId}
    (h : (∃ vt, apps a = forceMoveRules vt) ∨ apps a = consensusRules) : (apps a).SupportWindow := by
  rcases h with ⟨vt, h⟩ | h <;> rw [h]
  · exact forceMoveRules_supportWindow vt
  · exact consensusRules_supportWindow

/-- **The exit strategy finalizes `c`** from every reachable state where
    `p` is ready to exit (`ExitReady`). -/
theorem exit_finalizes [Inhabited E] {apps : Apps E} {p : Participant} {T : Threat E p}
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T) (c : TimedChannel T.ε)
    (hp : p ∈ (c : FixedPart).participants)
    (hrules : (∃ vt, apps (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps (c : FixedPart).appDef = consensusRules)
    {proof : SupportProof E} {cand : State E} (R : ExitReady apps T net.state c proof cand) :
    UnbeatableBy apps T (exitStrategy apps c proof cand) (Goal c default 0) net.state := by
  have hsw := supportWindow_of_rules hrules
  have hU0 := Nitro.participant_received_unforged A.toBounds net
  obtain ⟨net, _hr⟩ := net
  obtain ⟨c, hdur⟩ := c
  dsimp only at hp hsw hU0 R ⊢
  obtain ⟨S, hS⟩ : ∃ S, ∀ s ∈ net.sent, s.state.turnNum ≤ S :=
    ⟨(net.sent.map (·.state.turnNum)).sum, fun s hs =>
      List.le_sum_of_mem (List.mem_map_of_mem (f := (·.state.turnNum)) hs)⟩
  have hn : 0 < c.n := List.length_pos_of_mem hp
  have C : Ctx apps p c default 0 cand.turnNum (max cand.turnNum S + c.n) net.sent := by
    refine ⟨hp, fun s hs _ => by have := hS s hs; omega, by omega, fun proof' cand' hSg h => ?_,
      fun _ _ _ _ _ _ => Nat.zero_le _, fun _ _ _ => Nat.zero_le _⟩
    obtain ⟨ss, hss, hps, -, -, hlt⟩ := hsw c proof' cand' h p hp
    obtain ⟨s, hs, hse⟩ := hSg ss hss hps
    have := hS s hs
    rw [hse] at this
    omega
  refine exit_by C A hdur ⟨R.supports, R.channel, rfl⟩ ⟨hU0, rfl, R.held, fun t ht => .inl ?_,
    fun _ _ _ _ => Nat.zero_le _, fun _ _ _ _ => Nat.zero_le _, ?_, fun t ch h _ => R.pending t ch h⟩
  · have := R.record
    rwa [ht, ChannelStatus.turnNumRecord_open] at this
  · have := R.record
    omega

/-- Nitro-24. Nitro:653-656: "For any participant, p, in a channel, χ, exactly one
    of the following statements is true at a given point in time: 1. p has at
    least one finalizable outcome. 2. p has at least two enabled outcomes."
    Design decision 2026-11-02: the enabled outcomes are measured against
    `p`'s own strategy, the exit strategy (`EnabledBy`, `exitStrategy`).
    Measured against every strategy at once (`Enabled`), each outcome can
    need a different strategy to prevent it, and the claim fails
    (`docs/counterexamples/proposal_escape.lean`). The claim has the paper's
    scope, a ForceMove app or the consensus app (Nitro:633 "for a ForceMove
    channel"; Nitro:662-664). `p` holds a support of `c` at least as new as
    the chain's record, and a running challenge ends no sooner than `ε`
    (`ExitReady`; `docs/counterexamples/pending_deadline.lean`). -/
theorem _root_.ArmadaLean.Nitro.finalizable_or_two_enabled [Inhabited E] (apps : Apps E)
    {p : Participant} (T : Threat E p) (A : Assumptions apps p T)
    (net : Nitro.ReachableParticipant apps T) (c : TimedChannel T.ε)
    (hrules : (∃ vt, apps (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps (c : FixedPart).appDef = consensusRules)
    (hp : p ∈ (c : FixedPart).participants) (proof : SupportProof E) (cand : State E)
    (R : ExitReady apps T net.state c proof cand) :
    (∃ Ω, Finalizable apps T (c : FixedPart) Ω net.state) ∨
    ∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧
      EnabledBy apps T (exitStrategy apps c proof cand) (c : FixedPart) Ω1 net.state ∧
      EnabledBy apps T (exitStrategy apps c proof cand) (c : FixedPart) Ω2 net.state := by
  obtain ⟨⟨n, hrun, Ω, hf, -⟩, hU⟩ := (exit_finalizes A net c hp hrules R).sound
  by_cases hall : ∀ Ω', EnabledBy apps T (exitStrategy apps c proof cand) (c : FixedPart) Ω' net.state →
      Ω' = Ω
  · exact .inl ⟨Ω, hU _ fun n' hr ⟨Ω', hf', _⟩ => hall Ω' ⟨n', hr, hf'⟩ ▸ hf'⟩
  · push Not at hall
    obtain ⟨Ω', hen, hne⟩ := hall
    exact .inr ⟨Ω', Ω, hne, hen, n, hrun, hf⟩

/-- Nitro-24. Nitro:657-658: "if a participant has only enabled a single outcome,
    that outcome must be finalizable for them." Design decision 2026-11-02:
    the enabled outcomes are measured against `p`'s own strategy, the exit
    strategy (`EnabledBy`, `exitStrategy`); against every strategy at once
    the claim fails (`docs/counterexamples/proposal_escape.lean`). The scope
    and `ExitReady` are those of `finalizable_or_two_enabled`. -/
theorem _root_.ArmadaLean.Nitro.single_enabled_is_finalizable [Inhabited E] (apps : Apps E)
    {p : Participant} (T : Threat E p) (A : Assumptions apps p T)
    (net : Nitro.ReachableParticipant apps T) (c : TimedChannel T.ε)
    (hrules : (∃ vt, apps (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps (c : FixedPart).appDef = consensusRules)
    (hp : p ∈ (c : FixedPart).participants) (proof : SupportProof E) (cand : State E)
    (R : ExitReady apps T net.state c proof cand) (Ω : Outcome E)
    (huniq : ∀ Ω', EnabledBy apps T (exitStrategy apps c proof cand) (c : FixedPart) Ω' net.state →
      Ω' = Ω) :
    Finalizable apps T (c : FixedPart) Ω net.state :=
  (exit_finalizes A net c hp hrules R).sound.2 _ fun n hr ⟨Ω', hf, _⟩ => huniq Ω' ⟨n, hr, hf⟩ ▸ hf


/-- **ForceMove apps whose game library takes nothing from a non-mover are
    IR.** Every ForceMove support of `c` at a turn from `Th` on pays `p` at
    least `x`: the run holds a move of `p` in the window of `Th`, which pays
    `p` at least `x`, and no later move of another participant reduces it. -/
theorem forceMove_IR {apps : Apps E} {a : AppId} {vt : State E → State E → Bool}
    {dest : Participant → E} (ha : apps a = forceMoveRules vt) (hNT : NoTakeFromNonMover vt dest) :
    AppIR apps a dest := by
  refine ⟨fun {p} T A net c x hca hp hH => ?_⟩
  obtain ⟨c, hdur⟩ := c
  dsimp only at hca hp
  have happ : apps c.appDef = forceMoveRules vt := by rw [hca, ha]
  refine canTakeOut_of A net ⟨c, hdur⟩ hp (by rw [happ]; exact forceMoveRules_supportWindow vt)
    (fun Th proof cand hB hS hsu hTh => ?_) hH
  dsimp only at hB hsu
  rw [happ] at hsu
  obtain ⟨hlen, hstep, ml, hml, hmls⟩ := forceMove_supports_valid_run vt c proof cand hsu
  have hkeep := forceMove_conclude_keeps_outcome vt c proof cand hsu
  have h' := hsu
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨-, hhead⟩, -⟩, hchAll⟩, -⟩ := h'
  have hn : 0 < c.n := List.length_pos_of_mem hp
  obtain ⟨m0, hm0⟩ : ∃ m0, proof[0]? = some m0 := by
    cases proof with
    | nil => (simp? at hlen says simp only [List.length_nil] at hlen); omega
    | cons a _ => exact ⟨a, rfl⟩
  -- the turns of the run
  have hind : ∀ j, j < proof.length → ∃ m, proof[j]? = some m ∧ m.state.turnNum = m0.state.turnNum + j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨m0, hm0, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨m, hm, ht⟩ := ih (by omega)
      obtain ⟨m', hm'⟩ : ∃ m', proof[j + 1]? = some m' := ⟨_, List.getElem?_eq_getElem hj⟩
      obtain ⟨-, ht', -, -⟩ := hstep j m m' hm hm'
      exact ⟨m', hm', by omega⟩
  -- a state of `p` in the window pays `p` at least `x`
  have hpstate : ∀ (j : Nat) (m : SignedState E), proof[j]? = some m → p ∈ m.signers →
      x ≤ share m.state.outcome (dest p) := by
    intro j m hm hpm
    obtain ⟨s, hs, hse⟩ := hS m (List.mem_of_getElem? hm) hpm
    have hc : s.state.channel = c := by rw [hse]; exact hchAll m (List.mem_of_getElem? hm)
    obtain ⟨hle, hpay⟩ := hB s hs hc
    rw [← hse]
    refine hpay (Or.inl ?_)
    have hj : j < proof.length := (List.getElem?_eq_some_iff.mp hm).1
    obtain ⟨m', hm', ht'⟩ := hind j hj
    obtain rfl := Option.some.inj (hm.symm.trans hm')
    obtain ⟨ml', hml', htl⟩ := hind (proof.length - 1) (by omega)
    rw [List.getLast?_eq_getElem?] at hml
    obtain rfl := Option.some.inj (hml.symm.trans hml')
    rw [hse, ht']
    rw [← hmls, htl] at hTh
    omega
  -- the mover of `p`'s turn in the run
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem?.mp hp |> fun ⟨k, hk⟩ =>
    (⟨k, (List.getElem?_eq_some_iff.mp hk).1, hk⟩ : ∃ k, k < c.n ∧ c.participants[k]? = some p)
  obtain ⟨i, hi, hik⟩ := turn_mod_exists c.n m0.state.turnNum k hn hk
  obtain ⟨mi, hmi, hti⟩ := hind i (by omega)
  have hmimv : mi.ByMover := by
    cases i with
    | zero =>
      rw [hm0] at hmi; obtain rfl := Option.some.inj hmi
      simp only [List.head?_eq_getElem?, hm0, Option.all_some] at hhead
      exact (SignedState.byMover_iff _).1 hhead
    | succ i =>
      obtain ⟨mprev, hmprev⟩ : ∃ mp, proof[i]? = some mp := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact (hstep i mprev mi hmprev hmi).2.2.1
  have hmip : p ∈ mi.signers := by
    obtain ⟨w, hw, hwm⟩ := hmimv
    have hc : mi.state.channel = c := hchAll mi (List.mem_of_getElem? hmi)
    have : mi.state.mover = some p := by
      unfold State.mover; rw [hc, hti, hik]; exact hkp
    rw [this] at hw; obtain rfl := Option.some.inj hw; exact hwm
  -- forward along the run
  have hfwd : ∀ j, i + j < proof.length → ∃ m, proof[i + j]? = some m ∧
      x ≤ share m.state.outcome (dest p) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨mi, hmi, hpstate i mi hmi hmip⟩
    | succ j ih =>
      intro hj
      obtain ⟨m, hm, hx⟩ := ih (by omega)
      obtain ⟨m', hm'⟩ : ∃ m', proof[i + j + 1]? = some m' := ⟨_, List.getElem?_eq_getElem hj⟩
      refine ⟨m', hm', ?_⟩
      obtain ⟨-, -, hmv', hvt⟩ := hstep (i + j) m m' hm hm'
      have hfin := (hkeep (i + j) m m' hm hm').1
      cases hf : m'.state.isFinal with
      | true => rw [hfin hf]; exact hx
      | false =>
        by_cases hmov : m'.state.mover = some p
        · obtain ⟨w, hw, hwm⟩ := hmv'
          rw [hmov] at hw; obtain rfl := Option.some.inj hw
          exact hpstate (i + j + 1) m' hm' hwm
        · exact le_trans hx (hNT _ _ (hvt hf) p hmov)
  obtain ⟨m, hm, hx⟩ := hfwd (proof.length - 1 - i) (by omega)
  have : i + (proof.length - 1 - i) = proof.length - 1 := by omega
  rw [this, ← List.getLast?_eq_getElem?, hml] at hm
  obtain rfl := Option.some.inj hm
  rw [← hmls]; exact hx


/-- **The consensus app is IR.** Every consensus support of `c` at a turn
    from `Th` on pays `p` at least `x`: its one state is the candidate, and
    `p` signed it. -/
theorem consensus_IR {apps : Apps E} {a : AppId} {dest : Participant → E}
    (ha : apps a = consensusRules) : AppIR apps a dest := by
  refine ⟨fun {p} T A net c x hca hp hH => ?_⟩
  obtain ⟨c, hdur⟩ := c
  dsimp only at hca hp
  have happ : apps c.appDef = consensusRules := by rw [hca, ha]
  refine canTakeOut_of A net ⟨c, hdur⟩ hp (by rw [happ]; exact consensusRules_supportWindow)
    (fun Th proof cand hB hS hsu hTh => ?_) hH
  dsimp only at hB hsu
  rw [happ] at hsu
  match proof, hsu, hS with
  | [ss], h, hS =>
    simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hst, hch⟩, hall⟩ := h
    obtain ⟨s, hs, hse⟩ := hS ss (List.mem_singleton_self ss) (hall p (by rw [hch]; exact hp))
    obtain ⟨hle, hpay⟩ := hB s hs (by rw [hse]; exact hch)
    have hn : 0 < c.n := List.length_pos_of_mem hp
    rw [← hst, ← hse]
    refine hpay (Or.inl ?_)
    rw [hse, hst]; omega
  | [], h, _ => (simp? [consensusRules] at h says simp only [consensusRules, Bool.false_eq_true] at h)
  | _ :: _ :: _, h, _ =>
    (simp? [consensusRules] at h says simp only [consensusRules, Bool.false_eq_true] at h)

/-! ## IC, and desirable apps -/

/-- A valid run, with one more valid move after its last state `y`. -/
theorem validRun_snoc {vt : State E → State E → Bool} {y new : SignedState E}
    (hy : ∀ z, validMove vt z y = true → validMove vt y new = true) :
    ∀ (l : SupportProof E) (x : SignedState E), validRun vt (x :: l) = true →
      (x :: l).getLast? = some y → l ≠ [] → validRun vt (l ++ [new]) = true
  | [], _, _, _, hne => absurd rfl hne
  | [m], x, h, hl, _ => by
    simp only [validRun, Bool.and_true] at h
    rw [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    show validRun vt [m, new] = true
    simp only [validRun, Bool.and_true]
    exact hy x h
  | m :: m2 :: l, x, h, hl, _ => by
    rw [validRun, Bool.and_eq_true] at h
    have h2 := h.2
    have ih := validRun_snoc hy (m2 :: l) m h2 (by rw [List.getLast?_cons_cons] at hl; exact hl)
      (List.cons_ne_nil _ _)
    rw [validRun, Bool.and_eq_true] at h2
    rw [List.cons_append] at ih
    rw [List.cons_append, List.cons_append, validRun, Bool.and_eq_true]
    exact ⟨h2.1, ih⟩

/-- **A ForceMove app is IC** when its game library lets the mover keep
    the state of a valid move: from a supported non-final candidate, the
    mover of the next turn moves to the same outcome. -/
theorem forceMove_IC {vt : State E → State E → Bool} {dest : Participant → E}
    (hstay : ∀ s s', vt s s' = true → vt s' { s' with turnNum := s'.turnNum + 1 } = true)
    (a : AppId) : AppIC (fun _ => forceMoveRules vt) a dest := by
  refine ⟨fun c proof cand q _ hsup hc hfin hq _ => ?_⟩
  have hsup' := hsup
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsup'
  obtain ⟨⟨⟨⟨hlen, hhead⟩, hrun⟩, hch⟩, hlast⟩ := hsup'
  obtain ⟨mlast, hml, hmls⟩ := Option.map_eq_some_iff.1 hlast
  let new : SignedState E := ⟨{ cand with turnNum := cand.turnNum + 1 }, [q]⟩
  have hnewM : new.ByMover := ⟨q, hq, List.mem_singleton_self q⟩
  have hstep : ∀ z, validMove vt z mlast = true → validMove vt mlast new = true := by
    intro z hz
    obtain ⟨-, -, hzv, -⟩ := (validMove_iff vt z mlast).1 hz
    refine (validMove_iff vt mlast new).2 ⟨⟨?_, ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun _ => ?_, hnewM⟩
    · show cand.channel = mlast.state.channel
      rw [hmls]
    · show cand.turnNum + 1 = mlast.state.turnNum + 1
      rw [hmls]
    · exact absurd h (by rw [show new.state.isFinal = cand.isFinal from rfl, hfin]; decide)
    · rw [hmls, hfin] at h; cases h
    · have hv := hzv (by rw [hmls]; exact hfin)
      rw [hmls] at hv
      show vt mlast.state new.state = true
      rw [hmls]
      exact hstay _ _ hv
  match proof, hlen, hhead, hrun, hch, hml with
  | [], _, _, _, _, hml => (simp? at hml says simp only [List.getLast?_nil, reduceCtorEq] at hml)
  | m0 :: rest, hlen, hhead, hrun, hch, hml =>
    refine ⟨rest ++ [new], new.state, ⟨?_, hc, rfl, hfin, fun ss hss => ?_⟩, le_refl _⟩
    · simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fun m hm => ?_⟩, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        simp only [List.length_cons] at hlen
        exact hlen
      · cases rest with
        | nil => exact (SignedState.byMover_iff new).2 hnewM
        | cons m1 r =>
          rw [validRun, Bool.and_eq_true] at hrun
          exact (SignedState.byMover_iff m1).2 ((validMove_iff vt m0 m1).1 hrun.1).2.2.2
      · cases rest with
        | nil => rfl
        | cons m1 r => exact validRun_snoc hstep (m1 :: r) m0 hrun hml (List.cons_ne_nil _ _)
      · rcases List.mem_append.1 hm with hm | hm
        · exact hch m (List.mem_cons_of_mem _ hm)
        · rw [List.mem_singleton.1 hm]; exact hc
      · rw [List.getLast?_append, List.getLast?_singleton]
        rfl
    · rcases List.mem_append.1 hss with hss | hss
      · exact Or.inl (List.mem_cons_of_mem _ hss)
      · exact Or.inr (by rw [List.mem_singleton.1 hss])

/-- **The consensus app is IC**: the next state, with the same outcome and
    every signature, is a move by the rules. -/
theorem consensus_IC {dest : Participant → E} (a : AppId) :
    AppIC (fun _ => consensusRules) a dest := by
  refine ⟨fun c proof cand q _ _ hc hfin _ _ => ?_⟩
  let cand' : State E := { cand with turnNum := cand.turnNum + 1 }
  refine ⟨[⟨cand', c.participants⟩], cand', ⟨?_, hc, rfl, hfin, fun ss hss => ?_⟩, le_refl _⟩
  · show (decide (cand' = cand') && decide (cand'.channel = c) &&
      decide (SignedState.ByAll ⟨cand', c.participants⟩)) = true
    simp only [decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hc, fun x hx => by
      have hx' : x ∈ cand.channel.participants := hx
      rwa [hc] at hx'⟩
  · exact Or.inr (by rw [List.mem_singleton.1 hss])

/-- The amount owed to `d` does not fall when the destinations stay and no
    entry of `d` falls. -/
theorem owed_le_of_entrywise {o o' : Allocation E} (hd : o'.map Entry.dest = o.map Entry.dest)
    {d : Address E} (h : ∀ (i : Nat) (e e' : Entry E), o[i]? = some e → o'[i]? = some e' →
      e.dest = d → e.amount ≤ e'.amount) : o.owed d ≤ o'.owed d := by
  induction o generalizing o' with
  | nil =>
    simp only [Allocation.owed, Allocation.find, List.find?_nil, Option.map_none, Option.getD_none]
    exact Nat.zero_le _
  | cons e r ih =>
    cases o' with
    | nil => simp at hd
    | cons e' r' =>
      simp only [List.map_cons, List.cons.injEq] at hd
      obtain ⟨hde, hdr⟩ := hd
      by_cases hed : e.dest = d
      · have he' : e'.dest = d := hde.trans hed
        simp only [Allocation.owed, Allocation.find, List.find?_cons, hed, he', decide_true,
          Option.map_some, Option.getD_some]
        exact h 0 e e' rfl rfl hed
      · have he' : ¬ e'.dest = d := by rw [hde]; exact hed
        simp only [Allocation.owed, Allocation.find, List.find?_cons, hed, he', decide_false]
        exact ih hdr (fun i x x' hx hx' => h (i + 1) x x' hx hx')

/-- The go-nitro payment rules take nothing from a non-mover. -/
theorem paymentRules_noTake {vt : State E → State E → Bool} {dest : Participant → E}
    (h : PaymentRules vt dest) : NoTakeFromNonMover vt dest := by
  intro s s' hv r hr
  obtain ⟨q, hq, hstep⟩ := (h.valid_iff s s').1 hv
  rcases hstep with heq | ⟨hd, -, -, -, hlow⟩
  · rw [heq]
  · show s.outcome.entries.owed _ ≤ s'.outcome.entries.owed _
    refine owed_le_of_entrywise hd fun i e e' he he' hed => ?_
    by_contra hlt
    obtain ⟨-, hown⟩ := hlow i e e' he he' (Nat.lt_of_not_le hlt)
    exact hr (by rw [hq, hown r hed])

/-- **A ForceMove app conserves value** when every valid transition of its
    game library is a `ConservingStep` with the mover. A final move keeps
    the outcome (`ConclusionTransition`). -/
theorem forceMove_conserving {vt : State E → State E → Bool} {dest : Participant → E}
    (hv : ∀ s s' q, vt s s' = true → s'.mover = some q → ConservingStep dest q s.outcome s'.outcome)
    (a : AppId) : Conserving (fun _ => forceMoveRules vt) a dest := by
  refine ⟨fun c proof cand _ hsup i m1 m2 q h1 h2 hq => ?_⟩
  have hsup' := hsup
  simp only [forceMoveRules, Bool.and_eq_true] at hsup'
  obtain ⟨-, hfin, hvt, -⟩ := (validMove_iff vt m1 m2).1 (validRun_getElem? hsup'.1.1.2 h1 h2)
  cases hf : m2.state.isFinal with
  | true => exact Or.inl (hfin.1 hf)
  | false => exact hv _ _ q (hvt hf) hq

/-- **The consensus app conserves value**: a consensus support holds one
    state, so no transition. -/
theorem consensus_conserving {dest : Participant → E} (a : AppId) :
    Conserving (fun _ => consensusRules) a dest := by
  refine ⟨fun c proof cand _ hsup i m1 m2 q h1 h2 _ => ?_⟩
  match proof, hsup with
  | [m], _ =>
    have hlen : [m].length ≤ i + 1 := by
      simp only [List.length_singleton]; omega
    rw [List.getElem?_eq_none hlen] at h2
    cases h2
  | [], h => (simp? [consensusRules] at h says simp only [consensusRules, Bool.false_eq_true] at h)
  | _ :: _ :: _, h =>
    (simp? [consensusRules] at h says simp only [consensusRules, Bool.false_eq_true] at h)

omit [DecidableEq E] in
/-- A state with a mover has a mover at the next turn. -/
theorem mover_next {s : State E} {q : Participant} (h : s.mover = some q) :
    ∃ q', ({ s with turnNum := s.turnNum + 1 } : State E).mover = some q' := by
  unfold State.mover at h ⊢
  have hlt := (List.getElem?_eq_some_iff.1 h).1
  have hpos : 0 < s.channel.n := lt_of_le_of_lt (Nat.zero_le _) hlt
  exact ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)⟩

/-- **A ForceMove app with the go-nitro payment rules is desirable.** The
    mover may keep the state (IC), and every valid move is a
    `ConservingStep` (value conservation). -/
theorem paymentRules_desirable {vt : State E → State E → Bool} {dest : Participant → E}
    (h : PaymentRules vt dest) (a : AppId) : Desirable (fun _ => forceMoveRules vt) a dest := by
  refine ⟨forceMove_IR rfl (paymentRules_noTake h), forceMove_IC (fun s s' hv => ?_) a,
    forceMove_conserving (fun s s' q hv hq => ?_) a⟩
  · obtain ⟨q, hq, -⟩ := (h.valid_iff s s').1 hv
    obtain ⟨q', hq'⟩ := mover_next hq
    exact (h.valid_iff s' _).2 ⟨q', hq', Or.inl rfl⟩
  · obtain ⟨q', hq', hstep⟩ := (h.valid_iff s s').1 hv
    rw [hq] at hq'
    rw [Option.some.inj hq']
    exact hstep

/-- **The consensus app is desirable.** -/
theorem consensus_desirable {dest : Participant → E} (a : AppId) :
    Desirable (fun _ => consensusRules) a dest :=
  ⟨consensus_IR rfl, consensus_IC a, consensus_conserving a⟩

end ArmadaLean.Nitro.TakeOut
