/-
  Counterexample to `satp_theorem_3_2` (`Liveness.lean`).

  `satp_theorem_3_2`'s own hypothesis `HoldsVirtualSetup net r alice bob true` bounds only
  what the intermediary `q0` has SENT for the virtual channel `V`. It gives no bound, and no
  witness, of anything `q0` has RECEIVED for `V`. `NetworkState.Holds` needs a claimed
  co-signer's state to come from `received`; `satpVirtualRules`' every turn `q0` could use to
  move `V` on its own needs `ByAll` (`consensusRules` at turn <= 1; `validStart`'s own `ByAll`
  at the head of any `validateOutcomeChange` proof, turns 2 and 3). So if `q0` has received
  nothing at all for `V`, `q0` can never submit a feasible `challenge`, `checkpoint` or
  `conclude` call that targets `V` at all: `apply_fails_V3` below.

  This is a different, more basic gap than the "voucher stall" a prior pass found and the
  operator ruled resolved by a counter-challenge (`counter_after_adv_checkpoint`, pebble
  aln-a73): that mechanism answers an adversary move on `V`. It does not make the adversary
  move at all. The instance below, `net3` (`NonVacuity.lean`'s own existing nonvacuity witness
  for this exact theorem, `NonVacuity.lean:2397-2452`), has an empty receive record for `V3`:
  `net3.received = [⟨Sm, [p0]⟩, ⟨Sp, [w0]⟩]`, neither entry touching `V3`. The adversary,
  controlling `p0` and `w0`, is free to leave `V3` untouched forever: nothing in the game
  requires it to act. `V3` then never finalizes, so `Adjudicator.reclaim` on `Lm3` can never
  run (it needs `V3` finalized), and `Lm3` can only ever finalize with `om3` (`cand_eq`, via
  the same "nothing beats the one state anyone can get `q0`'s `ByAll` cosignature on" argument
  the library's own `latest_state_finalizable` uses for a channel `q0` CAN act on), which
  carries an un-reclaimable guarantee entry for `V3` (`r3.guarantee p0 q0`).
  `IntermediaryRecovered`'s own `om.find r3.V.address = none` clause is then permanently out
  of reach: `not_goal`. `UnbeatableIn` is inductively defined (a finite move-tree, by its own
  doc comment) — one adversary answer to every move of `q0` (land every one of `q0`'s own
  pending calls, do nothing else) keeps that permanently, so no finite derivation exists:
  `not_unbeatable`, by induction on the hypothetical `UnbeatableIn` proof.

  `net3_holds_no_V3_prefund` records the load-bearing fact precisely: `q0` holds no `ByAll`
  support for `V3`'s own pre-fund (turn 0) state. The UNQUALIFIED claim ("`q0` holds no
  support at all") is false — `q0` trivially `Holds` its own singly-signed send `⟨V0, [q0]⟩` —
  `ByAll` is the fact `satpVirtualRules` and `validStart` actually need, and the one
  `apply_fails_V3` rests on.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/satp_theorem_3_2.lean`.
-/
import ArmadaLean.Nitro.NonVacuity

namespace ArmadaLean.Nitro.Counterexample.Theorem32

open ArmadaLean.Nitro ArmadaLean.Nitro.NonVacuity

theorem validChallenge_channel {alice bob : Participant} {c : FixedPart}
    {s ch : SignedState Nat} (h : validChallenge c alice bob s ch = true) : ch.state.channel = c := by
  unfold validChallenge at h
  split at h
  · obtain ⟨⟨⟨⟨⟨hchan, hor⟩, hsig⟩, hav⟩, hbv⟩, hout⟩ := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    exact hchan.2
  · cases h

theorem validResponse_channel {alice bob : Participant} {c : FixedPart}
    {s ch re : SignedState Nat} (h : validResponse c alice bob s ch re = true) :
    re.state.channel = c := by
  unfold validResponse at h
  split at h
  · have h' := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    exact h'.1.1.1.1.1.1.1.1.2
  · cases h

theorem satp_proof_channels' {alice bob : Participant} {c : FixedPart} {proof : SupportProof Nat}
    {cand : State Nat} (hhead : c.participants.head? = some alice)
    (hlast : c.participants.getLast? = some bob)
    (hsupp : satpVirtualRules.supports c proof cand = true) :
    ∀ ss ∈ proof, ss.state.channel = c := by
  simp only [satpVirtualRules, hhead, hlast] at hsupp
  split_ifs at hsupp with ht1 ht4
  · match proof, hsupp with
    | [ssx], hsupp =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      intro ss hmem; rw [List.mem_singleton] at hmem; subst hmem; exact hsupp.1.2
    | [], hsupp => simp [consensusRules] at hsupp
    | _ :: _ :: _, hsupp => simp [consensusRules] at hsupp
  · simp only [Bool.and_eq_true] at hsupp
    obtain ⟨hcon, -⟩ := hsupp
    match proof, hcon with
    | [ssx], hcon =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
      intro ss hmem; rw [List.mem_singleton] at hmem; subst hmem; exact hcon.1.2
    | [], hcon => simp [consensusRules] at hcon
    | _ :: _ :: _, hcon => simp [consensusRules] at hcon
  · match proof, hsupp with
    | [s], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvs, -⟩ := hsupp
      obtain ⟨-, hchan⟩ := satp_validStart_byAll hvs
      intro ss hmem; rw [List.mem_singleton] at hmem; subst hmem; exact hchan
    | [s, ch], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvc, -⟩ := hsupp
      have hvs := satp_validChallenge_start hvc
      obtain ⟨-, hschan⟩ := satp_validStart_byAll hvs
      have hchchan := validChallenge_channel hvc
      intro ss hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hschan
      · exact hchchan
    | [s, ch, re], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvr, -⟩ := hsupp
      have hvc : validChallenge c alice bob s ch = true := by
        unfold validResponse at hvr
        split at hvr
        · simp only [Bool.and_eq_true] at hvr
          repeat (obtain ⟨hvr, -⟩ := hvr)
          exact hvr
        · cases hvr
      have hvs := satp_validChallenge_start hvc
      obtain ⟨-, hschan⟩ := satp_validStart_byAll hvs
      have hchchan := validChallenge_channel hvc
      have hrechan := validResponse_channel hvr
      intro ss hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hschan
      · exact hchchan
      · exact hrechan
    | [], hsupp => simp [validateOutcomeChange] at hsupp
    | _ :: _ :: _ :: _ :: _, hsupp => simp [validateOutcomeChange] at hsupp

theorem satp_proof_channels {c : FixedPart} {proof : SupportProof Nat}
    {cand : State Nat} (hsupp : satpVirtualRules.supports c proof cand = true) :
    ∀ ss ∈ proof, ss.state.channel = c := by
  cases hh1 : c.participants.head? with
  | none =>
    simp only [satpVirtualRules, hh1] at hsupp
    cases hsupp
  | some alice =>
    cases hh2 : c.participants.getLast? with
    | none =>
      simp only [satpVirtualRules, hh1, hh2] at hsupp
      cases hsupp
    | some bob => exact satp_proof_channels' hh1 hh2 hsupp

/-- `q0` has received nothing at all for `V3`. -/
def RecVOK (n : NetworkState Nat q0) : Prop :=
  ∀ r ∈ n.received, r.state.channel ≠ V3

theorem apps2_V3 : apps2 V3.appDef = satpVirtualRules := rfl

/-- Any `satpVirtualRules`-supported proof has a `ByAll`-signed element of channel `V3`. -/
theorem satpVirtual_head_byAll {proof : SupportProof Nat} {cand : State Nat}
    (hsupp : satpVirtualRules.supports V3 proof cand = true) :
    ∃ e ∈ proof, e.ByAll ∧ e.state.channel = V3 := by
  simp only [satpVirtualRules] at hsupp
  have hhead : V3.participants.head? = some p0 := rfl
  have hlast : V3.participants.getLast? = some w0 := rfl
  rw [hhead, hlast] at hsupp
  split_ifs at hsupp with ht1 ht4
  · match proof, hsupp with
    | [ssx], hsupp =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      exact ⟨ssx, List.mem_singleton_self _, hsupp.2, hsupp.1.2⟩
    | [], hsupp => simp [consensusRules] at hsupp
    | _ :: _ :: _, hsupp => simp [consensusRules] at hsupp
  · simp only [Bool.and_eq_true] at hsupp
    obtain ⟨hcon, -⟩ := hsupp
    match proof, hcon with
    | [ssx], hcon =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
      exact ⟨ssx, List.mem_singleton_self _, hcon.2, hcon.1.2⟩
    | [], hcon => simp [consensusRules] at hcon
    | _ :: _ :: _, hcon => simp [consensusRules] at hcon
  · match proof, hsupp with
    | [s], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvs, -⟩ := hsupp
      obtain ⟨hall, hchan⟩ := satp_validStart_byAll hvs
      exact ⟨s, List.mem_singleton_self _, hall, hchan⟩
    | [s, ch], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvc, -⟩ := hsupp
      have hvs := satp_validChallenge_start hvc
      obtain ⟨hall, hchan⟩ := satp_validStart_byAll hvs
      exact ⟨s, List.mem_cons_self .., hall, hchan⟩
    | [s, ch, re], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvr, -⟩ := hsupp
      have hvs := satp_validResponse_start hvr
      obtain ⟨hall, hchan⟩ := satp_validStart_byAll hvs
      exact ⟨s, List.mem_cons_self .., hall, hchan⟩
    | [], hsupp => simp [validateOutcomeChange] at hsupp
    | _ :: _ :: _ :: _ :: _, hsupp => simp [validateOutcomeChange] at hsupp

theorem apply_fails_V3 {n : NetworkState Nat q0} (hV : RecVOK n) (hVopen : n.chain.statusOf V3 = .open 0)
    {op : Op Nat} (hfeas : op.HonestFeasible n) (ht : Op.targets op V3) :
    n.chain.apply apps2 q0 op = none := by
  cases hs' : n.chain.apply apps2 q0 op with
  | none => rfl
  | some s' =>
    exfalso
    cases op with
    | deposit a e x => simp [Op.targets] at ht
    | tick dt => simp [Op.targets] at ht
    | transfer a b =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨o, -, -, hf, -⟩ := Adjudicator.transfer_some hs'
      rw [show n.chain.finalOutcome V3.address = (n.chain.statusOf V3).finalOutcome n.chain.now from rfl,
        hVopen] at hf
      simp [ChannelStatus.finalOutcome] at hf
    | reclaim l v =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨oL, -, -, -, -, hf, -⟩ := Adjudicator.reclaim_some hs'
      rw [show n.chain.finalOutcome V3.address = (n.chain.statusOf V3).finalOutcome n.chain.now from rfl,
        hVopen] at hf
      simp [ChannelStatus.finalOutcome] at hf
    | challenge c proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hsupp, -, -⟩, -⟩ := Adjudicator.challenge_some hs'
      rw [apps2_V3] at hsupp
      obtain ⟨e, hemem, heall, hechan⟩ := satpVirtual_head_byAll hsupp
      have hp0 : p0 ∈ e.signers := heall p0 (by rw [hechan]; decide)
      have hHe : n.Holds e := hfeas e hemem
      rcases hHe.1 p0 hp0 with ⟨hp0q0, -⟩ | ⟨r, hr, hrs, -⟩
      · exact absurd hp0q0 (by decide)
      · exact hV r hr (by rw [hrs]; exact hechan)
    | checkpoint c proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hsupp, -, -⟩, -⟩ := Adjudicator.checkpoint_some hs'
      rw [apps2_V3] at hsupp
      obtain ⟨e, hemem, heall, hechan⟩ := satpVirtual_head_byAll hsupp
      have hp0 : p0 ∈ e.signers := heall p0 (by rw [hechan]; decide)
      have hHe : n.Holds e := hfeas e hemem
      rcases hHe.1 p0 hp0 with ⟨hp0q0, -⟩ | ⟨r, hr, hrs, -⟩
      · exact absurd hp0q0 (by decide)
      · exact hV r hr (by rw [hrs]; exact hechan)
    | conclude c ss =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hchan, -, hall⟩, -⟩ := Adjudicator.conclude_some hs'
      have hp0 : p0 ∈ ss.signers := hall p0 (by rw [hchan]; decide)
      have hHss : n.Holds ss := hfeas ss (by simp [Op.proofStates])
      rcases hHss.1 p0 hp0 with ⟨hp0q0, -⟩ | ⟨r, hr, hrs, -⟩
      · exact absurd hp0q0 (by decide)
      · exact hV r hr (by rw [hrs]; exact hchan)

theorem apps2_Lm3 : apps2 Lm3.appDef = consensusRules := rfl

/-- Every state of `Lm3` that `q0` has received and that carries `p0`'s claimed
    co-signature is `Sm` — the one state `net3` already carries `p0`'s partial signature of. -/
def RecChanOK (n : NetworkState Nat q0) : Prop :=
  ∀ r ∈ n.received, r.state.channel = Lm3 → r.state = Sm

/-- `Lm3`'s finalized allocation shape: it still carries `V3`'s own guarantee entry, and
    that is the only address it carries any guarantee entry for. -/
def LmFinalShape (o : Allocation Nat) : Prop :=
  o.find V3.address = some (r3.guarantee p0 q0) ∧
  ∀ addr x ps, o.find addr = some ⟨addr, .guarantee x ps⟩ → addr = V3.address

theorem LmFinalShape.reduceOwed {o : Allocation Nat} (h : LmFinalShape o) (b : Address Nat)
    (x : Coins) (hb : b ≠ V3.address) : LmFinalShape (o.reduceOwed b x) := by
  obtain ⟨hV, honly⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Allocation.find_reduceOwed, if_neg (Ne.symm hb)]; exact hV
  · intro addr y ps hfa
    by_cases hab : addr = b
    · subst hab
      rw [Allocation.find_reduceOwed, if_pos rfl] at hfa
      cases hom : o.find addr with
      | none => rw [hom] at hfa; simp at hfa
      | some e => rw [hom] at hfa; simp only [Option.map_some] at hfa; cases hfa
    · rw [Allocation.find_reduceOwed, if_neg hab] at hfa
      exact honly addr y ps hfa

theorem lmFinalShape_om3 : LmFinalShape om3 := by
  refine ⟨by decide, ?_⟩
  intro addr x ps hfa
  simp only [om3] at hfa
  rw [Allocation.find_cons] at hfa
  by_cases h0 : (alloc (Address.external 0) 0 : Entry Nat).dest = addr
  · rw [if_pos h0] at hfa; simp [alloc] at hfa
  · rw [if_neg h0] at hfa
    rw [Allocation.find_cons] at hfa
    by_cases h1 : (alloc (Address.external 1) 0 : Entry Nat).dest = addr
    · rw [if_pos h1] at hfa; simp [alloc] at hfa
    · rw [if_neg h1] at hfa
      rw [Allocation.find_cons] at hfa
      by_cases h2 : (r3.guarantee p0 q0 : Entry Nat).dest = addr
      · rw [if_pos h2] at hfa
        rw [← h2]; rfl
      · rw [if_neg h2] at hfa; simp [Allocation.find] at hfa

/-- `Lm3`'s shape: open, challenged with the fixed `Sm`, or finalized with an
    allocation that still carries `V3`'s own guarantee entry. -/
def LShape (s : Adjudicator Nat) : Prop :=
  (∃ k, s.statusOf Lm3 = .open k) ∨ (∃ k d, s.statusOf Lm3 = .challenged k ⟨Sm, d⟩) ∨
  (∃ t f o, s.statusOf Lm3 = .finalized t f (.allocation o) ∧ LmFinalShape o)

def Inv (n : NetworkState Nat q0) : Prop :=
  RecChanOK n ∧ RecVOK n ∧ n.chain.statusOf V3 = .open 0 ∧ LShape n.chain

/-- A call `q0` can issue when `RecChanOK` and `RecVOK` hold: it never targets `V3`
    (`apply_fails_V3`), and any claim of `p0`'s co-signature on a state of `Lm3` is `Sm`. -/
def Good (op : Op Nat) : Prop :=
  (∀ dt, op ≠ .tick dt) ∧ (∀ a e x, op ≠ .deposit a e x) ∧
    (∀ ss ∈ op.proofStates, p0 ∈ ss.signers → ss.state.channel = Lm3 → ss.state = Sm)

theorem good_of_feasible {n : NetworkState Nat q0} (hR : RecChanOK n) {op : Op Nat}
    (h : op.HonestFeasible n) : Good op := by
  refine ⟨?_, ?_, ?_⟩
  · intro dt heq; subst heq; exact h
  · intro a e x heq; subst heq; exact h
  · intro ss hss hq hc
    have hh : n.Holds ss := by
      cases op with
      | deposit => exact h.elim
      | tick => exact h.elim
      | transfer => exact h ss hss
      | reclaim => exact h ss hss
      | challenge => exact h ss hss
      | checkpoint => exact h ss hss
      | conclude => exact h ss hss
    rcases hh.1 p0 hq with ⟨hp0q0, -⟩ | ⟨r, hr, hrs, hqr⟩
    · exact absurd hp0q0 (by decide)
    · rw [← hrs]; exact hR r hr (by rw [hrs]; exact hc)

/-- A `consensus` support of a state of `Lm3` whose proof meets `Good` is a support of `Sm`. -/
theorem cand_eq {proof : SupportProof Nat} {cand : State Nat}
    (hgp : ∀ ss ∈ proof, p0 ∈ ss.signers → ss.state.channel = Lm3 → ss.state = Sm)
    (hsupp : (apps2 Lm3.appDef).supports Lm3 proof cand = true) : cand = Sm := by
  rw [apps2_Lm3] at hsupp
  rcases proof with _ | ⟨ss, _ | ⟨ss', rest⟩⟩
  · simp [consensusRules] at hsupp
  · simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hsupp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsupp
    have hq : p0 ∈ ss.signers := h3 p0 (by rw [h2]; decide)
    rw [← h1]; exact hgp ss List.mem_cons_self hq h2
  · simp [consensusRules] at hsupp


/-- Every element of a successfully-supported proof carries the supported candidate's own
    channel, regardless of which of `apps2`'s two rule sets governs it. -/
theorem apps2_proof_channel {c : FixedPart} {proof : SupportProof Nat} {cand : State Nat}
    (hsupp : (apps2 c.appDef).supports c proof cand = true) :
    ∀ ss ∈ proof, ss.state.channel = c := by
  unfold apps2 at hsupp
  split at hsupp
  · exact satp_proof_channels hsupp
  · intro ss hss
    match proof, hsupp with
    | [ssx], hsupp =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      rw [List.mem_singleton] at hss; subst hss; exact hsupp.1.2
    | [], hsupp => simp [consensusRules] at hsupp
    | _ :: _ :: _, hsupp => simp [consensusRules] at hsupp
/-- Landing one `q0` call that does not target `Lm3` or `V3` changes neither channel's
    status, and (challenge/checkpoint/conclude being structurally bound to their own target
    channel) never adds a `Lm3`- or `V3`-channel entry to `received`. -/
theorem land_step_elsewhere {n : NetworkState Nat q0} {op : Op Nat} (hg : Good op)
    (htLm : ¬ Op.targets op Lm3) (htV : ¬ Op.targets op V3) :
    (n.applyAdv apps2 (.land op)).chain.statusOf Lm3 = n.chain.statusOf Lm3 ∧
    (n.applyAdv apps2 (.land op)).chain.statusOf V3 = n.chain.statusOf V3 ∧
    (n.applyAdv apps2 (.land op)).chain.now = n.chain.now ∧
    ∀ r ∈ (n.applyAdv apps2 (.land op)).received, r ∈ n.received ∨
      (r.state.channel ≠ Lm3 ∧ r.state.channel ≠ V3) := by
  cases hs : n.chain.apply apps2 q0 op with
  | none =>
    rw [NetworkState.applyAdv_land_none _ hs]
    exact ⟨rfl, rfl, rfl, fun r hr => .inl hr⟩
  | some s' =>
    have hLm' := statusOf_apply_of_not_targets hs htLm
    have hV' := statusOf_apply_of_not_targets hs htV
    have hnow' := Adjudicator.apply_now_eq_of_not_tick hg.1 hs
    have hrec : ∀ r ∈ op.proofStates, r.state.channel ≠ Lm3 ∧ r.state.channel ≠ V3 := by
      cases op with
      | deposit a e x => simp [Op.proofStates]
      | tick dt => simp [Op.proofStates]
      | transfer a b => simp [Op.proofStates]
      | reclaim l v => simp [Op.proofStates]
      | challenge c proof cand =>
        simp only [Op.targets] at htLm htV
        obtain ⟨⟨-, hsupp, -, -⟩, -⟩ := Adjudicator.challenge_some hs
        have hch := apps2_proof_channel hsupp
        intro r hr
        simp only [Op.proofStates] at hr
        rw [hch r hr]
        exact ⟨htLm, htV⟩
      | checkpoint c proof cand =>
        simp only [Op.targets] at htLm htV
        obtain ⟨⟨-, hsupp, -, -⟩, -⟩ := Adjudicator.checkpoint_some hs
        have hch := apps2_proof_channel hsupp
        intro r hr
        simp only [Op.proofStates] at hr
        rw [hch r hr]
        exact ⟨htLm, htV⟩
      | conclude c ss =>
        simp only [Op.targets] at htLm htV
        obtain ⟨⟨-, hchan, -, -⟩, -⟩ := Adjudicator.conclude_some hs
        intro r hr
        simp only [Op.proofStates, List.mem_singleton] at hr
        subst hr
        rw [hchan]
        exact ⟨htLm, htV⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [NetworkState.applyAdv_land_some _ hs]; exact hLm'
    · rw [NetworkState.applyAdv_land_some _ hs]; exact hV'
    · rw [NetworkState.applyAdv_land_some _ hs]; exact hnow'
    · rw [NetworkState.applyAdv_land_some _ hs]
      intro r hr
      simp only [List.mem_append] at hr
      rcases hr with hr | hr
      · exact .inr (hrec r hr)
      · exact .inl hr

/-- Landing one `q0` call that targets `Lm3` keeps `LShape`: a `transfer`/`reclaim` never
    reaches `V3`'s guarantee entry, whether `Lm3` is already stored `.finalized` or is
    `.challenged` past its deadline (`ChannelStatus.withOutcome` promotes a `.challenged`
    status straight to `.finalized` once a step reads past its deadline); a
    `challenge`/`checkpoint`/`conclude` is bound by `Good` to `Sm`, whose `isFinal` is `false`
    (ruling out `conclude`). -/
theorem land_step_lm3 {n : NetworkState Nat q0} {op : Op Nat} (hg : Good op)
    (htLm : Op.targets op Lm3) (hVopen : n.chain.statusOf V3 = .open 0)
    (hL : LShape n.chain) :
    LShape (n.applyAdv apps2 (.land op)).chain := by
  cases hs : n.chain.apply apps2 q0 op with
  | none => rw [NetworkState.applyAdv_land_none _ hs]; exact hL
  | some s' =>
    rw [NetworkState.applyAdv_land_some _ hs]
    simp only [Op.targets] at htLm
    cases op with
    | deposit a e x => exact absurd rfl (hg.2.1 a e x)
    | tick dt => exact absurd rfl (hg.1 dt)
    | transfer a b =>
      subst htLm
      obtain ⟨o, -, x, hf, hfind, -, -, -, hstatus, -, -, hfundable⟩ := Adjudicator.transfer_some hs
      have hbV : b ≠ V3.address := by
        intro heq; rw [heq] at hfundable; exact absurd hfundable (by decide)
      rcases hL with ⟨k, hk⟩ | ⟨k, d, hk⟩ | ⟨t, fo, o1, hk, hfs⟩
      · exfalso
        have hnf : n.chain.finalOutcome Lm3.address = none := by
          show (n.chain.statusOf Lm3).finalOutcome n.chain.now = none; rw [hk]; rfl
        rw [hnf] at hf; cases hf
      · by_cases hexp : d ≤ n.chain.now
        · have hfo1 : n.chain.finalOutcome Lm3.address = some (.allocation om3) := by
            show (n.chain.statusOf Lm3).finalOutcome n.chain.now = _
            rw [hk]; simp only [ChannelStatus.finalOutcome]; rw [if_pos hexp]; rfl
          rw [hfo1] at hf
          simp only [Option.some.injEq, Outcome.allocation.injEq] at hf
          subst hf
          refine .inr (.inr ⟨k, Sm.outcome, om3.reduceOwed b x, ?_,
            lmFinalShape_om3.reduceOwed b x hbV⟩)
          rw [Adjudicator.statusOf_of_status hstatus]; simp [hk]
        · exfalso
          have hnf : n.chain.finalOutcome Lm3.address = none := by
            show (n.chain.statusOf Lm3).finalOutcome n.chain.now = none
            rw [hk]; simp only [ChannelStatus.finalOutcome]; rw [if_neg hexp]
          rw [hnf] at hf; cases hf
      · have hfo1 : n.chain.finalOutcome Lm3.address = some (.allocation o1) := by
          show (n.chain.statusOf Lm3).finalOutcome n.chain.now = _; rw [hk]; rfl
        rw [hfo1] at hf
        simp only [Option.some.injEq, Outcome.allocation.injEq] at hf
        subst hf
        refine .inr (.inr ⟨t, fo, o1.reduceOwed b x, ?_, hfs.reduceOwed b x hbV⟩)
        rw [Adjudicator.statusOf_of_status hstatus]; simp [hk]
    | reclaim l v =>
      subst htLm
      obtain ⟨oL, oV, x, left, right, hf, hv, hgfind, -, -, -, hstatus, -, hvk⟩ :=
        Adjudicator.reclaim_some hs
      have hfinish : ∀ (o1 : Allocation Nat),
          n.chain.finalOutcome Lm3.address = some (.allocation o1) → LmFinalShape o1 →
          LShape s' := by
        intro o1 hfo1 hfs
        rw [hfo1] at hf
        simp only [Option.some.injEq, Outcome.allocation.injEq] at hf
        subst hf
        exfalso
        have hveq : v.address = V3.address := hfs.2 v.address x [left, right] hgfind
        have hnone : n.chain.finalizedWith V3.address = none := by
          show (n.chain.statusOf V3).finalizedWith n.chain.now = none
          rw [hVopen]; rfl
        rw [hveq, hnone] at hv; cases hv
      rcases hL with ⟨k, hk⟩ | ⟨k, d, hk⟩ | ⟨t, fo, o1, hk, hfs⟩
      · exfalso
        have hnf : n.chain.finalOutcome Lm3.address = none := by
          show (n.chain.statusOf Lm3).finalOutcome n.chain.now = none; rw [hk]; rfl
        rw [hnf] at hf; cases hf
      · by_cases hexp : d ≤ n.chain.now
        · have hfo1 : n.chain.finalOutcome Lm3.address = some (.allocation om3) := by
            show (n.chain.statusOf Lm3).finalOutcome n.chain.now = _
            rw [hk]; simp only [ChannelStatus.finalOutcome]; rw [if_pos hexp]; rfl
          exact hfinish om3 hfo1 lmFinalShape_om3
        · exfalso
          have hnf : n.chain.finalOutcome Lm3.address = none := by
            show (n.chain.statusOf Lm3).finalOutcome n.chain.now = none
            rw [hk]; simp only [ChannelStatus.finalOutcome]; rw [if_neg hexp]
          rw [hnf] at hf; cases hf
      · have hfo1 : n.chain.finalOutcome Lm3.address = some (.allocation o1) := by
          show (n.chain.statusOf Lm3).finalOutcome n.chain.now = _; rw [hk]; rfl
        exact hfinish o1 hfo1 hfs
    | challenge c proof cand =>
      subst htLm
      obtain ⟨⟨-, hsupp, -, -⟩, hseq⟩ := Adjudicator.challenge_some hs
      have hcand := cand_eq hg.2.2 hsupp
      subst hcand
      refine .inr (.inl ⟨Sm.turnNum, n.chain.now + Lm3.challengeDuration, ?_⟩)
      rw [hseq]; simp
    | checkpoint c proof cand =>
      subst htLm
      obtain ⟨⟨-, hsupp, -, -⟩, hseq⟩ := Adjudicator.checkpoint_some hs
      have hcand := cand_eq hg.2.2 hsupp
      subst hcand
      refine .inl ⟨Sm.turnNum, ?_⟩
      rw [hseq]; simp
    | conclude c ss =>
      subst htLm
      obtain ⟨⟨-, hchan, hfin, hall⟩, -⟩ := Adjudicator.conclude_some hs
      have hp0 : p0 ∈ ss.signers := hall p0 (by rw [hchan]; decide)
      have hss := hg.2.2 ss (by simp [Op.proofStates]) hp0 hchan
      rw [hss] at hfin
      cases hfin

/-- Landing one `q0` call keeps `Inv`, whichever of `Lm3`, `V3` or neither it targets. -/
theorem land_step_full {n : NetworkState Nat q0} {op : Op Nat} (hg : Good op)
    (hfeas : op.HonestFeasible n) (hI : Inv n) :
    Inv (n.applyAdv apps2 (.land op)) := by
  obtain ⟨hR, hV, hVopen, hL⟩ := hI
  by_cases htLm : Op.targets op Lm3
  · have htV : ¬ Op.targets op V3 := by cases op <;> simp_all [Op.targets] <;> decide
    have hL' := land_step_lm3 hg htLm hVopen hL
    cases hs : n.chain.apply apps2 q0 op with
    | none =>
      rw [NetworkState.applyAdv_land_none _ hs]
      exact ⟨hR, hV, hVopen, hL⟩
    | some s' =>
      have hadded : ∀ r ∈ op.proofStates, r.state = Sm := by
        simp only [Op.targets] at htLm
        cases op with
        | deposit a e x => exact absurd rfl (hg.2.1 a e x)
        | tick dt => exact absurd rfl (hg.1 dt)
        | transfer a b => simp [Op.proofStates]
        | reclaim l v => simp [Op.proofStates]
        | challenge c proof cand =>
          subst htLm
          obtain ⟨⟨-, hsupp, -, -⟩, -⟩ := Adjudicator.challenge_some hs
          have hcand := cand_eq hg.2.2 hsupp
          match proof, hsupp with
          | [ssx], hsupp =>
            simp only [consensusRules, apps2_Lm3, Bool.and_eq_true, decide_eq_true_eq] at hsupp
            intro r hr
            simp only [Op.proofStates, List.mem_singleton] at hr
            rw [hr, hsupp.1.1]; exact hcand
        | checkpoint c proof cand =>
          subst htLm
          obtain ⟨⟨-, hsupp, -, -⟩, -⟩ := Adjudicator.checkpoint_some hs
          have hcand := cand_eq hg.2.2 hsupp
          match proof, hsupp with
          | [ssx], hsupp =>
            simp only [consensusRules, apps2_Lm3, Bool.and_eq_true, decide_eq_true_eq] at hsupp
            intro r hr
            simp only [Op.proofStates, List.mem_singleton] at hr
            rw [hr, hsupp.1.1]; exact hcand
        | conclude c ss =>
          subst htLm
          exfalso
          obtain ⟨⟨-, hchan, hfin, hall⟩, -⟩ := Adjudicator.conclude_some hs
          have hp0 : p0 ∈ ss.signers := hall p0 (by rw [hchan]; decide)
          have hss := hg.2.2 ss (by simp [Op.proofStates]) hp0 hchan
          rw [hss] at hfin; cases hfin
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [NetworkState.applyAdv_land_some _ hs]
        intro r hr hc
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · exact hadded r hr
        · exact hR r hr hc
      · rw [NetworkState.applyAdv_land_some _ hs]
        intro r hr
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · rw [hadded r hr]; decide
        · exact hV r hr
      · rw [NetworkState.applyAdv_land_some _ hs]
        rw [statusOf_apply_of_not_targets hs htV]; exact hVopen
      · exact hL'
  · by_cases htV : Op.targets op V3
    · have hfail := apply_fails_V3 hV hVopen hfeas htV
      rw [NetworkState.applyAdv_land_none _ hfail]
      exact ⟨hR, hV, hVopen, hL⟩
    · obtain ⟨hLm'', hV'', hnow'', hrec''⟩ := land_step_elsewhere (n := n) (op := op) hg htLm htV
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r hr hc
        rcases hrec'' r hr with hr' | ⟨hr1, -⟩
        · exact hR r hr' hc
        · exact absurd hc hr1
      · intro r hr
        rcases hrec'' r hr with hr' | ⟨-, hr2⟩
        · exact hV r hr'
        · exact hr2
      · rw [hV'']; exact hVopen
      · rcases hL with ⟨k, hk⟩ | ⟨k, d, hk⟩ | ⟨t, f, o, hk, hfs⟩
        · exact .inl ⟨k, by rw [hLm'']; exact hk⟩
        · exact .inr (.inl ⟨k, d, by rw [hLm'']; exact hk⟩)
        · exact .inr (.inr ⟨t, f, o, by rw [hLm'']; exact hk, hfs⟩)

/-- `q0`'s pending calls, landed one at a time: `Inv` survives, and the clock does not move
    (`Good`'s own `hg.1` rules out a `.tick` call). -/
theorem land_all (t : Time) : ∀ (pending : List (Op Nat)),
    ∀ (n : NetworkState Nat q0), (∀ op ∈ pending, Good op ∧ op.HonestFeasible n) → Inv n →
      ∃ n', Threat.RoundSeq apps2 (canon q0) t pending n n' ∧ Inv n' ∧
        n'.chain.now = n.chain.now := by
  intro pending
  induction pending with
  | nil => intro n _ hI; exact ⟨n, .nil, hI, rfl⟩
  | cons op rest ih =>
    intro n hgf hI
    have hg := (hgf op List.mem_cons_self).1
    have hfeas := (hgf op List.mem_cons_self).2
    have hInv' := land_step_full hg hfeas hI
    have hnow' : (n.applyAdv apps2 (.land op)).chain.now = n.chain.now := by
      cases hs : n.chain.apply apps2 q0 op with
      | none => rw [NetworkState.applyAdv_land_none _ hs]
      | some s' =>
        rw [NetworkState.applyAdv_land_some _ hs]
        exact Adjudicator.apply_now_eq_of_not_tick hg.1 hs
    have hgf' : ∀ op' ∈ rest, Good op' ∧ op'.HonestFeasible (n.applyAdv apps2 (.land op)) := by
      intro op' hop'
      exact ⟨(hgf op' (List.mem_cons_of_mem op hop')).1,
        Op.HonestFeasible.applyAdv _ (hgf op' (List.mem_cons_of_mem op hop')).2⟩
    obtain ⟨n', hseq, hI', hnow''⟩ := ih _ hgf' hInv'
    exact ⟨n', .land (l1 := []) (l2 := rest) rfl hseq, hI', by rw [hnow'', hnow']⟩

/-- The adversary's one strategy against any move of `q0`: land every one of `q0`'s own
    pending calls, and do nothing else (no `.chain`, `.deliver`, `.tick` of its own). -/
theorem round (n : NetworkState Nat q0) (hI : Inv n) (m : HonestMove Nat) (hfeas : m.Feasible n) :
    ∃ n', (canon q0).Round apps2 m n n' ∧ Inv (n'.applyHonest m) := by
  have hgood : ∀ op ∈ m.calls, Good op ∧ op.HonestFeasible n := by
    cases m with
    | react r => intro op hop; exact ⟨good_of_feasible hI.1 (hfeas op hop), hfeas op hop⟩
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  obtain ⟨n', hseq, hI', hnow'⟩ := land_all n.chain.now m.calls n hgood hI
  refine ⟨n', ⟨hseq, ?_⟩, ?_⟩
  · rw [hnow']; exact Nat.lt_add_of_pos_right (canon q0).ε_pos
  · cases m with
    | react r => exact hI'
    | wait dt =>
      obtain ⟨hR, hV, hVopen, hL⟩ := hI'
      have hVopen' : (n'.chain.tick dt).statusOf V3 = .open 0 := by
        rw [Adjudicator.tick_statusOf]; exact hVopen
      have hL' : LShape (n'.chain.tick dt) := by
        rcases hL with ⟨k, hk⟩ | ⟨k, d, hk⟩ | ⟨t, f, o, hk, hfs⟩
        · refine .inl ⟨k, ?_⟩; rw [Adjudicator.tick_statusOf]; exact hk
        · refine .inr (.inl ⟨k, d, ?_⟩); rw [Adjudicator.tick_statusOf]; exact hk
        · refine .inr (.inr ⟨t, f, o, ?_, hfs⟩); rw [Adjudicator.tick_statusOf]; exact hk
      exact ⟨hR, hV, hVopen', hL'⟩

/-- `Inv` rules out `IntermediaryRecovered`: `Lm3` can only ever be finalized with an
    allocation that still carries `V3`'s guarantee entry. -/
theorem not_goal (balm balp base : Coins) {n : NetworkState Nat q0} (hI : Inv n) :
    ¬ IntermediaryRecovered r3 Lm3 Lp3 balm balp base n := by
  rintro ⟨om, -, hf, -, hnone, -, -⟩
  change (n.chain.statusOf Lm3).finalOutcome n.chain.now = _ at hf
  change om.find V3.address = none at hnone
  rcases hI.2.2.2 with ⟨k, hk⟩ | ⟨k, d, hk⟩ | ⟨t, f, o, hk, hfs⟩
  · rw [hk] at hf; cases hf
  · rw [hk] at hf
    simp only [ChannelStatus.finalOutcome] at hf
    split at hf
    · simp only [Sm, Option.some.injEq, Outcome.allocation.injEq] at hf
      rw [← hf] at hnone
      rw [lmFinalShape_om3.1] at hnone
      cases hnone
    · cases hf
  · rw [hk] at hf
    simp only [ChannelStatus.finalOutcome, Option.some.injEq, Outcome.allocation.injEq] at hf
    rw [← hf, hfs.1] at hnone
    cases hnone


theorem not_unbeatable (balm balp base : Coins) (n : NetworkState Nat q0)
    (h : Unbeatable apps2 (canon q0) (IntermediaryRecovered r3 Lm3 Lp3 balm balp base) n) :
    Inv n → False := by
  induction h with
  | done hG => intro hI; exact not_goal balm balp base hI hG
  | move m _ hfeas _ ih =>
    intro hI
    obtain ⟨n', hR, hI'⟩ := round _ hI m hfeas
    exact ih n' hR hI'


theorem inv_net3 : Inv net3 := by
  refine ⟨?_, ?_, rfl, .inl ⟨0, rfl⟩⟩
  · intro r hr hc
    simp only [net3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rfl
    · exact absurd hc (by decide)
  · intro r hr
    simp only [net3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

/-- `net3` satisfies every hypothesis of `satp_theorem_3_2` for the route `r3`, peers
    `alice := p0`, `bob := w0`, intermediary `P := q0`, ledgers `Lm3`, `Lp3`, balances
    `balm = balp = 1` — the same witness `NonVacuity.lean`'s own nonvacuity example for this
    theorem already uses. -/
theorem netX_not_unbeatable :
    ¬ Unbeatable apps2 (canon q0)
      (IntermediaryRecovered r3 Lm3 Lp3 1 1 (net3.chain.balances.get (.external (r3.dest q0))))
      net3 :=
  fun h => not_unbeatable 1 1 _ net3 h inv_net3

/-- `q0` holds no `ByAll` support proof at all for `V3`'s own pre-fund (turn 0) state: it has
    received nothing for `V3`, and `NetworkState.Holds` needs every other signer's claim to
    come from `received`. (The unqualified claim is false: `q0` trivially `Holds` its own
    singly-signed send `⟨V0, [q0]⟩`; `ByAll` is the fact `satpVirtualRules`'s consensus branch
    and `validStart` both actually need, and the one `apply_fails_V3` rests on.) -/
theorem net3_holds_no_V3_prefund :
    ¬ ∃ ss : SignedState Nat, net3.Holds ss ∧ ss.ByAll ∧ ss.state.channel = V3 ∧
      ss.state.turnNum = 0 := by
  rintro ⟨ss, hH, hall, hchan, -⟩
  have hp0 : p0 ∈ ss.signers := hall p0 (by rw [hchan]; decide)
  rcases hH.1 p0 hp0 with ⟨hp0q0, -⟩ | ⟨r, hr, hrs, -⟩
  · exact absurd hp0q0 (by decide)
  · have hV : RecVOK net3 := inv_net3.2.1
    exact hV r hr (by rw [hrs]; exact hchan)


/-- `satp_theorem_3_2`, applied to `net3`, is false. -/
example : False :=
  netX_not_unbeatable
    (satp_theorem_3_2 apps2 (canon q0) (canon_ok _ _) r3 p0 w0 r3_wf rfl rfl rfl 1 le_rfl (by decide)
      rfl p0 w0 rfl rfl Lm3 Lp3 rfl rfl ⟨by decide, by decide, by decide⟩ om3 op3 1 1
      (by unfold Route.LedgerAfterRound2; decide) (by unfold Route.LedgerAfterRound2; decide)
      net3 net3_reach net3_latest_m net3_latest_p
      ⟨fun t ht hc => by
          simp [net3] at ht
          rcases ht with rfl | rfl | rfl <;>
            first | exact ⟨rfl, rfl, .inl rfl⟩ | exact absurd hc (by decide),
        ⟨V0, [q0]⟩, by simp [net3], rfl, rfl⟩
      ⟨deadlineAfter_open (t := 0) rfl _, deadlineAfter_open (t := 0) rfl _,
        deadlineAfter_open (t := 0) rfl _⟩
      ⟨by decide, by decide, by decide⟩)

#print axioms netX_not_unbeatable
#print axioms net3_reach
#print axioms net3_latest_m
#print axioms net3_latest_p
#print axioms net3_holds_no_V3_prefund

end ArmadaLean.Nitro.Counterexample.Theorem32
