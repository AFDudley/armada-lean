/-
  Counterexample to `satp_end_user_recovers` (Liveness.lean), pebble `aln-223`.

  The instance is the two-peer route `r2` of `NonVacuity.lean` (Alice `p0`,
  Bob `q0`, ledger `Lr`, virtual channel `Vr`). Alice's latest ledger state
  `SL` has the allocation `oX`. `oX` satisfies `r2.LedgerAfterRound2`, and it
  also carries a guarantee `gX` for a second virtual channel `Vx`. The left
  peer of `gX` is the address of `Vr`, not an external destination.

  The adversary `q0` alone signs `Vx`. It challenged `Vx` before the start
  state, and `Vx` finalized with `ΩX`. The answer of the adversary to each
  move of Alice: call `reclaim Lr Vx` first, then land Alice's calls.
  * While `Lr` is not finalized, the reclaim reverts.
  * When `Lr` is finalized with `oX`, the reclaim succeeds.
    `Allocation.addTo` rewrites the entry of `Vr` from a guarantee to `.alloc`.
  * After that, `reclaim Lr Vr` reverts: the entry of `Vr` is not a guarantee.
    `transfer Lr Vr.address` reverts: `Vr` is virtual, so its address is not
    fundable. No operation removes the entry of `Vr`.

  So the stored outcome of `Lr` always has an entry for `Vr`, and the goal
  `EndUserRecovered` never holds (`not_unbeatable`). The `example` at the end
  applies the library theorem to this instance and derives `False`.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/satp_end_user_recovers.lean`.
-/
import ArmadaLean.Nitro.NonVacuity

namespace ArmadaLean.Nitro.Counterexample.EndUser

open ArmadaLean.Nitro ArmadaLean.Nitro.NonVacuity

/-! ## The instance -/

/-- A second virtual channel. Only the adversary `q0` signs it. -/
def Vx : FixedPart := ⟨[q0], 12, ⟨0⟩, 2, .virtual⟩

def ΩX : Outcome Nat := .allocation [alloc (.external 1) 1, alloc (.external 1) 0]

def SX : State Nat := ⟨Vx, 0, ΩX, false, .opaque 0⟩

/-- The guarantee for `Vx`. Its left peer is the address of `Vr`. -/
def gX : Entry Nat := ⟨Vx.address, .guarantee 1 [Vr.address, .external 1]⟩

/-- Alice's latest allocation of `Lr`. -/
def oX : Allocation Nat := [alloc (.external 0) 0, alloc (.external 1) 0, r2.guarantee p0 q0, gX]

def SL : State Nat := ⟨Lr, 1, .allocation oX, false, .opaque 0⟩

def sX : Adjudicator Nat :=
  ((g0.setStatus Vr (.challenged 0 ⟨V0r, 0 + Vr.challengeDuration⟩)).setStatus Vx
    (.challenged 0 ⟨SX, 0 + Vx.challengeDuration⟩)).tick 2

def netX : NetworkState Nat p0 :=
  ⟨sX, [⟨SX, [q0]⟩, ⟨V0r, [p0, q0]⟩, ⟨SL, [q0]⟩, ⟨V0r, [q0]⟩], [⟨SL, [p0]⟩, ⟨V0r, [p0]⟩]⟩

/-- `netX` is reachable: `netE_reach` of `NonVacuity.lean` with `SL` for
    `S0`, and one more adversary move before the wait: `q0` challenges `Vx`. -/
theorem netX_reach : (Nitro.participant apps2 (canon p0)).Reachable netX :=
  participant_reachable_honest
    (participant_reachable_adv
      (participant_reachable_land
        (participant_reachable_adv
          (participant_reachable_honest
            (participant_reachable_adv
              (participant_reachable_honest (participant_reachable_init apps2 (canon p0))
                (.send V0r) (by simp))
              (.deliver ⟨V0r, [q0]⟩) (by
                refine ⟨fun h => absurd h (by decide), fun v h hp => ?_⟩
                cases h; exact absurd hp (by decide)))
            (.send SL) (by simp))
          (.deliver ⟨SL, [q0]⟩) (by
            refine ⟨fun h => absurd h (by decide), fun v h => ?_⟩
            cases h))
        (.challenge Vr [⟨V0r, [p0, q0]⟩] V0r)
        (fun ss h => by
          simp only [Op.proofStates, List.mem_singleton] at h; subst h
          refine ⟨fun q hq => ?_, fun v hv => ?_⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact .inl ⟨rfl, ⟨V0r, [p0]⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
            · exact .inr ⟨⟨V0r, [q0]⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
                List.mem_cons_self⟩
          · cases hv
            exact fun q hq => absurd hq List.not_mem_nil))
      (.chain q0 (.challenge Vx [⟨SX, [q0]⟩] SX))
      ⟨by decide, fun ss h => by
        simp only [Op.proofStates, List.mem_singleton] at h; subst h
        exact ⟨fun h => absurd h (by decide), fun v h => by cases h⟩⟩)
    (.wait 2) trivial

/-! ## Allocation facts -/

/-- `addTo` keeps an `.alloc` entry for `d` an `.alloc` entry. -/
theorem find_addTo_alloc {o : Allocation Nat} {d : Address Nat} {a : Coins}
    (h : o.find d = some ⟨d, .alloc a⟩) (e : Address Nat) (x : Coins) :
    ∃ a', (o.addTo e x).find d = some ⟨d, .alloc a'⟩ := by
  by_cases he : d = e
  · subst he
    rw [Allocation.find_addTo_self, h]
    exact ⟨_, rfl⟩
  · rw [Allocation.find_addTo_of_ne _ _ he]
    exact ⟨a, h⟩

/-! ## The invariant -/

/-- Every state of `Lr` that carries the signature of `q0` and that `p0`
    received is `SL`. -/
def RecOK (n : NetworkState Nat p0) : Prop :=
  ∀ r ∈ n.received, q0 ∈ r.signers → r.state.channel = Lr → r.state = SL

/-- `Lr` is finalized and its entry for `Vr` is an `.alloc` entry. -/
def Corrupt (s : Adjudicator Nat) : Prop :=
  ∃ t f o1 a, s.statusOf Lr = .finalized t f (.allocation o1) ∧
    o1.find Vr.address = some ⟨Vr.address, .alloc a⟩

/-- The status of `Lr` at the start of a round. -/
def LShape (s : Adjudicator Nat) : Prop :=
  (∃ k, s.statusOf Lr = .open k) ∨ (∃ k d, s.statusOf Lr = .challenged k ⟨SL, d⟩) ∨ Corrupt s

/-- The status of `Lr` while the calls of `p0` land: a challenge has not
    expired. -/
def LShapeLive (s : Adjudicator Nat) : Prop :=
  (∃ k, s.statusOf Lr = .open k) ∨ (∃ k d, s.statusOf Lr = .challenged k ⟨SL, d⟩ ∧ s.now < d) ∨
    Corrupt s

def Inv (n : NetworkState Nat p0) : Prop :=
  RecOK n ∧ n.chain.finalizedWith Vx.address = some ΩX ∧ LShape n.chain

def InvL (n : NetworkState Nat p0) : Prop :=
  RecOK n ∧ n.chain.finalizedWith Vx.address = some ΩX ∧ LShapeLive n.chain

/-- A call `p0` can issue when `RecOK` holds. -/
def Good (op : Op Nat) : Prop :=
  (∀ dt, op ≠ .tick dt) ∧ (∀ a e x, op ≠ .deposit a e x) ∧
    ∀ ss ∈ op.proofStates, q0 ∈ ss.signers → ss.state.channel = Lr → ss.state = SL

theorem good_of_feasible {n : NetworkState Nat p0} (hR : RecOK n) {op : Op Nat}
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
    rcases hh.1 q0 hq with ⟨hqp, -⟩ | ⟨r, hr, hrs, hqr⟩
    · exact absurd hqp (by decide)
    · rw [← hrs]; exact hR r hr hqr (by rw [hrs]; exact hc)

theorem apps2_Lr : apps2 Lr.appDef = consensusRules := rfl

/-- A consensus support of a state of `Lr` whose proof meets `Good` is a
    support of `SL`. -/
theorem cand_eq {proof : SupportProof Nat} {cand : State Nat}
    (hgp : ∀ ss ∈ proof, q0 ∈ ss.signers → ss.state.channel = Lr → ss.state = SL)
    (hsupp : (apps2 Lr.appDef).supports Lr proof cand = true) : cand = SL := by
  rw [apps2_Lr] at hsupp
  rcases proof with _ | ⟨ss, _ | ⟨ss', rest⟩⟩
  · simp [consensusRules] at hsupp
  · simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hsupp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsupp
    have hq : q0 ∈ ss.signers := h3 q0 (by rw [h2]; decide)
    rw [← h1]; exact hgp ss List.mem_cons_self hq h2
  · simp [consensusRules] at hsupp

/-- `Corrupt` survives every successful operation. -/
theorem corrupt_step {caller : Participant} {op : Op Nat} {s s' : Adjudicator Nat}
    (h : s.apply apps2 caller op = some s') (hc : Corrupt s) : Corrupt s' := by
  obtain ⟨t, f, o1, a, hs, hfind⟩ := hc
  have hmode : (s.statusOf Lr).mode s.now = .finalized := by rw [hs]; rfl
  have hfo : s.finalOutcome Lr.address = some (.allocation o1) := by
    show (s.statusOf Lr).finalOutcome s.now = _; rw [hs]; rfl
  by_cases ht : Op.targets op Lr
  · cases op with
    | deposit => simp [Op.targets] at ht
    | tick => simp [Op.targets] at ht
    | transfer a' b =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨o, -, x, hf, -, -, -, -, hst, -, -, hb⟩ := Adjudicator.transfer_some h
      rw [hfo] at hf; cases hf
      have hbV : (Vr.address : Address Nat) ≠ b := by
        rintro rfl; exact absurd hb (by decide)
      refine ⟨t, f, o1.reduceOwed b x, a, ?_, ?_⟩
      · rw [Adjudicator.statusOf_of_status hst]; simp [hs]
      · rw [Allocation.find_reduceOwed, if_neg hbV]; exact hfind
    | reclaim l v =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨oL, oV, x, left, right, hL, -, hfv, -, -, -, rfl, -, -⟩ := Adjudicator.reclaim_some h
      rw [hfo] at hL; cases hL
      have hvV : (Vr.address : Address Nat) ≠ v.address := by
        intro heq; rw [← heq, hfind] at hfv; cases hfv
      obtain ⟨a1, h1⟩ := find_addTo_alloc hfind left (oV.amountAt 0)
      obtain ⟨a2, h2⟩ := find_addTo_alloc h1 right (oV.amountAt 1)
      refine ⟨t, f, ((o1.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address,
        a2, ?_, ?_⟩
      · simp [hs]
      · rw [Allocation.find_remove, if_neg hvV]; exact h2
    | challenge c proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, -, -, hm⟩, -⟩ := Adjudicator.challenge_some h
      rw [Adjudicator.mode_eq, hmode] at hm
      rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
    | checkpoint c proof cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨ho, -⟩, -⟩ := Adjudicator.checkpoint_some h
      exact absurd hmode ho
    | conclude c ss =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨ho, -⟩, -⟩ := Adjudicator.conclude_some h
      exact absurd hmode ho
  · refine ⟨t, f, o1, a, ?_, hfind⟩
    rw [statusOf_apply_of_not_targets h ht, hs]

/-- A call of `p0` that meets `Good`, while `Lr` has no final outcome. -/
theorem live_pre {op : Op Nat} {s s' : Adjudicator Nat} (hg : Good op)
    (h : s.apply apps2 p0 op = some s') (hnow : s'.now = s.now)
    (hL : (∃ k, s.statusOf Lr = .open k) ∨
      (∃ k d, s.statusOf Lr = .challenged k ⟨SL, d⟩ ∧ s.now < d)) : LShapeLive s' := by
    have hnf : s.finalOutcome Lr.address = none := by
      show (s.statusOf Lr).finalOutcome s.now = none
      rcases hL with ⟨k, hk⟩ | ⟨k, d, hk, hd⟩
      · rw [hk]; rfl
      · rw [hk]; simp only [ChannelStatus.finalOutcome]; rw [if_neg (Nat.not_le.mpr hd)]
    by_cases ht : Op.targets op Lr
    · cases op with
      | deposit a e x => exact absurd rfl (hg.2.1 a e x)
      | tick dt => exact absurd rfl (hg.1 dt)
      | transfer a b =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨o, -, -, hf, -⟩ := Adjudicator.transfer_some h
        rw [hnf] at hf; cases hf
      | reclaim l v =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨oL, -, -, -, -, hf, -⟩ := Adjudicator.reclaim_some h
        rw [hnf] at hf; cases hf
      | challenge c proof cand =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨⟨-, hsupp, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
        have hcand := cand_eq hg.2.2 hsupp
        subst hcand
        refine .inr (.inl ⟨SL.turnNum, s.now + Lr.challengeDuration, by simp, ?_⟩)
        simp [Lr]
      | checkpoint c proof cand =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        exact .inl ⟨cand.turnNum, by simp⟩
      | conclude c ss =>
        simp only [Op.targets] at ht; subst ht
        obtain ⟨⟨-, hc, hfin, hall⟩, -⟩ := Adjudicator.conclude_some h
        have hq : q0 ∈ ss.signers := hall q0 (by rw [hc]; decide)
        have hss := hg.2.2 ss List.mem_cons_self hq hc
        rw [hss] at hfin; cases hfin
    · have hst := statusOf_apply_of_not_targets h ht
      rcases hL with ⟨k, hk⟩ | ⟨k, d, hk, hd⟩
      · exact .inl ⟨k, by rw [hst, hk]⟩
      · exact .inr (.inl ⟨k, d, by rw [hst, hk], by rw [hnow]; exact hd⟩)

/-- A call of `p0` that meets `Good` keeps `LShapeLive`. -/
theorem live_step {op : Op Nat} {s s' : Adjudicator Nat} (hg : Good op)
    (h : s.apply apps2 p0 op = some s') (hL : LShapeLive s) : LShapeLive s' := by
  have hnow : s'.now = s.now := Adjudicator.apply_now_eq_of_not_tick hg.1 h
  rcases hL with hL | hL | hc
  · exact live_pre hg h hnow (.inl hL)
  · exact live_pre hg h hnow (.inr hL)
  · exact .inr (.inr (corrupt_step h hc))

/-- The calls of `p0` land one after the other; `InvL` holds and the clock
    does not move. -/
theorem land_all (t : Time) : ∀ (pending : List (Op Nat)), (∀ op ∈ pending, Good op) →
    ∀ (n : NetworkState Nat p0), InvL n →
      ∃ n', Threat.RoundSeq apps2 (canon p0) t pending n n' ∧ InvL n' ∧
        n'.chain.now = n.chain.now := by
  intro pending
  induction pending with
  | nil => intro _ n hI; exact ⟨n, .nil, hI, rfl⟩
  | cons op rest ih =>
    intro hgood n hI
    have hg := hgood op List.mem_cons_self
    have hrest : ∀ op' ∈ rest, Good op' := fun op' h => hgood op' (List.mem_cons_of_mem op h)
    have key : InvL (n.applyAdv apps2 (.land op)) ∧
        (n.applyAdv apps2 (.land op)).chain.now = n.chain.now := by
      simp only [NetworkState.applyAdv]
      cases happ : n.chain.apply apps2 p0 op with
      | none => exact ⟨hI, rfl⟩
      | some s' =>
        obtain ⟨hR, hv, hL⟩ := hI
        refine ⟨⟨?_, Adjudicator.finalizedWith_apply happ hv, live_step hg happ hL⟩,
          Adjudicator.apply_now_eq_of_not_tick hg.1 happ⟩
        intro r hr hq hc
        rcases List.mem_append.1 hr with hr | hr
        · exact hg.2.2 r hr hq hc
        · exact hR r hr hq hc
    obtain ⟨hI1, hnow1⟩ := key
    obtain ⟨n', hseq, hI', hnow'⟩ := ih hrest _ hI1
    exact ⟨n', .land (l1 := []) (l2 := rest) rfl hseq, hI', by rw [hnow', hnow1]⟩

/-- The final allocation of `Lr` after the reclaim of `Vx`. -/
def oX' : Allocation Nat :=
  [alloc (.external 0) 0, alloc (.external 1) (0 + 0), ⟨Vr.address, .alloc (1 + 1)⟩]

/-- When the challenge of `Lr` has expired, `reclaim Lr Vx` succeeds. -/
theorem reclaim_Vx {s : Adjudicator Nat} {k : Nat} {d : Time}
    (hk : s.statusOf Lr = .challenged k ⟨SL, d⟩) (hd : d ≤ s.now)
    (hv : s.finalizedWith Vx.address = some ΩX) :
    s.reclaim Lr Vx = some (s.setStatus Lr (.finalized k (.allocation oX) (.allocation oX'))) := by
  have hfo : s.finalOutcome Lr.address = some (.allocation oX) := by
    show (s.statusOf Lr).finalOutcome s.now = _
    rw [hk]; simp only [ChannelStatus.finalOutcome]; rw [if_pos hd]; rfl
  have hfind : oX.find Vx.address = some gX := by decide
  unfold Adjudicator.reclaim
  rw [if_pos ⟨rfl, rfl⟩, hfo, hv]
  simp only [ΩX, gX] at hfind ⊢
  rw [hfind]
  dsimp only
  split_ifs with hc
  · rw [hk]; rfl
  · exact absurd (by decide) hc

/-- The adversary's first move of each round: `reclaim Lr Vx`. -/
theorem adv_first {n : NetworkState Nat p0} (hI : Inv n) :
    InvL (n.applyAdv apps2 (.chain q0 (.reclaim Lr Vx))) ∧
      (n.applyAdv apps2 (.chain q0 (.reclaim Lr Vx))).chain.now = n.chain.now := by
  obtain ⟨hR, hv, hL⟩ := hI
  have hnot : ∀ dt, (Op.reclaim Lr Vx : Op Nat) ≠ .tick dt := by intro dt h; cases h
  -- The expired challenge: the reclaim succeeds and the entry of `Vr` becomes `.alloc`.
  by_cases hexp : ∃ k d, n.chain.statusOf Lr = .challenged k ⟨SL, d⟩ ∧ d ≤ n.chain.now
  · obtain ⟨k, d, hk, hd⟩ := hexp
    have happ : n.chain.apply apps2 q0 (.reclaim Lr Vx) =
        some (n.chain.setStatus Lr (.finalized k (.allocation oX) (.allocation oX'))) :=
      reclaim_Vx hk hd hv
    rw [NetworkState.applyAdv_chain_some _ happ]
    refine ⟨⟨fun r hr => hR r (by simpa [Op.proofStates] using hr),
      Adjudicator.finalizedWith_apply happ hv,
      .inr (.inr ⟨k, .allocation oX, oX', 1 + 1, by simp, by decide⟩)⟩, rfl⟩
  · have hL' : LShapeLive n.chain := by
      rcases hL with h | ⟨k, d, hk⟩ | h
      · exact .inl h
      · exact .inr (.inl ⟨k, d, hk, by
          by_contra hlt; exact hexp ⟨k, d, hk, Nat.not_lt.mp hlt⟩⟩)
      · exact .inr (.inr h)
    cases happ : n.chain.apply apps2 q0 (.reclaim Lr Vx) with
    | none => rw [NetworkState.applyAdv_chain_none _ happ]; exact ⟨⟨hR, hv, hL'⟩, rfl⟩
    | some s' =>
      rw [NetworkState.applyAdv_chain_some _ happ]
      refine ⟨⟨fun r hr => hR r (by simpa [Op.proofStates] using hr),
        Adjudicator.finalizedWith_apply happ hv, ?_⟩,
        Adjudicator.apply_now_eq_of_not_tick hnot happ⟩
      rcases hL' with ⟨k, hk⟩ | ⟨k, d, hk, hd⟩ | hc
      · obtain ⟨oL, -, -, -, -, hf, -⟩ := Adjudicator.reclaim_some happ
        have : n.chain.finalOutcome Lr.address = none := by
          show (n.chain.statusOf Lr).finalOutcome n.chain.now = none; rw [hk]; rfl
        rw [this] at hf; cases hf
      · obtain ⟨oL, -, -, -, -, hf, -⟩ := Adjudicator.reclaim_some happ
        have : n.chain.finalOutcome Lr.address = none := by
          show (n.chain.statusOf Lr).finalOutcome n.chain.now = none
          rw [hk]; simp only [ChannelStatus.finalOutcome]; rw [if_neg (Nat.not_le.mpr hd)]
        rw [this] at hf; cases hf
      · exact .inr (.inr (corrupt_step happ hc))

/-- The answer of the adversary to any move of `p0`. -/
theorem round (n : NetworkState Nat p0) (hI : Inv n) (m : HonestMove Nat) (hfeas : m.Feasible n) :
    ∃ n', (canon p0).Round apps2 m n n' ∧ Inv (n'.applyHonest m) := by
  have hgood : ∀ op ∈ m.calls, Good op := by
    cases m with
    | react r => intro op hop; exact good_of_feasible hI.1 (hfeas op hop)
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  set n1 := n.applyAdv apps2 (.chain q0 (.reclaim Lr Vx)) with hn1
  obtain ⟨hI1, hnow1⟩ := adv_first hI
  obtain ⟨n', hseq, ⟨hR', hv', hL'⟩, hnow'⟩ := land_all n.chain.now m.calls hgood n1 hI1
  have hfeasq : (canon p0).feasible n (.chain q0 (.reclaim Lr Vx)) :=
    ⟨by decide, by simp [Op.proofStates]⟩
  refine ⟨n', ⟨.other hfeasq (by intro dt h; cases h) (by intro o h; cases h) hseq, ?_⟩, ?_⟩
  · rw [hnow', hnow1]; exact Nat.lt_add_of_pos_right (canon p0).ε_pos
  · have hL : LShape n'.chain := by
      rcases hL' with h | ⟨k, d, hk, -⟩ | h
      · exact .inl h
      · exact .inr (.inl ⟨k, d, hk⟩)
      · exact .inr (.inr h)
    cases m with
    | react r => exact ⟨hR', hv', hL⟩
    | wait dt =>
      refine ⟨hR', ?_, ?_⟩
      · simp only [NetworkState.applyHonest, FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.tick_statusOf, Adjudicator.tick_now] at hv' ⊢
        exact ChannelStatus.finalizedWith_mono hv' (Nat.le_add_right _ _)
      · simp only [NetworkState.applyHonest, LShape, Corrupt, Adjudicator.tick_statusOf]
        exact hL

/-- `Inv` rules out the goal. -/
theorem not_goal (bal share base : Coins) {n : NetworkState Nat p0} (hI : Inv n) :
    ¬ EndUserRecovered r2 Lr bal share base n := by
  rintro ⟨o, hf, hnone, -⟩
  change (n.chain.statusOf Lr).finalOutcome n.chain.now = _ at hf
  change o.find Vr.address = none at hnone
  rcases hI.2.2 with ⟨k, hk⟩ | ⟨k, d, hk⟩ | ⟨t, f, o1, a, hk, hfind⟩
  · rw [hk] at hf; cases hf
  · rw [hk] at hf
    simp only [ChannelStatus.finalOutcome] at hf
    split at hf
    · cases hf; exact absurd hnone (by decide)
    · cases hf
  · rw [hk] at hf; cases hf; rw [hfind] at hnone; cases hnone

theorem not_unbeatable (bal share base : Coins) (n : NetworkState Nat p0)
    (h : Unbeatable apps2 (canon p0) (EndUserRecovered r2 Lr bal share base) n) : Inv n → False := by
  induction h with
  | done hG => intro hI; exact not_goal bal share base hI hG
  | move m _ hfeas _ ih =>
    intro hI
    obtain ⟨n', hR, hI'⟩ := round _ hI m hfeas
    exact ih n' hR hI'

theorem inv_netX : Inv netX := by
  refine ⟨?_, by decide, .inl ⟨0, by decide⟩⟩
  intro r hr hq hc
  simp only [netX, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · rfl
  · exact absurd hc (by decide)

/-- `p0` has no unbeatable strategy for `EndUserRecovered` from `netX`. -/
theorem netX_not_unbeatable :
    ¬ Unbeatable apps2 (canon p0)
      (EndUserRecovered r2 Lr 1 1 (netX.chain.balances.get (.external (r2.dest p0)))) netX :=
  fun h => not_unbeatable _ _ _ netX h inv_netX

/-! ## The hypotheses of `satp_end_user_recovers` hold at `netX`. -/

theorem netX_latest : HoldsLatestLedger netX Lr oX := by
  refine ⟨⟨SL, [p0, q0]⟩, ⟨fun q hq => ?_, fun v hv => ?_⟩, by decide, rfl, rfl, rfl, ?_,
    .inl ⟨0, by decide, by decide⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact .inl ⟨rfl, ⟨SL, [p0]⟩, List.mem_cons_self, rfl⟩
    · exact .inr ⟨⟨SL, [q0]⟩, by simp [netX], rfl, List.mem_cons_self⟩
  · simp [SL, State.voucher?] at hv
  · intro t ht hc
    simp only [netX, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨Or.inr rfl, rfl⟩
    · exact absurd hc (by decide)

theorem netX_setup : HoldsVirtualSetup netX r2 p0 q0 true := by
  refine ⟨?_, ⟨V0r, [p0]⟩, by simp [netX], rfl, rfl⟩
  intro t ht hc
  simp only [netX, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact absurd hc (by decide)
  · exact ⟨rfl, rfl, .inl rfl⟩


/-
  The own-violation: Alice's `oX` holds a guarantee whose peer is the virtual
    channel `Vr`, so the restated theorem makes no promise to her. -/
theorem oX_violates_hog : ¬ (∀ e ∈ oX, ∀ x ps, e.item = .guarantee x ps → ∀ d ∈ ps, d.isExternal = true) := by
  intro h
  have hmem : gX ∈ oX := by decide
  have hspec : ∀ x ps, gX.item = .guarantee x ps → ∀ d ∈ ps, d.isExternal = true := h gX hmem
  have hinst : ∀ d ∈ [Vr.address, .external 1], d.isExternal = true := hspec 1 [Vr.address, .external 1] (by decide)
  have hd : Vr.address ∈ [Vr.address, .external 1] := by decide
  have htrue : (Vr.address : Address Nat).isExternal = true := hinst Vr.address hd
  have hfalse : (Vr.address : Address Nat).isExternal = false := by decide
  contradiction
end ArmadaLean.Nitro.Counterexample.EndUser

#print axioms ArmadaLean.Nitro.Counterexample.EndUser.netX_not_unbeatable
#print axioms ArmadaLean.Nitro.Counterexample.EndUser.netX_reach
#print axioms ArmadaLean.Nitro.Counterexample.EndUser.netX_latest
#print axioms ArmadaLean.Nitro.Counterexample.EndUser.netX_setup
