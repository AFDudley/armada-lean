/-
  Failure test: both Nitro-24 statements without the premise
  `hpend : net.state.DeadlineAfter c T.ε` (Nitro:653-658;
  `NoDeadline_finalizable_or_two_enabled`, `NoDeadline_single_enabled_is_finalizable`
  below, the forms of `ArmadaLean/Spec/Nitro/Liveness.lean` before that premise).

  The app is go-nitro's payment app `SingleAssetPayments.sol` on a two-party
  channel, as in `single_asset_payments_ir.lean`: a ForceMove app
  (`forceMoveRules vtS`), desirable for the destination map `destS`
  (`appsS_desirable`). The threat is `T0.noOwnViolation destS`: the adversary
  commits no own-violation. The channel `c0` has the participants `[q0, p0]`,
  so `q0` moves at even turns and `p0` at odd turns (`n = 2`), and `ε = 2`.

  The history (`net_reachable`): the setup states `r0` (turn 0, `q0`) and `s1`
  (turn 1, `p0`) carry `OC = pay 5 5`. `q0` keeps `OC` at turn 2 (`r2`). `p0`
  pays 2 coins at turn 3 (`s3`, `OA = pay 3 7`), and `q0` keeps `OA` at turn 4
  (`r4`). Turn 5 is `p0`'s turn, and `p0` has not moved. At time 0 the
  adversary challenged with `[r0, s1]`, so the status is a challenge with `OC`
  at turn 1 and the deadline 6. `p0` did not answer. The clock is now 5: the
  challenge ends within `ε`.

  * `OC` is enabled (`enabled_OC`): the adversary ticks to the deadline before
    `p0`'s calls land.
  * No outcome but `OC` is enabled (`prevents_other`). For a target `Ω ≠ OC`,
    `p0` signs `s5 X`, a move at turn 5 that pays `q0` more (`X ≠ Ω`), and it
    answers every challenge with `OA` by a challenge with `[r4, s5 X]`. Every
    support that the adversary can use carries the outcome of the state of
    `p0` in it (`cand_outcome`): a later move of `q0` that changes the outcome
    pays `p0` from `q0`'s own entry, a gift. So only `OC` and `X` finalize.
  * No outcome is finalizable (`not_finalizable`). For `OC`: the adversary
    challenges with `[r2, s3]` (`OA`, turn 3) before the deadline, and no move
    by the rules gives `p0` its 5 coins back. For every other outcome: the
    adversary lets `OC` finalize.

  So `p0` has no finalizable outcome and exactly one enabled outcome. The
  cause is timing: a pending challenge ends within `ε`. With
  `DeadlineAfter c ε` the history cannot end in this state
  (`net_not_deadlineAfter`).

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/pending_deadline.lean`.
  The theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Spec.Nitro.Liveness
import ArmadaLean.Nitro.TakeOut

namespace ArmadaLean.Nitro.CounterexamplePending

open ArmadaLean.Nitro

/-! ## The instance -/

def q0 : Participant := ⟨0⟩
def p0 : Participant := ⟨1⟩

theorem p0_ne_q0 : p0 ≠ q0 := by decide

/-- The destination map: a participant is paid at its own key. -/
def destS (q : Participant) : Nat := q.key

def dQ : Address Nat := .external (destS q0)
def dP : Address Nat := .external (destS p0)

/-- The two-slot allocation: `a` to `p0`, `b` to `q0`. -/
def pay (a b : Nat) : Outcome Nat := .allocation [alloc dQ b, alloc dP a]

/-- The setup outcome. -/
def OC : Outcome Nat := pay 5 5
/-- The outcome after `p0` paid 2 coins. -/
def OA : Outcome Nat := pay 3 7

def decode : Outcome Nat → Option (Nat × Nat)
  | .allocation [⟨.external 0, .alloc b⟩, ⟨.external 1, .alloc a⟩] => some (a, b)
  | _ => none

theorem decode_pay (a b : Nat) : decode (pay a b) = some (a, b) := rfl

theorem decode_eq_some {Ω : Outcome Nat} {a b : Nat} : decode Ω = some (a, b) ↔ Ω = pay a b := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · cases h; rfl
    · cases h
  · rintro rfl; rfl

theorem pay_inj {a b a' b' : Nat} (h : pay a b = pay a' b') : a = a' ∧ b = b' := by
  have := congrArg decode h
  rw [decode_pay, decode_pay] at this
  exact Prod.mk.inj (Option.some.inj this)

def c0 : FixedPart :=
  { participants := [q0, p0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 6, kind := .ledger }

/-- The game library of go-nitro `SingleAssetPayments.sol` on the two slots of
    `c0`: the total stays, and a non-mover's balance does not fall. -/
def vtS (s s' : State Nat) : Bool :=
  match decode s.outcome, decode s'.outcome with
  | some (a, b), some (a', b') =>
    decide (a + b = a' + b') && (decide (s'.mover = some q0) || decide (b ≤ b')) &&
      (decide (s'.mover = some p0) || decide (a ≤ a'))
  | _, _ => false

theorem vtS_iff (s s' : State Nat) : vtS s s' = true ↔ ∃ a b a' b', decode s.outcome = some (a, b) ∧
    decode s'.outcome = some (a', b') ∧ a + b = a' + b' ∧ (s'.mover = some q0 ∨ b ≤ b') ∧
    (s'.mover = some p0 ∨ a ≤ a') := by
  unfold vtS
  split
  · rename_i a b a' b' h1 h2
    simp [h1, h2, and_assoc]
  · rename_i h
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro a b a' b' h1 h2
    exact (h a b a' b' h1 h2).elim

def appsS : Apps Nat := fun _ => forceMoveRules vtS

/-- The non-final state of `c0` at turn `k` with the outcome `o`. -/
def st (k : Nat) (o : Outcome Nat) : State Nat :=
  { channel := c0, turnNum := k, outcome := o, isFinal := false, appData := .opaque 0 }

def r0 : SignedState Nat := ⟨st 0 OC, [q0]⟩
def s1 : SignedState Nat := ⟨st 1 OC, [p0]⟩
def r2 : SignedState Nat := ⟨st 2 OC, [q0]⟩
def s3 : SignedState Nat := ⟨st 3 OA, [p0]⟩
def r4 : SignedState Nat := ⟨st 4 OA, [q0]⟩

/-- The base threat: any call by another participant that forges no
    signature of `p0`, any unforged delivery, any tick. -/
def T0 : Threat Nat p0 where
  feasible net m := match m with
    | .chain caller op => caller ≠ p0 ∧ ∀ ss ∈ op.proofStates, net.Unforged ss
    | .deliver ss => net.Unforged ss
    | .tick _ => True
    | .land _ => True
  ε := 2
  ε_pos := Nat.two_pos

theorem A0 : Assumptions appsS p0 T0 where
  unforgeable := fun _ _ _ h => h.2
  unforgeableDeliver := fun _ _ h => h
  notHonest := fun _ _ _ h => h.1
  capable := fun _ _ _ h1 h2 => ⟨h1, h2⟩
  capableDeliver := fun _ _ h => h
  capableTick := fun _ _ => trivial
  clockRuns := le_refl 2

/-- The threat of the statements: no own-violation of `q0`. -/
abbrev TN : Threat Nat p0 := T0.noOwnViolation destS

def tc0 : TimedChannel T0.ε := ⟨c0, by decide⟩

theorem round_bound {m : HonestMove Nat} {n n' : NetworkState Nat p0}
    (h : TN.Round appsS m n n') : n'.chain.now < n.chain.now + 2 := h.2

theorem mkRound {m : HonestMove Nat} {n n' : NetworkState Nat p0}
    (hseq : TN.RoundSeq appsS n.chain.now m.calls n n') (hnow : n'.chain.now = n.chain.now + 1) :
    TN.Round appsS m n n' :=
  ⟨hseq, by rw [hnow]; exact Nat.add_lt_add_left (show 1 < T0.ε by decide) _⟩

/-! ## The app is desirable -/

theorem share_pay (a b k : Nat) :
    share (pay a b) k = if k = 0 then b else if k = 1 then a else 0 := by
  rcases k with _ | _ | k <;>
    simp [share, pay, Outcome.entries, Allocation.owed, Allocation.find, alloc, dQ, dP, destS, q0, p0,
      Entry.amount, Item.amount]

theorem noTake_vtS : NoTakeFromNonMover vtS destS := by
  intro s s' h q hq
  obtain ⟨a, b, a', b', h0, h1, -, hb, ha⟩ := (vtS_iff _ _).1 h
  rw [decode_eq_some.1 h0, decode_eq_some.1 h1, share_pay, share_pay]
  rcases q with ⟨_ | _ | k⟩
  · have : b ≤ b' := by
      rcases hb with h | h
      · exact absurd h hq
      · exact h
    simpa [destS] using this
  · have : a ≤ a' := by
      rcases ha with h | h
      · exact absurd h hq
      · exact h
    simpa [destS] using this
  · simp [destS]

theorem stay_vtS : ∀ s s', vtS s s' = true → vtS s' { s' with turnNum := s'.turnNum + 1 } = true := by
  intro s s' h
  obtain ⟨-, -, a', b', -, h1, -⟩ := (vtS_iff _ _).1 h
  exact (vtS_iff _ _).2 ⟨a', b', a', b', h1, h1, rfl, Or.inr (le_refl _), Or.inr (le_refl _)⟩

theorem conserve_vtS : ∀ s s' q, vtS s s' = true → s'.mover = some q →
    ConservingStep destS q s.outcome s'.outcome := by
  intro s s' q h hq
  obtain ⟨a, b, a', b', h0, h1, hsum, hb, ha⟩ := (vtS_iff _ _).1 h
  rw [decode_eq_some.1 h0, decode_eq_some.1 h1]
  refine Or.inr ⟨rfl, (by decide : List.Nodup [dQ, dP]), fun e he => ?_, ?_,
    fun i e e' he he' hlt => ?_⟩
  · simp only [pay, Outcome.entries, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> rfl
  · simp only [pay, Outcome.entries, Allocation.total, alloc, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Entry.amount, Item.amount]
    show (b' + (a' + 0) : Nat) = b + (a + 0)
    omega
  · rcases i with _ | _ | i
    · obtain rfl := Option.some.inj he.symm
      obtain rfl := Option.some.inj he'.symm
      have hlt' : b' < b := hlt
      rcases hb with h | h
      · rw [hq] at h
        obtain rfl := Option.some.inj h
        exact ⟨rfl, fun r hr => by
          rcases r with ⟨k⟩
          have : 0 = k := by simpa [alloc, dQ, destS, q0] using hr
          rw [← this]; rfl⟩
      · omega
    · obtain rfl := Option.some.inj he.symm
      obtain rfl := Option.some.inj he'.symm
      have hlt' : a' < a := hlt
      rcases ha with h | h
      · rw [hq] at h
        obtain rfl := Option.some.inj h
        exact ⟨rfl, fun r hr => by
          rcases r with ⟨k⟩
          have : 1 = k := by simpa [alloc, dP, destS, p0] using hr
          rw [← this]; rfl⟩
      · omega
    · cases he

/-- `SingleAssetPayments` is desirable: IR, IC and value conservation. -/
theorem appsS_desirable : Desirable appsS (tc0 : FixedPart).appDef destS :=
  ⟨TakeOut.forceMove_IR rfl noTake_vtS, TakeOut.forceMove_IC stay_vtS _,
    TakeOut.forceMove_conserving conserve_vtS _⟩

/-! ## Supports of `c0` -/

theorem mover_c0 {s : State Nat} (hc : s.channel = c0) :
    s.mover = some (if s.turnNum % 2 = 0 then q0 else p0) := by
  unfold State.mover
  rw [hc]
  rcases Nat.mod_two_eq_zero_or_one s.turnNum with h | h <;> simp [h, c0, FixedPart.n]

theorem byMover_even {m : SignedState Nat} (hc : m.state.channel = c0) (h : m.ByMover)
    (he : m.state.turnNum % 2 = 0) : q0 ∈ m.signers := by
  obtain ⟨w, hw, hmem⟩ := h
  rw [mover_c0 hc, if_pos he] at hw
  obtain rfl := Option.some.inj hw
  exact hmem

theorem byMover_odd {m : SignedState Nat} (hc : m.state.channel = c0) (h : m.ByMover)
    (ho : m.state.turnNum % 2 = 1) : p0 ∈ m.signers := by
  obtain ⟨w, hw, hmem⟩ := h
  rw [mover_c0 hc, if_neg (by omega)] at hw
  obtain rfl := Option.some.inj hw
  exact hmem

/-- A support of `c0` under `appsS`: two consecutive moves, each signed by
    its mover, the second the candidate, a valid move of `vtS` unless final. -/
structure Two (P : SupportProof Nat) (cand : State Nat) (m0 m1 : SignedState Nat) : Prop where
  eq : P = [m0, m1]
  last : m1.state = cand
  ch0 : m0.state.channel = c0
  ch1 : m1.state.channel = c0
  turn : m1.state.turnNum = m0.state.turnNum + 1
  mv0 : m0.ByMover
  mv1 : m1.ByMover
  fin : m1.state.isFinal = true → m1.state.outcome = m0.state.outcome
  vt : m1.state.isFinal = false → vtS m0.state m1.state = true

theorem fm2 {P : SupportProof Nat} {cand : State Nat}
    (h : (appsS c0.appDef).supports c0 P cand = true) : ∃ m0 m1, Two P cand m0 m1 := by
  have hv := forceMove_supports_valid_run vtS c0 P cand h
  have hk := forceMove_conclude_keeps_outcome vtS c0 P cand h
  have h' := h
  simp only [appsS, forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨hlen, hhead⟩, -⟩, hch⟩, -⟩ := h'
  obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, P = [m0, m1] := by
    rcases P with _ | ⟨m0, _ | ⟨m1, _ | ⟨m2, rest⟩⟩⟩ <;> simp [c0, FixedPart.n] at hlen ⊢
  obtain ⟨-, hstep, ml, hml, hmls⟩ := hv
  obtain ⟨-, ht, hmv1, hvt⟩ := hstep 0 m0 m1 rfl rfl
  have hfin := (hk 0 m0 m1 rfl rfl).1
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hml
  subst hml
  refine ⟨m0, m1, rfl, hmls, hch m0 (by simp), hch m1 (by simp), ht, ?_, hmv1, hfin, hvt⟩
  simp only [List.head?_cons, Option.all_some] at hhead
  exact (SignedState.byMover_iff _).1 hhead

theorem held_q {n : NetworkState Nat p0} {ss : SignedState Nat} (h : n.Holds ss)
    (hq : q0 ∈ ss.signers) : ∃ r ∈ n.received, r.state = ss.state ∧ q0 ∈ r.signers := by
  rcases h.1 q0 hq with ⟨hqp, -⟩ | hr
  · exact absurd hqp.symm p0_ne_q0
  · exact hr

theorem conclusion_p0 {ss : SignedState Nat} (h : ConclusionProof c0 ss) :
    p0 ∈ ss.signers ∧ ss.state.isFinal = true := by
  obtain ⟨hch, hfin, hall⟩ := h
  exact ⟨hall p0 (by rw [hch]; decide), hfin⟩

/-- One successful operation on `c0`: the status it leaves. -/
theorem status_cases {s s' : Adjudicator Nat} {caller : Participant} {op : Op Nat}
    (h : s.apply appsS caller op = some s') :
    s'.statusOf c0 = s.statusOf c0 ∨
    (∃ P cand, op = .challenge c0 P cand ∧ (appsS c0.appDef).supports c0 P cand = true ∧
      cand.channel = c0 ∧
      ((s.mode c0 = .open ∧ (s.statusOf c0).turnNumRecord ≤ cand.turnNum) ∨
        (s.mode c0 = .challenge ∧ (s.statusOf c0).turnNumRecord < cand.turnNum)) ∧
      s'.statusOf c0 = .challenged cand.turnNum ⟨cand, s.now + 6⟩) ∨
    (∃ P cand, op = .checkpoint c0 P cand ∧ (appsS c0.appDef).supports c0 P cand = true ∧
      (s.statusOf c0).IsOpen s.now ∧ (s.statusOf c0).turnNumRecord < cand.turnNum ∧
      s'.statusOf c0 = .open cand.turnNum) ∨
    (∃ ss, op = .conclude c0 ss ∧ ConclusionProof c0 ss) ∨
    (∃ o0 o', (s.statusOf c0).finalOutcome s.now = some o0 ∧
      s'.statusOf c0 = (s.statusOf c0).withOutcome o') := by
  rcases TakeOut.status_cases (c := c0) h with heq | ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩ |
      ⟨P, cand, rfl, hsup, -, hopen, hlt, hst⟩ | ⟨ss, rfl, hcp, -⟩ | hpay
  · exact Or.inl heq
  · exact Or.inr (Or.inl ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨P, cand, rfl, hsup, hopen, hlt, hst⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ss, rfl, hcp⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hpay)))

theorem holds_mono {n n' : NetworkState Nat p0} {ss : SignedState Nat}
    (hs : n.sent = n'.sent) (hr : ∀ r ∈ n.received, r ∈ n'.received) (h : n.Holds ss) :
    n'.Holds ss :=
  NetworkState.Holds.of_subset (fun _ hx => hs ▸ hx) hr h

theorem landed_now {n : NetworkState Nat p0} {op : Op Nat} (hop : ∀ dt, op ≠ .tick dt) :
    (n.applyAdv appsS (.land op)).chain.now = n.chain.now := by
  cases h : n.chain.apply appsS p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsS h]
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsS h]
    exact Adjudicator.apply_now_eq_of_not_tick hop h

theorem apply_now_le {s s' : Adjudicator Nat} {caller : Participant} {op : Op Nat}
    (h : s.apply appsS caller op = some s') : s.now ≤ s'.now := by
  by_cases ht : ∃ dt, op = .tick dt
  · obtain ⟨dt, rfl⟩ := ht
    simp only [Adjudicator.apply_tick, Option.some.injEq] at h
    subst h
    exact Nat.le_add_right _ _
  · exact le_of_eq (Adjudicator.apply_now_eq_of_not_tick (fun dt h => ht ⟨dt, h⟩) h).symm

/-! ## The reachable start -/

def ch1 : Challenge Nat := ⟨st 1 OC, 6⟩
def opC : Op Nat := .challenge c0 [r0, s1] (st 1 OC)
def sCh : Adjudicator Nat := Adjudicator.genesis.setStatus c0 (.challenged 1 ch1)

theorem opC_apply : Adjudicator.genesis.apply appsS q0 opC = some sCh := by
  show Adjudicator.genesis.challenge appsS q0 c0 [r0, s1] (st 1 OC) = some sCh
  unfold Adjudicator.challenge
  rw [if_pos (by decide)]
  rfl

def net : NetworkState Nat p0 := ⟨sCh.tick 5, [r4, r2, r0, s1, r0], [s3, s1]⟩

theorem unforged_q {n : NetworkState Nat p0} {k : Nat} {o : Outcome Nat} :
    n.Unforged ⟨st k o, [q0]⟩ :=
  ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0, fun v hv => by simp [st, State.voucher?] at hv⟩

theorem unforged_sent {n : NetworkState Nat p0} {s : SignedState Nat} (hs : s ∈ n.sent) :
    n.Unforged s :=
  ⟨fun _ => ⟨s, hs, rfl⟩, fun _ hv _ => ⟨s, hs, hv⟩⟩

/-- A delivery of a state that only `q0` signed, with no own-violation of
    `q0` against `received`. -/
theorem deliver_ok {n : NetworkState Nat p0} {k : Nat} {o : Outcome Nat}
    (h : ¬ OwnViolation destS q0 n.received ⟨st k o, [q0]⟩) :
    (AdvMove.deliver ⟨st k o, [q0]⟩).NoOwnViolation destS n := fun q hq _ => by
  rw [List.mem_singleton.1 hq]; exact h

theorem net_reachable : (Nitro.participant appsS TN).Reachable net := by
  refine ⟨⟨Adjudicator.genesis, [], []⟩, rfl, ?_⟩
  have hC : (⟨Adjudicator.genesis, [r0], [s1]⟩ : NetworkState Nat p0).applyAdv appsS (.chain q0 opC) =
      ⟨sCh, [r0, s1, r0], [s1]⟩ := NetworkState.applyAdv_chain_some appsS opC_apply
  refine .tail (b := ⟨sCh, [r4, r2, r0, s1, r0], [s3, s1]⟩) ?_
    (Or.inr (Or.inr (Or.inl ⟨.tick 5, ⟨trivial, trivial⟩, fun op h => (by cases h), rfl⟩)))
  refine .tail (b := ⟨sCh, [r2, r0, s1, r0], [s3, s1]⟩) ?_
    (Or.inr (Or.inr (Or.inl ⟨.deliver r4, ⟨unforged_q, deliver_ok (by decide)⟩,
      fun op h => (by cases h), rfl⟩)))
  refine .tail (b := ⟨sCh, [r2, r0, s1, r0], [s1]⟩) ?_ (Or.inl ⟨.send (st 3 OA),
    (HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
      HonestSend.fundsCommitted_of_fundable (by decide), fun _ => ⟨⟨[s1, r2], st 2 OC, ?_, by decide,
        rfl, rfl⟩, [r2, s3], ?_, by decide⟩, by decide, by decide⟩, rfl⟩)
  rotate_left
  · intro ss hss
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s1, List.mem_singleton_self _, rfl⟩,
        fun v hv => by simp [s1, st, State.voucher?] at hv⟩
    · exact holds_of_mem_received (by decide)
  · intro ss hss
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact .inl (holds_of_mem_received (by decide))
    · exact .inr rfl
  refine .tail (b := ⟨sCh, [r0, s1, r0], [s1]⟩) ?_
    (Or.inr (Or.inr (Or.inl ⟨.deliver r2, ⟨unforged_q, deliver_ok (by decide)⟩,
      fun op h => (by cases h), rfl⟩)))
  refine .tail (b := ⟨Adjudicator.genesis, [r0], [s1]⟩) ?_
    (Or.inr (Or.inr (Or.inl ⟨.chain q0 opC, ⟨⟨by decide, fun ss hss => ?_⟩,
      AdvMove.NoOwnViolation.chain_of (by decide)⟩, fun op h => (by cases h), hC.symm⟩)))
  rotate_left
  · simp only [opC, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact unforged_q
    · exact unforged_sent (n := ⟨Adjudicator.genesis, [r0], [s1]⟩) (List.mem_singleton_self _)
  refine .tail (b := ⟨Adjudicator.genesis, [r0], []⟩) ?_ (Or.inl ⟨.send (st 1 OC),
    (HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
      HonestSend.fundsCommitted_of_fundable (by decide), fun h => absurd h (by decide), by decide,
      by decide⟩, rfl⟩)
  exact .tail .refl
    (Or.inr (Or.inr (Or.inl ⟨.deliver r0, ⟨unforged_q, deliver_ok (by decide)⟩,
      fun op h => (by cases h), rfl⟩)))

/-- The challenge at `net` ends within `ε`: `net` breaks `DeadlineAfter`. -/
theorem net_not_deadlineAfter : ¬ net.DeadlineAfter c0 T0.ε := fun h =>
  absurd (h 1 ch1 rfl) (by decide)

/-! ## `OC` is enabled, and no other outcome is finalizable

The adversary ticks by 1 to the deadline 6 of `ch1` before `p0`'s calls
land. Then `c0` is finalized with `OC`, and a finalized outcome never
changes. -/

/-- The calls of `p0` land in order; the clock stays. -/
theorem land_all (t : Time) : ∀ (pending : List (Op Nat)), (∀ op ∈ pending, ∀ dt, op ≠ .tick dt) →
    ∀ x : NetworkState Nat p0, ∃ x', TN.RoundSeq appsS t pending x x' ∧ x'.chain.now = x.chain.now := by
  intro pending
  induction pending with
  | nil => exact fun _ x => ⟨x, .nil, rfl⟩
  | cons op rest ih =>
    intro hnt x
    obtain ⟨x', hseq, hnow⟩ := ih (fun o ho => hnt o (List.mem_cons_of_mem _ ho))
      (x.applyAdv appsS (.land op))
    exact ⟨x', .land (l1 := []) (l2 := rest) rfl hseq,
      by rw [hnow, landed_now (hnt op List.mem_cons_self)]⟩

theorem calls_not_tick {n : NetworkState Nat p0} {m : HonestMove Nat} (hfeas : m.Feasible appsS n) :
    ∀ op ∈ m.calls, ∀ dt, op ≠ .tick dt := by
  cases m with
  | react r => exact fun op hop => (hfeas.1 op hop).not_tick
  | wait dt => intro op hop; simp [HonestMove.calls] at hop

theorem net_tick_finalized : (net.applyAdv appsS (.tick 1)).chain.finalizedWith c0.address = some OC := by
  decide

/-- The first round of the adversary that finalizes `OC`: a tick of 1, then
    `p0`'s calls. -/
theorem roundOC {m : HonestMove Nat} (hfeas : m.Feasible appsS net) :
    ∃ n', TN.Round appsS m net n' ∧ n'.chain.finalizedWith c0.address = some OC := by
  obtain ⟨x', hseq, hnow⟩ := land_all 5 m.calls (calls_not_tick hfeas) (net.applyAdv appsS (.tick 1))
  refine ⟨x', ⟨.tick ⟨trivial, trivial⟩ (Or.inr (by decide)) hseq, ?_⟩,
    hseq.finalizedWith_mono net_tick_finalized⟩
  rw [hnow]; decide

theorem enabled_OC : Enabled appsS TN c0 OC net := by
  rintro ⟨σ, hσ, hprev⟩
  obtain ⟨n', hround, hf⟩ := roundOC (hσ net)
  exact hprev net n' .refl hround hf

theorem finalizedWith_applyHonest' (m : HonestMove Nat) (n : NetworkState Nat p0) {f : Outcome Nat}
    (hf : n.chain.finalizedWith c0.address = some f) :
    (n.applyHonest m).chain.finalizedWith c0.address = some f := by
  cases m with
  | react r => exact hf
  | wait dt => exact Adjudicator.finalizedWith_apply (show n.chain.apply appsS p0 (.tick dt) = _ from rfl) hf

theorem net_not_finalized (Ω : Outcome Nat) : ¬ net.Finalized c0 Ω := by
  intro h
  have : net.chain.finalizedWith c0.address = none := by decide
  rw [NetworkState.Finalized, this] at h
  cases h

theorem not_finalizable_other {Ω : Outcome Nat} (hΩ : Ω ≠ OC) : ¬ Finalizable appsS TN c0 Ω net := by
  intro hU
  cases hU with
  | done h => exact net_not_finalized Ω h
  | move m _ hfeas hcont =>
    obtain ⟨n', hround, hf⟩ := roundOC hfeas
    exact hΩ (UnbeatableIn.finalized_eq (hcont n' hround) (finalizedWith_applyHonest' m n' hf)).symm

/-! ## `OC` is not finalizable

In the first round the adversary challenges with `[r2, s3]` (`OA`, turn 3)
before the deadline of `ch1`. Then it only lands `p0`'s calls and ticks.
Every support of `c0` at a turn from 3 on that `p0` can use pays `p0` at
most 3: a state of `q0` from turn 4 on is `r4`'s state, and a state of `p0`
at an odd turn from 3 on is `s3`'s outcome or a move of `p0` after `r4`, in
which `p0` pays more. `OC` pays `p0` 5. -/

/-- The states that `q0` signed in the play. -/
def QOK (s : State Nat) : Prop := s = st 0 OC ∨ s = st 2 OC ∨ s = st 4 OA

/-- `p0`'s amount in an outcome. -/
abbrev amtP (Ω : Outcome Nat) : Nat := share Ω 1

theorem amtP_pay (a b : Nat) : amtP (pay a b) = a := by
  simp only [amtP, share_pay]; rfl

/-- A state of `p0` at an odd turn from 3 on pays `p0` at most 3. -/
def SentLow (n : NetworkState Nat p0) : Prop :=
  ∀ s ∈ n.sent, s.state.channel = c0 → s.state.turnNum % 2 = 1 → 3 ≤ s.state.turnNum →
    amtP s.state.outcome ≤ 3

structure InvN (n : NetworkState Nat p0) : Prop where
  recvQ : ∀ r ∈ n.received, q0 ∈ r.signers → QOK r.state
  recvU : ∀ r ∈ n.received, n.Unforged r
  s3in : s3 ∈ n.sent
  low : SentLow n

/-- The statuses from which `OC` is never finalized. -/
def SafeN (x : ChannelStatus Nat) : Prop :=
  (∃ t, x = .open t ∧ 3 ≤ t) ∨ (∃ t ch, x = .challenged t ch ∧ 3 ≤ t ∧ amtP ch.state.outcome ≤ 3) ∨
    (∃ t f o, x = .finalized t f o ∧ amtP f ≤ 3)

theorem safeN_not_finalized {n : NetworkState Nat p0} (h : SafeN (n.chain.statusOf c0)) :
    ¬ n.Finalized c0 OC := by
  intro hf
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf
  rcases h with ⟨t, ht, -⟩ | ⟨t, ch, ht, -, hle⟩ | ⟨t, f, o, ht, hle⟩
  · rw [ht] at hf; simp at hf
  · rw [ht] at hf
    simp only [ChannelStatus.finalizedWith_challenged] at hf
    split at hf
    · rw [Option.some.inj hf] at hle; exact absurd hle (by decide)
    · cases hf
  · rw [ht, ChannelStatus.finalizedWith_finalized] at hf
    rw [Option.some.inj hf] at hle; exact absurd hle (by decide)

theorem held_QOK {n : NetworkState Nat p0} (hI : InvN n) {ss : SignedState Nat} (h : n.Holds ss)
    (hq : q0 ∈ ss.signers) : QOK ss.state := by
  obtain ⟨r, hr, hrs, hrq⟩ := held_q h hq
  rw [← hrs]; exact hI.recvQ r hr hrq

theorem QOK_final {s : State Nat} (h : QOK s) : s.isFinal = false := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- A support that `p0` holds, at a turn from 3 on, pays `p0` at most 3. -/
theorem cand_low {n : NetworkState Nat p0} (hI : InvN n) {P : SupportProof Nat} {cand : State Nat}
    (h : (appsS c0.appDef).supports c0 P cand = true) (hH : ∀ ss ∈ P, n.Holds ss)
    (h3 : 3 ≤ cand.turnNum) : amtP cand.outcome ≤ 3 := by
  obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht, hmv0, hmv1, -, -⟩⟩ := fm2 h
  subst hlast
  have hH1 := hH m1 (by simp)
  rcases Nat.mod_two_eq_zero_or_one m1.state.turnNum with he | ho
  · rcases held_QOK hI hH1 (byMover_even hc1 hmv1 he) with h0 | h0 | h0 <;> rw [h0] at h3 ⊢
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · decide
  · obtain ⟨y, hy, hys⟩ := (hH1.unforged hI.recvU).1 (byMover_odd hc1 hmv1 ho)
    have := hI.low y hy (by rw [hys]; exact hc1) (by rw [hys]; exact ho) (by rw [hys]; exact h3)
    rwa [hys] at this

/-- One land of a call of `p0` whose proof states `p0` holds keeps `InvN`
    and a safe status. -/
theorem landN {m : NetworkState Nat p0} (hI : InvN m) (hS : SafeN (m.chain.statusOf c0)) {op : Op Nat}
    (hH : ∀ ss ∈ op.proofStates, m.Holds ss) :
    InvN (m.applyAdv appsS (.land op)) ∧ SafeN ((m.applyAdv appsS (.land op)).chain.statusOf c0) := by
  cases happ : m.chain.apply appsS p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsS happ]; exact ⟨hI, hS⟩
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsS happ]
    refine ⟨⟨fun x hx hxq => ?_, fun x hx => ?_, hI.s3in, hI.low⟩, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact held_QOK hI (hH x hx) hxq
      · exact hI.recvQ x hx hxq
    · rcases List.mem_append.1 hx with hx | hx
      · exact (hH x hx).unforged hI.recvU
      · exact hI.recvU x hx
    rcases status_cases happ with heq | ⟨P, cand, rfl, hsup, -, hmode, hst⟩ |
        ⟨P, cand, rfl, -, hopen, hlt, hst⟩ | ⟨ss, rfl, hcp⟩ | ⟨o0, o', hfo, hst⟩
    · rw [heq]; exact hS
    · have h3 : 3 ≤ cand.turnNum := by
        have hrec : 3 ≤ (m.chain.statusOf c0).turnNumRecord := by
          rcases hS with ⟨t, ht, h3⟩ | ⟨t, ch, ht, h3, -⟩ | ⟨t, f, o, ht, -⟩ <;> rw [ht]
          · exact h3
          · exact h3
          · rw [Adjudicator.mode_eq, ht] at hmode
            rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
        rcases hmode with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
      exact Or.inr (Or.inl ⟨_, _, hst, h3, cand_low hI hsup (fun ss hss => hH ss hss) h3⟩)
    · have h3 : 3 ≤ cand.turnNum := by
        rcases hS with ⟨t, ht, h3⟩ | ⟨t, ch, ht, h3, -⟩ | ⟨t, f, o, ht, -⟩ <;> rw [ht] at hlt
        · simp only [ChannelStatus.turnNumRecord_open] at hlt; omega
        · simp only [ChannelStatus.turnNumRecord_challenged] at hlt; omega
        · rw [ht] at hopen
          exact absurd hopen (by simp [ChannelStatus.IsOpen, ChannelStatus.mode])
      exact Or.inl ⟨_, hst, h3⟩
    · obtain ⟨-, hfin⟩ := conclusion_p0 hcp
      have hq0 : q0 ∈ ss.signers := hcp.2.2 q0 (by rw [hcp.1]; decide)
      rw [QOK_final (held_QOK hI (hH ss (List.mem_singleton_self ss)) hq0)] at hfin
      cases hfin
    · rw [hst]
      rcases hS with ⟨t, ht, -⟩ | ⟨t, ch, ht, -, hle⟩ | ⟨t, f, o, ht, hle⟩
      · rw [ht, ChannelStatus.finalOutcome_open] at hfo; cases hfo
      · rw [ht, ChannelStatus.withOutcome_challenged]
        exact Or.inr (Or.inr ⟨_, _, _, rfl, hle⟩)
      · rw [ht, ChannelStatus.withOutcome_finalized]
        exact Or.inr (Or.inr ⟨_, _, _, rfl, hle⟩)

/-- The calls of `p0` land in order, then one tick of 1 closes the round. -/
theorem roundN (n0 : NetworkState Nat p0) (t : Time) :
    ∀ (pending : List (Op Nat)), (∀ op ∈ pending, op.HonestFeasible n0) →
    ∀ m : NetworkState Nat p0, InvN m → SafeN (m.chain.statusOf c0) → m.sent = n0.sent →
      (∀ r ∈ n0.received, r ∈ m.received) →
      ∃ m', TN.RoundSeq appsS t pending m m' ∧ InvN m' ∧ SafeN (m'.chain.statusOf c0) ∧
        m'.chain.now = m.chain.now + 1 ∧ m'.sent = m.sent := by
  intro pending
  induction pending with
  | nil =>
    intro _ m hI hS _ _
    refine ⟨m.applyAdv appsS (.tick 1), .tick ⟨trivial, trivial⟩ (Or.inl rfl) .nil,
      ⟨hI.recvQ, fun x hx => (hI.recvU x hx).of_sent rfl, hI.s3in, hI.low⟩, ?_, rfl, rfl⟩
    rw [NetworkState.applyAdv_tick, Adjudicator.tick_statusOf]; exact hS
  | cons op rest ih =>
    intro hfeas m hI hS hsent hrecv
    have hop := hfeas op List.mem_cons_self
    have hH : ∀ ss ∈ op.proofStates, m.Holds ss := fun ss hss =>
      holds_mono hsent.symm hrecv (hop.mem ss hss)
    obtain ⟨hI1, hS1⟩ := landN hI hS hH
    obtain ⟨m', hseq, hI', hS', hnow, hs'⟩ := ih (fun o ho => hfeas o (List.mem_cons_of_mem _ ho))
      _ hI1 hS1 (by rw [NetworkState.applyAdv_sent]; exact hsent)
      (fun r hr => (NetworkState.applyAdv_sent_received appsS m (.land op)).2 r (hrecv r hr))
    refine ⟨m', .land (l1 := []) (l2 := rest) rfl hseq, hI', hS', ?_, ?_⟩
    · rw [hnow, landed_now hop.not_tick]
    · rw [hs', NetworkState.applyAdv_sent]

/-- A state that `p0` may sign at an odd turn from 3 on pays it at most 3:
    at turn 3 it carries `s3`'s outcome (`HonestSend.noConflict`); at a later
    turn it is a move of `p0` after a held state of `q0`, which is `r4`'s
    state (`HonestSend.movesFrom`). -/
theorem send_low {n0 : NetworkState Nat p0} (hI0 : InvN n0) {signed : List (SignedState Nat)}
    {st' : State Nat} (hs3 : s3 ∈ signed)
    (hsend : HonestSend signed n0.HoldsPrefund (n0.CanMoveTo appsS) st') (hc : st'.channel = c0)
    (ho : st'.turnNum % 2 = 1) (h3 : 3 ≤ st'.turnNum) : amtP st'.outcome ≤ 3 := by
  by_cases ht : st'.turnNum = 3
  · have heq := hsend.outcome_eq s3 hs3 (by rw [hc]; rfl)
      (by simp only [State.signSlot, s3, st, hc, ht, c0, FixedPart.n]; decide)
    rw [← heq]; decide
  · obtain ⟨-, proof', hH', hsup'⟩ := hsend.movesFrom (by rw [hc]; show 2 ≤ _; omega)
    rw [hc] at hsup'
    obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht1, hmv0, hmv1, hfin, hvt⟩⟩ := fm2 hsup'
    subst hlast
    have he0 : m0.state.turnNum % 2 = 0 := by omega
    rcases hH' m0 (by simp) with hH0 | heq0
    · have hq := held_QOK hI0 hH0 (byMover_even hc0 hmv0 he0)
      have h4 : m0.state = st 4 OA := by
        rcases hq with h0 | h0 | h0 <;> rw [h0] at ht1 ⊢
        · exfalso; simp only [st] at ht1; omega
        · exfalso; simp only [st] at ht1; omega
      cases hf : m1.state.isFinal with
      | true => rw [hfin hf, h4]; decide
      | false =>
        have hv := hvt hf
        rw [h4] at hv
        obtain ⟨a, b, a', b', h0, h1, hsum, hb, -⟩ := (vtS_iff _ _).1 hv
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h0)
        have hm : m1.state.mover = some p0 := by rw [mover_c0 hc1, if_neg (by omega)]
        rcases hb with hb | hb
        · rw [hm] at hb; exact absurd (Option.some.inj hb) p0_ne_q0
        · rw [decode_eq_some.1 h1, amtP_pay]; omega
    · rw [heq0] at ht1; omega

theorem InvN.applyHonest {n0 n : NetworkState Nat p0} (hI0 : InvN n0) (hI : InvN n)
    (hS : SafeN (n.chain.statusOf c0)) {m : HonestMove Nat}
    (hfeas : m.Feasible appsS n0) :
    InvN (n.applyHonest m) ∧ SafeN ((n.applyHonest m).chain.statusOf c0) := by
  cases m with
  | react r =>
    refine ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).mono (fun y hy => List.mem_append_right _ hy),
      List.mem_append_right _ hI.s3in, fun s hs hc ho h3 => ?_⟩, hS⟩
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨st', hst, rfl⟩ := List.mem_map.1 hs
      exact send_low hI0 (List.mem_append_right _ hI0.s3in) (hfeas.2 st' hst) hc ho h3
    · exact hI.low s hs hc ho h3
  | wait dt =>
    exact ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).of_sent rfl, hI.s3in, hI.low⟩,
      by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; exact hS⟩

theorem not_finalizable_from (n : NetworkState Nat p0) (hI : InvN n) (hS : SafeN (n.chain.statusOf c0)) :
    ¬ UnbeatableIn appsS TN (fun _ => True) (fun n => n.Finalized c0 OC) n := by
  intro hU
  induction hU with
  | done hG => exact safeN_not_finalized hS hG
  | @move n m _ hfeas _ ih =>
    have hcalls : ∀ op ∈ m.calls, op.HonestFeasible n := by
      cases m with
      | react r => exact hfeas.1
      | wait dt => intro op hop; simp [HonestMove.calls] at hop
    obtain ⟨n', hseq, hI', hS', hnow, -⟩ :=
      roundN n n.chain.now m.calls hcalls n hI hS rfl (fun _ hr => hr)
    obtain ⟨hI'', hS''⟩ := InvN.applyHonest hI hI' hS' hfeas
    exact ih n' (mkRound hseq hnow) hI'' hS''

/-- The adversary's challenge of the first round: `OA` at turn 3. -/
def opA : Op Nat := .challenge c0 [r2, s3] (st 3 OA)

def sA : Adjudicator Nat := (sCh.tick 5).setStatus c0 (.challenged 3 ⟨st 3 OA, 11⟩)

theorem opA_apply : (sCh.tick 5).apply appsS q0 opA = some sA := by
  show (sCh.tick 5).challenge appsS q0 c0 [r2, s3] (st 3 OA) = some sA
  unfold Adjudicator.challenge
  rw [if_pos (by decide)]
  rfl

theorem invN_net : InvN net := by
  refine ⟨fun x hx hxq => ?_, fun x hx => ?_, by decide, fun s hs hc ho h3 => ?_⟩
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact absurd hxq (by decide)
    · exact Or.inl rfl
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact unforged_q
    · exact unforged_q
    · exact unforged_q
    · exact unforged_sent (n := net) (by decide)
    · exact unforged_q
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · decide
    · exact absurd h3 (by decide)

theorem not_finalizable_OC : ¬ Finalizable appsS TN c0 OC net := by
  intro hU
  cases hU with
  | done h => exact net_not_finalized OC h
  | move m _ hfeas hcont =>
    let n1 : NetworkState Nat p0 := net.applyAdv appsS (.chain q0 opA)
    have hn1 : n1 = ⟨sA, [r2, s3] ++ net.received, net.sent⟩ :=
      NetworkState.applyAdv_chain_some appsS opA_apply
    have hI1 : InvN n1 := by
      rw [hn1]
      refine ⟨fun x hx hxq => ?_, fun x hx => ?_, by decide, invN_net.low⟩
      · rcases List.mem_append.1 hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact absurd hxq (by decide)
        · exact invN_net.recvQ x hx hxq
      · rcases List.mem_append.1 hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact unforged_q
          · exact unforged_sent (by decide)
        · exact (invN_net.recvU x hx).of_sent rfl
    have hS1 : SafeN (n1.chain.statusOf c0) := by
      rw [hn1]; exact Or.inr (Or.inl ⟨3, ⟨st 3 OA, 11⟩, by decide, le_refl _, by decide⟩)
    have hcalls : ∀ op ∈ m.calls, op.HonestFeasible net := by
      cases m with
      | react r => exact hfeas.1
      | wait dt => intro op hop; simp [HonestMove.calls] at hop
    obtain ⟨n', hseq, hI', hS', hnow, -⟩ := roundN net 5 m.calls hcalls n1 hI1 hS1
      (by rw [hn1]) (fun r hr => by rw [hn1]; exact List.mem_append_right _ hr)
    have hfe : TN.feasible net (.chain q0 opA) := by
      refine ⟨⟨by decide, fun ss hss => ?_⟩, AdvMove.NoOwnViolation.chain_of (by decide)⟩
      simp only [opA, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
      rcases hss with rfl | rfl
      · exact unforged_q
      · exact unforged_sent (by decide)
    have hround : TN.Round appsS m net n' :=
      mkRound (.other hfe (fun _ h => by cases h) (fun _ h => by cases h) hseq)
        (by rw [hnow, hn1]; rfl)
    obtain ⟨hI'', hS''⟩ := InvN.applyHonest invN_net hI' hS' hfeas
    exact not_finalizable_from _ hI'' hS'' (hcont n' hround)

/-! ## Every outcome but `OC` is prevented

For a target `Ω ≠ OC`, `p0` picks a sacrifice outcome `X` (`sacr Ω`): it
pays `q0` more than `OA`, and `X ≠ Ω`. In the first round `p0` signs
`s5 X`, a move by the rules after `r4`. Then it answers every challenge with
`OA` by a challenge with `[r4, s5 X]` at turn 5. Every support that the
adversary can use carries the outcome of the state of `p0` in it
(`cand_outcome`): a move of `q0` that changes the outcome pays `p0` from
`q0`'s own entry, a gift, unless a later state of `p0` accepts it. So only
`OC`, `OA` and `X` can stand, and `OA` never finalizes. -/

/-- The sacrifice outcome for the target `Ω`. -/
def sacr (Ω : Outcome Nat) : Outcome Nat := if Ω = pay 2 8 then pay 1 9 else pay 2 8

/-- What `p0` needs of `X`: it is neither `OC` nor `OA`, it is a move of
    `p0` after `r4`, and it is one of the two sacrifice outcomes. -/
structure Sacr (X : Outcome Nat) : Prop where
  neC : X ≠ OC
  neA : X ≠ OA
  valid : vtS (st 4 OA) (st 5 X) = true
  cases : X = pay 2 8 ∨ X = pay 1 9

theorem sacr_ok (Ω : Outcome Nat) : Sacr (sacr Ω) := by
  unfold sacr
  split
  · exact ⟨by decide, by decide, by decide, .inr rfl⟩
  · exact ⟨by decide, by decide, by decide, .inl rfl⟩

theorem sacr_ne (Ω : Outcome Nat) : sacr Ω ≠ Ω := by
  unfold sacr
  split
  · rename_i h; rw [h]; decide
  · rename_i h; exact fun h' => h h'.symm

def s5 (X : Outcome Nat) : SignedState Nat := ⟨st 5 X, [p0]⟩

/-- `p0`'s answer to a challenge with `OA`. -/
def opP (X : Outcome Nat) : Op Nat := .challenge c0 [r4, s5 X] (st 5 X)

/-- The states that `p0` signs in the play. -/
def SentP (X : Outcome Nat) (n : NetworkState Nat p0) : Prop :=
  ∀ s ∈ n.sent, s = s1 ∨ s = s3 ∨ s = s5 X

/-- The candidates the play can carry: the outcome of the state of `p0` in
    the support, by turn. -/
def CandOK (X : Outcome Nat) (cand : State Nat) : Prop :=
  (cand.turnNum ≤ 2 ∧ cand.outcome = OC) ∨ (cand.turnNum ≤ 4 ∧ cand.outcome = OA) ∨
    cand.outcome = X

theorem sentP_state {X : Outcome Nat} {n : NetworkState Nat p0} (hS : SentP X n)
    {s : SignedState Nat} (hs : s ∈ n.sent) :
    s.state = st 1 OC ∨ s.state = st 3 OA ∨ s.state = st 5 X := by
  rcases hS s hs with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- A move of `q0` after a state of `p0` that is no gift keeps the outcome:
    `vtS` keeps the total and `p0`'s amount, and `q0`'s amount does not fall. -/
theorem keep_of_noGift {s s' : State Nat} (hv : vtS s s' = true) (hm : s'.mover = some q0)
    (hng : ¬ share s'.outcome (destS q0) < share s.outcome (destS q0)) : s'.outcome = s.outcome := by
  obtain ⟨a, b, a', b', h0, h1, hsum, -, ha⟩ := (vtS_iff _ _).1 hv
  rw [decode_eq_some.1 h0, decode_eq_some.1 h1] at hng ⊢
  have hng' : ¬ b' < b := by simpa [share_pay, destS, q0] using hng
  have ha' : a ≤ a' := by
    rcases ha with h | h
    · rw [hm] at h; exact absurd (Option.some.inj h) (Ne.symm p0_ne_q0)
    · exact h
  have : a = a' ∧ b = b' := by omega
  rw [this.1, this.2]

/-- Every support of `c0` that the adversary can use, with unforged states
    and no own-violation of `q0`, carries the outcome of the state of `p0` in
    it. -/
theorem cand_outcome {X : Outcome Nat} {n : NetworkState Nat p0} (hS : SentP X n)
    {P : SupportProof Nat} {cand : State Nat} (h : (appsS c0.appDef).supports c0 P cand = true)
    (hU : ∀ ss ∈ P, n.Unforged ss)
    (hnv : ∀ ss ∈ P, ∀ q ∈ ss.signers, q ≠ p0 →
      (SupportProof.AcceptedBy (p := p0) P ss ∨ ¬ OwnViolation destS q (P ++ n.received) ss)) :
    CandOK X cand := by
  obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht, hmv0, hmv1, hfin, hvt⟩⟩ := fm2 h
  subst hlast
  rcases Nat.mod_two_eq_zero_or_one m1.state.turnNum with he | ho
  · have ho0 : m0.state.turnNum % 2 = 1 := by omega
    obtain ⟨y, hy, hys⟩ := (hU m0 (by simp)).1 (byMover_odd hc0 hmv0 ho0)
    have hkeep : m1.state.outcome = m0.state.outcome := by
      cases hf : m1.state.isFinal with
      | true => exact hfin hf
      | false =>
        have hq := byMover_even hc1 hmv1 he
        have hnp : p0 ∉ m1.signers := by
          intro hp
          obtain ⟨y1, hy1, hy1s⟩ := (hU m1 (by simp)).1 hp
          rcases sentP_state hS hy1 with h1 | h1 | h1 <;> rw [h1] at hy1s <;>
            rw [← hy1s] at he <;> simp [st] at he
        rcases hnv m1 (by simp) q0 hq (Ne.symm p0_ne_q0) with ⟨i, j, t, hi, hij, hj, hpt⟩ | hno
        · rcases i with _ | _ | i
          · rcases j with _ | _ | j
            · omega
            · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj
              subst hj; exact absurd hpt hnp
            · simp at hj
          · rcases j with _ | _ | j
            · omega
            · omega
            · simp at hj
          · simp at hi
        · have hng : ¬ share m1.state.outcome (destS q0) < share m0.state.outcome (destS q0) :=
            fun hlt => hno (Or.inr ⟨fun hall => hnp (hall p0 (by rw [hc1]; decide)),
              m0, by simp, by rw [hc0, hc1], ht.symm, hlt⟩)
          exact keep_of_noGift (hvt hf) (by rw [mover_c0 hc1, if_pos he]) hng
    have hcm : m0.state = st 1 OC ∨ m0.state = st 3 OA ∨ m0.state = st 5 X := by
      rw [← hys]; exact sentP_state hS hy
    unfold CandOK
    rw [hkeep]
    rcases hcm with h1 | h1 | h1 <;> rw [h1] <;> rw [h1] at ht <;> simp only [st] at ht
    · exact Or.inl ⟨by omega, rfl⟩
    · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    · exact Or.inr (Or.inr rfl)
  · obtain ⟨y, hy, hys⟩ := (hU m1 (by simp)).1 (byMover_odd hc1 hmv1 ho)
    rw [← hys]
    rcases sentP_state hS hy with h1 | h1 | h1 <;> rw [h1]
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨by decide, rfl⟩)
    · exact Or.inr (Or.inr rfl)

/-- The invariant at the start of each round of `p0`'s strategy. -/
structure InvP (X : Outcome Nat) (n : NetworkState Nat p0) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  r4in : r4 ∈ n.received
  s3in : s3 ∈ n.sent
  sentOK : SentP X n
  noFin : ∀ t f o, n.chain.statusOf c0 = .finalized t f o → f = OC ∨ f = X
  chOut : ∀ t ch, n.chain.statusOf c0 = .challenged t ch →
    ch.state.outcome = OC ∨ ch.state.outcome = X ∨ ch.state.outcome = OA
  timing : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome = OA →
    t < 5 ∧ n.chain.now + 2 ≤ ch.deadline ∧ (s5 X ∉ n.sent → n.chain.now + 4 ≤ ch.deadline)

/-- The invariant inside a round that starts at `n0`; the turn record stays
    at least `R`. -/
structure KP (X : Outcome Nat) (n0 : NetworkState Nat p0) (R : Nat) (n : NetworkState Nat p0) :
    Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = n0.sent
  recv : ∀ r ∈ n0.received, r ∈ n.received
  now0 : n0.chain.now ≤ n.chain.now
  noFin : ∀ t f o, n.chain.statusOf c0 = .finalized t f o → f = OC ∨ f = X
  chOut : ∀ t ch, n.chain.statusOf c0 = .challenged t ch →
    ch.state.outcome = OC ∨ ch.state.outcome = X ∨ ch.state.outcome = OA
  chA : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome = OA →
    t < 5 ∧ (n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ n0.chain.now + 6 ≤ ch.deadline)
  left : ∀ t0 ch0, n0.chain.statusOf c0 = .challenged t0 ch0 → ch0.state.outcome = OA →
    n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ t0 < (n.chain.statusOf c0).turnNumRecord
  recR : R ≤ (n.chain.statusOf c0).turnNumRecord

theorem KP.start {X : Outcome Nat} {n0 : NetworkState Nat p0} (hI : InvP X n0) :
    KP X n0 (n0.chain.statusOf c0).turnNumRecord n0 :=
  ⟨hI.recvU, rfl, fun _ h => h, le_refl _, hI.noFin, hI.chOut,
    fun t ch h hx => ⟨(hI.timing t ch h hx).1, Or.inl rfl⟩, fun _ _ _ _ => Or.inl rfl, le_refl _⟩

theorem KP.lower {X : Outcome Nat} {n0 n : NetworkState Nat p0} {R R' : Nat}
    (hK : KP X n0 R n) (hR : R' ≤ (n.chain.statusOf c0).turnNumRecord) : KP X n0 R' n :=
  ⟨hK.recvU, hK.sent, hK.recv, hK.now0, hK.noFin, hK.chOut, hK.chA, hK.left, hR⟩

/-- A standing challenge with `OA` inside a round has not expired. -/
theorem KP.liveA {X : Outcome Nat} {n0 n : NetworkState Nat p0} {R : Nat} (hI0 : InvP X n0)
    (hK : KP X n0 R n) (hnow : n.chain.now < n0.chain.now + 2) {t : Nat} {ch : Challenge Nat}
    (hc : n.chain.statusOf c0 = .challenged t ch) (hx : ch.state.outcome = OA) :
    n.chain.now < ch.deadline := by
  rcases (hK.chA t ch hc hx).2 with h0 | h6
  · rw [h0] at hc
    exact lt_of_lt_of_le hnow (hI0.timing t ch hc hx).2.1
  · exact lt_of_lt_of_le hnow (le_trans (Nat.add_le_add_left (by decide) _) h6)

/-- One successful operation whose candidate, if any, is one the play can
    carry, keeps `KP`, inside a round whose clock stays below `n0`'s clock
    plus 2. -/
theorem stepK {X : Outcome Nat} (hX : Sacr X) {n0 n : NetworkState Nat p0} {R : Nat} (hI0 : InvP X n0)
    (hK : KP X n0 R n) (hnow : n.chain.now < n0.chain.now + 2)
    {caller : Participant} {op : Op Nat} {s' : Adjudicator Nat}
    (h : n.chain.apply appsS caller op = some s') (hU : ∀ ss ∈ op.proofStates, n.Unforged ss)
    (hcand : ∀ P cand, op = .challenge c0 P cand → CandOK X cand)
    (hs'now : n.chain.now ≤ s'.now) :
    KP X n0 R { n with chain := s', received := op.proofStates ++ n.received } := by
  have hrec : ∀ r ∈ n.received, r ∈ op.proofStates ++ n.received :=
    fun r hr => List.mem_append_right _ hr
  have hRecU : ∀ r ∈ op.proofStates ++ n.received,
      ({ n with chain := s', received := op.proofStates ++ n.received } : NetworkState Nat p0).Unforged r := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact (hU r hr).of_sent rfl
    · exact (hK.recvU r hr).of_sent rfl
  -- the challenge of `n0` with `OA`, while it stands, keeps the mode
  have hleft : ∀ t0 ch0, n0.chain.statusOf c0 = .challenged t0 ch0 → ch0.state.outcome = OA →
      n.chain.statusOf c0 = n0.chain.statusOf c0 → n.chain.mode c0 = .challenge := by
    intro t0 ch0 h0 hx hs
    have hlive := hK.liveA hI0 hnow (hs.trans h0) hx
    rw [Adjudicator.mode_eq, hs, h0, ChannelStatus.mode_challenged, if_neg (not_le.mpr hlive)]
  rcases status_cases h with heq | ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩ |
      ⟨P, cand, rfl, hsup, hopen, hlt, hst⟩ | ⟨ss, rfl, hcp⟩ | ⟨o0, o', hfo, hst⟩
  · refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => by rw [heq]; exact hK.noFin t f o, fun t ch hc => by rw [heq] at hc; exact hK.chOut t ch hc,
      fun t ch hc hx => ?_, fun t0 ch0 h0 hx => by rw [heq]; exact hK.left t0 ch0 h0 hx,
      by rw [heq]; exact hK.recR⟩
    rw [heq] at hc ⊢
    exact hK.chA t ch hc hx
  · have hge : (n.chain.statusOf c0).turnNumRecord ≤ cand.turnNum := by
      rcases hmode with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · exact le_of_lt h
    have hc := hcand P cand rfl
    refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => (by rw [hst]; intro h; cases h), fun t ch hch => ?_, fun t ch hch hx => ?_,
      fun t0 ch0 h0 hx => ?_, by rw [hst]; exact le_trans hK.recR hge⟩
    · rw [hst] at hch
      obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hch
      rcases hc with ⟨-, h⟩ | ⟨-, h⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rw [hst] at hch
      obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hch
      refine ⟨?_, Or.inr (Nat.add_le_add_right hK.now0 6)⟩
      rcases hc with ⟨h2, -⟩ | ⟨h4, -⟩ | h
      · omega
      · omega
      · exact absurd (h.symm.trans hx) hX.neA
    · right
      rw [hst]
      show t0 < cand.turnNum
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0
      · rw [Adjudicator.mode_eq, hs0, h0] at hmode
        rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
        · have := hleft t0 ch0 h0 hx hs0
          rw [Adjudicator.mode_eq, hs0, h0] at this
          rw [this] at hm; cases hm
        · simpa using hr
      · exact lt_of_lt_of_le hlt0 hge
  · refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => (by rw [hst]; intro h; cases h), fun t ch hc => (by rw [hst] at hc; cases hc),
      fun t ch hc _ => (by rw [hst] at hc; cases hc), fun t0 ch0 h0 hx => ?_, ?_⟩
    · right
      rw [hst]
      show t0 < cand.turnNum
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0
      · rw [hs0, h0] at hlt; simpa using hlt
      · exact lt_trans hlt0 hlt
    · rw [hst]; exact le_trans hK.recR (le_of_lt hlt)
  · exfalso
    obtain ⟨hp, hfin⟩ := conclusion_p0 hcp
    obtain ⟨y, hy, hys⟩ := (hU ss (List.mem_singleton_self ss)).1 hp
    rw [hK.sent] at hy
    rcases sentP_state hI0.sentOK hy with h1 | h1 | h1 <;> rw [← hys, h1] at hfin <;> cases hfin
  · -- a payout: the status was final; the record and the finalized outcome stay
    have hrec' : (s'.statusOf c0).turnNumRecord = (n.chain.statusOf c0).turnNumRecord := by
      rw [hst]; cases n.chain.statusOf c0 <;> rfl
    have hfin' : ∀ t f o, s'.statusOf c0 = .finalized t f o → f = OC ∨ f = X := by
      intro t f o hf
      rw [hst] at hf
      cases hs : n.chain.statusOf c0 with
      | «open» r =>
        rw [hs, ChannelStatus.finalOutcome_open] at hfo; cases hfo
      | challenged r ch =>
        rw [hs, ChannelStatus.withOutcome_challenged] at hf
        obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hf
        rcases hK.chOut r ch hs with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · have hlive := hK.liveA hI0 hnow hs h1
          rw [hs, ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hlive)] at hfo
          cases hfo
      | finalized r f' o'' =>
        rw [hs, ChannelStatus.withOutcome_finalized] at hf
        obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hf
        exact hK.noFin r f' o'' hs
    refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now, hfin',
      fun t ch hc => ?_, fun t ch hc _ => ?_, fun t0 ch0 h0 hx => ?_, by rw [hrec']; exact hK.recR⟩
    · rw [hst] at hc
      cases hs : n.chain.statusOf c0 <;> rw [hs] at hc <;> cases hc
    · rw [hst] at hc
      cases hs : n.chain.statusOf c0 <;> rw [hs] at hc <;> cases hc
    · right
      rw [hrec']
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0
      · have hlive := hK.liveA hI0 hnow (hs0.trans h0) hx
        rw [hs0, h0, ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hlive)] at hfo
        cases hfo
      · exact hlt0

theorem holds_s5 {X : Outcome Nat} {n : NetworkState Nat p0} (h : s5 X ∈ n.sent) : n.Holds (s5 X) :=
  ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s5 X, h, rfl⟩,
    fun v hv => by simp [s5, st, State.voucher?] at hv⟩

theorem supports_P {X : Outcome Nat} (hX : Sacr X) :
    (appsS c0.appDef).supports c0 [r4, s5 X] (st 5 X) = true := by
  rcases hX.cases with rfl | rfl <;> decide

/-- `p0` may sign `s5 X`: a move by the rules after `r4`, whose support
    `[s3, r4]` it holds, at a slot where it signed no other outcome. -/
theorem send_feasible {X : Outcome Nat} (hX : Sacr X) {n : NetworkState Nat p0} (hI : InvP X n) :
    (HonestMove.send (st 5 X)).Feasible appsS n := by
  refine (HonestMove.Feasible_send appsS n (st 5 X)).mpr
    ⟨fun ⟨s, hs, _, hslot, hne⟩ => ?_, ?_, ?_, fun _ => ⟨⟨[s3, r4], st 4 OA, fun ss hss => ?_,
      by show (appsS c0.appDef).supports c0 [s3, r4] (st 4 OA) = true; decide, rfl, rfl⟩,
      [r4, s5 X], fun ss hss => ?_, supports_P hX⟩, fun ⟨s, hs, _, htn, hne⟩ => ?_,
      fun ⟨s, hs, _, hfb⟩ => ?_⟩
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact hne rfl
    · rcases hI.sentOK s hs with rfl | rfl | rfl
      · exact absurd hslot (by show (st 1 OC).signSlot ≠ (st 5 OC).signSlot; decide)
      · exact absurd hslot (by show (st 3 OA).signSlot ≠ (st 5 OC).signSlot; decide)
      · exact hne rfl
  · rcases hX.cases with rfl | rfl <;> decide
  · rcases hX.cases with rfl | rfl <;> exact HonestSend.fundsCommitted_of_fundable (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s3, hI.s3in, rfl⟩,
        fun v hv => by simp [s3, st, State.voucher?] at hv⟩
    · exact holds_of_mem_received hI.r4in
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact .inl (holds_of_mem_received hI.r4in)
    · exact .inr rfl
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact hne rfl
    · rcases hI.sentOK s hs with rfl | rfl | rfl
      · exact absurd htn (by show (st 1 OC).turnNum ≠ (st 5 OC).turnNum; decide)
      · exact absurd htn (by show (st 3 OA).turnNum ≠ (st 5 OC).turnNum; decide)
      · exact hne rfl
  · rcases List.mem_cons.1 hs with rfl | hs
    · rcases hfb with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ <;> simp [st] at h1
    · rcases hI.sentOK s hs with rfl | rfl | rfl <;>
        rcases hfb with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ <;> simp [s1, s3, s5, st] at h1

theorem counter_feasible {X : Outcome Nat} {n : NetworkState Nat p0} (hr : r4 ∈ n.received)
    (hs : s5 X ∈ n.sent) : (HonestMove.chain (opP X)).Feasible appsS n := by
  refine (HonestMove.Feasible_chain _ _ _).2 fun ss hss => ?_
  simp only [opP, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact holds_of_mem_received hr
  · exact holds_s5 hs

open Classical in
/-- `p0`'s move: sign `s5 X` first, then answer every challenge with `OA`. -/
noncomputable def idealP (X : Outcome Nat) (n : NetworkState Nat p0) : HonestMove Nat :=
  if s5 X ∈ n.sent then
    match n.chain.statusOf c0 with
    | .challenged _ ch => if ch.state.outcome = OA then .chain (opP X) else .wait 0
    | _ => .wait 0
  else .send (st 5 X)

open Classical in
/-- The strategy: `idealP` where it is feasible, a wait otherwise. -/
noncomputable def σP (X : Outcome Nat) : Strategy Nat p0 := fun n =>
  if (idealP X n).Feasible appsS n then idealP X n else .wait 0

theorem σP_feasible (X : Outcome Nat) (n : NetworkState Nat p0) : (σP X n).Feasible appsS n := by
  unfold σP
  split
  · assumption
  · trivial

/-- The three shapes of `σP X n`. -/
theorem σP_cases {X : Outcome Nat} (hX : Sacr X) {n : NetworkState Nat p0} (hI : InvP X n) :
    (σP X n = .wait 0 ∧ s5 X ∈ n.sent ∧
      ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome ≠ OA) ∨
    (s5 X ∉ n.sent ∧ σP X n = .send (st 5 X)) ∨
    (s5 X ∈ n.sent ∧ ∃ t ch, n.chain.statusOf c0 = .challenged t ch ∧ ch.state.outcome = OA ∧
      σP X n = .chain (opP X)) := by
  have hwait : idealP X n = .wait 0 → σP X n = .wait 0 := fun h => by
    unfold σP; rw [h]; exact ite_self _
  by_cases hs : s5 X ∈ n.sent
  · cases hst : n.chain.statusOf c0 with
    | «open» t =>
      exact Or.inl ⟨hwait (by unfold idealP; rw [if_pos hs, hst]), hs, fun t ch h => by cases h⟩
    | finalized t f o =>
      exact Or.inl ⟨hwait (by unfold idealP; rw [if_pos hs, hst]), hs, fun t ch h => by cases h⟩
    | challenged t ch =>
      by_cases hx : ch.state.outcome = OA
      · refine Or.inr (Or.inr ⟨hs, t, ch, rfl, hx, ?_⟩)
        have hid : idealP X n = .chain (opP X) := by
          unfold idealP; rw [if_pos hs, hst]; simp only [if_pos hx]
        unfold σP
        rw [hid, if_pos (counter_feasible hI.r4in hs)]
      · refine Or.inl ⟨hwait (by unfold idealP; rw [if_pos hs, hst]; simp only [if_neg hx]), hs,
          fun t' ch' h => ?_⟩
        cases h; exact hx
  · refine Or.inr (Or.inl ⟨hs, ?_⟩)
    have hid : idealP X n = .send (st 5 X) := by unfold idealP; rw [if_neg hs]
    unfold σP
    rw [hid, if_pos (send_feasible hX hI)]

/-- `p0`'s answer turns a standing challenge below turn 5 into a challenge
    with `X` at turn 5. -/
theorem counter_apply {X : Outcome Nat} (hX : Sacr X) {s : Adjudicator Nat} {t0 : Nat}
    {ch : Challenge Nat} (hs : s.statusOf c0 = .challenged t0 ch) (hd : s.now < ch.deadline)
    (ht : t0 < 5) :
    s.apply appsS p0 (opP X) = some (s.setStatus c0 (.challenged 5 ⟨st 5 X, s.now + 6⟩)) := by
  show s.challenge appsS p0 c0 _ _ = _
  unfold Adjudicator.challenge
  have hmode : s.mode c0 = .challenge := by
    rw [Adjudicator.mode_eq, hs]
    simp only [ChannelStatus.mode, if_neg (not_le.mpr hd)]
  rw [if_pos ⟨by decide, supports_P hX, rfl, Or.inr ⟨hmode, by
    rw [hs]; simp only [ChannelStatus.turnNumRecord_challenged, st]; exact ht⟩⟩]
  rfl

/-- `KP` as a step invariant of a sub-round of pure adversary play that ends
    before `n0`'s clock plus 2. -/
theorem KP.stepInv {X : Outcome Nat} (hX : Sacr X) {n0 : NetworkState Nat p0} {R : Nat}
    (hI0 : InvP X n0) {Eend : Time} (hE : Eend < n0.chain.now + 2) :
    TN.StepInvariant appsS (fun n => n.chain.now ≤ Eend) (KP X n0 R) (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {n ss} _ hfe hK => by
    rw [NetworkState.applyAdv_deliver]
    refine ⟨fun r hr => ?_, hK.sent, fun r hr => List.mem_cons_of_mem _ (hK.recv r hr), hK.now0,
      hK.noFin, hK.chOut, hK.chA, hK.left, hK.recR⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hfe.1.of_sent rfl
    · exact (hK.recvU r hr).of_sent rfl
  tick := fun {n dt} _ _ hK => by
    rw [NetworkState.applyAdv_tick]
    refine ⟨fun r hr => (hK.recvU r hr).of_sent rfl, hK.sent, hK.recv,
      le_trans hK.now0 (Nat.le_add_right _ _), fun t f o => ?_, fun t ch hc => ?_,
      fun t ch hc hx => ?_, fun t0 ch0 h0 hx => ?_, ?_⟩
    · rw [Adjudicator.tick_statusOf]; exact hK.noFin t f o
    · rw [Adjudicator.tick_statusOf] at hc; exact hK.chOut t ch hc
    · rw [Adjudicator.tick_statusOf] at hc ⊢; exact hK.chA t ch hc hx
    · rw [Adjudicator.tick_statusOf]; exact hK.left t0 ch0 h0 hx
    · rw [Adjudicator.tick_statusOf]; exact hK.recR
  chain := fun {n caller op} hg hfe hK => by
    cases happ : n.chain.apply appsS caller op with
    | none => rw [NetworkState.applyAdv_chain_none appsS happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_chain_some appsS happ]
      refine stepK hX hI0 hK (lt_of_le_of_lt hg hE) happ hfe.1.2 (fun P cand hop => ?_)
        (apply_now_le happ)
      subst hop
      obtain ⟨⟨-, hsup, -, -⟩, -⟩ := Adjudicator.challenge_some happ
      exact cand_outcome (fun s hs => hI0.sentOK s (hK.sent ▸ hs)) hsup hfe.1.2
        (fun ss hss q hq hqp => (hfe.2 ss hss q hq hqp).2)

theorem KP.nil {X : Outcome Nat} (hX : Sacr X) {n0 n n' : NetworkState Nat p0} {R : Nat}
    {t : Time} (hI0 : InvP X n0) (hseq : TN.RoundSeq appsS t [] n n') (hK : KP X n0 R n)
    (hE : n'.chain.now < n0.chain.now + 2) : KP X n0 R n' :=
  Threat.RoundSeq.nil_invariant hseq (KP.stepInv hX hI0 hE) hK

/-- At the end of a round from `n0`, only `OC` or `X` can be finalized. -/
theorem notFinP {X : Outcome Nat} {n0 n : NetworkState Nat p0} {R : Nat} (hI0 : InvP X n0)
    (hK : KP X n0 R n) (hnow : n.chain.now < n0.chain.now + 2) {Ω : Outcome Nat}
    (hC : Ω ≠ OC) (hXΩ : X ≠ Ω) : ¬ n.Finalized c0 Ω := by
  intro hf
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf
  cases hs : n.chain.statusOf c0 with
  | «open» t => rw [hs] at hf; simp at hf
  | finalized t f o =>
    rw [hs, ChannelStatus.finalizedWith_finalized] at hf
    rcases hK.noFin t f o hs with h | h
    · exact hC ((Option.some.inj hf).symm.trans h)
    · exact hXΩ (h.symm.trans (Option.some.inj hf))
  | challenged t ch =>
    rw [hs] at hf
    simp only [ChannelStatus.finalizedWith_challenged] at hf
    split at hf
    · rename_i hd
      have hΩ : ch.state.outcome = Ω := Option.some.inj hf
      rcases hK.chOut t ch hs with h | h | h
      · exact hC (hΩ.symm.trans h)
      · exact hXΩ (h.symm.trans hΩ)
      · exact absurd hd (not_le.mpr (hK.liveA hI0 hnow hs h))
    · cases hf

theorem bound6 {a b : Nat} (h : a < b + 2) : a + 4 ≤ b + 6 := by omega
theorem bound4 {a b : Nat} (h : a < b + 2) : a + 2 ≤ b + 4 := by omega

/-- One round of `σP X`: `Ω` is not finalized at its end, and `InvP` holds at
    the start of the next round. -/
theorem roundP {X : Outcome Nat} (hX : Sacr X) {Ω : Outcome Nat} (hC : Ω ≠ OC) (hXΩ : X ≠ Ω)
    {n0 n' : NetworkState Nat p0} (hI0 : InvP X n0) (hround : TN.Round appsS (σP X n0) n0 n') :
    ¬ n'.Finalized c0 Ω ∧ InvP X (n'.applyHonest (σP X n0)) := by
  have hbound := round_bound hround
  have hK0 := KP.start hI0
  have hnext : ∀ {R : Nat} (hK : KP X n0 R n') (m : HonestMove Nat)
      (hsent : ∀ s ∈ (n'.applyHonest m).sent, s ∈ n'.sent ∨ s = s5 X)
      (hsub : ∀ s ∈ n'.sent, s ∈ (n'.applyHonest m).sent)
      (hrecv : (n'.applyHonest m).received = n'.received)
      (hchain : (n'.applyHonest m).chain.statusOf c0 = n'.chain.statusOf c0 ∧
        (n'.applyHonest m).chain.now = n'.chain.now)
      (hS0 : ∀ t ch, n'.chain.statusOf c0 = .challenged t ch → ch.state.outcome = OA →
        n'.chain.statusOf c0 = n0.chain.statusOf c0 →
        (n'.applyHonest m).chain.now + 2 ≤ ch.deadline ∧
          (s5 X ∉ (n'.applyHonest m).sent → (n'.applyHonest m).chain.now + 4 ≤ ch.deadline)),
      InvP X (n'.applyHonest m) := by
    intro R hK m hsent hsub hrecv hchain hS0
    refine ⟨fun r hr => ?_, by rw [hrecv]; exact hK.recv _ hI0.r4in,
      hsub _ (by rw [hK.sent]; exact hI0.s3in), fun s hs => ?_, fun t f o => ?_, fun t ch hc => ?_,
      fun t ch hc hx => ?_⟩
    · rw [hrecv] at hr; exact (hK.recvU r hr).mono hsub
    · rcases hsent s hs with hs | rfl
      · rw [hK.sent] at hs; exact hI0.sentOK s hs
      · exact Or.inr (Or.inr rfl)
    · rw [hchain.1]; exact hK.noFin t f o
    · rw [hchain.1] at hc; exact hK.chOut t ch hc
    · rw [hchain.1] at hc
      obtain ⟨ht5, hor⟩ := hK.chA t ch hc hx
      refine ⟨ht5, ?_⟩
      rcases hor with h0 | h6
      · exact hS0 t ch hc hx h0
      · rw [hchain.2]
        have : n'.chain.now + 4 ≤ ch.deadline := le_trans (bound6 hbound) h6
        exact ⟨le_trans (Nat.add_le_add_left (by decide) _) this, fun _ => this⟩
  rcases σP_cases hX hI0 with ⟨hσ, -, hnx⟩ | ⟨hns, hσ⟩ | ⟨hsa, t0, ch0, hs0, hx0, hσ⟩
  · -- wait: a sub-round of pure adversary play
    rw [hσ] at hround ⊢
    have hK := KP.nil hX hI0 hround.1 hK0 hbound
    refine ⟨notFinP hI0 hK hbound hC hXΩ, hnext hK _ (fun s hs => .inl hs) (fun s hs => hs) rfl
      ⟨by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf], by
        simp only [NetworkState.applyHonest, Adjudicator.tick_now]; rfl⟩ ?_⟩
    intro t ch hc hx h0
    rw [h0] at hc
    exact absurd hx (hnx t ch hc)
  · -- send `s5 X`
    rw [hσ] at hround ⊢
    have hK := KP.nil hX hI0 hround.1 hK0 hbound
    refine ⟨notFinP hI0 hK hbound hC hXΩ, hnext hK _ ?_ ?_ rfl ⟨rfl, rfl⟩ ?_⟩
    · intro s hs
      rw [NetworkState.applyHonest_send] at hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact .inr rfl
      · exact .inl hs
    · intro s hs
      rw [NetworkState.applyHonest_send]
      exact List.mem_cons_of_mem _ hs
    · intro t ch hc hx h0
      rw [h0] at hc
      have h4 := (hI0.timing _ _ hc hx).2.2 hns
      rw [NetworkState.applyHonest_send]
      exact ⟨le_trans (bound4 hbound) h4, fun hn => absurd List.mem_cons_self hn⟩
  · -- the answer `opP X`
    rw [hσ] at hround ⊢
    rw [NetworkState.applyHonest_chain]
    obtain ⟨n1, hA, hB⟩ := Threat.Round.single hround
    have hnow1 : n1.chain.now ≤ n'.chain.now :=
      le_trans (NetworkState.applyAdv_now_le appsS n1 _) hB.now_le
    have hK1 := KP.nil hX hI0 hA hK0 (lt_of_le_of_lt hnow1 hbound)
    have htm := hI0.timing _ _ hs0 hx0
    have hU : ∀ ss ∈ (opP X).proofStates, n1.Unforged ss := by
      intro ss hss
      simp only [opP, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
      rcases hss with rfl | rfl
      · exact hK1.recvU _ (hK1.recv _ hI0.r4in)
      · exact unforged_sent (by rw [hK1.sent]; exact hsa)
    have hcand : ∀ P cand, opP X = .challenge c0 P cand → CandOK X cand := by
      intro P cand h
      injection h with _ _ hc
      subst hc
      exact Or.inr (Or.inr rfl)
    have hKL : KP X n0 (t0 + 1) (n1.applyAdv appsS (.land (opP X))) := by
      rcases hK1.left t0 ch0 hs0 hx0 with heq | hlt
      · have happ := counter_apply hX (s := n1.chain) (by rw [heq, hs0])
          (lt_of_lt_of_le (lt_of_le_of_lt hnow1 hbound) htm.2.1) htm.1
        rw [NetworkState.applyAdv_land_some appsS happ]
        exact (stepK hX hI0 hK1 (lt_of_le_of_lt hnow1 hbound) happ hU hcand (le_of_eq rfl)).lower
          (by simp only [Adjudicator.statusOf_setStatus, if_true, ChannelStatus.turnNumRecord_challenged]
              omega)
      · have hK1' := hK1.lower hlt
        cases happ : n1.chain.apply appsS p0 (opP X) with
        | none =>
          rw [NetworkState.applyAdv_land_none appsS happ]
          exact hK1'
        | some s' =>
          rw [NetworkState.applyAdv_land_some appsS happ]
          exact stepK hX hI0 hK1' (lt_of_le_of_lt hnow1 hbound) happ hU hcand (apply_now_le happ)
    have hK := KP.nil hX hI0 hB hKL hbound
    refine ⟨notFinP hI0 hK hbound hC hXΩ, ?_⟩
    have := hnext hK (HonestMove.chain (opP X))
      (fun s hs => .inl (by rwa [NetworkState.applyHonest_chain] at hs))
      (fun s hs => by rwa [NetworkState.applyHonest_chain])
      (by rw [NetworkState.applyHonest_chain]) (by rw [NetworkState.applyHonest_chain]; exact ⟨rfl, rfl⟩) ?_
    · rwa [NetworkState.applyHonest_chain] at this
    intro t ch hc hx h0
    have hr := hK.recR
    rw [h0, hs0] at hr
    simp only [ChannelStatus.turnNumRecord_challenged] at hr
    omega

theorem net_status : net.chain.statusOf c0 = .challenged 1 ch1 := by decide

theorem invP_net (X : Outcome Nat) : InvP X net := by
  refine ⟨invN_net.recvU, by decide, by decide, fun s hs => ?_, fun t f o h => ?_,
    fun t ch h => ?_, fun t ch h hx => ?_⟩
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · rw [net_status] at h; cases h
  · rw [net_status] at h
    obtain ⟨-, rfl⟩ := ChannelStatus.challenged.inj h
    exact Or.inl rfl
  · rw [net_status] at h
    obtain ⟨-, rfl⟩ := ChannelStatus.challenged.inj h
    exact absurd hx (by decide)

theorem prevents_other {Ω : Outcome Nat} (hC : Ω ≠ OC) :
    Prevents appsS TN (fun n => n.Finalized c0 Ω) net := by
  have hX := sacr_ok Ω
  have hXΩ := sacr_ne Ω
  have hrun : ∀ {n1}, Run appsS TN (σP (sacr Ω)) net n1 → InvP (sacr Ω) n1 := by
    intro n1 h
    induction h with
    | refl => exact invP_net _
    | round _ hr ih => exact (roundP hX hC hXΩ ih hr).2
  exact ⟨σP (sacr Ω), σP_feasible _, fun n1 n2 hr hround => (roundP hX hC hXΩ (hrun hr) hround).1⟩

/-! ## The two statements fail without `DeadlineAfter` -/

theorem not_finalizable (Ω : Outcome Nat) : ¬ Finalizable appsS TN c0 Ω net := by
  by_cases h : Ω = OC
  · subst h; exact not_finalizable_OC
  · exact not_finalizable_other h

/-- `Spec.finalizable_or_two_enabled` without the premise
    `hpend : net.state.DeadlineAfter c T.ε`. -/
def NoDeadline_finalizable_or_two_enabled : Prop :=
  ∀ (apps : Apps Nat) {p : Participant} (T : Threat Nat p)
    (_A : Assumptions apps p T) (dest : Participant → Nat)
    (net : Nitro.ReachableParticipant apps (T.noOwnViolation dest))
    (c : TimedChannel T.ε)
    (_hrules : (∃ vt, apps (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps (c : FixedPart).appDef = consensusRules)
    (_hdes : Desirable apps (c : FixedPart).appDef dest)
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof candidate = true ∧
      candidate.channel = (c : FixedPart)),
    (∃ Ω, Finalizable apps (T.noOwnViolation dest) (c : FixedPart) Ω net.state) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω1 net.state ∧
      Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω2 net.state)

/-- `Spec.single_enabled_is_finalizable` without the premise
    `hpend : net.state.DeadlineAfter c T.ε`. -/
def NoDeadline_single_enabled_is_finalizable : Prop :=
  ∀ (apps : Apps Nat) {p : Participant} (T : Threat Nat p)
    (_A : Assumptions apps p T) (dest : Participant → Nat)
    (net : Nitro.ReachableParticipant apps (T.noOwnViolation dest))
    (c : TimedChannel T.ε)
    (_hrules : (∃ vt, apps (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps (c : FixedPart).appDef = consensusRules)
    (_hdes : Desirable apps (c : FixedPart).appDef dest)
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) →
      ∃ proof, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof t.state = true)
    (Ω : Outcome Nat) (_hΩ : Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω net.state)
    (_huniq : ∀ Ω', Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω' net.state → Ω' = Ω),
    Finalizable apps (T.noOwnViolation dest) (c : FixedPart) Ω net.state

theorem holds_r0s1 : ∀ ss ∈ [r0, s1], net.Holds ss := by
  intro ss hss
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact holds_of_mem_received (by decide)
  · exact ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s1, by decide, rfl⟩,
      fun v hv => by simp [s1, st, State.voucher?] at hv⟩

theorem holds_r2s3 : ∀ ss ∈ [r2, s3], net.Holds ss := by
  intro ss hss
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact holds_of_mem_received (by decide)
  · exact ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s3, by decide, rfl⟩,
      fun v hv => by simp [s3, st, State.voucher?] at hv⟩

theorem finalizable_or_two_enabled_false : ¬ NoDeadline_finalizable_or_two_enabled := by
  intro h
  rcases h appsS T0 A0 destS ⟨net, net_reachable⟩ tc0 (Or.inl ⟨vtS, rfl⟩) appsS_desirable
      (by decide) ⟨[r0, s1], st 1 OC, holds_r0s1, by decide, rfl⟩ with
    ⟨Ω, hΩ⟩ | ⟨Ω1, Ω2, hne, hE1, hE2⟩
  · exact not_finalizable Ω hΩ
  · by_cases h1 : Ω1 = OC
    · exact hE2 (prevents_other (fun h2 => hne (h1.trans h2.symm)))
    · exact hE1 (prevents_other h1)

theorem single_enabled_is_finalizable_false : ¬ NoDeadline_single_enabled_is_finalizable := by
  intro h
  refine not_finalizable OC (h appsS T0 A0 destS ⟨net, net_reachable⟩ tc0 (Or.inl ⟨vtS, rfl⟩)
    appsS_desirable (by decide) (fun t ht _ => ?_) OC enabled_OC (fun Ω' hE => ?_))
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨[r2, s3], holds_r2s3, by decide⟩
    · exact ⟨[r0, s1], holds_r0s1, by decide⟩
  · by_contra hne
    exact hE (prevents_other hne)

#print axioms appsS_desirable
#print axioms net_reachable
#print axioms net_not_deadlineAfter
#print axioms finalizable_or_two_enabled_false
#print axioms single_enabled_is_finalizable_false

end ArmadaLean.Nitro.CounterexamplePending
