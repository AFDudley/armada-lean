/-
  Failure test: the rule `HonestSend.oneState` (an honest participant signs
  at most one state per turn number of a channel; Main's decision of
  2026-11-02) is needed for both Nitro-24 statements (Nitro:653-658). Without
  it, the honest participant may sign a final state and a non-final state at
  one turn, and both statements fail with the premise `hpend`.

  The app is go-nitro's payment app `SingleAssetPayments.sol` on a two-party
  channel, as in `pending_deadline.lean`: a ForceMove app (`forceMoveRules
  vtS`), desirable for the destination map `destS` (`appsS_desirable`). The
  threat is `T0.noOwnViolation destS`: the adversary commits no
  own-violation. The channel `c0` has the participants `[q0, p0]`, so `q0`
  moves at even turns and `p0` at odd turns (`n = 2`), and `ε = 2`.

  The history: the setup states `r0` (turn 0, `q0`) and `s1`
  (turn 1, `p0`) carry `OC = pay 5 5`. `q0` keeps `OC` at turn 2 (`r2`). At
  turn 3 `p0` signs two states with `OC`: `sF`, a final state (the graceful
  end, ForceMove:887-888), and `s3`, a non-final state. `q0` keeps `OC` at
  turn 4 (`r4`), after `s3`. `p0` pays 2 coins at turn 5 (`s5`,
  `OA = pay 3 7`), and `q0` keeps `OA` at turn 6 (`r6`). Turn 7 is `p0`'s
  turn, and `p0` has not moved. `q0` never gave `p0` its signature on `sF`.
  The status of `c0` is open, so `hpend` holds (`net_deadlineAfter`).

  * `OC` is enabled (`enabled_OC`): the adversary concludes with `sF`, signed
    by both, before `p0`'s calls land. A state that every participant signed
    is no gift, and `q0` signed no other state at turn 3.
  * No outcome but `OC` is enabled (`prevents_other`). For a target `Ω ≠ OC`,
    `p0` signs `s7 X`, a move at turn 7 that pays `q0` more (`X ≠ Ω`), and it
    answers every challenge with `OA` by a challenge with `[r6, s7 X]`. Every
    support that the adversary can use carries the outcome of the state of
    `p0` in it (`cand_outcome`). So only `OC` and `X` finalize.
  * No outcome is finalizable (`not_finalizable`). For `OC`: `p0` holds no
    signature of `q0` on `sF`, so it cannot conclude. The adversary challenges
    with `[s5, r6]` (`OA`, turn 6), and no move by the rules gives `p0` its 5
    coins back. For every other outcome: the adversary concludes with `OC`.

  So `p0` had no finalizable outcome and exactly one enabled outcome. Before
  the rule, the history was reachable, and this file refuted
  `Spec.finalizable_or_two_enabled` and `Spec.single_enabled_is_finalizable`
  (commit `40e75719`, with the proofs of the game facts above). The rule
  excludes the history (`net_not_honest`). It binds the honest participant
  only.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/final_branch.lean`.
  The theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Spec.Nitro.Liveness
import ArmadaLean.Nitro.TakeOut

namespace ArmadaLean.Nitro.CounterexampleFinalBranch

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
/-- The final state of `c0` at turn 3 with `OC`. -/
def stF : State Nat := { st 3 OC with isFinal := true }
def sF : SignedState Nat := ⟨stF, [p0]⟩
def s3 : SignedState Nat := ⟨st 3 OC, [p0]⟩
def r4 : SignedState Nat := ⟨st 4 OC, [q0]⟩
def s5 : SignedState Nat := ⟨st 5 OA, [p0]⟩
def r6 : SignedState Nat := ⟨st 6 OA, [q0]⟩

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
    (∃ ss, op = .conclude c0 ss ∧ ConclusionProof c0 ss ∧
      s'.statusOf c0 = .finalized ss.state.turnNum ss.state.outcome ss.state.outcome) ∨
    (∃ o0 o', (s.statusOf c0).finalOutcome s.now = some o0 ∧
      s'.statusOf c0 = (s.statusOf c0).withOutcome o') := by
  rcases TakeOut.status_cases (c := c0) h with heq | ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩ |
      ⟨P, cand, rfl, hsup, -, hopen, hlt, hst⟩ | ⟨ss, rfl, hcp, hst⟩ | hpay
  · exact Or.inl heq
  · exact Or.inr (Or.inl ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨P, cand, rfl, hsup, hopen, hlt, hst⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ss, rfl, hcp, hst⟩)))
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

def net : NetworkState Nat p0 := ⟨Adjudicator.genesis, [r6, r4, r2, r0], [s5, s3, sF, s1]⟩

theorem unforged_q {n : NetworkState Nat p0} {k : Nat} {o : Outcome Nat} :
    n.Unforged ⟨st k o, [q0]⟩ :=
  ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0, fun v hv => by simp [st, State.voucher?] at hv⟩

theorem unforged_sent {n : NetworkState Nat p0} {s : SignedState Nat} (hs : s ∈ n.sent) :
    n.Unforged s :=
  ⟨fun _ => ⟨s, hs, rfl⟩, fun _ hv _ => ⟨s, hs, hv⟩⟩

/-- A state that only `p0` signed, with no voucher, and that `p0` sent, is held. -/
theorem holds_sent {n : NetworkState Nat p0} {s : SignedState Nat} (hs : s ∈ n.sent)
    (hsig : s.signers = [p0]) (hv : s.state.voucher? = none) : n.Holds s :=
  ⟨fun q hq => .inl ⟨by rw [hsig] at hq; exact List.mem_singleton.1 hq, s, hs, rfl⟩,
    fun v h => by rw [hv] at h; cases h⟩

/-- Two held states, in a list. -/
theorem holds_two {n : NetworkState Nat p0} {a b : SignedState Nat} (ha : n.Holds a) (hb : n.Holds b) :
    ∀ ss ∈ [a, b], n.Holds ss := by
  intro ss hss
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact ha
  · exact hb

/-- A held state of the turn before, then the new state. -/
theorem moved {n : NetworkState Nat p0} {a : SignedState Nat} {s : State Nat} (ha : n.Holds a) :
    ∀ ss ∈ [a, (⟨s, [p0]⟩ : SignedState Nat)], n.Holds ss ∨ ss.state = s := by
  intro ss hss
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact .inl ha
  · exact .inr rfl

/-- The rule `HonestSend.oneState` excludes `net`: `p0` signed `sF` and `s3`,
    two different states at turn 3. Without the rule, `net` is reachable by
    the history of this file's header (commit `40e75719`, where this file
    refutes both Spec statements). -/
theorem net_not_honest : ¬ (Nitro.participant appsS TN).Reachable net := fun h =>
  (Nitro.participant_sent_honest ⟨net, h⟩ sF (show sF ∈ net.sent by decide)).oneState
    ⟨s3, show s3 ∈ net.sent by decide, rfl, rfl, by decide⟩

theorem net_status : net.chain.statusOf c0 = .open 0 := by decide

/-- No challenge is running at `net`: `hpend` holds. -/
theorem net_deadlineAfter : net.DeadlineAfter c0 T0.ε := fun _ _ h => by
  rw [net_status] at h; cases h

/-! ## Why the rules exclude `net`

Before the rules `oneState` and `finalLast`, `net` was reachable, and this
file refuted both Spec statements (commit `40e75719`). The game at `net`
needed `p0` to answer with a non-final move at turn 7 after its final state
`sF`; `finalLast` forbids that move too. -/

#print axioms appsS_desirable
#print axioms net_not_honest

end ArmadaLean.Nitro.CounterexampleFinalBranch
