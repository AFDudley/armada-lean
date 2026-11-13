/-
  Failure test: an app that is IR and IC and conserves every amount, but
  changes a destination, so it fails value conservation with go-nitro's
  form rule and is not desirable. Nitro-24
  (Nitro:653-658) in the old form, with IR, IC and amount conservation in
  place of `Desirable` (`Old_finalizable_or_two_enabled`,
  `Old_single_enabled_is_finalizable`), fails for it, against the threat
  `Threat.noOwnViolation`.

  The app is a three-slot ForceMove app on a two-party ledger channel `c0`
  (`[q0, p0]`, `n = 2`). An outcome `pay a f` pays 5 to `q0`, `a` to `p0`,
  and 0 to the destination `f + 3`, which belongs to no participant (the
  tag `f`). A valid move keeps every amount; any mover may change the tag.
  The app is IR (`appsS_IR`), IC (`appsS_IC`) and keeps every amount
  (`amountConserving`).
  The adversary is the threat `T1 = T0.noOwnViolation destS`. Its answers
  change the tag. That is no gift (`q0`'s amount stays 5) and no conflict
  (one answer per slot), so it is no own-violation (`answer_clean`).

  The play is the play of `unowned_pool_take.lean` with the tag in place of
  the pool. `p0` deposits 5, `q0` deposits 5, so `c0` holds 10, all of
  `O1 = pay 5 0` (`net1_funded`).
  * `O1` is enabled (`enabled_O1`): the adversary challenges with `[r0, s1]`.
  * No outcome but `O1` is enabled (`prevents_other`): `p0` restores the tag
    0 after every move of `q0` from `O1`.
  * No outcome is finalizable (`not_finalizable`): the adversary answers
    every challenge with the target `Ω` by a new tag (`ansQ`).
  Both old forms fail (`finalizable_or_two_enabled_false`,
  `single_enabled_is_finalizable_false`).

  No value moves in this play: every outcome pays `q0` 5 and `p0` 5. The
  answers only change who a zero entry pays. go-nitro
  `SingleAssetPayments.sol` refuses a changed destination ("Destinations may
  not change"), so the app fails value conservation
  (`appsS_not_conserving`), is not desirable (`appsS_not_desirable`), and
  lacks the go-nitro payment rules (`appsS_not_paymentRules`).

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/zero_entry_tag.lean`.
  The theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Spec.Nitro.Liveness
import ArmadaLean.Nitro.TakeOut

namespace ArmadaLean.Nitro.CounterexampleTag

open ArmadaLean.Nitro

/-! ## The instance -/

def q0 : Participant := ⟨0⟩
def p0 : Participant := ⟨1⟩

theorem p0_ne_q0 : p0 ≠ q0 := by decide

/-- The destination map: a participant is paid at its own key plus one.
    `q0` is paid at `1`, `p0` at `2`. The destinations `0` and from `3` on
    belong to no participant. -/
def destS (q : Participant) : Nat := q.key + 1

/-- The allocation slots of `c0`: slot 0 pays `q0`, slot 1 pays `p0`. -/
def dQ : Address Nat := .external (destS q0)
def dP : Address Nat := .external (destS p0)

/-- The three-slot allocation: 5 to `q0`, `a` to `p0`, and a zero entry for
    the destination `f + 3`, the tag `f`. The tag moves no value. -/
def pay (a f : Nat) : Outcome Nat := .allocation [alloc dQ 5, alloc dP a, alloc (.external (f + 3)) 0]

/-- The outcome of `p0`'s states: 5 to `p0`, the tag 0. -/
def O1 : Outcome Nat := pay 5 0

/-- The amount of `p0` and the tag of a three-slot allocation, `(a, f)` for
    `pay a f`. -/
def decode : Outcome Nat → Option (Nat × Nat)
  | .allocation [⟨.external 1, .alloc 5⟩, ⟨.external 2, .alloc a⟩, ⟨.external (f + 3), .alloc 0⟩] =>
    some (a, f)
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

/-- The adversary's answer to the target `Ω`: `q0` changes the tag. `O1`
    when `Ω` is no three-slot allocation; the adversary then never answers
    (`adv_target`). -/
def ansQ (Ω : Outcome Nat) : Outcome Nat :=
  match decode Ω with
  | some (a, f) => pay a (f + 1)
  | none => O1

theorem ansQ_ne (Ω : Outcome Nat) : ansQ Ω ≠ Ω := by
  unfold ansQ
  split
  · rename_i a f hd
    rw [decode_eq_some.1 hd]
    intro h
    have := congrArg decode h
    rw [decode_pay, decode_pay] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    omega
  · rename_i hne
    intro h
    rw [← h] at hne
    cases hne

/-- A ledger channel, so that both parties can deposit into it. `q0` moves
    at even turns, `p0` at odd turns. -/
def c0 : FixedPart :=
  { participants := [q0, p0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 6, kind := .ledger }

theorem c0_n : c0.n = 2 := rfl

/-- The game library: both outcomes are three-slot allocations, and every
    amount stays. Any mover may change the tag. -/
def vtS (s s' : State Nat) : Bool :=
  match decode s.outcome, decode s'.outcome with
  | some (a, _), some (a', _) => decide (a = a')
  | _, _ => false

theorem vtS_iff (s s' : State Nat) : vtS s s' = true ↔ ∃ a b a' b', decode s.outcome = some (a, b) ∧
    decode s'.outcome = some (a', b') ∧ a = a' := by
  unfold vtS
  split
  · rename_i a b a' b' h1 h2
    simp [h1, h2]
  · rename_i h
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro a b a' b' h1 h2
    exact (h a b a' b' h1 h2).elim

def appsS : Apps Nat := fun _ => forceMoveRules vtS

theorem appsS_supportWindow : (appsS c0.appDef).SupportWindow :=
  forceMoveRules_supportWindow vtS

/-- The amount `pay a f` gives the destination `k`: 5 at `q0`'s `1`, `a` at
    `p0`'s `2`, nothing elsewhere. -/
theorem share_pay (a f k : Nat) :
    share (pay a f) k = if k = 1 then 5 else if k = 2 then a else 0 := by
  rcases k with _ | _ | _ | k <;>
    simp [share, pay, Outcome.entries, Allocation.owed, Allocation.find, alloc, dQ, dP, destS, q0,
      p0, Entry.amount, Item.amount] <;> split <;> rfl

/-- A valid move keeps `q0`'s amount: 5 on both sides. -/
theorem vtS_share {s s' : State Nat} (h : vtS s s' = true) :
    share s.outcome (destS q0) = share s'.outcome (destS q0) := by
  obtain ⟨a, f, a', f', h0, h1, -⟩ := (vtS_iff _ _).1 h
  rw [decode_eq_some.1 h0, decode_eq_some.1 h1, share_pay, share_pay]
  rfl

/-- The non-final state of `c0` at turn `k` with the outcome `o`. -/
def st (k : Nat) (o : Outcome Nat) : State Nat :=
  { channel := c0, turnNum := k, outcome := o, isFinal := false, appData := .opaque 0 }

def r0 : SignedState Nat := ⟨st 0 O1, [q0]⟩
def s1 : SignedState Nat := ⟨st 1 O1, [p0]⟩

/-- The adversary: any call by another participant that forges no
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

/-- The channel with its timing fact: `2 * ε ≤ 6`. -/
def tc0 : TimedChannel T0.ε := ⟨c0, by decide⟩

/-- The adversary without own-violations of `q0` (`Threat.noOwnViolation`):
    the threat of both Nitro-24 statements. -/
def T1 : Threat Nat p0 := T0.noOwnViolation destS

/-- The round bound, read off a round. -/
theorem round_bound {apps : Apps Nat} {m : HonestMove Nat} {n n' : NetworkState Nat p0}
    (h : T1.Round apps m n n') : n'.chain.now < n.chain.now + 2 := h.2

/-- A round from a derivation that ends one tick later. -/
theorem mkRound {apps : Apps Nat} {m : HonestMove Nat} {n n' : NetworkState Nat p0}
    (hseq : T1.RoundSeq apps n.chain.now m.calls n n') (hnow : n'.chain.now = n.chain.now + 1) :
    T1.Round apps m n n' :=
  ⟨hseq, by rw [hnow]; exact Nat.add_lt_add_left (show 1 < T1.ε by decide) _⟩

/-! ## The funded start

`p0` deposits its share 5 (its own `deposit` call, the fourth step of
`Nitro.participantWith`), then `q0` deposits its share 5. `c0` then holds
10, the whole of `O1` (`net1_funded`). -/

/-- The deposit of `p0`: 5 into `c0`, which holds 0. -/
def depP : Op Nat := .deposit (.channel c0) 0 5
/-- The deposit of `q0`: 5 into `c0`, which holds 5. -/
def depQ : Op Nat := .deposit (.channel c0) 5 5

/-- The chain after `p0`'s deposit. -/
def s5 : Adjudicator Nat :=
  { Adjudicator.genesis with balances := Adjudicator.genesis.balances.add (.channel c0) 5, held := 5 }
/-- The chain after both deposits: `c0` holds 10. -/
def sF : Adjudicator Nat := { s5 with balances := s5.balances.add (.channel c0) 5, held := 10 }

theorem depP_apply : Adjudicator.genesis.apply appsS p0 depP = some s5 := rfl
theorem depQ_apply : s5.apply appsS q0 depQ = some sF := rfl

def net1 : NetworkState Nat p0 := ⟨sF, [r0], [s1]⟩

/-- `c0` holds 10 coins at `net1`: all of `O1`. -/
theorem net1_funded : net1.chain.DirectlyFundedWith c0 10 := by
  show 10 ≤ sF.balances.get c0.address
  decide

theorem unforged_r0 (n : NetworkState Nat p0) : n.Unforged r0 :=
  ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0, fun v hv => by simp [r0, st, State.voucher?] at hv⟩

theorem send_feasible :
    (HonestMove.send (st 1 O1)).Feasible appsS (⟨sF, [r0], []⟩ : NetworkState Nat p0) :=
  (HonestMove.Feasible_send _ _ _).mpr
    ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide), fun h => absurd h (by decide), by decide, by decide⟩

theorem net1_reachable : (Nitro.participant appsS T1).Reachable net1 := by
  refine ⟨⟨Adjudicator.genesis, [], []⟩, rfl, ?_⟩
  have h1 : (⟨Adjudicator.genesis, [], []⟩ : NetworkState Nat p0).applyAdv appsS (.land depP) =
      ⟨s5, [], []⟩ := NetworkState.applyAdv_land_some appsS depP_apply
  have h2 : (⟨s5, [], []⟩ : NetworkState Nat p0).applyAdv appsS (.chain q0 depQ) = ⟨sF, [], []⟩ :=
    NetworkState.applyAdv_chain_some appsS depQ_apply
  refine .tail (b := ⟨sF, [r0], []⟩) ?_ (Or.inl ⟨.send (st 1 O1), send_feasible, rfl⟩)
  refine .tail (b := ⟨sF, [], []⟩) ?_
    (Or.inr (Or.inr (Or.inl ⟨.deliver r0, ⟨unforged_r0 _, fun q _ _ h => by
      rcases h with ⟨s, hs, -⟩ | ⟨-, s, hs, -⟩ <;> simp at hs⟩, fun op h => (by cases h), rfl⟩)))
  refine .tail (b := ⟨s5, [], []⟩) ?_ (Or.inr (Or.inr (Or.inl ⟨.chain q0 depQ,
    ⟨⟨by decide, fun ss hss => by cases hss⟩, fun ss hss => by cases hss⟩, fun op h => (by cases h),
    h2.symm⟩)))
  exact .tail .refl (Or.inr (Or.inr (Or.inr ⟨.channel c0, 0, 5, h1.symm⟩)))

theorem supports_r0s1 : (appsS c0.appDef).supports c0 [r0, s1] (st 1 O1) = true := by decide

theorem holds_r0s1 : ∀ ss ∈ [r0, s1], net1.Holds ss := by
  intro ss hss
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact holds_of_mem_received (List.mem_singleton_self _)
  · refine ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s1, List.mem_singleton_self _, rfl⟩,
      fun v hv => by simp [s1, st, State.voucher?] at hv⟩

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

/-- A state `p0` holds with a signature of `q0` is a received state with it. -/
theorem held_q {n : NetworkState Nat p0} {ss : SignedState Nat} (h : n.Holds ss)
    (hq : q0 ∈ ss.signers) : ∃ r ∈ n.received, r.state = ss.state ∧ q0 ∈ r.signers := by
  rcases h.1 q0 hq with ⟨hqp, -⟩ | hr
  · exact absurd hqp.symm p0_ne_q0
  · exact hr

/-- `q0` is a participant of `c0`, so a conclusion proof of `c0` carries
    its signature. -/
theorem conclusion_q0 {ss : SignedState Nat} (h : ConclusionProof c0 ss) :
    q0 ∈ ss.signers ∧ ss.state.isFinal = true := by
  obtain ⟨hch, hfin, hall⟩ := h
  exact ⟨hall q0 (by rw [hch]; decide), hfin⟩

theorem conclusion_p0 {ss : SignedState Nat} (h : ConclusionProof c0 ss) : p0 ∈ ss.signers := by
  obtain ⟨hch, -, hall⟩ := h
  exact hall p0 (by rw [hch]; decide)

/-- One successful operation on `c0`: the status it leaves. A transfer or a
    reclaim of the ledger `c0` pays out from a final status, and keeps its
    finalized outcome (`ChannelStatus.withOutcome`). -/
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

/-! ## `O1` is enabled

The adversary challenges with `[r0, s1]` in the first round. A support at a
turn above 1 needs a state of `q0` at an even turn from 2 on, and `q0` signs
none. So the challenge stands, and the clock reaches its deadline. -/

def ch1 : Challenge Nat := ⟨st 1 O1, 6⟩

/-- Every support whose `q0`-signed states are `r0`'s state has a turn of
    at most 1. -/
theorem low_turn {P : SupportProof Nat} {cand : State Nat}
    (h : (appsS c0.appDef).supports c0 P cand = true)
    (hq : ∀ ss ∈ P, q0 ∈ ss.signers → ss.state = st 0 O1) : cand.turnNum ≤ 1 := by
  obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht, hmv0, hmv1, -⟩⟩ := fm2 h
  rw [← hlast, ht]
  rcases Nat.mod_two_eq_zero_or_one m0.state.turnNum with he | ho
  · have h0 := hq m0 (by simp) (byMover_even hc0 hmv0 he)
    rw [h0]; decide
  · have h1 : m1.state.turnNum % 2 = 0 := by omega
    have h0 := hq m1 (by simp) (byMover_even hc1 hmv1 h1)
    have : m1.state.turnNum = 0 := by rw [h0]; rfl
    omega

/-- The status of the play that finalizes `O1`: the challenge `ch1`, or
    `c0` finalized with `O1` after a payout. -/
def StE (x : ChannelStatus Nat) : Prop :=
  x = .challenged 1 ch1 ∨ ∃ o, x = .finalized 1 O1 o

theorem StE.withOutcome {x : ChannelStatus Nat} (h : StE x) (o : Outcome Nat) :
    StE (x.withOutcome o) := by
  rcases h with rfl | ⟨o', rfl⟩
  · exact Or.inr ⟨o, rfl⟩
  · exact Or.inr ⟨o, rfl⟩

/-- The challenge `ch1` stands, or `c0` is finalized with `O1`, against every
    operation whose `q0`-signed states are `r0`'s state. -/
theorem stay {s s' : Adjudicator Nat} {caller : Participant} {op : Op Nat}
    (hs : StE (s.statusOf c0)) (h : s.apply appsS caller op = some s')
    (hq : ∀ ss ∈ op.proofStates, q0 ∈ ss.signers → ss.state = st 0 O1) :
    StE (s'.statusOf c0) := by
  rcases status_cases h with heq | ⟨P, cand, rfl, hsup, -, hmode, -⟩ |
      ⟨P, cand, rfl, hsup, hopen, hlt, -⟩ | ⟨ss, rfl, hcp⟩ | ⟨o0, o', -, hst⟩
  · rw [heq]; exact hs
  · have hlow := low_turn hsup hq
    rw [Adjudicator.mode_eq] at hmode
    rcases hs with hs | ⟨o, hs⟩ <;> rw [hs] at hmode
    · rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
      · simp only [ChannelStatus.mode] at hm
        split at hm <;> cases hm
      · simp only [ChannelStatus.turnNumRecord_challenged] at hr
        omega
    · rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
  · rcases hs with hs | ⟨o, hs⟩ <;> rw [hs] at hlt hopen
    · have hlow := low_turn hsup hq
      simp only [ChannelStatus.turnNumRecord_challenged] at hlt
      omega
    · exact absurd hopen (by simp [ChannelStatus.IsOpen, ChannelStatus.mode])
  · obtain ⟨hq0, hfin⟩ := conclusion_q0 hcp
    have h0 := hq ss (List.mem_singleton_self ss) hq0
    rw [h0] at hfin
    cases hfin
  · rw [hst]; exact hs.withOutcome o'

/-- The invariant of the play that finalizes `O1`. -/
structure InvE (n : NetworkState Nat p0) : Prop where
  recvQ : ∀ r ∈ n.received, q0 ∈ r.signers → r.state = st 0 O1
  recvU : ∀ r ∈ n.received, n.Unforged r
  status : StE (n.chain.statusOf c0)

theorem InvE.applyHonest {n : NetworkState Nat p0} (hI : InvE n) (m : HonestMove Nat) :
    InvE (n.applyHonest m) := by
  cases m with
  | react r =>
    exact ⟨hI.recvQ, fun x hx => (hI.recvU x hx).mono (fun y hy => List.mem_append_right _ hy),
      hI.status⟩
  | wait dt =>
    exact ⟨hI.recvQ, fun x hx => (hI.recvU x hx).of_sent rfl,
      by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; exact hI.status⟩

/-- The calls of `p0` land in order, then one tick of 1 closes the round;
    `InvE` holds throughout. -/
theorem roundE {n0 : NetworkState Nat p0} (hI0 : InvE n0) (t : Time) :
    ∀ (pending : List (Op Nat)), (∀ op ∈ pending, op.HonestFeasible n0) →
    ∀ m : NetworkState Nat p0, InvE m → m.sent = n0.sent →
      ∃ m', T1.RoundSeq appsS t pending m m' ∧ InvE m' ∧ m'.chain.now = m.chain.now + 1 ∧
        m'.sent = m.sent := by
  intro pending
  induction pending with
  | nil =>
    intro _ m hI _
    refine ⟨m.applyAdv appsS (.tick 1), .tick ⟨trivial, trivial⟩ (Or.inl rfl) .nil, ?_, rfl, rfl⟩
    exact ⟨hI.recvQ, fun x hx => (hI.recvU x hx).of_sent rfl,
      by rw [NetworkState.applyAdv_tick, Adjudicator.tick_statusOf]; exact hI.status⟩
  | cons op rest ih =>
    intro hfeas m hI hsent
    have hop := hfeas op List.mem_cons_self
    have hheld : ∀ ss ∈ op.proofStates, n0.Holds ss := hop.mem
    have hq : ∀ ss ∈ op.proofStates, q0 ∈ ss.signers → ss.state = st 0 O1 := by
      intro ss hss hq0
      obtain ⟨r, hr, hrs, hrq⟩ := held_q (hheld ss hss) hq0
      rw [← hrs]; exact hI0.recvQ r hr hrq
    have hI1 : InvE (m.applyAdv appsS (.land op)) := by
      cases happ : m.chain.apply appsS p0 op with
      | none => rw [NetworkState.applyAdv_land_none appsS happ]; exact hI
      | some s' =>
        rw [NetworkState.applyAdv_land_some appsS happ]
        refine ⟨fun x hx hxq => ?_, fun x hx => ?_, stay hI.status happ hq⟩
        · rcases List.mem_append.1 hx with hx | hx
          · exact hq x hx hxq
          · exact hI.recvQ x hx hxq
        · rcases List.mem_append.1 hx with hx | hx
          · exact ((hheld x hx).unforged hI0.recvU).of_sent hsent.symm
          · exact (hI.recvU x hx).of_sent rfl
    obtain ⟨m', hseq, hI', hnow, hs'⟩ := ih (fun o ho => hfeas o (List.mem_cons_of_mem _ ho))
      (m.applyAdv appsS (.land op)) hI1 (by rw [NetworkState.applyAdv_sent]; exact hsent)
    refine ⟨m', .land (l1 := []) (l2 := rest) rfl hseq, hI', ?_, ?_⟩
    · rw [hnow, landed_now hop.not_tick]
    · rw [hs', NetworkState.applyAdv_sent]

/-- Every feasible move of `p0` has a round, one tick long, that keeps
    `InvE`. -/
theorem roundE_exists {n : NetworkState Nat p0} (hI : InvE n) {m : HonestMove Nat}
    (hfeas : m.Feasible appsS n) :
    ∃ n', T1.Round appsS m n n' ∧ InvE n' ∧ n'.chain.now = n.chain.now + 1 := by
  have hcalls : ∀ op ∈ m.calls, op.HonestFeasible n := by
    cases m with
    | react r => exact hfeas.1
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  obtain ⟨n', hseq, hI', hnow, -⟩ := roundE hI n.chain.now m.calls hcalls n hI rfl
  exact ⟨n', mkRound hseq hnow, hI', hnow⟩

/-- The adversary's challenge of the first round. -/
def opE : Op Nat := .challenge c0 [r0, s1] (st 1 O1)

def sChE : Adjudicator Nat := sF.setStatus c0 (.challenged 1 ch1)

theorem opE_apply : sF.apply appsS q0 opE = some sChE := by
  show sF.challenge appsS q0 c0 [r0, s1] (st 1 O1) = some sChE
  unfold Adjudicator.challenge
  rw [if_pos (by decide)]
  rfl

/-- The first round: the adversary challenges, then `p0`'s calls land, then
    one tick. -/
theorem roundE_first {m : HonestMove Nat} (hfeas : m.Feasible appsS net1) :
    ∃ n', T1.Round appsS m net1 n' ∧ InvE n' ∧ n'.chain.now = 1 := by
  let n1 : NetworkState Nat p0 := net1.applyAdv appsS (.chain q0 opE)
  have hn1 : n1 = ⟨sChE, [r0, s1] ++ [r0], [s1]⟩ := by
    show net1.applyAdv appsS (.chain q0 opE) = _
    rw [NetworkState.applyAdv_chain_some appsS opE_apply]; rfl
  have hI1 : InvE n1 := by
    rw [hn1]
    refine ⟨fun x hx hxq => ?_, fun x hx => ?_, Or.inl rfl⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rfl
      · exact absurd hxq (by decide)
      · rfl
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact unforged_r0 _
      · exact ⟨fun _ => ⟨s1, List.mem_singleton_self _, rfl⟩, fun v hv => by simp [s1, st, State.voucher?] at hv⟩
      · exact unforged_r0 _
  have hI0 : InvE n1 := hI1
  have hcalls : ∀ op ∈ m.calls, op.HonestFeasible n1 := by
    intro op hop
    have h0 : op.HonestFeasible net1 := by
      cases m with
      | react r => exact hfeas.1 op hop
      | wait dt => simp [HonestMove.calls] at hop
    cases op with
    | deposit a e x => exact h0.elim
    | tick dt => exact h0.elim
    | _ =>
      intro ss hss
      have hs : net1.sent = n1.sent := by rw [hn1]; rfl
      have hr : ∀ r ∈ net1.received, r ∈ n1.received := fun r hr => by
        rw [hn1]; exact List.mem_append_right _ hr
      exact holds_mono hs hr (h0 ss hss)
  obtain ⟨n', hseq, hI', hnow, -⟩ := roundE hI0 0 m.calls hcalls n1 hI1 rfl
  have hfeasE : T1.feasible net1 (.chain q0 opE) := by
    refine ⟨⟨by decide, fun ss hss => ?_⟩, AdvMove.NoOwnViolation.chain_of ?_⟩
    · simp only [opE, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
      rcases hss with rfl | rfl
      · exact unforged_r0 _
      · exact ⟨fun _ => ⟨s1, List.mem_singleton_self _, rfl⟩, fun v hv => by simp [s1, st, State.voucher?] at hv⟩
    · show ∀ ss ∈ [r0, s1], ∀ q ∈ ss.signers, q ≠ p0 →
        ¬ OwnViolation destS q ([r0, s1] ++ [r0]) ss
      decide
  have hnow1 : n1.chain.now = 0 := by rw [hn1]; rfl
  refine ⟨n', mkRound (.other hfeasE (fun _ h => by cases h) (fun _ h => by cases h) hseq)
    (by rw [hnow, hnow1]; rfl), hI', by rw [hnow, hnow1]⟩

theorem enabled_O1 : Enabled appsS T1 c0 O1 net1 := by
  rintro ⟨σ, hσ, hprev⟩
  have hrun : ∀ k, ∃ n1 n2, Run appsS T1 σ net1 n1 ∧ T1.Round appsS (σ n1) n1 n2 ∧ InvE n2 ∧
      k + 1 ≤ n2.chain.now := by
    intro k
    induction k with
    | zero =>
      obtain ⟨n2, hr, hI, hnow⟩ := roundE_first (hσ net1)
      exact ⟨net1, n2, .refl, hr, hI, by rw [hnow]⟩
    | succ k ih =>
      obtain ⟨n1, n2, hrun, hr, hI, hle⟩ := ih
      have hI1 := hI.applyHonest (σ n1)
      have hnow1 : n2.chain.now ≤ (n2.applyHonest (σ n1)).chain.now := by
        cases σ n1 with
        | react r => exact le_refl _
        | wait dt => exact Nat.le_add_right _ _
      obtain ⟨n3, hr', hI', hnow'⟩ := roundE_exists hI1 (hσ _)
      refine ⟨_, n3, .round hrun hr, hr', hI', ?_⟩
      rw [hnow']
      exact Nat.succ_le_succ (le_trans hle hnow1)
  obtain ⟨n1, n2, hr, hround, hI, hle⟩ := hrun 5
  apply hprev n1 n2 hr hround
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel]
  rcases hI.status with hs | ⟨o, hs⟩ <;> rw [hs]
  · simp only [ChannelStatus.finalizedWith_challenged]
    rw [if_pos (show ch1.deadline ≤ n2.chain.now from hle)]
    rfl
  · rfl

/-! ## No outcome is finalizable

The adversary has a set `G` of outcomes to avoid and an answer outcome
`A ∉ G`. It lands `p0`'s calls, then answers a challenge whose outcome is in
`G` by a move of `q0` at the next turn, with the outcome `A`. Then one tick.
For one target `Ω`, `G = {Ω}` and `A = ansQ Ω`. -/

/-- A state that `q0` signed in the play: `r0`'s state, or a non-final
    state with the answer outcome `A`. -/
def QOK (A : Outcome Nat) (s : State Nat) : Prop :=
  s = st 0 O1 ∨ (s.outcome = A ∧ s.isFinal = false)

/-- The adversary's choice: `A` avoids `G`, and `A` is a valid move of `q0`
    from every state of `p0` with an outcome in `G` that a support of the
    play can carry: a valid move from a state of `q0`, or `s1`'s state. -/
structure Adv (G : Outcome Nat → Prop) (A : Outcome Nat) : Prop where
  notG : ¬ G A
  valid : ∀ y : State Nat, y.channel = c0 → y.turnNum % 2 = 1 → G y.outcome →
    ((∃ m0 : State Nat, QOK A m0 ∧ vtS m0 y = true) ∨ y = st 1 O1) →
    vtS y (st (y.turnNum + 1) A) = true

structure InvA (A : Outcome Nat) (n : NetworkState Nat p0) : Prop where
  recvQ : ∀ r ∈ n.received, q0 ∈ r.signers → QOK A r.state
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent1 : ∃ s ∈ n.sent, s.state = st 1 O1
  /-- Every received state of `c0` carries the signature of `q0` or `p0`. -/
  recvSig : ∀ r ∈ n.received, r.state.channel = c0 → q0 ∈ r.signers ∨ p0 ∈ r.signers
  /-- `p0` signed one outcome per channel and turn (`HonestSend.noConflict`). -/
  sentNC : ∀ s ∈ n.sent, ∀ s' ∈ n.sent, s.state.channel = s'.state.channel →
    s.state.turnNum = s'.state.turnNum → s.state.outcome = s'.state.outcome

/-- The statuses from which no outcome in `G` is finalized: open, a
    challenge with an outcome outside `G`, or finalized outside `G` (a payout
    after an expired challenge keeps the finalized outcome). -/
def SafeA (G : Outcome Nat → Prop) (x : ChannelStatus Nat) : Prop :=
  (∃ t, x = .open t) ∨ (∃ t ch, x = .challenged t ch ∧ ¬ G ch.state.outcome) ∨
    (∃ t f o, x = .finalized t f o ∧ ¬ G f)

/-- A running challenge with an outcome in `G` at an odd turn `t`, where `p0`
    signed a non-final state `y` of `c0` at turn `t`, and `A` is a valid move
    from `y`: the adversary can answer it. -/
def Answerable (G : Outcome Nat → Prop) (A : Outcome Nat) (n : NetworkState Nat p0) : Prop :=
  ∃ t ch y, n.chain.statusOf c0 = .challenged t ch ∧ n.chain.now < ch.deadline ∧
    G ch.state.outcome ∧ t % 2 = 1 ∧ y ∈ n.sent ∧ y.state.channel = c0 ∧
    y.state.turnNum = t ∧ y.state.isFinal = false ∧ vtS y.state (st (t + 1) A) = true

theorem safeA_not_finalized {G : Outcome Nat → Prop} {Ω : Outcome Nat}
    {n : NetworkState Nat p0} (h : SafeA G (n.chain.statusOf c0)) (hG : G Ω) :
    ¬ n.Finalized c0 Ω := by
  intro hf
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf
  rcases h with ⟨t, ht⟩ | ⟨t, ch, ht, hne⟩ | ⟨t, f, o, ht, hne⟩
  · rw [ht] at hf; simp at hf
  · rw [ht] at hf
    simp only [ChannelStatus.finalizedWith_challenged] at hf
    split at hf
    · exact hne (Option.some.inj hf ▸ hG)
    · cases hf
  · rw [ht, ChannelStatus.finalizedWith_finalized] at hf
    exact hne (Option.some.inj hf ▸ hG)

theorem held_QOK {A : Outcome Nat} {n : NetworkState Nat p0} (hI : InvA A n)
    {ss : SignedState Nat} (h : n.Holds ss) (hq : q0 ∈ ss.signers) : QOK A ss.state := by
  obtain ⟨r, hr, hrs, hrq⟩ := held_q h hq
  rw [← hrs]; exact hI.recvQ r hr hrq

/-- A support of `c0` that `p0` holds, with an outcome in `G`: its candidate is
    at an odd turn, and `p0` signed a non-final state of `c0` at that turn,
    from which `A` is a valid move. -/
theorem answerable_of_support {G : Outcome Nat → Prop} {A : Outcome Nat} (hA : Adv G A)
    {n : NetworkState Nat p0} (hI : InvA A n)
    {P : SupportProof Nat} {cand : State Nat} (h : (appsS c0.appDef).supports c0 P cand = true)
    (hH : ∀ ss ∈ P, n.Holds ss) (hΩ : G cand.outcome) :
    cand.turnNum % 2 = 1 ∧ ∃ y ∈ n.sent, y.state.channel = c0 ∧ y.state.turnNum = cand.turnNum ∧
      y.state.isFinal = false ∧ vtS y.state (st (cand.turnNum + 1) A) = true := by
  obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht, hmv0, hmv1, hfin, hvt⟩⟩ := fm2 h
  have hH0 := hH m0 (by simp)
  have hH1 := hH m1 (by simp)
  subst hlast
  rcases Nat.mod_two_eq_zero_or_one m1.state.turnNum with he | ho
  · rcases held_QOK hI hH1 (byMover_even hc1 hmv1 he) with h0 | ⟨hcut, -⟩
    · have : m1.state.turnNum = 0 := by rw [h0]; rfl
      omega
    · exact absurd (hcut ▸ hΩ) hA.notG
  · refine ⟨ho, ?_⟩
    have he0 : m0.state.turnNum % 2 = 0 := by omega
    have hq0 := held_QOK hI hH0 (byMover_even hc0 hmv0 he0)
    obtain ⟨y, hy, hys⟩ := (hH1.unforged hI.recvU).1 (byMover_odd hc1 hmv1 ho)
    cases hf : m1.state.isFinal with
    | false =>
      refine ⟨y, hy, by rw [hys]; exact hc1, by rw [hys], by rw [hys]; exact hf, ?_⟩
      rw [hys]
      exact hA.valid m1.state hc1 ho hΩ (Or.inl ⟨m0.state, hq0, hvt hf⟩)
    | true =>
      have hout := hfin hf
      rcases hq0 with h0 | ⟨hcut, -⟩
      · obtain ⟨y, hy, hys⟩ := hI.sent1
        have h00 : m0.state.turnNum = 0 := by rw [h0]; rfl
        have h11 : m1.state.turnNum = 1 := by rw [ht, h00]
        have hO1 : G (st 1 O1).outcome := by
          show G O1
          rw [← show m0.state.outcome = O1 by rw [h0]; rfl, ← hout]; exact hΩ
        refine ⟨y, hy, by rw [hys]; rfl, by rw [hys, h11]; rfl, by rw [hys]; rfl, ?_⟩
        rw [hys, h11]
        exact hA.valid (st 1 O1) rfl rfl hO1 (Or.inr rfl)
      · exact absurd ((hout.trans hcut) ▸ hΩ) hA.notG

/-- The answer of `q0` to `p0`'s state `y`. -/
def opAns (A : Outcome Nat) (y : State Nat) : Op Nat :=
  .challenge c0 [⟨y, [p0]⟩, ⟨st (y.turnNum + 1) A, [q0]⟩] (st (y.turnNum + 1) A)

/-- A state of `c0` in the proof of a successful call carries the signature
    of `q0` or of `p0`: a support of `c0` is signed by its movers, and a
    conclusion proof by everyone. -/
theorem proof_signed {s s' : Adjudicator Nat} {caller : Participant} {op : Op Nat}
    (h : s.apply appsS caller op = some s') {ss : SignedState Nat} (hss : ss ∈ op.proofStates)
    (hc : ss.state.channel = c0) : q0 ∈ ss.signers ∨ p0 ∈ ss.signers := by
  have hfm : ∀ c' P cand, (appsS c'.appDef).supports c' P cand = true → ss ∈ P →
      q0 ∈ ss.signers ∨ p0 ∈ ss.signers := by
    intro c' P cand hsup hP
    have h' := hsup
    simp only [appsS, forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
    obtain rfl : c' = c0 := (h'.1.2 ss hP).symm.trans hc
    obtain ⟨m0, m1, htwo⟩ := fm2 hsup
    rw [htwo.eq] at hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · rcases Nat.mod_two_eq_zero_or_one ss.state.turnNum with he | ho
      · exact Or.inl (byMover_even htwo.ch0 htwo.mv0 he)
      · exact Or.inr (byMover_odd htwo.ch0 htwo.mv0 ho)
    · rcases Nat.mod_two_eq_zero_or_one ss.state.turnNum with he | ho
      · exact Or.inl (byMover_even htwo.ch1 htwo.mv1 he)
      · exact Or.inr (byMover_odd htwo.ch1 htwo.mv1 ho)
  cases op with
  | challenge c' P cand => exact hfm c' P cand (Adjudicator.challenge_some h).1.2.1 hss
  | checkpoint c' P cand => exact hfm c' P cand (Adjudicator.checkpoint_some h).1.2.1 hss
  | conclude c' ss' =>
    obtain ⟨⟨-, hcp⟩, -⟩ := Adjudicator.conclude_some h
    obtain rfl := List.mem_singleton.1 hss
    exact Or.inr (hcp.2.2 p0 (by rw [hc]; decide))
  | _ => simp [Op.proofStates] at hss

/-- The answer of `q0` is no own-violation: `q0` signed no other outcome at
    its slot, and no state of `c0` at the turn before pays `q0` more than
    the answer. -/
theorem answer_clean {A : Outcome Nat} {m : NetworkState Nat p0} (hI : InvA A m)
    {y : SignedState Nat} (hy : y ∈ m.sent) (hyc : y.state.channel = c0)
    (ho : y.state.turnNum % 2 = 1) (hyv : vtS y.state (st (y.state.turnNum + 1) A) = true) :
    ¬ OwnViolation destS q0 ((opAns A y.state).proofStates ++ m.received)
      ⟨st (y.state.turnNum + 1) A, [q0]⟩ := by
  have hsh := vtS_share hyv
  rintro (⟨s, hs, hc, hslot, hne⟩ | ⟨-, s, hs, hc, ht, hlt⟩)
  · obtain ⟨hs, hsq⟩ := List.mem_filter.1 hs
    have hsq : q0 ∈ s.signers := of_decide_eq_true hsq
    simp only [opAns, Op.proofStates, List.cons_append, List.nil_append, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact absurd (List.mem_singleton.1 hsq) (Ne.symm p0_ne_q0)
    · exact hne rfl
    · rcases hI.recvQ s hs hsq with h0 | ⟨hA', -⟩
      · have hsA : (st (y.state.turnNum + 1) A).signSlot = y.state.turnNum + 1 :=
          if_neg (by simp only [st, c0, FixedPart.n, List.length_cons, List.length_nil]; omega)
        rw [h0, hsA, show (st 0 O1).signSlot = 0 from rfl] at hslot
        omega
      · exact hne hA'
  · simp only [opAns, Op.proofStates, List.cons_append, List.nil_append, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · rw [hsh] at hlt; exact lt_irrefl _ hlt
    · simp only [st] at ht; omega
    · simp only [st] at ht
      rcases hI.recvSig s hs hc with hq | hp
      · rcases hI.recvQ s hs hq with h0 | ⟨hA', -⟩
        · rw [h0] at ht; simp only [st] at ht; omega
        · rw [hA'] at hlt; exact lt_irrefl _ hlt
      · obtain ⟨z, hz, hzs⟩ := (hI.recvU s hs).1 hp
        have hzy := hI.sentNC z hz y hy (by rw [hzs, hc, hyc]; rfl) (by rw [hzs]; omega)
        rw [← hzs, hzy, hsh] at hlt; exact lt_irrefl _ hlt

theorem supports_answer {y : State Nat} (A : Outcome Nat) (hc : y.channel = c0)
    (ht : y.turnNum % 2 = 1) (hf : y.isFinal = false) (hv : vtS y (st (y.turnNum + 1) A) = true) :
    (appsS c0.appDef).supports c0 [⟨y, [p0]⟩, ⟨st (y.turnNum + 1) A, [q0]⟩]
      (st (y.turnNum + 1) A) = true := by
  have hm1 : y.mover = some p0 := by rw [mover_c0 hc, if_neg (by omega)]
  have hm2 : (st (y.turnNum + 1) A).mover = some q0 := by
    rw [mover_c0 rfl, if_pos (by simp only [st]; omega)]
  have hb1 : (⟨y, [p0]⟩ : SignedState Nat).byMover = true := by
    simp [SignedState.byMover, hm1]
  have hb2 : (⟨st (y.turnNum + 1) A, [q0]⟩ : SignedState Nat).byMover = true := by
    simp [SignedState.byMover, hm2]
  simp only [appsS, forceMoveRules, validRun, validMove, hb2, hv]
  simp [hc, hf, st, c0, FixedPart.n, hb1]

theorem answer_apply {s : Adjudicator Nat} {ch : Challenge Nat} {y : State Nat}
    (A : Outcome Nat) (hs : s.statusOf c0 = .challenged y.turnNum ch) (hd : s.now < ch.deadline)
    (hc : y.channel = c0) (ht : y.turnNum % 2 = 1) (hf : y.isFinal = false)
    (hv : vtS y (st (y.turnNum + 1) A) = true) :
    s.apply appsS q0 (opAns A y) = some (s.setStatus c0
      (.challenged (y.turnNum + 1) ⟨st (y.turnNum + 1) A, s.now + 6⟩)) := by
  show s.challenge appsS q0 c0 _ _ = _
  unfold Adjudicator.challenge
  have hmode : s.mode c0 = .challenge := by
    rw [Adjudicator.mode_eq, hs]
    simp only [ChannelStatus.mode, if_neg (not_le.mpr hd)]
  rw [if_pos ⟨by decide, supports_answer _ hc ht hf hv, rfl, Or.inr ⟨hmode, by rw [hs]; simp [st]⟩⟩]
  rfl

/-- One land of a call of `p0` whose proof states `p0` holds keeps `InvA`, and
    leaves a safe or an answerable status. -/
theorem landA {G : Outcome Nat → Prop} {A : Outcome Nat} (hA : Adv G A)
    {m : NetworkState Nat p0} (hI : InvA A m) {op : Op Nat}
    (hop : ∀ dt, op ≠ .tick dt) (hH : ∀ ss ∈ op.proofStates, m.Holds ss)
    (hS : SafeA G (m.chain.statusOf c0) ∨ Answerable G A m) :
    InvA A (m.applyAdv appsS (.land op)) ∧
      (SafeA G ((m.applyAdv appsS (.land op)).chain.statusOf c0) ∨
        Answerable G A (m.applyAdv appsS (.land op))) := by
  cases happ : m.chain.apply appsS p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsS happ]; exact ⟨hI, hS⟩
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsS happ]
    have hnow : s'.now = m.chain.now := Adjudicator.apply_now_eq_of_not_tick hop happ
    refine ⟨⟨fun x hx hxq => ?_, fun x hx => ?_, hI.sent1, fun x hx hxc => ?_, hI.sentNC⟩, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact held_QOK hI (hH x hx) hxq
      · exact hI.recvQ x hx hxq
    · rcases List.mem_append.1 hx with hx | hx
      · exact (hH x hx).unforged hI.recvU
      · exact hI.recvU x hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact proof_signed happ hx hxc
      · exact hI.recvSig x hx hxc
    rcases status_cases happ with heq | ⟨P, cand, rfl, hsup, hcc, -, hst⟩ |
        ⟨P, cand, rfl, -, -, -, hst⟩ | ⟨ss, rfl, hcp⟩ | ⟨o0, o', hfo, hst⟩
    · rcases hS with hS | ⟨t, ch, y, hs, hd, hΩ, ho, hy, hyc, hyt, hyf, hyv⟩
      · exact Or.inl (by rw [heq]; exact hS)
      · exact Or.inr ⟨t, ch, y, by rw [heq]; exact hs, by rw [hnow]; exact hd, hΩ, ho, hy, hyc, hyt,
          hyf, hyv⟩
    · by_cases hΩ : G cand.outcome
      · obtain ⟨ho, y, hy, hyc, hyt, hyf, hyv⟩ := answerable_of_support hA hI hsup hH hΩ
        refine Or.inr ⟨cand.turnNum, _, y, hst, ?_, hΩ, ho, hy, hyc, hyt, hyf, hyv⟩
        show s'.now < m.chain.now + 6
        rw [hnow]; exact Nat.lt_add_of_pos_right (by decide)
      · exact Or.inl (Or.inr (Or.inl ⟨_, _, hst, hΩ⟩))
    · exact Or.inl (Or.inl ⟨_, hst⟩)
    · obtain ⟨hq0, hfin⟩ := conclusion_q0 hcp
      rcases held_QOK hI (hH ss (List.mem_singleton_self ss)) hq0 with h0 | ⟨-, hf⟩
      · rw [h0] at hfin; cases hfin
      · rw [hf] at hfin; cases hfin
    · -- a payout: the status was final, and keeps its finalized outcome
      left
      rw [hst]
      rcases hS with (⟨t, hs⟩ | ⟨t, ch, hs, hne⟩ | ⟨t, f, o, hs, hne⟩) |
          ⟨t, ch, y, hs, hd, -⟩
      · rw [hs, ChannelStatus.finalOutcome_open] at hfo; cases hfo
      · rw [hs, ChannelStatus.withOutcome_challenged]
        exact Or.inr (Or.inr ⟨_, _, _, rfl, hne⟩)
      · rw [hs, ChannelStatus.withOutcome_finalized]
        exact Or.inr (Or.inr ⟨_, _, _, rfl, hne⟩)
      · rw [hs, ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hd)] at hfo
        cases hfo

/-- The end of the round: the adversary answers an answerable challenge, then
    one tick of 1. -/
theorem closeA {G : Outcome Nat → Prop} {A : Outcome Nat} (hA : Adv G A)
    {m : NetworkState Nat p0} (hI : InvA A m)
    (hS : SafeA G (m.chain.statusOf c0) ∨ Answerable G A m) (t : Time) :
    ∃ m', T1.RoundSeq appsS t [] m m' ∧ InvA A m' ∧ SafeA G (m'.chain.statusOf c0) ∧
      m'.chain.now = m.chain.now + 1 ∧ m'.sent = m.sent := by
  have htick : ∀ x : NetworkState Nat p0, InvA A x → SafeA G (x.chain.statusOf c0) →
      ∃ m', T1.RoundSeq appsS t [] x m' ∧ InvA A m' ∧ SafeA G (m'.chain.statusOf c0) ∧
        m'.chain.now = x.chain.now + 1 ∧ m'.sent = x.sent := fun x hx hs =>
    ⟨x.applyAdv appsS (.tick 1), .tick ⟨trivial, trivial⟩ (Or.inl rfl) .nil,
      ⟨hx.recvQ, fun r hr => (hx.recvU r hr).of_sent rfl, hx.sent1, hx.recvSig, hx.sentNC⟩,
      by rw [NetworkState.applyAdv_tick, Adjudicator.tick_statusOf]; exact hs, rfl, rfl⟩
  rcases hS with hS | ⟨t', ch, y, hs, hd, -, ho, hy, hyc, hyt, hyf, hyv⟩
  · exact htick m hI hS
  · subst hyt
    have happ := answer_apply A hs hd hyc ho hyf hyv
    let ma := m.applyAdv appsS (.chain q0 (opAns A y.state))
    have hma : ma = ⟨m.chain.setStatus c0
        (.challenged (y.state.turnNum + 1) ⟨st (y.state.turnNum + 1) (A), m.chain.now + 6⟩),
        (opAns A y.state).proofStates ++ m.received, m.sent⟩ :=
      NetworkState.applyAdv_chain_some appsS happ
    have hUy : ∀ x : NetworkState Nat p0, y ∈ x.sent → x.Unforged ⟨y.state, [p0]⟩ := fun x hx =>
      ⟨fun _ => ⟨y, hx, rfl⟩, fun v hv _ => ⟨y, hx, hv⟩⟩
    have hUa : ∀ x : NetworkState Nat p0, x.Unforged ⟨st (y.state.turnNum + 1) (A), [q0]⟩ :=
      fun x => ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0,
        fun v hv => by simp [st, State.voucher?] at hv⟩
    have hIa : InvA A ma := by
      rw [hma]
      refine ⟨fun x hx hxq => ?_, fun x hx => ?_, hI.sent1, fun x hx _ => ?_, hI.sentNC⟩
      · simp only [opAns, Op.proofStates, List.cons_append, List.nil_append, List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact absurd (List.mem_singleton.1 hxq) (Ne.symm p0_ne_q0)
        · exact Or.inr ⟨rfl, rfl⟩
        · exact hI.recvQ x hx hxq
      · simp only [opAns, Op.proofStates, List.cons_append, List.nil_append, List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact hUy _ hy
        · exact hUa _
        · exact hI.recvU x hx
      · simp only [opAns, Op.proofStates, List.cons_append, List.nil_append, List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact Or.inr (List.mem_singleton_self _)
        · exact Or.inl (List.mem_singleton_self _)
        · exact hI.recvSig x hx ‹_›
    have hSa : SafeA G (ma.chain.statusOf c0) := by
      rw [hma]
      exact Or.inr (Or.inl ⟨y.state.turnNum + 1, ⟨st (y.state.turnNum + 1) (A), m.chain.now + 6⟩,
        by simp, hA.notG⟩)
    obtain ⟨m', hseq, hI', hS', hnow, hsent⟩ := htick ma hIa hSa
    have hfe : T1.feasible m (.chain q0 (opAns A y.state)) := by
      refine ⟨⟨by decide, fun ss hss => ?_⟩,
        AdvMove.NoOwnViolation.chain_of fun ss hss q hq hqp => ?_⟩
      · simp only [opAns, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
        rcases hss with rfl | rfl
        · exact hUy _ hy
        · exact hUa _
      · simp only [opAns, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
        rcases hss with rfl | rfl
        · exact absurd (List.mem_singleton.1 hq) hqp
        · obtain rfl := List.mem_singleton.1 hq
          exact answer_clean hI hy hyc ho hyv
    refine ⟨m', .other hfe (fun _ h => by cases h) (fun _ h => by cases h) hseq, hI', hS', ?_, ?_⟩
    · rw [hnow, hma]; rfl
    · rw [hsent, hma]

theorem roundA {G : Outcome Nat → Prop} {A : Outcome Nat} (hA : Adv G A)
    {n0 : NetworkState Nat p0} (t : Time) :
    ∀ (pending : List (Op Nat)), (∀ op ∈ pending, op.HonestFeasible n0) →
    ∀ m : NetworkState Nat p0, InvA A m → (SafeA G (m.chain.statusOf c0) ∨ Answerable G A m) →
      m.sent = n0.sent → (∀ r ∈ n0.received, r ∈ m.received) →
      ∃ m', T1.RoundSeq appsS t pending m m' ∧ InvA A m' ∧ SafeA G (m'.chain.statusOf c0) ∧
        m'.chain.now = m.chain.now + 1 ∧ m'.sent = m.sent := by
  intro pending
  induction pending with
  | nil => intro _ m hI hS _ _; exact closeA hA hI hS t
  | cons op rest ih =>
    intro hfeas m hI hS hsent hrecv
    have hop := hfeas op List.mem_cons_self
    have hH : ∀ ss ∈ op.proofStates, m.Holds ss := fun ss hss =>
      holds_mono hsent.symm hrecv (hop.mem ss hss)
    obtain ⟨hI1, hS1⟩ := landA hA hI hop.not_tick hH hS
    obtain ⟨m', hseq, hI', hS', hnow, hs'⟩ := ih (fun o ho => hfeas o (List.mem_cons_of_mem _ ho))
      _ hI1 hS1 (by rw [NetworkState.applyAdv_sent]; exact hsent)
      (fun r hr => (NetworkState.applyAdv_sent_received appsS m (.land op)).2 r (hrecv r hr))
    refine ⟨m', .land (l1 := []) (l2 := rest) rfl hseq, hI', hS', ?_, ?_⟩
    · rw [hnow, landed_now hop.not_tick]
    · rw [hs', NetworkState.applyAdv_sent]

/-- A move of `p0` keeps `InvA`: a reaction adds sends that satisfy
    `HonestSend` against the record `n0.sent = n.sent`, so `p0` signs one
    outcome per channel and turn. -/
theorem InvA.applyHonest {G : Outcome Nat → Prop} {A : Outcome Nat} {n n0 : NetworkState Nat p0}
    (hI : InvA A n) (hS : SafeA G (n.chain.statusOf c0)) {m : HonestMove Nat} (hm : m.Feasible appsS n0)
    (hsent : n.sent = n0.sent) :
    InvA A (n.applyHonest m) ∧ SafeA G ((n.applyHonest m).chain.statusOf c0) := by
  cases m with
  | react r =>
    obtain ⟨y, hy, hys⟩ := hI.sent1
    have key : ∀ s ∈ r.sends.map (fun st => (⟨st, [p0]⟩ : SignedState Nat)),
        ∀ s' ∈ r.sends.map (fun st => (⟨st, [p0]⟩ : SignedState Nat)) ++ n.sent,
        s'.state.channel = s.state.channel → s'.state.turnNum = s.state.turnNum →
        s'.state.outcome = s.state.outcome := by
      intro s hs s' hs' hc ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
      refine (hm.2 x hx).outcome_eq _ (by rw [← hsent]; exact hs') hc ?_
      unfold State.signSlot
      rw [hc, ht]
    refine ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).mono (fun z hz => List.mem_append_right _ hz),
      ⟨y, List.mem_append_right _ hy, hys⟩, hI.recvSig, fun s hs s' hs' hc ht => ?_⟩, hS⟩
    by_cases hsL : s ∈ r.sends.map (fun st => (⟨st, [p0]⟩ : SignedState Nat))
    · exact (key s hsL s' hs' hc.symm ht.symm).symm
    · by_cases hs'L : s' ∈ r.sends.map (fun st => (⟨st, [p0]⟩ : SignedState Nat))
      · exact key s' hs'L s hs hc ht
      · exact hI.sentNC s ((List.mem_append.1 hs).resolve_left hsL) s'
          ((List.mem_append.1 hs').resolve_left hs'L) hc ht
  | wait dt =>
    exact ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).of_sent rfl, hI.sent1, hI.recvSig, hI.sentNC⟩,
      by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; exact hS⟩

/-- From a state with `InvA` and a safe status, `p0` has no strategy that
    finalizes `c0` with an outcome in `G`. -/
theorem not_finalizable_from (G : Outcome Nat → Prop) (A : Outcome Nat) (hA : Adv G A)
    (n : NetworkState Nat p0) (hI : InvA A n) (hS : SafeA G (n.chain.statusOf c0)) :
    ¬ UnbeatableIn appsS T1 (fun _ => True) (fun n => ∃ Ω, n.Finalized c0 Ω ∧ G Ω) n := by
  intro hU
  induction hU with
  | done hG =>
    obtain ⟨Ω, hf, hg⟩ := hG
    exact safeA_not_finalized hS hg hf
  | @move n m _ hfeas _ ih =>
    have hcalls : ∀ op ∈ m.calls, op.HonestFeasible n := by
      cases m with
      | react r => exact hfeas.1
      | wait dt => intro op hop; simp [HonestMove.calls] at hop
    obtain ⟨n', hseq, hI', hS', hnow, hsent'⟩ :=
      roundA hA n.chain.now m.calls hcalls n hI (Or.inl hS) rfl (fun _ hr => hr)
    obtain ⟨hI'', hS''⟩ := hI'.applyHonest hS' hfeas hsent'
    exact ih n' (mkRound hseq hnow) hI'' hS''

theorem invA_net1 (A : Outcome Nat) : InvA A net1 := by
  refine ⟨fun x hx _ => ?_, fun x hx => ?_, ⟨s1, List.mem_singleton_self _, rfl⟩, fun x hx _ => ?_,
    fun s hs s' hs' _ _ => ?_⟩
  · rw [List.mem_singleton.1 hx]; exact Or.inl rfl
  · rw [List.mem_singleton.1 hx]; exact unforged_r0 _
  · rw [List.mem_singleton.1 hx]; exact Or.inl (List.mem_singleton_self _)
  · rw [List.mem_singleton.1 hs, List.mem_singleton.1 hs']

/-- The adversary's answer to the target `Ω` is a valid move from every
    state of `p0` with the outcome `Ω` that a support of the play can carry:
    it keeps every amount and changes the tag. A state whose outcome is no
    three-slot allocation is no valid move. -/
theorem adv_target (Ω : Outcome Nat) : Adv (· = Ω) (ansQ Ω) := by
  refine ⟨ansQ_ne Ω, fun y hyc hyo hyΩ hy => ?_⟩
  cases hd : decode Ω with
  | none =>
    exfalso
    rcases hy with ⟨m0, -, hv⟩ | rfl
    · obtain ⟨_, _, a', b', -, hd', -⟩ := (vtS_iff _ _).1 hv
      rw [hyΩ, hd] at hd'; cases hd'
    · rw [← hyΩ] at hd; cases hd
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hans : ansQ Ω = pay a (b + 1) := by unfold ansQ; rw [hd]
    refine (vtS_iff _ _).2 ⟨a, b, a, b + 1, by rw [hyΩ]; exact hd, ?_, rfl⟩
    rw [hans]; rfl

theorem not_finalizable (Ω : Outcome Nat) : ¬ Finalizable appsS T1 c0 Ω net1 := fun h =>
  not_finalizable_from (· = Ω) (ansQ Ω) (adv_target Ω) net1 (invA_net1 _) (Or.inl ⟨0, rfl⟩)
    (UnbeatableIn.imp (fun hf => ⟨Ω, hf, rfl⟩) h)

/-! ## Every outcome but `O1` is prevented

`p0` answers a challenge with the outcome `X ≠ O1` at turn `t`: it signs
`ansP t`, its own move at turn `t + 1` with the outcome `O1`, and then
checkpoints with it. `X` is a move of `q0` from `O1`, so it keeps every
amount, and `ansP t` is a valid move of `p0` from it (`ansP_valid`). A
challenge has the deadline `now + 3 * ε`, and the answer takes at most three
rounds from the round in which the challenge lands. -/

def ansP (t : Nat) : State Nat := st (t + 1) O1

/-- `p0`'s move with `O1` is valid after a move of `q0` from `O1`: `q0`
    kept every amount, and `p0` restores the tag 0. -/
theorem ansP_valid {y m0 : State Nat} (hm0 : m0.outcome = O1) (hv : vtS m0 y = true) :
    vtS y (ansP y.turnNum) = true := by
  obtain ⟨a, b, a', b', h0, h1, ha⟩ := (vtS_iff _ _).1 hv
  rw [hm0] at h0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h0)
  exact (vtS_iff _ _).2 ⟨a', b', 5, 0, h1, rfl, ha.symm⟩

/-- What `p0` holds of a challenge with the outcome `X` at turn `t`. -/
def XInfo (n : NetworkState Nat p0) (t : Nat) (ch : Challenge Nat) : Prop :=
  ch.state.turnNum = t ∧ t % 2 = 0 ∧ 2 ≤ t ∧ ch.state.isFinal = false ∧ ch.state.channel = c0 ∧
    vtS ch.state (ansP t) = true ∧ (∃ x ∈ n.received, x.state = ch.state ∧ q0 ∈ x.signers) ∧
    n.HoldsSupportAt appsS c0 t

/-- Every state of `c0` that `p0` signs: the outcome `O1`, non-final, at an
    odd turn. -/
def SentOK (n : NetworkState Nat p0) : Prop :=
  ∀ s ∈ n.sent, s.state.channel = c0 →
    s.state.outcome = O1 ∧ s.state.isFinal = false ∧ s.state.turnNum % 2 = 1 ∧
      s.state = st s.state.turnNum O1

/-- A support of `c0` with unforged states and an outcome other than `O1`:
    its candidate is a non-final move of `q0` from `O1` at an even turn from 2
    on. -/
theorem candX {n : NetworkState Nat p0} (hS : SentOK n) {P : SupportProof Nat}
    {cand : State Nat} (h : (appsS c0.appDef).supports c0 P cand = true)
    (hU : ∀ ss ∈ P, n.Unforged ss) (hne : cand.outcome ≠ O1) :
    cand.turnNum % 2 = 0 ∧ 2 ≤ cand.turnNum ∧ cand.isFinal = false ∧ cand.channel = c0 ∧
      vtS cand (ansP cand.turnNum) = true ∧ ∃ m1 ∈ P, m1.state = cand ∧ q0 ∈ m1.signers := by
  obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht, hmv0, hmv1, hfin, hvt⟩⟩ := fm2 h
  subst hlast
  have hU0 := hU m0 (by simp)
  have hU1 := hU m1 (by simp)
  rcases Nat.mod_two_eq_zero_or_one m1.state.turnNum with he | ho
  · have ho0 : m0.state.turnNum % 2 = 1 := by omega
    obtain ⟨s, hs, hss⟩ := hU0.1 (byMover_odd hc0 hmv0 ho0)
    have hm0 := (hS s hs (by rw [hss]; exact hc0)).1
    rw [hss] at hm0
    have hf : m1.state.isFinal = false := by
      cases hf : m1.state.isFinal with
      | false => rfl
      | true => exact absurd ((hfin hf).trans hm0) hne
    exact ⟨he, by omega, hf, hc1, ansP_valid hm0 (hvt hf), m1, by simp, rfl,
      byMover_even hc1 hmv1 he⟩
  · obtain ⟨s, hs, hss⟩ := hU1.1 (byMover_odd hc1 hmv1 ho)
    have := (hS s hs (by rw [hss]; exact hc1)).1
    rw [hss] at this
    exact absurd this hne

theorem no_conclusion {n : NetworkState Nat p0} (hS : SentOK n) {ss : SignedState Nat}
    (hU : n.Unforged ss) (hcp : ConclusionProof c0 ss) : False := by
  obtain ⟨s, hs, hss⟩ := hU.1 (conclusion_p0 hcp)
  have := (hS s hs (by rw [hss]; exact hcp.1)).2.1
  rw [hss, hcp.2.1] at this
  cases this

/-- The invariant at the start of each round of `p0`'s strategy. -/
structure InvX (X : Outcome Nat) (n : NetworkState Nat p0) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sentOK : SentOK n
  noFin : ∀ t f o, n.chain.statusOf c0 = .finalized t f o → f ≠ X
  timing : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome = X →
    XInfo n t ch ∧ n.chain.now + 2 ≤ ch.deadline ∧
      ((¬ ∃ s ∈ n.sent, s.state = ansP t) → n.chain.now + 4 ≤ ch.deadline)

/-- The invariant inside a round that starts at `n0`; the turn record stays
    at least `R`. -/
structure KX (X : Outcome Nat) (n0 : NetworkState Nat p0) (R : Nat) (n : NetworkState Nat p0) :
    Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = n0.sent
  recv : ∀ r ∈ n0.received, r ∈ n.received
  now0 : n0.chain.now ≤ n.chain.now
  noFin : ∀ t f o, n.chain.statusOf c0 = .finalized t f o → f ≠ X
  chX : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome = X →
    XInfo n t ch ∧ (n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ n0.chain.now + 6 ≤ ch.deadline)
  left : ∀ t0 ch0, n0.chain.statusOf c0 = .challenged t0 ch0 → ch0.state.outcome = X →
    n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ t0 < (n.chain.statusOf c0).turnNumRecord
  recR : R ≤ (n.chain.statusOf c0).turnNumRecord

theorem KX.start {X : Outcome Nat} {n0 : NetworkState Nat p0} (hI : InvX X n0) :
    KX X n0 (n0.chain.statusOf c0).turnNumRecord n0 :=
  ⟨hI.recvU, rfl, fun _ h => h, le_refl _, hI.noFin,
    fun t ch h hx => ⟨(hI.timing t ch h hx).1, Or.inl rfl⟩, fun _ _ _ _ => Or.inl rfl, le_refl _⟩

theorem XInfo.mono {n n' : NetworkState Nat p0} {t : Nat} {ch : Challenge Nat}
    (h : XInfo n t ch) (hs : ∀ s ∈ n.sent, s ∈ n'.sent) (hr : ∀ r ∈ n.received, r ∈ n'.received) :
    XInfo n' t ch := by
  obtain ⟨h1, h2, h3, h4, h5, h6, ⟨x, hx, hxs, hxq⟩, P, cd, hH, hsP, hcd, hk⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨x, hr x hx, hxs, hxq⟩, P, cd, fun ss h => (hH ss h).of_subset hs hr, hsP, hcd, hk⟩

theorem apply_now_le {s s' : Adjudicator Nat} {caller : Participant} {op : Op Nat}
    (h : s.apply appsS caller op = some s') : s.now ≤ s'.now := by
  by_cases ht : ∃ dt, op = .tick dt
  · obtain ⟨dt, rfl⟩ := ht
    simp only [Adjudicator.apply_tick, Option.some.injEq] at h
    subst h
    exact Nat.le_add_right _ _
  · exact le_of_eq (Adjudicator.apply_now_eq_of_not_tick (fun dt h => ht ⟨dt, h⟩) h).symm

/-- One successful operation with unforged proof states keeps `KX`, inside
    a round whose clock stays below `n0`'s clock plus 2. A payout needs a
    final status, and no challenge with `X` expires inside the round. -/
theorem stepK {X : Outcome Nat} (hX : X ≠ O1) {n0 n : NetworkState Nat p0} {R : Nat}
    (hI0 : InvX X n0) (hK : KX X n0 R n) (hnow : n.chain.now < n0.chain.now + 2)
    {caller : Participant} {op : Op Nat} {s' : Adjudicator Nat}
    (h : n.chain.apply appsS caller op = some s') (hU : ∀ ss ∈ op.proofStates, n.Unforged ss)
    (hs'now : n.chain.now ≤ s'.now) :
    KX X n0 R { n with chain := s', received := op.proofStates ++ n.received } := by
  have hSn : SentOK n := by
    intro s hs hc; rw [hK.sent] at hs; exact hI0.sentOK s hs hc
  have hrec : ∀ r ∈ n.received, r ∈ op.proofStates ++ n.received :=
    fun r hr => List.mem_append_right _ hr
  have hRecU : ∀ r ∈ op.proofStates ++ n.received,
      ({ n with chain := s', received := op.proofStates ++ n.received } : NetworkState Nat p0).Unforged r := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact (hU r hr).of_sent rfl
    · exact (hK.recvU r hr).of_sent rfl
  -- a challenge with `X` at `n` has not expired
  have hliveX : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome = X →
      n.chain.now < ch.deadline := by
    intro t ch hc hx
    rcases (hK.chX t ch hc hx).2 with h0 | h6
    · rw [h0] at hc
      exact lt_of_lt_of_le hnow (hI0.timing t ch hc hx).2.1
    · exact lt_of_lt_of_le hnow (le_trans (Nat.add_le_add_left (by decide) _) h6)
  rcases status_cases h with heq | ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩ |
      ⟨P, cand, rfl, -, -, hlt, hst⟩ | ⟨ss, rfl, hcp⟩ | ⟨o0, o', hfo, hst⟩
  · refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => by rw [heq]; exact hK.noFin t f o, fun t ch hc hx => ?_, fun t0 ch0 h0 hx => ?_,
      by rw [heq]; exact hK.recR⟩
    · rw [heq] at hc
      obtain ⟨hinfo, hor⟩ := hK.chX t ch hc hx
      exact ⟨hinfo.mono (fun _ h => h) hrec, by rw [heq]; exact hor⟩
    · rw [heq]; exact hK.left t0 ch0 h0 hx
  · have hge : (n.chain.statusOf c0).turnNumRecord ≤ cand.turnNum := by
      rcases hmode with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · exact le_of_lt h
    refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => (by rw [hst]; intro h; cases h), fun t ch hc hx => ?_,
      fun t0 ch0 h0 hx => ?_, ?_⟩
    · rw [hst] at hc
      obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hc
      obtain ⟨he, h2, hnf, hch, hvt, m1, hm1, hm1s, hm1q⟩ := candX hSn hsup hU
        (fun h => hX (hx.symm.trans h))
      refine ⟨⟨rfl, he, h2, hnf, hch, hvt, ⟨m1, List.mem_append_left _ hm1, hm1s, hm1q⟩,
        P, _, fun ss hss => holds_of_mem_received (List.mem_append_left _ hss), hsup, hcc, rfl⟩,
        Or.inr (Nat.add_le_add_right hK.now0 6)⟩
    · right
      rw [hst]
      show t0 < cand.turnNum
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0
      · rw [Adjudicator.mode_eq, hs0, h0] at hmode
        rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
        · simp only [ChannelStatus.mode] at hm
          split at hm <;> cases hm
        · simpa using hr
      · exact lt_of_lt_of_le hlt0 hge
    · rw [hst]; exact le_trans hK.recR hge
  · refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => (by rw [hst]; intro h; cases h),
      fun t ch hc _ => (by rw [hst] at hc; cases hc), fun t0 ch0 h0 hx => ?_, ?_⟩
    · right
      rw [hst]
      show t0 < cand.turnNum
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0
      · rw [hs0, h0] at hlt; simpa using hlt
      · exact lt_trans hlt0 hlt
    · rw [hst]; exact le_trans hK.recR (le_of_lt hlt)
  · exact (no_conclusion hSn (hU ss (List.mem_singleton_self ss)) hcp).elim
  · -- a payout: the status was final; the turn record and the finalized
    -- outcome stay
    have hrec' : (s'.statusOf c0).turnNumRecord = (n.chain.statusOf c0).turnNumRecord := by
      rw [hst]; cases n.chain.statusOf c0 <;> rfl
    have hfin' : ∀ t f o, s'.statusOf c0 = .finalized t f o → f ≠ X := by
      intro t f o hf
      rw [hst] at hf
      cases hs : n.chain.statusOf c0 with
      | «open» r =>
        rw [hs, ChannelStatus.finalOutcome_open] at hfo; cases hfo
      | challenged r ch =>
        rw [hs, ChannelStatus.withOutcome_challenged] at hf
        obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hf
        intro hx
        have hlive := hliveX r ch hs hx
        rw [hs, ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hlive)] at hfo
        cases hfo
      | finalized r f' o'' =>
        rw [hs, ChannelStatus.withOutcome_finalized] at hf
        obtain ⟨-, hff, -⟩ := ChannelStatus.finalized.inj hf
        rw [← hff]; exact hK.noFin r f' o'' hs
    refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now, hfin',
      fun t ch hc _ => ?_, fun t0 ch0 h0 hx => ?_, by rw [hrec']; exact hK.recR⟩
    · rw [hst] at hc
      cases hs : n.chain.statusOf c0 <;> rw [hs] at hc <;> cases hc
    · right
      rw [hrec']
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0
      · have hlive := hliveX t0 ch0 (hs0.trans h0) hx
        rw [hs0, h0, ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hlive)] at hfo
        cases hfo
      · exact hlt0

/-- `KX` as a step invariant of a sub-round of pure adversary play that ends
    before `n0`'s clock plus 2. -/
theorem KX.stepInv {X : Outcome Nat} (hX : X ≠ O1) {n0 : NetworkState Nat p0} {R : Nat}
    (hI0 : InvX X n0) {Eend : Time} (hE : Eend < n0.chain.now + 2) :
    T1.StepInvariant appsS (fun n => n.chain.now ≤ Eend) (KX X n0 R) (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {n ss} _ hfe hK => by
    rw [NetworkState.applyAdv_deliver]
    refine ⟨fun r hr => ?_, hK.sent, fun r hr => List.mem_cons_of_mem _ (hK.recv r hr), hK.now0,
      hK.noFin, fun t ch hc hx => ?_, hK.left, hK.recR⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hfe.1.of_sent rfl
      · exact (hK.recvU r hr).of_sent rfl
    · obtain ⟨hinfo, hor⟩ := hK.chX t ch hc hx
      exact ⟨hinfo.mono (fun _ h => h) (fun r hr => List.mem_cons_of_mem _ hr), hor⟩
  tick := fun {n dt} _ _ hK => by
    rw [NetworkState.applyAdv_tick]
    refine ⟨fun r hr => (hK.recvU r hr).of_sent rfl, hK.sent, hK.recv,
      le_trans hK.now0 (Nat.le_add_right _ _), fun t f o => ?_, fun t ch hc hx => ?_,
      fun t0 ch0 h0 hx => ?_, ?_⟩
    · rw [Adjudicator.tick_statusOf]; exact hK.noFin t f o
    · rw [Adjudicator.tick_statusOf] at hc ⊢
      exact hK.chX t ch hc hx
    · rw [Adjudicator.tick_statusOf]; exact hK.left t0 ch0 h0 hx
    · rw [Adjudicator.tick_statusOf]; exact hK.recR
  chain := fun {n caller op} hg hfe hK => by
    cases happ : n.chain.apply appsS caller op with
    | none => rw [NetworkState.applyAdv_chain_none appsS happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_chain_some appsS happ]
      exact stepK hX hI0 hK (lt_of_le_of_lt hg hE) happ hfe.1.2 (apply_now_le happ)

open Classical in
/-- `p0`'s move against `X`: answer a challenge with the outcome `X`, first by
    signing `ansP t`, then by a checkpoint with it. -/
noncomputable def idealX (X : Outcome Nat) (n : NetworkState Nat p0) : HonestMove Nat :=
  match n.chain.statusOf c0 with
  | .challenged t ch =>
    if ch.state.outcome = X then
      if h : (∃ s ∈ n.sent, s.state = ansP t) ∧
          (∃ x ∈ n.received, x.state = ch.state ∧ q0 ∈ x.signers) then
        .chain (.checkpoint c0 [Classical.choose h.2, ⟨ansP t, [p0]⟩] (ansP t))
      else .send (ansP t)
    else .wait 0
  | _ => .wait 0

open Classical in
/-- The strategy: `idealX` where it is feasible, a wait otherwise. -/
noncomputable def σX (X : Outcome Nat) : Strategy Nat p0 := fun n =>
  if (idealX X n).Feasible appsS n then idealX X n else .wait 0

theorem σX_feasible (X : Outcome Nat) (n : NetworkState Nat p0) : (σX X n).Feasible appsS n := by
  unfold σX
  split
  · assumption
  · trivial

/-- `p0`'s move `ansP t0` after `q0`'s challenge state `x` at `t0` is a
    support of `ansP t0`. -/
theorem supports_ansP {ch : Challenge Nat} {t0 : Nat} {x : SignedState Nat}
    (hxs : x.state = ch.state) (hxq : q0 ∈ x.signers) (hinfo : ch.state.turnNum = t0 ∧ t0 % 2 = 0 ∧
      ch.state.isFinal = false ∧ ch.state.channel = c0 ∧ vtS ch.state (ansP t0) = true) :
    (appsS c0.appDef).supports c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0) = true := by
  obtain ⟨ht, he, hf, hc, hv⟩ := hinfo
  have hxc : x.state.channel = c0 := by rw [hxs]; exact hc
  have hb1 : x.byMover = true := (SignedState.byMover_iff _).2
    ⟨q0, by rw [mover_c0 hxc, if_pos (by rw [hxs, ht]; exact he)], hxq⟩
  have hm2 : (ansP t0).mover = some p0 := by
    rw [mover_c0 rfl, if_neg (by simp only [ansP, st]; omega)]
  have hb2 : (⟨ansP t0, [p0]⟩ : SignedState Nat).byMover = true := by
    simp [SignedState.byMover, hm2]
  have hv' : vtS x.state (ansP t0) = true := by rw [hxs]; exact hv
  simp only [appsS, forceMoveRules, validRun, validMove, hb2, hv']
  simp [hxs, hc, hf, ht, ansP, st, c0, FixedPart.n, hb1]

/-- `p0` may sign `ansP t`: every state it signed carries `O1` (`SentOK`), so
    the send commits no own-violation of kind (a) (`HonestSend.noConflict`),
    and `p0` moves by the rules from the challenge state at turn `t`, whose
    support it holds (`HonestSend.movesFrom`). -/
theorem send_ansP_feasible {n : NetworkState Nat p0} {t : Nat} {ch : Challenge Nat}
    (hS : SentOK n) (hinfo : XInfo n t ch) : (HonestMove.send (ansP t)).Feasible appsS n := by
  obtain ⟨ht, he, -, hf, hc, hv, ⟨x, hx, hxs, hxq⟩, hsup⟩ := hinfo
  refine (HonestMove.Feasible_send appsS n (ansP t)).mpr
    ⟨fun ⟨s, hs, hc, _, hne⟩ => ?_, ?_, ?_, fun _ => ⟨hsup, [x, ⟨ansP t, [p0]⟩], fun ss hss => ?_,
      supports_ansP hxs hxq ⟨ht, he, hf, hc, hv⟩⟩, fun ⟨s, hs, hc, htn, hne⟩ => ?_, fun ⟨s, hs, hc, hfb⟩ => ?_⟩
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact hne rfl
    · exact hne (hS s hs hc).1
  · show O1.entries.GuaranteesExternal
    decide
  · exact HonestSend.fundsCommitted_of_fundable (by show ∀ e ∈ O1.entries, _; decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact .inl (holds_of_mem_received hx)
    · exact .inr rfl
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact hne rfl
    · exact hne (by rw [(hS s hs hc).2.2.2, htn]; rfl)
  · rcases List.mem_cons.1 hs with rfl | hs
    · rcases hfb with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> rw [h1] at h2 <;> cases h2
    · have hnf := (hS s hs hc).2.1
      rcases hfb with ⟨h1, -, -⟩ | ⟨h1, -, -⟩
      · rw [hnf] at h1; cases h1
      · exact absurd h1 (by simp [ansP, st])

theorem holds_ansP {n : NetworkState Nat p0} {t : Nat} (h : ∃ s ∈ n.sent, s.state = ansP t) :
    n.Holds ⟨ansP t, [p0]⟩ := by
  obtain ⟨s, hs, hss⟩ := h
  exact ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s, hs, hss⟩,
    fun v hv => by simp [ansP, st, State.voucher?] at hv⟩

/-- The three shapes of `σX X n`. -/
theorem σX_cases {X : Outcome Nat} {n : NetworkState Nat p0} (hI : InvX X n) :
    (σX X n = .wait 0 ∧ ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome ≠ X) ∨
    (∃ t ch, n.chain.statusOf c0 = .challenged t ch ∧ ch.state.outcome = X ∧
      (¬ ∃ s ∈ n.sent, s.state = ansP t) ∧ σX X n = .send (ansP t)) ∨
    (∃ t ch x, n.chain.statusOf c0 = .challenged t ch ∧ ch.state.outcome = X ∧
      (∃ s ∈ n.sent, s.state = ansP t) ∧ x ∈ n.received ∧ x.state = ch.state ∧ q0 ∈ x.signers ∧
      σX X n = .chain (.checkpoint c0 [x, ⟨ansP t, [p0]⟩] (ansP t))) := by
  have hwait : idealX X n = .wait 0 → σX X n = .wait 0 := fun h => by
    unfold σX; rw [h]; exact ite_self _
  cases hs : n.chain.statusOf c0 with
  | «open» t =>
    exact Or.inl ⟨hwait (by unfold idealX; rw [hs]), fun t ch h => by cases h⟩
  | finalized t f o =>
    exact Or.inl ⟨hwait (by unfold idealX; rw [hs]), fun t ch h => by cases h⟩
  | challenged t ch =>
    by_cases hx : ch.state.outcome = X
    · have hinfo := (hI.timing t ch hs hx).1
      by_cases hd : (∃ s ∈ n.sent, s.state = ansP t) ∧
          (∃ x ∈ n.received, x.state = ch.state ∧ q0 ∈ x.signers)
      · right; right
        obtain ⟨hx1, hx2, hx3⟩ := Classical.choose_spec hd.2
        refine ⟨t, ch, Classical.choose hd.2, rfl, hx, hd.1, hx1, hx2, hx3, ?_⟩
        have hid : idealX X n = .chain (.checkpoint c0 [Classical.choose hd.2, ⟨ansP t, [p0]⟩] (ansP t)) := by
          unfold idealX; rw [hs]; simp only [if_pos hx, dif_pos hd]
        unfold σX
        rw [hid, if_pos]
        refine (HonestMove.Feasible_chain _ _ _).2 fun ss hss => ?_
        simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
        rcases hss with rfl | rfl
        · exact holds_of_mem_received hx1
        · exact holds_ansP hd.1
      · right; left
        have hns : ¬ ∃ s ∈ n.sent, s.state = ansP t := fun h =>
          hd ⟨h, hinfo.2.2.2.2.2.2.1⟩
        refine ⟨t, ch, rfl, hx, hns, ?_⟩
        have hid : idealX X n = .send (ansP t) := by
          unfold idealX; rw [hs]; simp only [if_pos hx, dif_neg hd]
        unfold σX
        rw [hid, if_pos (send_ansP_feasible hI.sentOK hinfo)]
    · exact Or.inl ⟨hwait (by unfold idealX; rw [hs]; simp only [if_neg hx]),
        fun t' ch' h => by cases h; exact hx⟩

/-- At the end of a round from `n0`, before `n0`'s clock plus 2, `X` is not
    finalized. -/
theorem notFinX {X : Outcome Nat} {n0 n : NetworkState Nat p0} {R : Nat} (hI0 : InvX X n0)
    (hK : KX X n0 R n) (hnow : n.chain.now < n0.chain.now + 2) : ¬ n.Finalized c0 X := by
  intro hf
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf
  cases hs : n.chain.statusOf c0 with
  | «open» t => rw [hs] at hf; simp at hf
  | finalized t f o =>
    rw [hs, ChannelStatus.finalizedWith_finalized] at hf
    exact hK.noFin t f o hs (Option.some.inj hf)
  | challenged t ch =>
    rw [hs] at hf
    simp only [ChannelStatus.finalizedWith_challenged] at hf
    split at hf
    · rename_i hd
      have hx : ch.state.outcome = X := Option.some.inj hf
      rcases (hK.chX t ch hs hx).2 with h0 | h6
      · rw [hs] at h0
        have := (hI0.timing t ch h0.symm hx).2.1
        exact absurd hd (not_le.mpr (lt_of_lt_of_le hnow this))
      · exact absurd hd (not_le.mpr (lt_of_lt_of_le hnow (le_trans (Nat.add_le_add_left (by decide) _) h6)))
    · cases hf

theorem bound6 {a b : Nat} (h : a < b + 2) : a + 4 ≤ b + 6 := by omega
theorem bound4 {a b : Nat} (h : a < b + 2) : a + 2 ≤ b + 4 := by omega

/-- `KX` over a sub-round of pure adversary play. -/
theorem KX.nil {X : Outcome Nat} (hX : X ≠ O1) {n0 n n' : NetworkState Nat p0} {R : Nat}
    {t : Time} (hI0 : InvX X n0) (hseq : T1.RoundSeq appsS t [] n n') (hK : KX X n0 R n)
    (hE : n'.chain.now < n0.chain.now + 2) : KX X n0 R n' :=
  Threat.RoundSeq.nil_invariant hseq (KX.stepInv hX hI0 hE) hK

theorem KX.lower {X : Outcome Nat} {n0 n : NetworkState Nat p0} {R R' : Nat}
    (hK : KX X n0 R n) (hR : R' ≤ (n.chain.statusOf c0).turnNumRecord) : KX X n0 R' n :=
  ⟨hK.recvU, hK.sent, hK.recv, hK.now0, hK.noFin, hK.chX, hK.left, hR⟩

/-- The answer of `p0`: its checkpoint with `ansP t0` turns a standing
    challenge at `t0` into an open status at `t0 + 1`. -/
theorem checkpoint_apply {s : Adjudicator Nat} {t0 : Nat} {ch : Challenge Nat}
    {x : SignedState Nat} (hs : s.statusOf c0 = .challenged t0 ch) (hd : s.now < ch.deadline)
    (hxs : x.state = ch.state) (hxq : q0 ∈ x.signers) (hinfo : ch.state.turnNum = t0 ∧ t0 % 2 = 0 ∧
      ch.state.isFinal = false ∧ ch.state.channel = c0 ∧ vtS ch.state (ansP t0) = true) :
    s.apply appsS p0 (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)) =
      some (s.setStatus c0 (.open (t0 + 1))) := by
  have hsup := supports_ansP hxs hxq hinfo
  show s.checkpoint appsS c0 _ _ = _
  unfold Adjudicator.checkpoint
  have hopen : (s.statusOf c0).IsOpen s.now := by
    rw [hs]
    simp only [ChannelStatus.IsOpen, ChannelStatus.mode, if_neg (not_le.mpr hd)]
    decide
  rw [if_pos ⟨hopen, hsup, rfl, by rw [hs]; simp [ansP, st]⟩]
  rfl

/-- One round of `σX`: `X` is not finalized at its end, and `InvX` holds at
    the start of the next round. -/
theorem roundX {X : Outcome Nat} (hX : X ≠ O1) {n0 n' : NetworkState Nat p0} (hI0 : InvX X n0)
    (hround : T1.Round appsS (σX X n0) n0 n') :
    ¬ n'.Finalized c0 X ∧ InvX X (n'.applyHonest (σX X n0)) := by
  have hbound := round_bound hround
  have hK0 := KX.start (X := X) hI0
  -- the start of the next round, from `KX` at the end and a fact about a
  -- standing challenge
  have hnext : ∀ {R : Nat} (hK : KX X n0 R n') (m : HonestMove Nat)
      (hsent : ∀ s ∈ (n'.applyHonest m).sent, s ∈ n'.sent ∨ ∃ t0 ch0,
        n0.chain.statusOf c0 = .challenged t0 ch0 ∧ ch0.state.outcome = X ∧ s = ⟨ansP t0, [p0]⟩)
      (hrecv : (n'.applyHonest m).received = n'.received)
      (hchain : (n'.applyHonest m).chain.statusOf c0 = n'.chain.statusOf c0 ∧
        (n'.applyHonest m).chain.now = n'.chain.now)
      (hS0 : ∀ t ch, n'.chain.statusOf c0 = .challenged t ch → ch.state.outcome = X →
        n'.chain.statusOf c0 = n0.chain.statusOf c0 →
        (n'.applyHonest m).chain.now + 2 ≤ ch.deadline ∧
          ((¬ ∃ s ∈ (n'.applyHonest m).sent, s.state = ansP t) →
            (n'.applyHonest m).chain.now + 4 ≤ ch.deadline)),
      InvX X (n'.applyHonest m) := by
    intro R hK m hsent hrecv hchain hS0
    have hsub : ∀ s ∈ n'.sent, s ∈ (n'.applyHonest m).sent := by
      cases m with
      | react r => exact fun s hs => List.mem_append_right _ hs
      | wait dt => exact fun s hs => hs
    refine ⟨fun r hr => ?_, fun s hs hc => ?_, fun t f o => ?_, fun t ch hc hx => ?_⟩
    · rw [hrecv] at hr; exact (hK.recvU r hr).mono hsub
    · rcases hsent s hs with hs | ⟨t0, ch0, h0, hx0, rfl⟩
      · rw [hK.sent] at hs; exact hI0.sentOK s hs hc
      · have he := (hI0.timing t0 ch0 h0 hx0).1.2.1
        exact ⟨rfl, rfl, by simp only [ansP, st]; omega, rfl⟩
    · rw [hchain.1]; exact hK.noFin t f o
    · rw [hchain.1] at hc
      obtain ⟨hinfo, hor⟩ := hK.chX t ch hc hx
      refine ⟨hinfo.mono hsub (fun r hr => by rw [hrecv]; exact hr), ?_⟩
      rcases hor with h0 | h6
      · exact hS0 t ch hc hx h0
      · rw [hchain.2]
        have : n'.chain.now + 4 ≤ ch.deadline := le_trans (bound6 hbound) h6
        exact ⟨le_trans (Nat.add_le_add_left (by decide) _) this, fun _ => this⟩
  rcases σX_cases hI0 with ⟨hσ, hnx⟩ | ⟨t0, ch0, hs0, hx0, hns, hσ⟩ |
      ⟨t0, ch0, x, hs0, hx0, hsa, hx, hxs, hxq, hσ⟩
  · -- wait: a sub-round of pure adversary play
    rw [hσ] at hround ⊢
    have hK := KX.nil hX hI0 hround.1 hK0 hbound
    refine ⟨notFinX hI0 hK hbound, hnext hK _ (fun s hs => .inl hs) rfl ⟨by
      simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf], by
      simp only [NetworkState.applyHonest, Adjudicator.tick_now]; rfl⟩ ?_⟩
    intro t ch hc hx h0
    rw [h0] at hc
    exact absurd hx (hnx t ch hc)
  · -- send `ansP t0`
    rw [hσ] at hround ⊢
    have hK := KX.nil hX hI0 hround.1 hK0 hbound
    refine ⟨notFinX hI0 hK hbound, hnext hK _ ?_ rfl ⟨rfl, rfl⟩ ?_⟩
    · intro s hs
      rw [NetworkState.applyHonest_send] at hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact .inr ⟨t0, ch0, hs0, hx0, rfl⟩
      · exact .inl hs
    · intro t ch hc hx h0
      rw [h0, hs0] at hc
      obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hc
      have h4 := (hI0.timing _ _ hs0 hx0).2.2 hns
      rw [NetworkState.applyHonest_send]
      refine ⟨le_trans (bound4 hbound) h4, fun hn => ?_⟩
      exact absurd ⟨_, List.mem_cons_self, rfl⟩ hn
  · -- checkpoint with `ansP t0`
    rw [hσ] at hround ⊢
    rw [NetworkState.applyHonest_chain]
    obtain ⟨n1, hA, hB⟩ := Threat.Round.single hround
    have hnow1 : n1.chain.now ≤ n'.chain.now :=
      le_trans (NetworkState.applyAdv_now_le appsS n1 _) hB.now_le
    have hK1 := KX.nil hX hI0 hA hK0 (lt_of_le_of_lt hnow1 hbound)
    have hinfo0 := (hI0.timing _ _ hs0 hx0)
    -- the land of the checkpoint
    have hKL : KX X n0 (t0 + 1) (n1.applyAdv appsS (.land (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)))) := by
      have hU : ∀ ss ∈ (Op.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)).proofStates, n1.Unforged ss := by
        intro ss hss
        simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
        rcases hss with rfl | rfl
        · exact hK1.recvU ss (hK1.recv ss hx)
        · obtain ⟨s, hs, hss⟩ := hsa
          exact ⟨fun _ => ⟨s, by rw [hK1.sent]; exact hs, hss⟩,
            fun v hv => by simp [ansP, st, State.voucher?] at hv⟩
      rcases hK1.left t0 ch0 hs0 hx0 with heq | hlt
      · have happ := checkpoint_apply (s := n1.chain) (by rw [heq, hs0])
          (lt_of_lt_of_le (lt_of_le_of_lt hnow1 hbound) hinfo0.2.1) hxs hxq
          ⟨hinfo0.1.1, hinfo0.1.2.1, hinfo0.1.2.2.2.1, hinfo0.1.2.2.2.2.1, hinfo0.1.2.2.2.2.2.1⟩
        rw [NetworkState.applyAdv_land_some appsS happ]
        exact (stepK hX hI0 hK1 (lt_of_le_of_lt hnow1 hbound) happ hU (le_of_eq rfl)).lower
          (by simp)
      · have hK1' := hK1.lower hlt
        cases happ : n1.chain.apply appsS p0 (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)) with
        | none =>
          rw [NetworkState.applyAdv_land_none appsS happ]
          exact hK1'
        | some s' =>
          rw [NetworkState.applyAdv_land_some appsS happ]
          exact stepK hX hI0 hK1' (lt_of_le_of_lt hnow1 hbound) happ hU (apply_now_le happ)
    have hK := KX.nil hX hI0 hB hKL hbound
    refine ⟨notFinX hI0 hK hbound, ?_⟩
    have := hnext hK (HonestMove.chain (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)))
      (fun s hs => .inl (by rwa [NetworkState.applyHonest_chain] at hs))
      (by rw [NetworkState.applyHonest_chain]) (by rw [NetworkState.applyHonest_chain]; exact ⟨rfl, rfl⟩) ?_
    · rwa [NetworkState.applyHonest_chain] at this
    intro t ch hc hx h0
    have hr := hK.recR
    rw [h0, hs0] at hr
    simp only [ChannelStatus.turnNumRecord_challenged] at hr
    omega

theorem prevents_other (X : Outcome Nat) (hX : X ≠ O1) :
    Prevents appsS T1 (fun n => n.Finalized c0 X) net1 := by
  have hI1 : InvX X net1 := by
    refine ⟨fun x hx => ?_, fun s hs _ => ?_,
      fun t f o h => (by simp [net1, sF, s5, Adjudicator.genesis, Adjudicator.statusOf] at h),
      fun t ch h => (by simp [net1, sF, s5, Adjudicator.genesis, Adjudicator.statusOf] at h)⟩
    · rw [List.mem_singleton.1 hx]; exact unforged_r0 _
    · rw [List.mem_singleton.1 hs]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hrun : ∀ {n1}, Run appsS T1 (σX X) net1 n1 → InvX X n1 := by
    intro n1 h
    induction h with
    | refl => exact hI1
    | round _ hr ih => exact (roundX hX ih hr).2
  exact ⟨σX X, σX_feasible X, fun n1 n2 hr hround => (roundX hX (hrun hr) hround).1⟩

/-! ## The old forms fail; the app is not desirable

The app is IR (`appsS_IR`), IC (`appsS_IC`) and conserves every amount
(`amountConserving`, the conservation rule before go-nitro's form rule).
The adversary's answers are no own-violations of `q0` (`answer_clean`), so
the play is a play of `T0.noOwnViolation destS`. The answers change a
destination, so the app fails value conservation with go-nitro's form rule
(`appsS_not_conserving`) and is not desirable (`appsS_not_desirable`). -/

/-- A valid move keeps every amount. -/
theorem vtS_amounts {s s' : State Nat} (h : vtS s s' = true) (k : Nat) :
    share s'.outcome k = share s.outcome k := by
  obtain ⟨a, b, a', b', h0, h1, ha⟩ := (vtS_iff _ _).1 h
  rw [decode_eq_some.1 h0, decode_eq_some.1 h1, share_pay, share_pay, ha]

/-- `vtS` lowers no entry. -/
theorem noTake_vtS : NoTakeFromNonMover vtS destS := fun _ _ h q _ =>
  le_of_eq (vtS_amounts h (destS q)).symm

/-- The app is IR at every state, for the destination map `destS`. -/
theorem appsS_IR : AppIR appsS (tc0 : FixedPart).appDef destS :=
  TakeOut.forceMove_IR rfl noTake_vtS

/-- A valid move can be kept: the next state with the same outcome is valid. -/
theorem stay_vtS : ∀ s s', vtS s s' = true → vtS s' { s' with turnNum := s'.turnNum + 1 } = true := by
  intro s s' h
  obtain ⟨-, -, a', b', -, h1, -⟩ := (vtS_iff _ _).1 h
  exact (vtS_iff _ _).2 ⟨a', b', a', b', h1, h1, rfl⟩

/-- The app is IC at every state (`TakeOut.forceMove_IC`). -/
theorem appsS_IC : AppIC appsS (tc0 : FixedPart).appDef destS :=
  TakeOut.forceMove_IC stay_vtS _

/-- Amount conservation, the rule before go-nitro's form rule: a valid move
    keeps the total and lowers no amount except the mover's own. -/
def AmountConserving (vt : State Nat → State Nat → Bool) (dest : Participant → Nat) : Prop :=
  ∀ s s' q, vt s s' = true → s'.mover = some q →
    s'.outcome.entries.total = s.outcome.entries.total ∧
    ∀ k, share s'.outcome k < share s.outcome k → k = dest q

/-- `vtS` keeps the total and lowers no amount. -/
theorem amountConserving : AmountConserving vtS destS := by
  intro s s' q h _
  obtain ⟨a, b, a', b', h0, h1, ha⟩ := (vtS_iff _ _).1 h
  refine ⟨?_, fun k hk => absurd (vtS_amounts h k) (Nat.ne_of_lt hk)⟩
  rw [decode_eq_some.1 h0, decode_eq_some.1 h1, ha]
  rfl

/-- The app fails value conservation: the answer of `q0` changes the
    destination of the third entry ("Destinations may not change",
    `SingleAssetPayments.sol`). -/
theorem appsS_not_conserving : ¬ Conserving appsS (tc0 : FixedPart).appDef destS := by
  intro h
  have := h.conserve c0 [s1, ⟨st 2 (pay 5 1), [q0]⟩] (st 2 (pay 5 1)) rfl (by decide) 0 s1
    ⟨st 2 (pay 5 1), [q0]⟩ q0 rfl rfl (by decide)
  rcases this with heq | ⟨hd, -⟩
  · exact absurd heq (by decide)
  · exact absurd hd (by decide)

theorem appsS_not_desirable : ¬ Desirable appsS (tc0 : FixedPart).appDef destS :=
  fun h => appsS_not_conserving h.conserves

/-- The app does not have the go-nitro payment rules ("Destinations may not
    change"): those rules give a desirable app. -/
theorem appsS_not_paymentRules : ¬ PaymentRules vtS destS := fun h =>
  appsS_not_desirable (TakeOut.paymentRules_desirable h _)

/-- Nitro-24's first claim with IR, IC and amount conservation in place of
    `Desirable`, for a ForceMove app (the form of 2026-11-02 before
    go-nitro's form rule). -/
def Old_finalizable_or_two_enabled : Prop :=
  ∀ (apps : Apps Nat) {p : Participant} (T : Threat Nat p)
    (_A : Assumptions apps p T) (dest : Participant → Nat)
    (net : Nitro.ReachableParticipant apps (T.noOwnViolation dest))
    (c : TimedChannel T.ε) (vt : State Nat → State Nat → Bool)
    (_hvt : apps (c : FixedPart).appDef = forceMoveRules vt)
    (_hir : AppIR apps (c : FixedPart).appDef dest) (_hic : AppIC apps (c : FixedPart).appDef dest)
    (_hcons : AmountConserving vt dest)
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof candidate = true ∧
      candidate.channel = (c : FixedPart)),
    (∃ Ω, Finalizable apps (T.noOwnViolation dest) (c : FixedPart) Ω net.state) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω1 net.state ∧
      Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω2 net.state)

/-- Nitro-24's second claim in the same old form. -/
def Old_single_enabled_is_finalizable : Prop :=
  ∀ (apps : Apps Nat) {p : Participant} (T : Threat Nat p)
    (_A : Assumptions apps p T) (dest : Participant → Nat)
    (net : Nitro.ReachableParticipant apps (T.noOwnViolation dest))
    (c : TimedChannel T.ε) (vt : State Nat → State Nat → Bool)
    (_hvt : apps (c : FixedPart).appDef = forceMoveRules vt)
    (_hir : AppIR apps (c : FixedPart).appDef dest) (_hic : AppIC apps (c : FixedPart).appDef dest)
    (_hcons : AmountConserving vt dest)
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) →
      ∃ proof, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof t.state = true)
    (Ω : Outcome Nat) (_hΩ : Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω net.state)
    (_huniq : ∀ Ω', Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω' net.state → Ω' = Ω),
    Finalizable apps (T.noOwnViolation dest) (c : FixedPart) Ω net.state

theorem finalizable_or_two_enabled_false : ¬ Old_finalizable_or_two_enabled := by
  intro h
  rcases h appsS T0 A0 destS ⟨net1, net1_reachable⟩ tc0 vtS rfl appsS_IR appsS_IC
      amountConserving (by decide) ⟨[r0, s1], st 1 O1, holds_r0s1, supports_r0s1, rfl⟩ with
    ⟨Ω, hΩ⟩ | ⟨Ω1, Ω2, hne, hE1, hE2⟩
  · exact not_finalizable Ω hΩ
  · by_cases h1 : Ω1 = O1
    · exact hE2 (prevents_other Ω2 (fun h2 => hne (h1.trans h2.symm)))
    · exact hE1 (prevents_other Ω1 h1)

theorem single_enabled_is_finalizable_false : ¬ Old_single_enabled_is_finalizable := by
  intro h
  refine not_finalizable O1 (h appsS T0 A0 destS ⟨net1, net1_reachable⟩ tc0 vtS rfl appsS_IR
    appsS_IC amountConserving (by decide) (fun t ht _ => ?_) O1 enabled_O1 (fun Ω' hE => ?_))
  · rw [List.mem_singleton.1 ht]
    exact ⟨[r0, s1], holds_r0s1, supports_r0s1⟩
  · by_contra hne
    exact hE (prevents_other Ω' hne)

#print axioms appsS_not_desirable
#print axioms finalizable_or_two_enabled_false
#print axioms single_enabled_is_finalizable_false

end ArmadaLean.Nitro.CounterexampleTag
