/-
  Counterexample to the literal reading of Nitro:653-656 (`Enabled` against
  every strategy at once, `Literal_finalizable_or_two_enabled` below), with
  every honest rule of `HonestSend` (`noConflict`, `movesFrom`, `oneState`,
  `finalLast`), the premise `hpend`, and the adversary threat
  `T0.noOwnViolation destS`.

  The app is the consensus app (`consensusRules`, Nitro:660-688), desirable
  for every destination map (`TakeOut.consensus_desirable`). The channel `c0`
  has the participants `[q0, p0]` (`n = 2`), `ε = 2`, and the challenge
  duration 6.

  The history (`net_reachable`):
  * `p0` signs `h`, the setup state at turn 1 with `OH = pay 5 5`, and `q0`
    signs it too. `p0` holds the support of `h` (`hsupp`).
  * `p0` proposes `S'` at turn 2 with `OS = pay 4 6` (a move by the rules
    after `h`, `HonestSend.movesFrom`). `q0` does not countersign it.
  * `q0` signs `X` at turn 3 with `OX = pay 3 7` and delivers it. No state at
    turn 2 is in `p0`'s received states, so this is no gift of `q0`, and it
    is no conflict.
  The status of `c0` is open at turn 0, so `hpend` holds.

  * No outcome other than `OH` is enabled:
    - `OS` (`prevents_OS`): when the adversary challenges with `S'`, `p0`
      holds `q0`'s signature on `S'`. Then `p0` signs `X` (a move by the
      rules after `S'`), and in the next round it challenges with `X`, signed
      by both. The challenge duration 6 leaves room for the two rounds.
    - Every other outcome (`prevents_wait`): `p0` waits. Every support of
      the adversary is a state that `p0` signed, so it carries `OH` or `OS`.
  * No outcome is finalizable (`not_finalizable`):
    - `OH`: in the first round the adversary checkpoints `S'`, signed by
      both. From then on every support that `p0` can hold at a turn from 2 on
      is `S'` or `X`, and neither carries `OH`.
    - Every other outcome: the adversary only lands `p0`'s calls. `p0` holds
      no signature of `q0` on a state at turn 2, so it cannot sign `X` by the
      rules, and the only support it holds is `h`.

  So `p0` has exactly one enabled outcome, `OH`, and no finalizable outcome.
  The exit-strategy rule (added 2026-11-02) measures the enabled outcomes against
  `p`'s own strategy (`EnabledBy`, `TakeOut.exitStrategy`); this play is the
  reason. The prevention of `OS` and the prevention of the other outcomes
  are two different strategies, and no single strategy does both.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/proposal_escape.lean`.
  The theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Spec.Nitro.Liveness
import ArmadaLean.Nitro.TakeOut

namespace ArmadaLean.Nitro.CounterexampleProposalEscape

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

/-- The outcome of `h`. -/
def OH : Outcome Nat := pay 5 5
/-- The outcome of `p0`'s proposal `S'`. -/
def OS : Outcome Nat := pay 4 6
/-- The outcome of `q0`'s state `X`. -/
def OX : Outcome Nat := pay 3 7

def c0 : FixedPart :=
  { participants := [q0, p0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 6, kind := .ledger }

def appsC : Apps Nat := fun _ => consensusRules

/-- The non-final state of `c0` at turn `k` with the outcome `o`. -/
def st (k : Nat) (o : Outcome Nat) : State Nat :=
  { channel := c0, turnNum := k, outcome := o, isFinal := false, appData := .opaque 0 }

/-- `p0`'s signature on `h`. -/
def sh : SignedState Nat := ⟨st 1 OH, [p0]⟩
/-- `q0`'s signature on `h`. -/
def rh : SignedState Nat := ⟨st 1 OH, [q0]⟩
/-- `p0`'s proposal `S'`. -/
def sS : SignedState Nat := ⟨st 2 OS, [p0]⟩
/-- `q0`'s state `X`. -/
def rX : SignedState Nat := ⟨st 3 OX, [q0]⟩
/-- `p0`'s signature on `X`. -/
def sX : SignedState Nat := ⟨st 3 OX, [p0]⟩

/-- A state signed by both participants. -/
def both (s : State Nat) : SignedState Nat := ⟨s, [q0, p0]⟩

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

theorem A0 : Assumptions appsC p0 T0 where
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

/-- The consensus app is desirable for every destination map. -/
theorem appsC_desirable : Desirable appsC (tc0 : FixedPart).appDef destS :=
  TakeOut.consensus_desirable _

theorem round_bound {m : HonestMove Nat} {n n' : NetworkState Nat p0}
    (h : TN.Round appsC m n n') : n'.chain.now < n.chain.now + 2 := h.2

/-- A round whose clock does not move. -/
theorem mkRound {m : HonestMove Nat} {n n' : NetworkState Nat p0}
    (hseq : TN.RoundSeq appsC n.chain.now m.calls n n') (hnow : n'.chain.now = n.chain.now) :
    TN.Round appsC m n n' :=
  ⟨hseq, by rw [hnow]; exact Nat.lt_add_of_pos_right T0.ε_pos⟩

/-! ## Supports and statuses of `c0` -/

/-- A support of `c0`: one state, signed by both. -/
theorem cons_support {P : SupportProof Nat} {cand : State Nat}
    (h : (appsC c0.appDef).supports c0 P cand = true) :
    ∃ ss, P = [ss] ∧ ss.state = cand ∧ ss.state.channel = c0 ∧ ss.ByAll := by
  match P, h with
  | [ss], h =>
    simp only [appsC, consensusRules, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨ss, rfl, h.1.1, h.1.2, h.2⟩
  | [], h => simp only [appsC, consensusRules, Bool.false_eq_true] at h
  | _ :: _ :: _, h => simp only [appsC, consensusRules, Bool.false_eq_true] at h

theorem q0_mem {ss : SignedState Nat} (hall : ss.ByAll) (hc : ss.state.channel = c0) :
    q0 ∈ ss.signers :=
  hall q0 (by rw [hc]; decide)

theorem p0_mem {ss : SignedState Nat} (hall : ss.ByAll) (hc : ss.state.channel = c0) :
    p0 ∈ ss.signers :=
  hall p0 (by rw [hc]; decide)

theorem held_q {n : NetworkState Nat p0} {ss : SignedState Nat} (h : n.Holds ss)
    (hq : q0 ∈ ss.signers) : ∃ r ∈ n.received, r.state = ss.state ∧ q0 ∈ r.signers := by
  rcases h.1 q0 hq with ⟨hqp, -⟩ | hr
  · exact absurd hqp.symm p0_ne_q0
  · exact hr

/-- One successful operation on `c0`: the status it leaves. -/
theorem status_cases {s s' : Adjudicator Nat} {caller : Participant} {op : Op Nat}
    (h : s.apply appsC caller op = some s') :
    s'.statusOf c0 = s.statusOf c0 ∨
    (∃ P cand, op = .challenge c0 P cand ∧ (appsC c0.appDef).supports c0 P cand = true ∧
      cand.channel = c0 ∧
      ((s.mode c0 = .open ∧ (s.statusOf c0).turnNumRecord ≤ cand.turnNum) ∨
        (s.mode c0 = .challenge ∧ (s.statusOf c0).turnNumRecord < cand.turnNum)) ∧
      s'.statusOf c0 = .challenged cand.turnNum ⟨cand, s.now + 6⟩) ∨
    (∃ P cand, op = .checkpoint c0 P cand ∧ (appsC c0.appDef).supports c0 P cand = true ∧
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

theorem landed_now {n : NetworkState Nat p0} {op : Op Nat} (hop : ∀ dt, op ≠ .tick dt) :
    (n.applyAdv appsC (.land op)).chain.now = n.chain.now := by
  cases h : n.chain.apply appsC p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsC h]
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsC h]
    exact Adjudicator.apply_now_eq_of_not_tick hop h

/-- The status is finalized. -/
def IsFin (x : ChannelStatus Nat) : Prop := ∃ t f o, x = .finalized t f o

/-- A finalized status has the mode `finalized`. -/
theorem mode_fin {s : Adjudicator Nat} (h : IsFin (s.statusOf c0)) : s.mode c0 = .finalized := by
  obtain ⟨t, f, o, hf⟩ := h
  rw [Adjudicator.mode_eq, hf]; rfl

/-- `c0` finalized with `Ω`, read from its status. -/
theorem finalized_iff {n : NetworkState Nat p0} {Ω : Outcome Nat} :
    n.Finalized c0 Ω ↔ (n.chain.statusOf c0).finalizedWith n.chain.now = some Ω := by
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel]

/-- A status that is open, challenged with an outcome in `S`, or finalized
    with an outcome in `S`, is finalized with no outcome outside `S`. -/
theorem finalizedWith_mem {x : ChannelStatus Nat} {S : Outcome Nat → Prop} {now : Time}
    {Ω : Outcome Nat} (hch : ∀ t ch, x = .challenged t ch → S ch.state.outcome)
    (hfin : ∀ t f o, x = .finalized t f o → S f) (h : x.finalizedWith now = some Ω) : S Ω := by
  cases x with
  | «open» t => simp only [ChannelStatus.finalizedWith, reduceCtorEq] at h
  | challenged t ch =>
    rw [ChannelStatus.finalizedWith_challenged] at h
    split at h
    · rw [← Option.some.inj h]; exact hch t ch rfl
    · cases h
  | finalized t f o =>
    rw [ChannelStatus.finalizedWith_finalized] at h
    rw [← Option.some.inj h]; exact hfin t f o rfl

/-! ## The reachable start -/

def net : NetworkState Nat p0 := ⟨Adjudicator.genesis, [rX, rh], [sS, sh]⟩

theorem unforged_q {n : NetworkState Nat p0} {k : Nat} {o : Outcome Nat} :
    n.Unforged ⟨st k o, [q0]⟩ :=
  ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0, fun v hv => by
    simp only [st, State.voucher?, reduceCtorEq] at hv⟩

theorem unforged_sent {n : NetworkState Nat p0} {s : SignedState Nat} (hs : s ∈ n.sent) :
    n.Unforged s :=
  ⟨fun _ => ⟨s, hs, rfl⟩, fun _ hv _ => ⟨s, hs, hv⟩⟩

/-- A state of `c0` that `q0` signed in a received state, and `p0` in a sent
    state, is held with both signatures. -/
theorem holds_both {n : NetworkState Nat p0} {k : Nat} {o : Outcome Nat}
    (hq : ∃ r ∈ n.received, r.state = st k o ∧ q0 ∈ r.signers) (hp : ∃ s ∈ n.sent, s.state = st k o) :
    n.Holds (both (st k o)) := by
  refine ⟨fun q hq' => ?_, fun v hv => by simp only [both, st, State.voucher?, reduceCtorEq] at hv⟩
  simp only [both, List.mem_cons, List.not_mem_nil, or_false] at hq'
  rcases hq' with rfl | rfl
  · exact .inr hq
  · exact .inl ⟨rfl, hp⟩

/-- A delivery of a state that only `q0` signed, with no own-violation of
    `q0` against `received`. -/
theorem deliver_ok {n : NetworkState Nat p0} {k : Nat} {o : Outcome Nat}
    (h : ¬ OwnViolation destS q0 n.received ⟨st k o, [q0]⟩) :
    (AdvMove.deliver ⟨st k o, [q0]⟩).NoOwnViolation destS n := fun q hq _ => by
  rw [List.mem_singleton.1 hq]; exact h

theorem net_reachable : (Nitro.participant appsC TN).Reachable net := by
  refine ⟨⟨Adjudicator.genesis, [], []⟩, rfl, ?_⟩
  refine .tail (b := ⟨Adjudicator.genesis, [rh], [sS, sh]⟩) ?_
    (Or.inr (Or.inr (Or.inl ⟨.deliver rX, ⟨unforged_q, deliver_ok (by decide)⟩,
      fun op h => (by cases h), rfl⟩)))
  refine .tail (b := ⟨Adjudicator.genesis, [rh], [sh]⟩) ?_ (Or.inl ⟨.send (st 2 OS),
    (HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
      HonestSend.fundsCommitted_of_fundable (by decide), fun _ => ⟨⟨[both (st 1 OH)], st 1 OH,
        fun ss hss => by
          rw [List.mem_singleton.1 hss]
          exact holds_both ⟨rh, by decide, rfl, by decide⟩ ⟨sh, by decide, rfl⟩,
        by decide, rfl, rfl⟩, [both (st 2 OS)], fun ss hss => .inr (by rw [List.mem_singleton.1 hss]; rfl),
        by decide⟩, by decide, by decide⟩, rfl⟩)
  refine .tail (b := ⟨Adjudicator.genesis, [], [sh]⟩) ?_
    (Or.inr (Or.inr (Or.inl ⟨.deliver rh, ⟨unforged_q, deliver_ok (by decide)⟩,
      fun op h => (by cases h), rfl⟩)))
  exact .tail .refl (Or.inl ⟨.send (st 1 OH),
    (HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
      HonestSend.fundsCommitted_of_fundable (by decide), fun h => absurd h (by decide), by decide,
      by decide⟩, rfl⟩)

theorem net_status : net.chain.statusOf c0 = .open 0 := by decide

/-- No challenge is running at `net`: `hpend` holds. -/
theorem net_deadlineAfter : net.DeadlineAfter c0 T0.ε := fun _ _ h => by
  rw [net_status] at h; cases h

/-- `p0` holds the support of `h` (`hsupp`). -/
theorem holds_hh : ∀ ss ∈ [both (st 1 OH)], net.Holds ss := fun ss hss => by
  rw [List.mem_singleton.1 hss]
  exact holds_both ⟨rh, by decide, rfl, by decide⟩ ⟨sh, by decide, rfl⟩

/-! ## No outcome is finalizable

Against every strategy tree of `p0`, the adversary lands `p0`'s calls and
does nothing else (for `OH`, it first checkpoints `S'`). An invariant `Inv`
of the network and a set `Safe` of statuses of `c0` survive each landed
call (`Lazy.land`) and each honest move (`Lazy.honest`), and no safe status
is finalized with the target. -/

/-- The two step obligations of an adversary that only lands `p0`'s calls. -/
structure Lazy (Inv : NetworkState Nat p0 → Prop) (Safe : ChannelStatus Nat → Prop) : Prop where
  land : ∀ {m : NetworkState Nat p0} {op : Op Nat}, Inv m → Safe (m.chain.statusOf c0) →
    (∀ ss ∈ op.proofStates, m.Holds ss) →
    Inv (m.applyAdv appsC (.land op)) ∧ Safe ((m.applyAdv appsC (.land op)).chain.statusOf c0)
  honest : ∀ {n0 n : NetworkState Nat p0} {mv : HonestMove Nat}, Inv n0 → Inv n →
    Safe (n.chain.statusOf c0) → mv.Feasible appsC n0 → n.sent = n0.sent →
    Inv (n.applyHonest mv) ∧ Safe ((n.applyHonest mv).chain.statusOf c0)

/-- The calls of `p0` land in order, and the clock stays. -/
theorem Lazy.round {Inv : NetworkState Nat p0 → Prop} {Safe : ChannelStatus Nat → Prop}
    (L : Lazy Inv Safe) (n0 : NetworkState Nat p0) (t : Time) :
    ∀ (pending : List (Op Nat)), (∀ op ∈ pending, op.HonestFeasible n0) →
    ∀ m : NetworkState Nat p0, Inv m → Safe (m.chain.statusOf c0) → m.sent = n0.sent →
      (∀ r ∈ n0.received, r ∈ m.received) →
      ∃ m', TN.RoundSeq appsC t pending m m' ∧ Inv m' ∧ Safe (m'.chain.statusOf c0) ∧
        m'.chain.now = m.chain.now ∧ m'.sent = m.sent := by
  intro pending
  induction pending with
  | nil => exact fun _ m hI hS _ _ => ⟨m, .nil, hI, hS, rfl, rfl⟩
  | cons op rest ih =>
    intro hfeas m hI hS hsent hrecv
    have hop := hfeas op List.mem_cons_self
    have hH : ∀ ss ∈ op.proofStates, m.Holds ss := fun ss hss =>
      NetworkState.Holds.mono hsent.symm hrecv (hop.mem ss hss)
    obtain ⟨hI1, hS1⟩ := L.land hI hS hH
    obtain ⟨m', hseq, hI', hS', hnow, hs'⟩ := ih (fun o ho => hfeas o (List.mem_cons_of_mem _ ho))
      _ hI1 hS1 (by rw [NetworkState.applyAdv_sent]; exact hsent)
      (fun r hr => (NetworkState.applyAdv_sent_received appsC m (.land op)).2 r (hrecv r hr))
    refine ⟨m', .land (l1 := []) (l2 := rest) rfl hseq, hI', hS', ?_, ?_⟩
    · rw [hnow, landed_now hop.not_tick]
    · rw [hs', NetworkState.applyAdv_sent]

/-- No strategy tree of `p0` reaches a status finalized with `Ω` from a state
    with `Inv` and a safe status. -/
theorem Lazy.not_unbeatable {Inv : NetworkState Nat p0 → Prop} {Safe : ChannelStatus Nat → Prop}
    {Ω : Outcome Nat} (L : Lazy Inv Safe)
    (hfin : ∀ x : ChannelStatus Nat, Safe x → ∀ now, x.finalizedWith now ≠ some Ω) :
    ∀ n, Inv n → Safe (n.chain.statusOf c0) →
      ¬ UnbeatableIn appsC TN (fun _ => True) (fun n => n.Finalized c0 Ω) n := by
  intro n hI hS hU
  induction hU with
  | done hG => exact hfin _ hS _ (finalized_iff.1 hG)
  | @move n m _ hfeas _ ih =>
    obtain ⟨n', hseq, hI', hS', hnow, hsent'⟩ :=
      L.round n n.chain.now m.calls hfeas.calls n hI hS rfl (fun _ hr => hr)
    obtain ⟨hI'', hS''⟩ := L.honest hI hI' hS' hfeas hsent'
    exact ih n' (mkRound hseq hnow) hI'' hS''

/-! ### Every outcome but `OH`: the adversary only lands `p0`'s calls -/

/-- The invariant: `q0` signed only `h` and `X`, and `p0` never signs `X`. -/
structure InvA (n : NetworkState Nat p0) : Prop where
  recvQ : ∀ r ∈ n.received, q0 ∈ r.signers → r.state = st 1 OH ∨ r.state = st 3 OX
  recvU : ∀ r ∈ n.received, n.Unforged r
  noX : ∀ s ∈ n.sent, s.state ≠ st 3 OX

/-- The statuses that carry `OH` only. -/
def SafeA (x : ChannelStatus Nat) : Prop :=
  (∃ t, x = .open t) ∨ (∃ t ch, x = .challenged t ch ∧ ch.state.outcome = OH) ∨
    (∃ t f o, x = .finalized t f o ∧ f = OH)

/-- Every state that `p0` holds with both signatures is `h`. -/
theorem held_A {n : NetworkState Nat p0} (hI : InvA n) {ss : SignedState Nat} (h : n.Holds ss)
    (hall : ss.ByAll) (hc : ss.state.channel = c0) : ss.state = st 1 OH := by
  obtain ⟨r, hr, hrs, hrq⟩ := held_q h (q0_mem hall hc)
  rcases hI.recvQ r hr hrq with h1 | h3
  · rw [← hrs]; exact h1
  · obtain ⟨s, hs, hss⟩ := (h.unforged hI.recvU).1 (p0_mem hall hc)
    exact absurd (hss.trans (hrs.symm.trans h3)) (hI.noX s hs)

theorem cand_A {n : NetworkState Nat p0} (hI : InvA n) {P : SupportProof Nat} {cand : State Nat}
    (h : (appsC c0.appDef).supports c0 P cand = true) (hH : ∀ ss ∈ P, n.Holds ss) :
    cand = st 1 OH := by
  obtain ⟨ss, rfl, hst, hc, hall⟩ := cons_support h
  rw [← hst]; exact held_A hI (hH ss (List.mem_singleton_self ss)) hall hc

/-- `p0` signs no state at turn 3 by the rules: it holds no support at
    turn 2. -/
theorem send_not_X {n0 : NetworkState Nat p0} (hI0 : InvA n0) {signed : List (SignedState Nat)}
    {held : FixedPart → Prop} {st' : State Nat}
    (hsend : HonestSend signed held (n0.CanMoveTo appsC) st') : st' ≠ st 3 OX := by
  rintro rfl
  obtain ⟨⟨P, cand, hH, hsup, -, ht⟩, -⟩ := hsend.movesFrom (by decide)
  rw [cand_A hI0 hsup hH] at ht
  exact absurd ht (by decide)

theorem landA {m : NetworkState Nat p0} (hI : InvA m) (hS : SafeA (m.chain.statusOf c0))
    {op : Op Nat} (hH : ∀ ss ∈ op.proofStates, m.Holds ss) :
    InvA (m.applyAdv appsC (.land op)) ∧ SafeA ((m.applyAdv appsC (.land op)).chain.statusOf c0) := by
  cases happ : m.chain.apply appsC p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsC happ]; exact ⟨hI, hS⟩
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsC happ]
    refine ⟨⟨fun x hx hxq => ?_, fun x hx => ?_, hI.noX⟩, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨r, hr, hrs, hrq⟩ := held_q (hH x hx) hxq
        rw [← hrs]; exact hI.recvQ r hr hrq
      · exact hI.recvQ x hx hxq
    · rcases List.mem_append.1 hx with hx | hx
      · exact (hH x hx).unforged hI.recvU
      · exact hI.recvU x hx
    rcases status_cases happ with heq | ⟨P, cand, rfl, hsup, -, -, hst⟩ |
        ⟨P, cand, rfl, -, -, -, hst⟩ | ⟨ss, rfl, hcp, -⟩ | ⟨o0, o', hfo, hst⟩
    · rw [heq]; exact hS
    · rw [hst, cand_A hI hsup hH]; exact Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)
    · rw [hst]; exact Or.inl ⟨_, rfl⟩
    · have h1 := held_A hI (hH ss (List.mem_singleton_self ss)) hcp.2.2 hcp.1
      have h2 := hcp.2.1
      rw [h1] at h2; cases h2
    · rw [hst]
      rcases hS with ⟨t, ht⟩ | ⟨t, ch, ht, hx⟩ | ⟨t, f, o, ht, hf⟩
      · rw [ht, ChannelStatus.finalOutcome_open] at hfo; cases hfo
      · rw [ht, ChannelStatus.withOutcome_challenged]; exact Or.inr (Or.inr ⟨_, _, _, rfl, hx⟩)
      · rw [ht, ChannelStatus.withOutcome_finalized]; exact Or.inr (Or.inr ⟨_, _, _, rfl, hf⟩)

theorem honestA {n0 n : NetworkState Nat p0} {mv : HonestMove Nat} (hI0 : InvA n0) (hI : InvA n)
    (hS : SafeA (n.chain.statusOf c0)) (hfeas : mv.Feasible appsC n0) (_hsent : n.sent = n0.sent) :
    InvA (n.applyHonest mv) ∧ SafeA ((n.applyHonest mv).chain.statusOf c0) := by
  cases mv with
  | react r =>
    refine ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).mono (fun y hy => List.mem_append_right _ hy),
      fun s hs => ?_⟩, hS⟩
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨st', hst, rfl⟩ := List.mem_map.1 hs
      exact send_not_X hI0 (hfeas.2 st' hst)
    · exact hI.noX s hs
  | wait dt =>
    exact ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).of_sent rfl, hI.noX⟩,
      by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; exact hS⟩

theorem lazyA : Lazy InvA SafeA := ⟨fun hI hS hH => landA hI hS hH, honestA⟩

theorem invA_net : InvA net := by
  refine ⟨fun x hx hxq => ?_, fun x hx => ?_, fun s hs => ?_⟩
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact unforged_q
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> decide

theorem not_finalizable_other {Ω : Outcome Nat} (hΩ : Ω ≠ OH) :
    ¬ Finalizable appsC TN c0 Ω net :=
  lazyA.not_unbeatable (fun x hx now h => hΩ (finalizedWith_mem (S := fun o => o = OH)
    (fun t ch hc => by
      rcases hx with ⟨t', ht⟩ | ⟨t', ch', ht, hx⟩ | ⟨t', f, o, ht, -⟩ <;> rw [hc] at ht <;> cases ht
      exact hx)
    (fun t f o hc => by
      rcases hx with ⟨t', ht⟩ | ⟨t', ch', ht, -⟩ | ⟨t', f', o', ht, hf⟩ <;> rw [hc] at ht <;> cases ht
      exact hf) h))
    net invA_net (by rw [net_status]; exact Or.inl ⟨0, rfl⟩)

/-! ### `OH`: the adversary checkpoints `S'`, then only lands `p0`'s calls -/

/-- The invariant: `q0` signed only `h`, `S'` and `X`. -/
structure InvB (n : NetworkState Nat p0) : Prop where
  recvQ : ∀ r ∈ n.received, q0 ∈ r.signers →
    r.state = st 1 OH ∨ r.state = st 2 OS ∨ r.state = st 3 OX

/-- The statuses at a turn from 2 on that never carry `OH`. -/
def SafeB (x : ChannelStatus Nat) : Prop :=
  (∃ t, x = .open t ∧ 2 ≤ t) ∨ (∃ t ch, x = .challenged t ch ∧ 2 ≤ t ∧ ch.state.outcome ≠ OH) ∨
    (∃ t f o, x = .finalized t f o ∧ f ≠ OH)

theorem held_B {n : NetworkState Nat p0} (hI : InvB n) {ss : SignedState Nat} (h : n.Holds ss)
    (hall : ss.ByAll) (hc : ss.state.channel = c0) :
    ss.state = st 1 OH ∨ ss.state = st 2 OS ∨ ss.state = st 3 OX := by
  obtain ⟨r, hr, hrs, hrq⟩ := held_q h (q0_mem hall hc)
  rw [← hrs]; exact hI.recvQ r hr hrq

/-- A support that `p0` holds, at a turn from 2 on, does not carry `OH`. -/
theorem cand_B {n : NetworkState Nat p0} (hI : InvB n) {P : SupportProof Nat} {cand : State Nat}
    (h : (appsC c0.appDef).supports c0 P cand = true) (hH : ∀ ss ∈ P, n.Holds ss)
    (h2 : 2 ≤ cand.turnNum) : cand.outcome ≠ OH := by
  obtain ⟨ss, rfl, hst, hc, hall⟩ := cons_support h
  subst hst
  rcases held_B hI (hH ss (List.mem_singleton_self ss)) hall hc with h1 | h1 | h1 <;>
    rw [h1] at h2 ⊢
  · exact absurd h2 (by decide)
  · decide
  · decide

theorem landB {m : NetworkState Nat p0} (hI : InvB m) (hS : SafeB (m.chain.statusOf c0))
    {op : Op Nat} (hH : ∀ ss ∈ op.proofStates, m.Holds ss) :
    InvB (m.applyAdv appsC (.land op)) ∧ SafeB ((m.applyAdv appsC (.land op)).chain.statusOf c0) := by
  cases happ : m.chain.apply appsC p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsC happ]; exact ⟨hI, hS⟩
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsC happ]
    refine ⟨⟨fun x hx hxq => ?_⟩, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨r, hr, hrs, hrq⟩ := held_q (hH x hx) hxq
        rw [← hrs]; exact hI.recvQ r hr hrq
      · exact hI.recvQ x hx hxq
    rcases status_cases happ with heq | ⟨P, cand, rfl, hsup, -, hmode, hst⟩ |
        ⟨P, cand, rfl, -, hopen, hlt, hst⟩ | ⟨ss, rfl, hcp, -⟩ | ⟨o0, o', hfo, hst⟩
    · rw [heq]; exact hS
    · have h2 : 2 ≤ cand.turnNum := by
        have hrec : 2 ≤ (m.chain.statusOf c0).turnNumRecord := by
          rcases hS with ⟨t, ht, h2⟩ | ⟨t, ch, ht, h2, -⟩ | ⟨t, f, o, ht, -⟩ <;> rw [ht]
          · exact h2
          · exact h2
          · rw [Adjudicator.mode_eq, ht] at hmode
            rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
        rcases hmode with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
      exact Or.inr (Or.inl ⟨_, _, hst, h2, cand_B hI hsup hH h2⟩)
    · have h2 : 2 ≤ cand.turnNum := by
        rcases hS with ⟨t, ht, h2⟩ | ⟨t, ch, ht, h2, -⟩ | ⟨t, f, o, ht, -⟩ <;> rw [ht] at hlt
        · simp only [ChannelStatus.turnNumRecord_open] at hlt; omega
        · simp only [ChannelStatus.turnNumRecord_challenged] at hlt; omega
        · rw [ht] at hopen
          exact absurd hopen (by simp only [ChannelStatus.IsOpen, ChannelStatus.mode, ne_eq,
            not_true_eq_false, not_false_eq_true])
      exact Or.inl ⟨_, hst, h2⟩
    · have h2 := hcp.2.1
      rcases held_B hI (hH ss (List.mem_singleton_self ss)) hcp.2.2 hcp.1 with h1 | h1 | h1 <;>
        rw [h1] at h2 <;> cases h2
    · rw [hst]
      rcases hS with ⟨t, ht, -⟩ | ⟨t, ch, ht, -, hle⟩ | ⟨t, f, o, ht, hle⟩
      · rw [ht, ChannelStatus.finalOutcome_open] at hfo; cases hfo
      · rw [ht, ChannelStatus.withOutcome_challenged]
        exact Or.inr (Or.inr ⟨_, _, _, rfl, hle⟩)
      · rw [ht, ChannelStatus.withOutcome_finalized]
        exact Or.inr (Or.inr ⟨_, _, _, rfl, hle⟩)

/-- An honest move keeps `received` and the status of `c0`. -/
theorem honestB {n : NetworkState Nat p0} {mv : HonestMove Nat} (hI : InvB n)
    (hS : SafeB (n.chain.statusOf c0)) :
    InvB (n.applyHonest mv) ∧ SafeB ((n.applyHonest mv).chain.statusOf c0) := by
  cases mv with
  | react r => exact ⟨⟨hI.recvQ⟩, hS⟩
  | wait dt =>
    exact ⟨⟨hI.recvQ⟩, by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; exact hS⟩

theorem lazyB : Lazy InvB SafeB :=
  ⟨fun hI hS hH => landB hI hS hH, fun _ hI hS _ _ => honestB hI hS⟩

/-- The adversary's first move: a checkpoint with `S'`, signed by both. -/
def opB : Op Nat := .checkpoint c0 [both (st 2 OS)] (st 2 OS)

def sB : Adjudicator Nat := Adjudicator.genesis.setStatus c0 (.open 2)

theorem opB_apply : Adjudicator.genesis.apply appsC q0 opB = some sB := by
  rw [opB, Adjudicator.apply_checkpoint_equation, dif_pos (by decide)]
  rfl

theorem opB_feasible : TN.feasible net (.chain q0 opB) := by
  refine ⟨⟨by decide, fun ss hss => ?_⟩, AdvMove.NoOwnViolation.chain_of (by decide)⟩
  rw [opB, Op.proofStates, List.mem_singleton] at hss
  subst hss
  exact ⟨fun _ => ⟨sS, by decide, rfl⟩, fun v hv => by
    simp only [both, st, State.voucher?, reduceCtorEq] at hv⟩

theorem net_not_finalized (Ω : Outcome Nat) : ¬ net.Finalized c0 Ω := by
  rw [finalized_iff, net_status]
  simp only [ChannelStatus.finalizedWith, reduceCtorEq, not_false_eq_true]

theorem not_finalizable_OH : ¬ Finalizable appsC TN c0 OH net := by
  intro hU
  cases hU with
  | done h => exact net_not_finalized OH h
  | move m _ hfeas hcont =>
    let n1 : NetworkState Nat p0 := net.applyAdv appsC (.chain q0 opB)
    have hn1 : n1 = ⟨sB, [both (st 2 OS)] ++ net.received, net.sent⟩ :=
      NetworkState.applyAdv_chain_some appsC opB_apply
    have hI1 : InvB n1 := by
      rw [hn1]
      refine ⟨fun x hx hxq => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton.1 hx]; exact Or.inr (Or.inl rfl)
      · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
    have hS1 : SafeB (n1.chain.statusOf c0) := by
      rw [hn1]; exact Or.inl ⟨2, by decide, le_refl _⟩
    obtain ⟨n', hseq, hI', hS', hnow, hsent'⟩ := lazyB.round net 0 m.calls hfeas.calls n1 hI1 hS1
      (by rw [hn1]) (fun r hr => by rw [hn1]; exact List.mem_append_right _ hr)
    have hround : TN.Round appsC m net n' :=
      mkRound (.other opB_feasible (fun _ h => by cases h) (fun _ h => by cases h) hseq)
        (by rw [hnow, hn1]; rfl)
    obtain ⟨hI'', hS''⟩ := honestB (mv := m) hI' hS'
    refine lazyB.not_unbeatable (fun x hx now h => ?_) _ hI'' hS'' (hcont n' hround)
    have := finalizedWith_mem (S := fun o => o ≠ OH)
      (fun t ch hc => by
        rcases hx with ⟨t', ht, -⟩ | ⟨t', ch', ht, -, hx⟩ | ⟨t', f, o, ht, -⟩ <;> rw [hc] at ht <;>
          cases ht
        exact hx)
      (fun t f o hc => by
        rcases hx with ⟨t', ht, -⟩ | ⟨t', ch', ht, -⟩ | ⟨t', f', o', ht, hf⟩ <;> rw [hc] at ht <;>
          cases ht
        exact hf) h
    exact this rfl

theorem not_finalizable (Ω : Outcome Nat) : ¬ Finalizable appsC TN c0 Ω net := by
  by_cases h : Ω = OH
  · subst h; exact not_finalizable_OH
  · exact not_finalizable_other h

/-! ## No outcome but `OH` is enabled -/

/-- A payout leaves a finalized status. Its outcome of finalization is the
    outcome of the expired challenge, or the old outcome of finalization. -/
theorem withOutcome_cases {x : ChannelStatus Nat} {now : Time} {o0 o' : Outcome Nat}
    (hfo : x.finalOutcome now = some o0) :
    IsFin (x.withOutcome o') ∧ ∀ t f o, x.withOutcome o' = .finalized t f o →
      (∃ ch, x = .challenged t ch ∧ ch.deadline ≤ now ∧ f = ch.state.outcome) ∨
        ∃ o1, x = .finalized t f o1 := by
  cases x with
  | «open» t => rw [ChannelStatus.finalOutcome_open] at hfo; cases hfo
  | challenged t ch =>
    rw [ChannelStatus.finalOutcome_challenged] at hfo
    have hd : ch.deadline ≤ now := by
      split at hfo
      · assumption
      · cases hfo
    refine ⟨⟨_, _, _, rfl⟩, fun t' f o h => Or.inl ⟨ch, ?_⟩⟩
    rw [ChannelStatus.withOutcome_challenged] at h
    obtain ⟨rfl, rfl, -⟩ := ChannelStatus.finalized.inj h
    exact ⟨rfl, hd, rfl⟩
  | finalized t f o =>
    refine ⟨⟨_, _, _, rfl⟩, fun t' f' o'' h => Or.inr ⟨o, ?_⟩⟩
    rw [ChannelStatus.withOutcome_finalized] at h
    obtain ⟨rfl, rfl, -⟩ := ChannelStatus.finalized.inj h
    rfl

theorem isFin_not_challenged {x : ChannelStatus Nat} (h : IsFin x) {t : Nat} {ch : Challenge Nat} :
    x ≠ .challenged t ch := by
  obtain ⟨_, _, _, hf⟩ := h
  rw [hf]; exact fun h => by cases h

/-! ### Every outcome but `OH` and `OS`: `p0` waits -/

/-- The invariant of the waiting strategy: `p0` signed only `h` and `S'`,
    and every challenge or finalization of `c0` carries `OH` or `OS`. -/
structure InvW (n : NetworkState Nat p0) : Prop where
  sent : n.sent = net.sent
  chOut : ∀ t ch, n.chain.statusOf c0 = .challenged t ch →
    ch.state.outcome = OH ∨ ch.state.outcome = OS
  noFin : ∀ t f o, n.chain.statusOf c0 = .finalized t f o → f = OH ∨ f = OS

/-- A state with `p0`'s signature, unforged, is `h` or `S'`. -/
theorem signed_W {n : NetworkState Nat p0} (hI : InvW n) {ss : SignedState Nat}
    (hU : n.Unforged ss) (hp : p0 ∈ ss.signers) : ss.state = st 1 OH ∨ ss.state = st 2 OS := by
  obtain ⟨s, hs, hss⟩ := hU.1 hp
  rw [hI.sent] at hs
  simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact Or.inr hss.symm
  · exact Or.inl hss.symm

theorem stepW {n : NetworkState Nat p0} (hI : InvW n) {caller : Participant} {op : Op Nat}
    {s' : Adjudicator Nat} (h : n.chain.apply appsC caller op = some s')
    (hU : ∀ ss ∈ op.proofStates, n.Unforged ss) :
    InvW { n with chain := s', received := op.proofStates ++ n.received } := by
  rcases status_cases h with heq | ⟨P, cand, rfl, hsup, -, -, hst⟩ |
      ⟨P, cand, rfl, -, -, -, hst⟩ | ⟨ss, rfl, hcp, -⟩ | ⟨o0, o', hfo, hst⟩
  · exact ⟨hI.sent, fun t ch hc => hI.chOut t ch (heq ▸ hc),
      fun t f o hc => hI.noFin t f o (heq ▸ hc)⟩
  · obtain ⟨ss, rfl, hss, hc, hall⟩ := cons_support hsup
    have hcand := signed_W hI (hU ss (List.mem_singleton_self ss)) (p0_mem hall hc)
    rw [hss] at hcand
    refine ⟨hI.sent, fun t ch hch => ?_, fun t f o hch => (by rw [hst] at hch; cases hch)⟩
    rw [hst] at hch
    obtain ⟨-, rfl⟩ := ChannelStatus.challenged.inj hch
    rcases hcand with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact ⟨hI.sent, fun t ch hch => (by rw [hst] at hch; cases hch),
      fun t f o hch => (by rw [hst] at hch; cases hch)⟩
  · exfalso
    obtain ⟨hc, hfin, hall⟩ := hcp
    rcases signed_W hI (hU ss (List.mem_singleton_self ss)) (p0_mem hall hc) with h1 | h1 <;>
      rw [h1] at hfin <;> cases hfin
  · obtain ⟨hF, hcases⟩ := withOutcome_cases (o' := o') hfo
    rw [← hst] at hF hcases
    refine ⟨hI.sent, fun t ch hch => absurd hch (isFin_not_challenged hF), fun t f o hf => ?_⟩
    rcases hcases t f o hf with ⟨ch, hch, -, rfl⟩ | ⟨o1, hf1⟩
    · exact hI.chOut t ch hch
    · exact hI.noFin t f o1 hf1

theorem stepInvW : TN.StepInvariant appsC (fun _ => True) InvW (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {n ss} _ _ hI => by
    rw [NetworkState.applyAdv_deliver]; exact ⟨hI.sent, hI.chOut, hI.noFin⟩
  tick := fun {n dt} _ _ hI => by
    rw [NetworkState.applyAdv_tick]; exact ⟨hI.sent, hI.chOut, hI.noFin⟩
  chain := fun {n caller op} _ hfe hI => by
    cases happ : n.chain.apply appsC caller op with
    | none => rw [NetworkState.applyAdv_chain_none appsC happ]; exact hI
    | some s' => rw [NetworkState.applyAdv_chain_some appsC happ]; exact stepW hI happ hfe.1.2

/-- One round of waiting keeps `InvW`, at its end and after the wait. -/
theorem roundW {n n' : NetworkState Nat p0} (hI : InvW n)
    (hround : TN.Round appsC (.wait 0) n n') : InvW n' ∧ InvW (n'.applyHonest (.wait 0)) := by
  have hI' : InvW n' := Threat.RoundSeq.nil_invariant hround.1 stepInvW.anyGuard hI
  exact ⟨hI', hI'.sent, hI'.chOut, hI'.noFin⟩

theorem invW_net : InvW net :=
  ⟨rfl, fun _ _ h => (by rw [net_status] at h; cases h),
    fun _ _ _ h => (by rw [net_status] at h; cases h)⟩

theorem prevents_wait {Ω : Outcome Nat} (hH : Ω ≠ OH) (hS : Ω ≠ OS) :
    Prevents appsC TN (fun n => n.Finalized c0 Ω) net := by
  have hrun : ∀ {n1}, Run appsC TN (fun _ => .wait 0) net n1 → InvW n1 := by
    intro n1 h
    induction h with
    | refl => exact invW_net
    | round _ hr ih => exact (roundW ih hr).2
  refine ⟨fun _ => .wait 0, fun _ => trivial, fun n1 n2 hr hround hf => ?_⟩
  have hI := (roundW (hrun hr) hround).1
  rcases finalizedWith_mem (S := fun o => o = OH ∨ o = OS) hI.chOut hI.noFin (finalized_iff.1 hf)
    with h1 | h1
  · exact hH h1
  · exact hS h1

/-! ### `OS`: `p0` escapes to `X`

When the adversary challenges with `S'`, its proof puts `q0`'s signature on
`S'` into `p0`'s received states. Then `p0` signs `X`, a move by the rules
after `S'`, and in the next round it challenges with `X`, signed by both.
Every support that the adversary can use is a state that `p0` signed, and
`p0` signed no final state. So only `OH` and `OX` can be finalized, and a
challenge with `S'` never ends before `p0`'s answer lands. -/

/-- `X`, signed by both. -/
def hX : SignedState Nat := both (st 3 OX)

/-- `p0`'s answer to a challenge with `S'`. -/
def opP : Op Nat := .challenge c0 [hX] (st 3 OX)

/-- `p0` holds `q0`'s signature on `S'`. -/
def SHeld (n : NetworkState Nat p0) : Prop :=
  ∃ r ∈ n.received, r.state = st 2 OS ∧ q0 ∈ r.signers

theorem SHeld.mono {n n' : NetworkState Nat p0} (h : SHeld n)
    (hr : ∀ r ∈ n.received, r ∈ n'.received) : SHeld n' :=
  let ⟨r, hrm, hrs, hrq⟩ := h
  ⟨r, hr r hrm, hrs, hrq⟩

/-- The states that `p0` signs in the play. -/
def SentP (n : NetworkState Nat p0) : Prop := ∀ s ∈ n.sent, s = sS ∨ s = sh ∨ s = sX

/-- The candidates the play can carry: the states that `p0` signs. -/
def CandOK (cand : State Nat) : Prop := cand = st 1 OH ∨ cand = st 2 OS ∨ cand = st 3 OX

/-- Every support with unforged states is a state that `p0` signed. -/
theorem cand_P {n : NetworkState Nat p0} (hS : SentP n) {P : SupportProof Nat} {cand : State Nat}
    (h : (appsC c0.appDef).supports c0 P cand = true) (hU : ∀ ss ∈ P, n.Unforged ss) :
    CandOK cand := by
  obtain ⟨ss, rfl, hst, hc, hall⟩ := cons_support h
  obtain ⟨s, hs, hss⟩ := (hU ss (List.mem_singleton_self ss)).1 (p0_mem hall hc)
  rw [← hst, ← hss]
  rcases hS s hs with rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

/-- The invariant at the start of each round of `p0`'s strategy. -/
structure InvP (n : NetworkState Nat p0) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  xin : rX ∈ n.received
  sSin : sS ∈ n.sent
  sentOK : SentP n
  noFin : ∀ t f o, n.chain.statusOf c0 = .finalized t f o → f = OH ∨ f = OX
  chOut : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → CandOK ch.state ∧ t = ch.state.turnNum
  timing : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state = st 2 OS →
    n.chain.now + 2 ≤ ch.deadline ∧ (sX ∉ n.sent → n.chain.now + 4 ≤ ch.deadline ∧ SHeld n)

/-- The invariant inside a round that starts at `n0`; the turn record stays
    at least `R`, unless `c0` is finalized. -/
structure KP (n0 : NetworkState Nat p0) (R : Nat) (n : NetworkState Nat p0) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = n0.sent
  recv : ∀ r ∈ n0.received, r ∈ n.received
  now0 : n0.chain.now ≤ n.chain.now
  noFin : ∀ t f o, n.chain.statusOf c0 = .finalized t f o → f = OH ∨ f = OX
  chOut : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → CandOK ch.state ∧ t = ch.state.turnNum
  chA : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state = st 2 OS →
    n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ (n0.chain.now + 6 ≤ ch.deadline ∧ SHeld n)
  left : ∀ t0 ch0, n0.chain.statusOf c0 = .challenged t0 ch0 → ch0.state = st 2 OS →
    n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ t0 < (n.chain.statusOf c0).turnNumRecord ∨
      IsFin (n.chain.statusOf c0)
  recR : R ≤ (n.chain.statusOf c0).turnNumRecord ∨ IsFin (n.chain.statusOf c0)

theorem KP.start {n0 : NetworkState Nat p0} (hI : InvP n0) :
    KP n0 (n0.chain.statusOf c0).turnNumRecord n0 :=
  ⟨hI.recvU, rfl, fun _ h => h, le_refl _, hI.noFin, hI.chOut, fun _ _ _ _ => Or.inl rfl,
    fun _ _ _ _ => Or.inl rfl, Or.inl (le_refl _)⟩

theorem KP.lower {n0 n : NetworkState Nat p0} {R R' : Nat} (hK : KP n0 R n)
    (hR : R' ≤ (n.chain.statusOf c0).turnNumRecord ∨ IsFin (n.chain.statusOf c0)) :
    KP n0 R' n :=
  ⟨hK.recvU, hK.sent, hK.recv, hK.now0, hK.noFin, hK.chOut, hK.chA, hK.left, hR⟩

/-- A standing challenge with `S'` inside a round has not expired. -/
theorem KP.liveA {n0 n : NetworkState Nat p0} {R : Nat} (hI0 : InvP n0)
    (hK : KP n0 R n) (hnow : n.chain.now < n0.chain.now + 2) {t : Nat} {ch : Challenge Nat}
    (hc : n.chain.statusOf c0 = .challenged t ch) (hx : ch.state = st 2 OS) :
    n.chain.now < ch.deadline := by
  rcases hK.chA t ch hc hx with h0 | ⟨h6, -⟩
  · rw [h0] at hc
    exact lt_of_lt_of_le hnow (hI0.timing t ch hc hx).1
  · exact lt_of_lt_of_le hnow (le_trans (Nat.add_le_add_left (by decide) _) h6)

/-- One successful operation whose candidate, if any, is one the play can
    carry, keeps `KP`, inside a round whose clock stays below `n0`'s clock
    plus 2. -/
theorem stepK {n0 n : NetworkState Nat p0} {R : Nat}
    (hI0 : InvP n0) (hK : KP n0 R n) (hnow : n.chain.now < n0.chain.now + 2)
    {caller : Participant} {op : Op Nat} {s' : Adjudicator Nat}
    (h : n.chain.apply appsC caller op = some s') (hU : ∀ ss ∈ op.proofStates, n.Unforged ss)
    (hcand : ∀ P cand, op = .challenge c0 P cand → CandOK cand)
    (hs'now : n.chain.now ≤ s'.now) :
    KP n0 R { n with chain := s', received := op.proofStates ++ n.received } := by
  have hrec : ∀ r ∈ n.received, r ∈ op.proofStates ++ n.received :=
    fun r hr => List.mem_append_right _ hr
  have hRecU : ∀ r ∈ op.proofStates ++ n.received,
      ({ n with chain := s', received := op.proofStates ++ n.received } : NetworkState Nat p0).Unforged r := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact (hU r hr).of_sent rfl
    · exact (hK.recvU r hr).of_sent rfl
  have hleft : ∀ t0 ch0, n0.chain.statusOf c0 = .challenged t0 ch0 → ch0.state = st 2 OS →
      n.chain.statusOf c0 = n0.chain.statusOf c0 → n.chain.mode c0 = .challenge := by
    intro t0 ch0 h0 hx hs
    have hlive := hK.liveA hI0 hnow (hs.trans h0) hx
    rw [Adjudicator.mode_eq, hs, h0, ChannelStatus.mode_challenged, if_neg (not_le.mpr hlive)]
  have hfin' : IsFin (n.chain.statusOf c0) → ¬ (n.chain.statusOf c0).IsOpen n.chain.now := by
    rintro ⟨t, f, o, hf⟩ ho
    rw [hf] at ho
    exact ho (by simp only [ChannelStatus.mode])
  rcases status_cases h with heq | ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩ |
      ⟨P, cand, rfl, hsup, hopen, hlt, hst⟩ | ⟨ss, rfl, hcp, hst⟩ | ⟨o0, o', hfo, hst⟩
  · refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => by rw [heq]; exact hK.noFin t f o, fun t ch hc => by rw [heq] at hc; exact hK.chOut t ch hc,
      fun t ch hc hx => ?_, fun t0 ch0 h0 hx => by rw [heq]; exact hK.left t0 ch0 h0 hx,
      by rw [heq]; exact hK.recR⟩
    rw [heq] at hc ⊢
    exact (hK.chA t ch hc hx).imp_right fun ⟨h6, hs⟩ => ⟨h6, hs.mono hrec⟩
  · have hnf : ¬ IsFin (n.chain.statusOf c0) := fun hf => by
      rw [mode_fin hf] at hmode
      rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
    have hge : (n.chain.statusOf c0).turnNumRecord ≤ cand.turnNum := by
      rcases hmode with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · exact le_of_lt h
    have hc := hcand P cand rfl
    refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => (by rw [hst]; intro h; cases h), fun t ch hch => ?_, fun t ch hch hx => ?_,
      fun t0 ch0 h0 hx => ?_, ?_⟩
    · rw [hst] at hch
      obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hch
      exact ⟨hc, rfl⟩
    · rw [hst] at hch
      obtain ⟨rfl, rfl⟩ := ChannelStatus.challenged.inj hch
      refine Or.inr ⟨Nat.add_le_add_right hK.now0 6, ?_⟩
      obtain ⟨ss, rfl, hss, hcs, hall⟩ := cons_support hsup
      exact ⟨ss, List.mem_append_left _ (List.mem_singleton_self ss), hss.trans hx, q0_mem hall hcs⟩
    · right; left
      rw [hst]
      show t0 < cand.turnNum
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0 | hf0
      · rw [Adjudicator.mode_eq, hs0, h0] at hmode
        rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
        · have := hleft t0 ch0 h0 hx hs0
          rw [Adjudicator.mode_eq, hs0, h0] at this
          rw [this] at hm; cases hm
        · simpa only [ChannelStatus.turnNumRecord_challenged] using hr
      · exact lt_of_lt_of_le hlt0 hge
      · exact absurd hf0 hnf
    · rcases hK.recR with hR | hf0
      · left; rw [hst]; exact le_trans hR hge
      · exact absurd hf0 hnf
  · have hnf : ¬ IsFin (n.chain.statusOf c0) := fun hf => hfin' hf hopen
    refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => (by rw [hst]; intro h; cases h), fun t ch hc => (by rw [hst] at hc; cases hc),
      fun t ch hc _ => (by rw [hst] at hc; cases hc), fun t0 ch0 h0 hx => ?_, ?_⟩
    · right; left
      rw [hst]
      show t0 < cand.turnNum
      rcases hK.left t0 ch0 h0 hx with hs0 | hlt0 | hf0
      · rw [hs0, h0] at hlt; simpa only [ChannelStatus.turnNumRecord_challenged] using hlt
      · exact lt_trans hlt0 hlt
      · exact absurd hf0 hnf
    · rcases hK.recR with hR | hf0
      · left; rw [hst]; exact le_trans hR (le_of_lt hlt)
      · exact absurd hf0 hnf
  · -- a conclusion: `p0` signed no final state
    exfalso
    obtain ⟨hc, hfin, hall⟩ := hcp
    obtain ⟨y, hy, hys⟩ := (hU ss (List.mem_singleton_self ss)).1 (p0_mem hall hc)
    rw [hK.sent] at hy
    rcases hI0.sentOK y hy with rfl | rfl | rfl <;> rw [← hys] at hfin <;> cases hfin
  · -- a payout: the status was final; the finalized outcome stays
    obtain ⟨hF, hcases⟩ := withOutcome_cases (o' := o') hfo
    rw [← hst] at hF hcases
    refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o hf => ?_, fun t ch hc => absurd hc (isFin_not_challenged hF),
      fun t ch hc _ => absurd hc (isFin_not_challenged hF), fun _ _ _ _ => Or.inr (Or.inr hF),
      Or.inr hF⟩
    rcases hcases t f o hf with ⟨ch, hch, hd, rfl⟩ | ⟨o1, hf1⟩
    · rcases (hK.chOut t ch hch).1 with h1 | h1 | h1
      · exact Or.inl (by rw [h1]; rfl)
      · exact absurd hd (not_le.mpr (hK.liveA hI0 hnow hch h1))
      · exact Or.inr (by rw [h1]; rfl)
    · exact hK.noFin t f o1 hf1

/-- `KP` as a step invariant of a sub-round of pure adversary play that ends
    before `n0`'s clock plus 2. -/
theorem KP.stepInv {n0 : NetworkState Nat p0} {R : Nat} (hI0 : InvP n0) {Eend : Time}
    (hE : Eend < n0.chain.now + 2) :
    TN.StepInvariant appsC (fun n => n.chain.now ≤ Eend) (KP n0 R) (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {n ss} _ hfe hK => by
    rw [NetworkState.applyAdv_deliver]
    refine ⟨fun r hr => ?_, hK.sent, fun r hr => List.mem_cons_of_mem _ (hK.recv r hr), hK.now0,
      hK.noFin, hK.chOut, fun t ch hc hx => (hK.chA t ch hc hx).imp_right fun ⟨h6, hs⟩ =>
        ⟨h6, hs.mono fun r hr => List.mem_cons_of_mem _ hr⟩, hK.left, hK.recR⟩
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
    cases happ : n.chain.apply appsC caller op with
    | none => rw [NetworkState.applyAdv_chain_none appsC happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_chain_some appsC happ]
      refine stepK hI0 hK (lt_of_le_of_lt hg hE) happ hfe.1.2 (fun P cand hop => ?_)
        (Adjudicator.apply_now_le happ)
      subst hop
      obtain ⟨⟨-, hsup, -, -⟩, -⟩ := Adjudicator.challenge_some happ
      exact cand_P (fun s hs => hI0.sentOK s (hK.sent ▸ hs)) hsup hfe.1.2

theorem KP.nil {n0 n n' : NetworkState Nat p0} {R : Nat} {t : Time} (hI0 : InvP n0)
    (hseq : TN.RoundSeq appsC t [] n n') (hK : KP n0 R n) (hE : n'.chain.now < n0.chain.now + 2) :
    KP n0 R n' :=
  Threat.RoundSeq.nil_invariant hseq (KP.stepInv hI0 hE) hK

/-- At the end of a round from `n0`, `OS` is not finalized. -/
theorem notFinP {n0 n : NetworkState Nat p0} {R : Nat} (hI0 : InvP n0)
    (hK : KP n0 R n) (hnow : n.chain.now < n0.chain.now + 2) : ¬ n.Finalized c0 OS := by
  intro hf
  rw [finalized_iff] at hf
  cases hs : n.chain.statusOf c0 with
  | «open» t => rw [hs] at hf; simp only [ChannelStatus.finalizedWith, reduceCtorEq] at hf
  | finalized t f o =>
    rw [hs, ChannelStatus.finalizedWith_finalized] at hf
    rcases hK.noFin t f o hs with h | h <;> rw [h] at hf <;>
      exact absurd (Option.some.inj hf) (by decide)
  | challenged t ch =>
    rw [hs, ChannelStatus.finalizedWith_challenged] at hf
    split at hf
    · rename_i hd
      rcases (hK.chOut t ch hs).1 with h | h | h
      · rw [h] at hf; exact absurd (Option.some.inj hf) (by decide)
      · exact absurd hd (not_le.mpr (hK.liveA hI0 hnow hs h))
      · rw [h] at hf; exact absurd (Option.some.inj hf) (by decide)
    · cases hf

/-- `p0` may sign `X`: a move by the rules after `S'`, whose support it holds,
    at a turn where it signed no other state. -/
theorem send_feasible {n : NetworkState Nat p0} (hI : InvP n) (hh : SHeld n) :
    (HonestMove.send (st 3 OX)).Feasible appsC n := by
  refine (HonestMove.Feasible_send appsC n (st 3 OX)).mpr
    ⟨fun ⟨s, hs, _, hslot, hne⟩ => ?_, by decide, HonestSend.fundsCommitted_of_fundable (by decide),
      fun _ => ⟨⟨[both (st 2 OS)], st 2 OS, fun ss hss => ?_, by decide, rfl, rfl⟩,
        [hX], fun ss hss => .inr (by rw [List.mem_singleton.1 hss]; rfl), by decide⟩,
      fun ⟨s, hs, _, htn, hne⟩ => ?_, fun ⟨s, hs, hfb⟩ => ?_⟩
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact hne rfl
    · rcases hI.sentOK s hs with rfl | rfl | rfl
      · exact absurd hslot (by decide)
      · exact absurd hslot (by decide)
      · exact hne rfl
  · rw [List.mem_singleton.1 hss]
    exact holds_both hh ⟨sS, hI.sSin, rfl⟩
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact hne rfl
    · rcases hI.sentOK s hs with rfl | rfl | rfl
      · exact absurd htn (by decide)
      · exact absurd htn (by decide)
      · exact hne rfl
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact absurd hfb (by decide)
    · rcases hI.sentOK s hs with rfl | rfl | rfl <;> exact absurd hfb (by decide)

theorem counter_feasible {n : NetworkState Nat p0} (hr : rX ∈ n.received) (hs : sX ∈ n.sent) :
    (HonestMove.chain opP).Feasible appsC n := by
  refine (HonestMove.Feasible_chain _ _ _).2 fun ss hss => ?_
  rw [opP, Op.proofStates, List.mem_singleton] at hss
  subst hss
  exact holds_both ⟨rX, hr, rfl, by decide⟩ ⟨sX, hs, rfl⟩

/-- `p0`'s answer turns a standing challenge below turn 3 into a challenge
    with `X` at turn 3. -/
theorem counter_apply {s : Adjudicator Nat} {t0 : Nat} {ch : Challenge Nat}
    (hs : s.statusOf c0 = .challenged t0 ch) (hd : s.now < ch.deadline) (ht : t0 < 3) :
    s.apply appsC p0 opP = some (s.setStatus c0 (.challenged 3 ⟨st 3 OX, s.now + 6⟩)) := by
  have hmode : s.mode c0 = .challenge := by
    rw [Adjudicator.mode_eq, hs, ChannelStatus.mode_challenged, if_neg (not_le.mpr hd)]
  rw [opP, Adjudicator.apply_challenge_equation, dif_pos ⟨by decide, by decide, rfl, Or.inr ⟨hmode, by
    rw [hs, ChannelStatus.turnNumRecord_challenged]; exact ht⟩⟩]
  rfl

open Classical in
/-- `p0`'s move: sign `X` once it holds `q0`'s signature on `S'`, then answer
    every challenge with `S'`. -/
noncomputable def idealP (n : NetworkState Nat p0) : HonestMove Nat :=
  if sX ∈ n.sent then
    match n.chain.statusOf c0 with
    | .challenged _ ch => if ch.state = st 2 OS then .chain opP else .wait 0
    | _ => .wait 0
  else if SHeld n then .send (st 3 OX) else .wait 0

open Classical in
/-- The strategy: `idealP` where it is feasible, a wait otherwise. -/
noncomputable def σP : Strategy Nat p0 := fun n =>
  if (idealP n).Feasible appsC n then idealP n else .wait 0

theorem σP_feasible (n : NetworkState Nat p0) : (σP n).Feasible appsC n := by
  unfold σP
  split
  · assumption
  · trivial

/-- The three shapes of `σP n`. -/
theorem σP_cases {n : NetworkState Nat p0} (hI : InvP n) :
    (σP n = .wait 0 ∧
      (sX ∈ n.sent → ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state ≠ st 2 OS) ∧
      (sX ∉ n.sent → ¬ SHeld n)) ∨
    (sX ∉ n.sent ∧ σP n = .send (st 3 OX)) ∨
    (sX ∈ n.sent ∧ ∃ t ch, n.chain.statusOf c0 = .challenged t ch ∧ ch.state = st 2 OS ∧
      σP n = .chain opP) := by
  have hwait : idealP n = .wait 0 → σP n = .wait 0 := fun h => by
    unfold σP; rw [h]; exact ite_self _
  by_cases hs : sX ∈ n.sent
  · cases hst : n.chain.statusOf c0 with
    | «open» t =>
      exact Or.inl ⟨hwait (by unfold idealP; rw [if_pos hs, hst]), fun _ t ch h => (by cases h),
        fun h => absurd hs h⟩
    | finalized t f o =>
      exact Or.inl ⟨hwait (by unfold idealP; rw [if_pos hs, hst]), fun _ t ch h => (by cases h),
        fun h => absurd hs h⟩
    | challenged t ch =>
      by_cases hx : ch.state = st 2 OS
      · refine Or.inr (Or.inr ⟨hs, t, ch, rfl, hx, ?_⟩)
        have hid : idealP n = .chain opP := by
          unfold idealP; rw [if_pos hs, hst]; simp only [if_pos hx]
        unfold σP
        rw [hid, if_pos (counter_feasible hI.xin hs)]
      · refine Or.inl ⟨hwait (by unfold idealP; rw [if_pos hs, hst]; simp only [if_neg hx]),
          fun _ t' ch' h => ?_, fun h => absurd hs h⟩
        cases h; exact hx
  · by_cases hh : SHeld n
    · refine Or.inr (Or.inl ⟨hs, ?_⟩)
      have hid : idealP n = .send (st 3 OX) := by unfold idealP; rw [if_neg hs, if_pos hh]
      unfold σP
      rw [hid, if_pos (send_feasible hI hh)]
    · exact Or.inl ⟨hwait (by unfold idealP; rw [if_neg hs, if_neg hh]), fun h => absurd h hs,
        fun _ => hh⟩

theorem bound6 {a b : Nat} (h : a < b + 2) : a + 4 ≤ b + 6 := by omega
theorem bound4 {a b : Nat} (h : a < b + 2) : a + 2 ≤ b + 4 := by omega

/-- One round of `σP`: `OS` is not finalized at its end, and `InvP` holds at
    the start of the next round. -/
theorem roundP {n0 n' : NetworkState Nat p0} (hI0 : InvP n0)
    (hround : TN.Round appsC (σP n0) n0 n') :
    ¬ n'.Finalized c0 OS ∧ InvP (n'.applyHonest (σP n0)) := by
  have hbound := round_bound hround
  have hK0 := KP.start hI0
  have hnext : ∀ {R : Nat} (hK : KP n0 R n') (m : HonestMove Nat)
      (hsent : ∀ s ∈ (n'.applyHonest m).sent, s ∈ n'.sent ∨ s = sX)
      (hsub : ∀ s ∈ n'.sent, s ∈ (n'.applyHonest m).sent)
      (hrecv : (n'.applyHonest m).received = n'.received)
      (hchain : (n'.applyHonest m).chain.statusOf c0 = n'.chain.statusOf c0 ∧
        (n'.applyHonest m).chain.now = n'.chain.now)
      (hS0 : ∀ t ch, n'.chain.statusOf c0 = .challenged t ch → ch.state = st 2 OS →
        n'.chain.statusOf c0 = n0.chain.statusOf c0 →
        (n'.applyHonest m).chain.now + 2 ≤ ch.deadline ∧
          (sX ∉ (n'.applyHonest m).sent → (n'.applyHonest m).chain.now + 4 ≤ ch.deadline ∧
            SHeld (n'.applyHonest m))),
      InvP (n'.applyHonest m) := by
    intro R hK m hsent hsub hrecv hchain hS0
    refine ⟨fun r hr => ?_, by rw [hrecv]; exact hK.recv _ hI0.xin,
      hsub _ (by rw [hK.sent]; exact hI0.sSin), fun s hs => ?_, fun t f o => ?_, fun t ch hc => ?_,
      fun t ch hc hx => ?_⟩
    · rw [hrecv] at hr; exact (hK.recvU r hr).mono hsub
    · rcases hsent s hs with hs | rfl
      · rw [hK.sent] at hs; exact hI0.sentOK s hs
      · exact Or.inr (Or.inr rfl)
    · rw [hchain.1]; exact hK.noFin t f o
    · rw [hchain.1] at hc; exact hK.chOut t ch hc
    · rw [hchain.1] at hc
      rcases hK.chA t ch hc hx with h0 | ⟨h6, hsh⟩
      · exact hS0 t ch hc hx h0
      · rw [hchain.2]
        have : n'.chain.now + 4 ≤ ch.deadline := le_trans (bound6 hbound) h6
        exact ⟨le_trans (Nat.add_le_add_left (by decide) _) this,
          fun _ => ⟨this, hsh.mono fun r hr => by rw [hrecv]; exact hr⟩⟩
  rcases σP_cases hI0 with ⟨hσ, hnx, hnh⟩ | ⟨hns, hσ⟩ | ⟨hsa, t0, ch0, hs0, hx0, hσ⟩
  · rw [hσ] at hround ⊢
    have hK := KP.nil hI0 hround.1 hK0 hbound
    refine ⟨notFinP hI0 hK hbound, hnext hK _ (fun s hs => .inl hs) (fun s hs => hs) rfl
      ⟨by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf], by
        simp only [NetworkState.applyHonest, Adjudicator.tick_now]; rfl⟩ ?_⟩
    intro t ch hc hx h0
    rw [h0] at hc
    by_cases hsx : sX ∈ n0.sent
    · exact absurd hx (hnx hsx t ch hc)
    · exact absurd ((hI0.timing t ch hc hx).2 hsx).2 (hnh hsx)
  · rw [hσ] at hround ⊢
    have hK := KP.nil hI0 hround.1 hK0 hbound
    refine ⟨notFinP hI0 hK hbound, hnext hK _ ?_ ?_ rfl ⟨rfl, rfl⟩ ?_⟩
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
      have h4 := ((hI0.timing _ _ hc hx).2 hns).1
      rw [NetworkState.applyHonest_send]
      exact ⟨le_trans (bound4 hbound) h4, fun hn => absurd List.mem_cons_self hn⟩
  · rw [hσ] at hround ⊢
    rw [NetworkState.applyHonest_chain]
    obtain ⟨n1, hA, hB⟩ := Threat.Round.single hround
    have hnow1 : n1.chain.now ≤ n'.chain.now :=
      le_trans (NetworkState.applyAdv_now_le appsC n1 _) hB.now_le
    have hK1 := KP.nil hI0 hA hK0 (lt_of_le_of_lt hnow1 hbound)
    have htm := hI0.timing _ _ hs0 hx0
    have ht0 : t0 < 3 := by
      have := (hI0.chOut _ _ hs0).2
      rw [hx0] at this
      rw [this]; decide
    have hU : ∀ ss ∈ opP.proofStates, n1.Unforged ss := by
      intro ss hss
      rw [opP, Op.proofStates, List.mem_singleton] at hss
      subst hss
      exact (holds_both ⟨rX, hK1.recv _ hI0.xin, rfl, by decide⟩
        ⟨sX, by rw [hK1.sent]; exact hsa, rfl⟩).unforged hK1.recvU
    have hcand : ∀ P cand, opP = .challenge c0 P cand → CandOK cand := by
      intro P cand h
      injection h with _ _ hc
      subst hc
      exact Or.inr (Or.inr rfl)
    have hKL : KP n0 (t0 + 1) (n1.applyAdv appsC (.land opP)) := by
      have hland : ∀ (hK1' : KP n0 (t0 + 1) n1),
          KP n0 (t0 + 1) (n1.applyAdv appsC (.land opP)) := fun hK1' => by
        cases happ : n1.chain.apply appsC p0 opP with
        | none =>
          rw [NetworkState.applyAdv_land_none appsC happ]
          exact hK1'
        | some s' =>
          rw [NetworkState.applyAdv_land_some appsC happ]
          exact stepK hI0 hK1' (lt_of_le_of_lt hnow1 hbound) happ hU hcand
            (Adjudicator.apply_now_le happ)
      rcases hK1.left t0 ch0 hs0 hx0 with heq | hlt | hf
      · have happ := counter_apply (s := n1.chain) (by rw [heq, hs0])
          (lt_of_lt_of_le (lt_of_le_of_lt hnow1 hbound) htm.1) ht0
        rw [NetworkState.applyAdv_land_some appsC happ]
        exact (stepK hI0 hK1 (lt_of_le_of_lt hnow1 hbound) happ hU hcand (le_of_eq rfl)).lower
          (Or.inl (by simp only [Adjudicator.statusOf_setStatus, if_true,
            ChannelStatus.turnNumRecord_challenged]; omega))
      · exact hland (hK1.lower (Or.inl hlt))
      · exact hland (hK1.lower (Or.inr hf))
    have hK := KP.nil hI0 hB hKL hbound
    refine ⟨notFinP hI0 hK hbound, ?_⟩
    have := hnext hK (HonestMove.chain opP)
      (fun s hs => .inl (by rwa [NetworkState.applyHonest_chain] at hs))
      (fun s hs => by rwa [NetworkState.applyHonest_chain])
      (by rw [NetworkState.applyHonest_chain])
      (by rw [NetworkState.applyHonest_chain]; exact ⟨rfl, rfl⟩) ?_
    · rwa [NetworkState.applyHonest_chain] at this
    intro t ch hc hx h0
    rcases hK.recR with hr | ⟨t', f, o, hf⟩
    · rw [h0, hs0] at hr
      simp only [ChannelStatus.turnNumRecord_challenged] at hr
      omega
    · rw [hc] at hf; cases hf

theorem invP_net : InvP net := by
  refine ⟨invA_net.recvU, by decide, by decide, fun s hs => ?_, fun t f o h => ?_,
    fun t ch h => ?_, fun t ch h hx => ?_⟩
  · simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rw [net_status] at h; cases h
  · rw [net_status] at h; cases h
  · rw [net_status] at h; cases h

theorem prevents_OS : Prevents appsC TN (fun n => n.Finalized c0 OS) net := by
  have hrun : ∀ {n1}, Run appsC TN σP net n1 → InvP n1 := by
    intro n1 h
    induction h with
    | refl => exact invP_net
    | round _ hr ih => exact (roundP ih hr).2
  exact ⟨σP, σP_feasible, fun n1 n2 hr hround => (roundP (hrun hr) hround).1⟩

/-- `OH` is the only outcome that can be enabled. -/
theorem enabled_eq {Ω : Outcome Nat} (hE : Enabled appsC TN c0 Ω net) : Ω = OH := by
  by_contra hH
  by_cases hS : Ω = OS
  · subst hS; exact hE prevents_OS
  · exact hE (prevents_wait hH hS)

/-! ## The statement fails -/

/-- `Spec.finalizable_or_two_enabled` before the exit-strategy rule added on
    2026-11-02: the enabled outcomes against every strategy at once. -/
def Literal_finalizable_or_two_enabled : Prop :=
  ∀ (apps : Apps Nat) {p : Participant} (T : Threat Nat p)
    (A : Assumptions apps p T) (dest : Participant → Nat)
    (net : Nitro.ReachableParticipant apps (T.noOwnViolation dest))
    (c : TimedChannel T.ε)
    (hrules : (∃ vt, apps (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps (c : FixedPart).appDef = consensusRules)
    (hdes : Desirable apps (c : FixedPart).appDef dest)
    (hp : p ∈ (c : FixedPart).participants)
    (hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof candidate = true ∧
      candidate.channel = (c : FixedPart))
    (hpend : net.state.DeadlineAfter (c : FixedPart) T.ε),
    (∃ Ω, Finalizable apps (T.noOwnViolation dest) (c : FixedPart) Ω net.state) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω1 net.state ∧
      Enabled apps (T.noOwnViolation dest) (c : FixedPart) Ω2 net.state)

theorem finalizable_or_two_enabled_false : ¬ Literal_finalizable_or_two_enabled := by
  intro h
  rcases h appsC T0 A0 destS ⟨net, net_reachable⟩ tc0 (Or.inr rfl) appsC_desirable
      (by decide) ⟨[both (st 1 OH)], st 1 OH, holds_hh, by decide, rfl⟩ net_deadlineAfter with
    ⟨Ω, hΩ⟩ | ⟨Ω1, Ω2, hne, hE1, hE2⟩
  · exact not_finalizable Ω hΩ
  · exact hne ((enabled_eq hE1).trans (enabled_eq hE2).symm)

#print axioms net_reachable
#print axioms finalizable_or_two_enabled_false

end ArmadaLean.Nitro.CounterexampleProposalEscape
