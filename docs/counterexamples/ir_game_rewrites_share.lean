/-
  Failure test: a game whose rules let the opponent rewrite `p`'s share
  (Nitro-24, Nitro:653-658). One entry in the catalogue of compliant but
  undesirable apps, armada-laconic `labbook/2026-10-30-app-classes-ic-ir.md`
  §5.

  The app is a real ForceMove app: `forceMoveRules vtAll`, whose game
  library accepts every transition (`vtAll`). It meets `Rules.SupportWindow`
  (`forceMoveRules_supportWindow`), the premise `happ` of the operator
  ruling of 2026-11-01. It still refutes both Nitro-24 statements
  (`finalizable_or_two_enabled_false`, `single_enabled_is_finalizable_false`).

  What fails is IR in the sense of the labbook §2 (operator, 2026-10-30): "from
  any state, an online honest participant can enforce at least what its
  holdings give it" (ForceMove:410-416, 125-130). An open game is acceptable;
  this app fails because `p` can never take its own assets out: each outcome
  that pays `p` is overridden. The violating step is exact: the opponent's
  valid move can cut `p`'s share, so `p` must answer every challenge and can
  never let one expire. This is not §5 "unbound griefing": that case re-posts
  a stale outcome at a higher turn, a support-rule failure that
  `SupportWindow` now excludes. Here every move of the opponent is a valid
  game move, signed at its own turn.

  The channel `c0` has the participants `[q0, p0]`, so `q0` moves at even
  turns and the honest `p0` at odd turns (`n = 2`). At `net1`, `p0` sent `s1`
  (turn 1, outcome `O1`, which pays `p0` 5) and received `r0` (turn 0, signed
  by `q0`). `p0` holds the support `[r0, s1]` of `s1`.
  * `O1` is enabled (`enabled_O1`): the adversary challenges with `[r0, s1]`.
    `p0` cannot answer, because an answer needs a state of `q0` at turn 2.
  * No outcome but `O1` is enabled (`prevents_other`): `p0` answers every
    challenge whose outcome is `X ≠ O1` with its own next move, which pays it
    5 again. Each answer takes two rounds (sign, then checkpoint), and
    `challengeDuration = 3 * ε` leaves room for them.
  * No outcome is finalizable (`not_finalizable`): after `p0`'s calls land,
    the adversary answers every challenge with the target outcome `Ω` by a
    move at the next turn whose outcome cuts `p0`'s share. `p0` cannot use a
    final state to exit (ForceMove:887-888): a final state keeps the outcome
    of the state before it, and that state is the adversary's.
  So `p0` has no finalizable outcome and exactly one enabled outcome.

  The last section drafts IR as a predicate (`AppIR`, no statement takes it)
  and proves it for ForceMove apps whose game library takes nothing from a
  non-mover (`forceMove_IR`, `NoTakeFromNonMover`) and for the consensus app
  (`consensus_IR`). `appsB_not_IR`: `p0` holds a support that pays it 5 and
  cannot finalize any outcome that pays it 5. `vtAll_not_noTake`: `q0`'s
  valid move cuts `p0`'s payment.

  The construction does not use the round clock: every round it builds
  advances the clock by 1, and `ε = 2`.

  This file is not part of the `ArmadaLean` library. Check it with
  `lake env lean docs/counterexamples/ir_game_rewrites_share.lean`.
  The theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import ArmadaLean.Spec.Nitro.Liveness

namespace ArmadaLean.Nitro.CounterexampleIRGame

open ArmadaLean.Nitro

/-! ## The instance -/

def q0 : Participant := ⟨0⟩
def p0 : Participant := ⟨1⟩

theorem p0_ne_q0 : p0 ≠ q0 := by decide

/-- The destination of `p0` and the destination of `q0`. -/
def dP : Address Bool := .external true
def dQ : Address Bool := .external false

/-- The outcome of `p0`'s states: 5 to each side. -/
def O1 : Outcome Bool := .allocation [alloc dP 5, alloc dQ 5]
/-- Two outcomes that cut `p0`'s share. -/
def cut1 : Outcome Bool := .allocation [alloc dP 0, alloc dQ 10]
def cut2 : Outcome Bool := .allocation [alloc dP 1, alloc dQ 9]

/-- The adversary's answer outcome against the target `Ω`: a cut, not `Ω`. -/
def cutFor (Ω : Outcome Bool) : Outcome Bool := if Ω = cut1 then cut2 else cut1

theorem cutFor_ne (Ω : Outcome Bool) : cutFor Ω ≠ Ω := by
  unfold cutFor
  by_cases h : Ω = cut1
  · subst h; decide
  · rw [if_neg h]; exact fun h' => h h'.symm

/-- A virtual channel: no transfer and no reclaim writes its status. `q0`
    moves at even turns, `p0` at odd turns. -/
def c0 : FixedPart :=
  { participants := [q0, p0], nonce := 0, appDef := ⟨0⟩, challengeDuration := 6, kind := .virtual }

theorem c0_not_ledger : c0.kind ≠ .ledger := by decide

theorem c0_n : c0.n = 2 := rfl

/-- The game library that accepts every transition. -/
def vtAll : State Bool → State Bool → Bool := fun _ _ => true

def appsB : Apps Bool := fun _ => forceMoveRules vtAll

theorem appsB_supportWindow : (appsB c0.appDef).SupportWindow :=
  forceMoveRules_supportWindow vtAll

/-- The non-final state of `c0` at turn `k` with the outcome `o`. -/
def st (k : Nat) (o : Outcome Bool) : State Bool :=
  { channel := c0, turnNum := k, outcome := o, isFinal := false, appData := .opaque 0 }

def r0 : SignedState Bool := ⟨st 0 O1, [q0]⟩
def s1 : SignedState Bool := ⟨st 1 O1, [p0]⟩

/-- The adversary: any call by another participant that forges no
    signature of `p0`, any unforged delivery, any tick. -/
def T0 : Threat Bool p0 where
  feasible net m := match m with
    | .chain caller op => caller ≠ p0 ∧ ∀ ss ∈ op.proofStates, net.Unforged ss
    | .deliver ss => net.Unforged ss
    | .tick _ => True
    | .land _ => True
  ε := 2
  ε_pos := Nat.two_pos

theorem A0 : Assumptions appsB p0 T0 where
  unforgeable := fun _ _ _ h => h.2
  unforgeableDeliver := fun _ _ h => h
  notHonest := fun _ _ _ h => h.1
  capable := fun _ _ _ h1 h2 => ⟨h1, h2⟩
  capableDeliver := fun _ _ h => h
  capableTick := fun _ _ => trivial
  clockRuns := le_refl 2

/-- The channel with its timing fact: `2 * ε ≤ 6`. -/
def tc0 : TimedChannel T0.ε := ⟨c0, by decide⟩

/-- The round bound, read off a round. -/
theorem round_bound {apps : Apps Bool} {m : HonestMove Bool} {n n' : NetworkState Bool p0}
    (h : T0.Round apps m n n') : n'.chain.now < n.chain.now + 2 := h.2

/-- A round from a derivation that ends one tick later. -/
theorem mkRound {apps : Apps Bool} {m : HonestMove Bool} {n n' : NetworkState Bool p0}
    (hseq : T0.RoundSeq apps n.chain.now m.calls n n') (hnow : n'.chain.now = n.chain.now + 1) :
    T0.Round apps m n n' :=
  ⟨hseq, by rw [hnow]; exact Nat.add_lt_add_left (show 1 < T0.ε by decide) _⟩

def net1 : NetworkState Bool p0 := ⟨Adjudicator.genesis, [r0], [s1]⟩

theorem unforged_r0 (n : NetworkState Bool p0) : n.Unforged r0 :=
  ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0, fun v hv => by simp [r0, st, State.voucher?] at hv⟩

theorem send_feasible :
    (HonestMove.send (st 1 O1)).Feasible (⟨Adjudicator.genesis, [r0], []⟩ : NetworkState Bool p0) :=
  (HonestMove.Feasible_send _ _).mpr
    ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide)⟩

theorem net1_reachable : (Nitro.participant appsB T0).Reachable net1 := by
  refine ⟨⟨Adjudicator.genesis, [], []⟩, rfl, ?_⟩
  refine .tail (.tail .refl ?_) (Or.inl ⟨.send (st 1 O1), send_feasible, rfl⟩)
  exact Or.inr (Or.inr (Or.inl ⟨.deliver r0, unforged_r0 _, fun op h => (by cases h), rfl⟩))

theorem supports_r0s1 : (appsB c0.appDef).supports c0 [r0, s1] (st 1 O1) = true := by decide

theorem holds_r0s1 : ∀ ss ∈ [r0, s1], net1.Holds ss := by
  intro ss hss
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hss
  rcases hss with rfl | rfl
  · exact holds_of_mem_received (List.mem_singleton_self _)
  · refine ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s1, List.mem_singleton_self _, rfl⟩,
      fun v hv => by simp [s1, st, State.voucher?] at hv⟩

/-! ## Supports of `c0` -/

theorem mover_c0 {s : State Bool} (hc : s.channel = c0) :
    s.mover = some (if s.turnNum % 2 = 0 then q0 else p0) := by
  unfold State.mover
  rw [hc]
  rcases Nat.mod_two_eq_zero_or_one s.turnNum with h | h <;> simp [h, c0, FixedPart.n]

theorem byMover_even {m : SignedState Bool} (hc : m.state.channel = c0) (h : m.ByMover)
    (he : m.state.turnNum % 2 = 0) : q0 ∈ m.signers := by
  obtain ⟨w, hw, hmem⟩ := h
  rw [mover_c0 hc, if_pos he] at hw
  obtain rfl := Option.some.inj hw
  exact hmem

theorem byMover_odd {m : SignedState Bool} (hc : m.state.channel = c0) (h : m.ByMover)
    (ho : m.state.turnNum % 2 = 1) : p0 ∈ m.signers := by
  obtain ⟨w, hw, hmem⟩ := h
  rw [mover_c0 hc, if_neg (by omega)] at hw
  obtain rfl := Option.some.inj hw
  exact hmem

/-- A support of `c0` under `appsB`: two consecutive moves, each signed by
    its mover, the second the candidate. -/
structure Two (P : SupportProof Bool) (cand : State Bool) (m0 m1 : SignedState Bool) : Prop where
  eq : P = [m0, m1]
  last : m1.state = cand
  ch0 : m0.state.channel = c0
  ch1 : m1.state.channel = c0
  turn : m1.state.turnNum = m0.state.turnNum + 1
  mv0 : m0.ByMover
  mv1 : m1.ByMover
  fin : m1.state.isFinal = true → m1.state.outcome = m0.state.outcome

theorem fm2 {P : SupportProof Bool} {cand : State Bool}
    (h : (appsB c0.appDef).supports c0 P cand = true) : ∃ m0 m1, Two P cand m0 m1 := by
  have hv := forceMove_supports_valid_run vtAll c0 P cand h
  have hk := forceMove_conclude_keeps_outcome vtAll c0 P cand h
  have h' := h
  simp only [appsB, forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨hlen, hhead⟩, -⟩, hch⟩, -⟩ := h'
  obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, P = [m0, m1] := by
    rcases P with _ | ⟨m0, _ | ⟨m1, _ | ⟨m2, rest⟩⟩⟩ <;> simp [c0, FixedPart.n] at hlen ⊢
  obtain ⟨-, hstep, ml, hml, hmls⟩ := hv
  obtain ⟨-, ht, hmv1, -⟩ := hstep 0 m0 m1 rfl rfl
  have hfin := (hk 0 m0 m1 rfl rfl).1
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hml
  subst hml
  refine ⟨m0, m1, rfl, hmls, hch m0 (by simp), hch m1 (by simp), ht, ?_, hmv1, hfin⟩
  simp only [List.head?_cons, Option.all_some] at hhead
  exact (SignedState.byMover_iff _).1 hhead

/-- A state `p0` holds with a signature of `q0` is a received state with it. -/
theorem held_q {n : NetworkState Bool p0} {ss : SignedState Bool} (h : n.Holds ss)
    (hq : q0 ∈ ss.signers) : ∃ r ∈ n.received, r.state = ss.state ∧ q0 ∈ r.signers := by
  rcases h.1 q0 hq with ⟨hqp, -⟩ | hr
  · exact absurd hqp.symm p0_ne_q0
  · exact hr

/-- `q0` is a participant of `c0`, so a conclusion proof of `c0` carries
    its signature. -/
theorem conclusion_q0 {ss : SignedState Bool} (h : ConclusionProof c0 ss) :
    q0 ∈ ss.signers ∧ ss.state.isFinal = true := by
  obtain ⟨hch, hfin, hall⟩ := h
  exact ⟨hall q0 (by rw [hch]; decide), hfin⟩

theorem conclusion_p0 {ss : SignedState Bool} (h : ConclusionProof c0 ss) : p0 ∈ ss.signers := by
  obtain ⟨hch, -, hall⟩ := h
  exact hall p0 (by rw [hch]; decide)

/-- One successful operation on `c0`: the status it leaves. A transfer or
    a reclaim of the virtual `c0` reverts. -/
theorem status_cases {s s' : Adjudicator Bool} {caller : Participant} {op : Op Bool}
    (h : s.apply appsB caller op = some s') :
    s'.statusOf c0 = s.statusOf c0 ∨
    (∃ P cand, op = .challenge c0 P cand ∧ (appsB c0.appDef).supports c0 P cand = true ∧
      cand.channel = c0 ∧
      ((s.mode c0 = .open ∧ (s.statusOf c0).turnNumRecord ≤ cand.turnNum) ∨
        (s.mode c0 = .challenge ∧ (s.statusOf c0).turnNumRecord < cand.turnNum)) ∧
      s'.statusOf c0 = .challenged cand.turnNum ⟨cand, s.now + 6⟩) ∨
    (∃ P cand, op = .checkpoint c0 P cand ∧ (appsB c0.appDef).supports c0 P cand = true ∧
      (s.statusOf c0).IsOpen s.now ∧ (s.statusOf c0).turnNumRecord < cand.turnNum ∧
      s'.statusOf c0 = .open cand.turnNum) ∨
    (∃ ss, op = .conclude c0 ss ∧ ConclusionProof c0 ss) := by
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
    | challenge c' P cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hsup, hcc, hmode⟩, rfl⟩ := Adjudicator.challenge_some h
      exact Or.inr (Or.inl ⟨P, cand, rfl, hsup, hcc, hmode, by simp [c0]⟩)
    | checkpoint c' P cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨hopen, hsup, -, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
      exact Or.inr (Or.inr (Or.inl ⟨P, cand, rfl, hsup, hopen, hlt, by simp⟩))
    | conclude c' ss =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hcp⟩, -⟩ := Adjudicator.conclude_some h
      exact Or.inr (Or.inr (Or.inr ⟨ss, rfl, hcp⟩))
  · exact Or.inl (statusOf_apply_of_not_targets h ht)

theorem holds_mono {n n' : NetworkState Bool p0} {ss : SignedState Bool}
    (hs : n.sent = n'.sent) (hr : ∀ r ∈ n.received, r ∈ n'.received) (h : n.Holds ss) :
    n'.Holds ss :=
  NetworkState.Holds.of_subset (fun _ hx => hs ▸ hx) hr h

theorem landed_now {n : NetworkState Bool p0} {op : Op Bool} (hop : ∀ dt, op ≠ .tick dt) :
    (n.applyAdv appsB (.land op)).chain.now = n.chain.now := by
  cases h : n.chain.apply appsB p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsB h]
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsB h]
    exact Adjudicator.apply_now_eq_of_not_tick hop h

/-! ## `O1` is enabled

The adversary challenges with `[r0, s1]` in the first round. A support at a
turn above 1 needs a state of `q0` at an even turn from 2 on, and `q0` signs
none. So the challenge stands, and the clock reaches its deadline. -/

def ch1 : Challenge Bool := ⟨st 1 O1, 6⟩

/-- Every support whose `q0`-signed states are `r0`'s state has a turn of
    at most 1. -/
theorem low_turn {P : SupportProof Bool} {cand : State Bool}
    (h : (appsB c0.appDef).supports c0 P cand = true)
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

/-- The challenge `ch1` stands against every operation whose `q0`-signed
    states are `r0`'s state. -/
theorem stay {s s' : Adjudicator Bool} {caller : Participant} {op : Op Bool}
    (hs : s.statusOf c0 = .challenged 1 ch1) (h : s.apply appsB caller op = some s')
    (hq : ∀ ss ∈ op.proofStates, q0 ∈ ss.signers → ss.state = st 0 O1) :
    s'.statusOf c0 = .challenged 1 ch1 := by
  rcases status_cases h with heq | ⟨P, cand, rfl, hsup, -, hmode, -⟩ |
      ⟨P, cand, rfl, hsup, -, hlt, -⟩ | ⟨ss, rfl, hcp⟩
  · rw [heq, hs]
  · have hlow := low_turn hsup hq
    rw [Adjudicator.mode_eq, hs] at hmode
    rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
    · simp only [ChannelStatus.mode] at hm
      split at hm <;> cases hm
    · simp only [ChannelStatus.turnNumRecord_challenged] at hr
      omega
  · have hlow := low_turn hsup hq
    rw [hs] at hlt
    simp only [ChannelStatus.turnNumRecord_challenged] at hlt
    omega
  · obtain ⟨hq0, hfin⟩ := conclusion_q0 hcp
    have h0 := hq ss (List.mem_singleton_self ss) hq0
    rw [h0] at hfin
    cases hfin

/-- The invariant of the play that finalizes `O1`. -/
structure InvE (n : NetworkState Bool p0) : Prop where
  recvQ : ∀ r ∈ n.received, q0 ∈ r.signers → r.state = st 0 O1
  recvU : ∀ r ∈ n.received, n.Unforged r
  status : n.chain.statusOf c0 = .challenged 1 ch1

theorem InvE.applyHonest {n : NetworkState Bool p0} (hI : InvE n) (m : HonestMove Bool) :
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
theorem roundE {n0 : NetworkState Bool p0} (hI0 : InvE n0) (t : Time) :
    ∀ (pending : List (Op Bool)), (∀ op ∈ pending, op.HonestFeasible n0) →
    ∀ m : NetworkState Bool p0, InvE m → m.sent = n0.sent →
      ∃ m', T0.RoundSeq appsB t pending m m' ∧ InvE m' ∧ m'.chain.now = m.chain.now + 1 ∧
        m'.sent = m.sent := by
  intro pending
  induction pending with
  | nil =>
    intro _ m hI _
    refine ⟨m.applyAdv appsB (.tick 1), .tick trivial (Or.inl rfl) .nil, ?_, rfl, rfl⟩
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
    have hI1 : InvE (m.applyAdv appsB (.land op)) := by
      cases happ : m.chain.apply appsB p0 op with
      | none => rw [NetworkState.applyAdv_land_none appsB happ]; exact hI
      | some s' =>
        rw [NetworkState.applyAdv_land_some appsB happ]
        refine ⟨fun x hx hxq => ?_, fun x hx => ?_, stay hI.status happ hq⟩
        · rcases List.mem_append.1 hx with hx | hx
          · exact hq x hx hxq
          · exact hI.recvQ x hx hxq
        · rcases List.mem_append.1 hx with hx | hx
          · exact ((hheld x hx).unforged hI0.recvU).of_sent hsent.symm
          · exact (hI.recvU x hx).of_sent rfl
    obtain ⟨m', hseq, hI', hnow, hs'⟩ := ih (fun o ho => hfeas o (List.mem_cons_of_mem _ ho))
      (m.applyAdv appsB (.land op)) hI1 (by rw [NetworkState.applyAdv_sent]; exact hsent)
    refine ⟨m', .land (l1 := []) (l2 := rest) rfl hseq, hI', ?_, ?_⟩
    · rw [hnow, landed_now hop.not_tick]
    · rw [hs', NetworkState.applyAdv_sent]

/-- Every feasible move of `p0` has a round, one tick long, that keeps
    `InvE`. -/
theorem roundE_exists {n : NetworkState Bool p0} (hI : InvE n) {m : HonestMove Bool}
    (hfeas : m.Feasible n) :
    ∃ n', T0.Round appsB m n n' ∧ InvE n' ∧ n'.chain.now = n.chain.now + 1 := by
  have hcalls : ∀ op ∈ m.calls, op.HonestFeasible n := by
    cases m with
    | react r => exact hfeas.1
    | wait dt => intro op hop; simp [HonestMove.calls] at hop
  obtain ⟨n', hseq, hI', hnow, -⟩ := roundE hI n.chain.now m.calls hcalls n hI rfl
  exact ⟨n', mkRound hseq hnow, hI', hnow⟩

/-- The adversary's challenge of the first round. -/
def opE : Op Bool := .challenge c0 [r0, s1] (st 1 O1)

def sChE : Adjudicator Bool := Adjudicator.genesis.setStatus c0 (.challenged 1 ch1)

theorem opE_apply : Adjudicator.genesis.apply appsB q0 opE = some sChE := by
  show Adjudicator.genesis.challenge appsB q0 c0 [r0, s1] (st 1 O1) = some sChE
  unfold Adjudicator.challenge
  rw [if_pos (by decide)]
  rfl

/-- The first round: the adversary challenges, then `p0`'s calls land, then
    one tick. -/
theorem roundE_first {m : HonestMove Bool} (hfeas : m.Feasible net1) :
    ∃ n', T0.Round appsB m net1 n' ∧ InvE n' ∧ n'.chain.now = 1 := by
  let n1 : NetworkState Bool p0 := net1.applyAdv appsB (.chain q0 opE)
  have hn1 : n1 = ⟨sChE, [r0, s1] ++ [r0], [s1]⟩ := by
    show net1.applyAdv appsB (.chain q0 opE) = _
    rw [NetworkState.applyAdv_chain_some appsB opE_apply]; rfl
  have hI1 : InvE n1 := by
    rw [hn1]
    refine ⟨fun x hx hxq => ?_, fun x hx => ?_, by decide⟩
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
  have hfeasE : T0.feasible net1 (.chain q0 opE) := by
    refine ⟨by decide, fun ss hss => ?_⟩
    simp only [opE, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with rfl | rfl
    · exact unforged_r0 _
    · exact ⟨fun _ => ⟨s1, List.mem_singleton_self _, rfl⟩, fun v hv => by simp [s1, st, State.voucher?] at hv⟩
  have hnow1 : n1.chain.now = 0 := by rw [hn1]; rfl
  refine ⟨n', mkRound (.other hfeasE (fun _ h => by cases h) (fun _ h => by cases h) hseq)
    (by rw [hnow, hnow1]; rfl), hI', by rw [hnow, hnow1]⟩

theorem enabled_O1 : Enabled appsB T0 c0 O1 net1 := by
  rintro ⟨σ, hσ, hprev⟩
  have hrun : ∀ k, ∃ n1 n2, Run appsB T0 σ net1 n1 ∧ T0.Round appsB (σ n1) n1 n2 ∧ InvE n2 ∧
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
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hI.status,
    ChannelStatus.finalizedWith_challenged]
  rw [if_pos (show ch1.deadline ≤ n2.chain.now from hle)]
  rfl

/-! ## No outcome is finalizable

The adversary has a set `G` of outcomes to avoid and an answer outcome
`A ∉ G`. It lands `p0`'s calls, then answers a challenge whose outcome is in
`G` by a move of `q0` at the next turn, with the outcome `A`. Then one tick.
For one target `Ω`, `G = {Ω}` and `A = A`. For IR, `G` is the set of
outcomes that pay `p0` at least 5, and `A = cut1`. -/

/-- A state that `q0` signed in the play: `r0`'s state, or a non-final
    state with the answer outcome `A`. -/
def QOK (A : Outcome Bool) (s : State Bool) : Prop :=
  s = st 0 O1 ∨ (s.outcome = A ∧ s.isFinal = false)

structure InvA (A : Outcome Bool) (n : NetworkState Bool p0) : Prop where
  recvQ : ∀ r ∈ n.received, q0 ∈ r.signers → QOK A r.state
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent1 : ∃ s ∈ n.sent, s.state = st 1 O1

/-- The statuses from which no outcome in `G` is finalized. -/
def SafeA (G : Outcome Bool → Prop) (x : ChannelStatus Bool) : Prop :=
  (∃ t, x = .open t) ∨ (∃ t ch, x = .challenged t ch ∧ ¬ G ch.state.outcome)

/-- A running challenge with an outcome in `G` at an odd turn `t`, where `p0`
    signed a non-final state of `c0` at turn `t`: the adversary can answer it. -/
def Answerable (G : Outcome Bool → Prop) (n : NetworkState Bool p0) : Prop :=
  ∃ t ch y, n.chain.statusOf c0 = .challenged t ch ∧ n.chain.now < ch.deadline ∧
    G ch.state.outcome ∧ t % 2 = 1 ∧ y ∈ n.sent ∧ y.state.channel = c0 ∧
    y.state.turnNum = t ∧ y.state.isFinal = false

theorem safeA_not_finalized {G : Outcome Bool → Prop} {Ω : Outcome Bool}
    {n : NetworkState Bool p0} (h : SafeA G (n.chain.statusOf c0)) (hG : G Ω) :
    ¬ n.Finalized c0 Ω := by
  intro hf
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf
  rcases h with ⟨t, ht⟩ | ⟨t, ch, ht, hne⟩
  · rw [ht] at hf; simp at hf
  · rw [ht] at hf
    simp only [ChannelStatus.finalizedWith_challenged] at hf
    split at hf
    · exact hne (Option.some.inj hf ▸ hG)
    · cases hf

theorem held_QOK {A : Outcome Bool} {n : NetworkState Bool p0} (hI : InvA A n)
    {ss : SignedState Bool} (h : n.Holds ss) (hq : q0 ∈ ss.signers) : QOK A ss.state := by
  obtain ⟨r, hr, hrs, hrq⟩ := held_q h hq
  rw [← hrs]; exact hI.recvQ r hr hrq

/-- A support of `c0` that `p0` holds, with an outcome in `G`: its candidate is
    at an odd turn, and `p0` signed a non-final state of `c0` at that turn. -/
theorem answerable_of_support {G : Outcome Bool → Prop} {A : Outcome Bool} (hA : ¬ G A)
    {n : NetworkState Bool p0} (hI : InvA A n)
    {P : SupportProof Bool} {cand : State Bool} (h : (appsB c0.appDef).supports c0 P cand = true)
    (hH : ∀ ss ∈ P, n.Holds ss) (hΩ : G cand.outcome) :
    cand.turnNum % 2 = 1 ∧ ∃ y ∈ n.sent, y.state.channel = c0 ∧ y.state.turnNum = cand.turnNum ∧
      y.state.isFinal = false := by
  obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht, hmv0, hmv1, hfin⟩⟩ := fm2 h
  have hH0 := hH m0 (by simp)
  have hH1 := hH m1 (by simp)
  subst hlast
  rcases Nat.mod_two_eq_zero_or_one m1.state.turnNum with he | ho
  · rcases held_QOK hI hH1 (byMover_even hc1 hmv1 he) with h0 | ⟨hcut, -⟩
    · have : m1.state.turnNum = 0 := by rw [h0]; rfl
      omega
    · exact absurd (hcut ▸ hΩ) hA
  · refine ⟨ho, ?_⟩
    obtain ⟨y, hy, hys⟩ := (hH1.unforged hI.recvU).1 (byMover_odd hc1 hmv1 ho)
    cases hf : m1.state.isFinal with
    | false => exact ⟨y, hy, by rw [hys]; exact hc1, by rw [hys], by rw [hys]; exact hf⟩
    | true =>
      have hout := hfin hf
      have he0 : m0.state.turnNum % 2 = 0 := by omega
      rcases held_QOK hI hH0 (byMover_even hc0 hmv0 he0) with h0 | ⟨hcut, -⟩
      · obtain ⟨y, hy, hys⟩ := hI.sent1
        have : m0.state.turnNum = 0 := by rw [h0]; rfl
        exact ⟨y, hy, by rw [hys]; rfl, by rw [hys, ht, this]; rfl, by rw [hys]; rfl⟩
      · exact absurd ((hout.trans hcut) ▸ hΩ) hA

/-- The answer of `q0` to `p0`'s state `y`. -/
def opAns (A : Outcome Bool) (y : State Bool) : Op Bool :=
  .challenge c0 [⟨y, [p0]⟩, ⟨st (y.turnNum + 1) A, [q0]⟩] (st (y.turnNum + 1) A)

theorem supports_answer {y : State Bool} (A : Outcome Bool) (hc : y.channel = c0)
    (ht : y.turnNum % 2 = 1) (hf : y.isFinal = false) :
    (appsB c0.appDef).supports c0 [⟨y, [p0]⟩, ⟨st (y.turnNum + 1) A, [q0]⟩]
      (st (y.turnNum + 1) A) = true := by
  have hm1 : y.mover = some p0 := by rw [mover_c0 hc, if_neg (by omega)]
  have hm2 : (st (y.turnNum + 1) A).mover = some q0 := by
    rw [mover_c0 rfl, if_pos (by simp only [st]; omega)]
  have hb1 : (⟨y, [p0]⟩ : SignedState Bool).byMover = true := by
    simp [SignedState.byMover, hm1]
  have hb2 : (⟨st (y.turnNum + 1) A, [q0]⟩ : SignedState Bool).byMover = true := by
    simp [SignedState.byMover, hm2]
  simp only [appsB, forceMoveRules, validRun, validMove, hb2]
  simp [hc, hf, st, vtAll, c0, FixedPart.n, hb1]

theorem answer_apply {s : Adjudicator Bool} {ch : Challenge Bool} {y : State Bool}
    (A : Outcome Bool) (hs : s.statusOf c0 = .challenged y.turnNum ch) (hd : s.now < ch.deadline)
    (hc : y.channel = c0) (ht : y.turnNum % 2 = 1) (hf : y.isFinal = false) :
    s.apply appsB q0 (opAns A y) = some (s.setStatus c0
      (.challenged (y.turnNum + 1) ⟨st (y.turnNum + 1) A, s.now + 6⟩)) := by
  show s.challenge appsB q0 c0 _ _ = _
  unfold Adjudicator.challenge
  have hmode : s.mode c0 = .challenge := by
    rw [Adjudicator.mode_eq, hs]
    simp only [ChannelStatus.mode, if_neg (not_le.mpr hd)]
  rw [if_pos ⟨by decide, supports_answer _ hc ht hf, rfl, Or.inr ⟨hmode, by rw [hs]; simp [st]⟩⟩]
  rfl

/-- One land of a call of `p0` whose proof states `p0` holds keeps `InvA`, and
    leaves a safe or an answerable status. -/
theorem landA {G : Outcome Bool → Prop} {A : Outcome Bool} (hA : ¬ G A)
    {m : NetworkState Bool p0} (hI : InvA A m) {op : Op Bool}
    (hop : ∀ dt, op ≠ .tick dt) (hH : ∀ ss ∈ op.proofStates, m.Holds ss)
    (hS : SafeA G (m.chain.statusOf c0) ∨ Answerable G m) :
    InvA A (m.applyAdv appsB (.land op)) ∧
      (SafeA G ((m.applyAdv appsB (.land op)).chain.statusOf c0) ∨
        Answerable G (m.applyAdv appsB (.land op))) := by
  cases happ : m.chain.apply appsB p0 op with
  | none => rw [NetworkState.applyAdv_land_none appsB happ]; exact ⟨hI, hS⟩
  | some s' =>
    rw [NetworkState.applyAdv_land_some appsB happ]
    have hnow : s'.now = m.chain.now := Adjudicator.apply_now_eq_of_not_tick hop happ
    refine ⟨⟨fun x hx hxq => ?_, fun x hx => ?_, hI.sent1⟩, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact held_QOK hI (hH x hx) hxq
      · exact hI.recvQ x hx hxq
    · rcases List.mem_append.1 hx with hx | hx
      · exact (hH x hx).unforged hI.recvU
      · exact hI.recvU x hx
    rcases status_cases happ with heq | ⟨P, cand, rfl, hsup, hcc, -, hst⟩ |
        ⟨P, cand, rfl, -, -, -, hst⟩ | ⟨ss, rfl, hcp⟩
    · rcases hS with hS | ⟨t, ch, y, hs, hd, hΩ, ho, hy, hyc, hyt, hyf⟩
      · exact Or.inl (by rw [heq]; exact hS)
      · exact Or.inr ⟨t, ch, y, by rw [heq]; exact hs, by rw [hnow]; exact hd, hΩ, ho, hy, hyc, hyt, hyf⟩
    · by_cases hΩ : G cand.outcome
      · obtain ⟨ho, y, hy, hyc, hyt, hyf⟩ := answerable_of_support hA hI hsup hH hΩ
        refine Or.inr ⟨cand.turnNum, _, y, hst, ?_, hΩ, ho, hy, hyc, hyt, hyf⟩
        show s'.now < m.chain.now + 6
        rw [hnow]; exact Nat.lt_add_of_pos_right (by decide)
      · exact Or.inl (Or.inr ⟨_, _, hst, hΩ⟩)
    · exact Or.inl (Or.inl ⟨_, hst⟩)
    · obtain ⟨hq0, hfin⟩ := conclusion_q0 hcp
      rcases held_QOK hI (hH ss (List.mem_singleton_self ss)) hq0 with h0 | ⟨-, hf⟩
      · rw [h0] at hfin; cases hfin
      · rw [hf] at hfin; cases hfin

/-- The end of the round: the adversary answers an answerable challenge, then
    one tick of 1. -/
theorem closeA {G : Outcome Bool → Prop} {A : Outcome Bool} (hA : ¬ G A)
    {m : NetworkState Bool p0} (hI : InvA A m)
    (hS : SafeA G (m.chain.statusOf c0) ∨ Answerable G m) (t : Time) :
    ∃ m', T0.RoundSeq appsB t [] m m' ∧ InvA A m' ∧ SafeA G (m'.chain.statusOf c0) ∧
      m'.chain.now = m.chain.now + 1 ∧ m'.sent = m.sent := by
  have htick : ∀ x : NetworkState Bool p0, InvA A x → SafeA G (x.chain.statusOf c0) →
      ∃ m', T0.RoundSeq appsB t [] x m' ∧ InvA A m' ∧ SafeA G (m'.chain.statusOf c0) ∧
        m'.chain.now = x.chain.now + 1 ∧ m'.sent = x.sent := fun x hx hs =>
    ⟨x.applyAdv appsB (.tick 1), .tick trivial (Or.inl rfl) .nil,
      ⟨hx.recvQ, fun r hr => (hx.recvU r hr).of_sent rfl, hx.sent1⟩,
      by rw [NetworkState.applyAdv_tick, Adjudicator.tick_statusOf]; exact hs, rfl, rfl⟩
  rcases hS with hS | ⟨t', ch, y, hs, hd, -, ho, hy, hyc, hyt, hyf⟩
  · exact htick m hI hS
  · subst hyt
    have happ := answer_apply A hs hd hyc ho hyf
    let ma := m.applyAdv appsB (.chain q0 (opAns A y.state))
    have hma : ma = ⟨m.chain.setStatus c0
        (.challenged (y.state.turnNum + 1) ⟨st (y.state.turnNum + 1) (A), m.chain.now + 6⟩),
        (opAns A y.state).proofStates ++ m.received, m.sent⟩ :=
      NetworkState.applyAdv_chain_some appsB happ
    have hUy : ∀ x : NetworkState Bool p0, y ∈ x.sent → x.Unforged ⟨y.state, [p0]⟩ := fun x hx =>
      ⟨fun _ => ⟨y, hx, rfl⟩, fun v hv _ => ⟨y, hx, hv⟩⟩
    have hUa : ∀ x : NetworkState Bool p0, x.Unforged ⟨st (y.state.turnNum + 1) (A), [q0]⟩ :=
      fun x => ⟨fun h => absurd (List.mem_singleton.1 h) p0_ne_q0,
        fun v hv => by simp [st, State.voucher?] at hv⟩
    have hIa : InvA A ma := by
      rw [hma]
      refine ⟨fun x hx hxq => ?_, fun x hx => ?_, hI.sent1⟩
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
    have hSa : SafeA G (ma.chain.statusOf c0) := by
      rw [hma]
      exact Or.inr ⟨y.state.turnNum + 1, ⟨st (y.state.turnNum + 1) (A), m.chain.now + 6⟩,
        by simp, hA⟩
    obtain ⟨m', hseq, hI', hS', hnow, hsent⟩ := htick ma hIa hSa
    have hfe : T0.feasible m (.chain q0 (opAns A y.state)) := by
      refine ⟨by decide, fun ss hss => ?_⟩
      simp only [opAns, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
      rcases hss with rfl | rfl
      · exact hUy _ hy
      · exact hUa _
    refine ⟨m', .other hfe (fun _ h => by cases h) (fun _ h => by cases h) hseq, hI', hS', ?_, ?_⟩
    · rw [hnow, hma]; rfl
    · rw [hsent, hma]

theorem roundA {G : Outcome Bool → Prop} {A : Outcome Bool} (hA : ¬ G A)
    {n0 : NetworkState Bool p0} (t : Time) :
    ∀ (pending : List (Op Bool)), (∀ op ∈ pending, op.HonestFeasible n0) →
    ∀ m : NetworkState Bool p0, InvA A m → (SafeA G (m.chain.statusOf c0) ∨ Answerable G m) →
      m.sent = n0.sent → (∀ r ∈ n0.received, r ∈ m.received) →
      ∃ m', T0.RoundSeq appsB t pending m m' ∧ InvA A m' ∧ SafeA G (m'.chain.statusOf c0) ∧
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
      (fun r hr => (NetworkState.applyAdv_sent_received appsB m (.land op)).2 r (hrecv r hr))
    refine ⟨m', .land (l1 := []) (l2 := rest) rfl hseq, hI', hS', ?_, ?_⟩
    · rw [hnow, landed_now hop.not_tick]
    · rw [hs', NetworkState.applyAdv_sent]

theorem InvA.applyHonest {G : Outcome Bool → Prop} {A : Outcome Bool} {n : NetworkState Bool p0} (hI : InvA A n)
    (hS : SafeA G (n.chain.statusOf c0)) (m : HonestMove Bool) :
    InvA A (n.applyHonest m) ∧ SafeA G ((n.applyHonest m).chain.statusOf c0) := by
  cases m with
  | react r =>
    obtain ⟨y, hy, hys⟩ := hI.sent1
    exact ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).mono (fun z hz => List.mem_append_right _ hz),
      ⟨y, List.mem_append_right _ hy, hys⟩⟩, hS⟩
  | wait dt =>
    exact ⟨⟨hI.recvQ, fun x hx => (hI.recvU x hx).of_sent rfl, hI.sent1⟩,
      by simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf]; exact hS⟩

/-- From a state with `InvA` and a safe status, `p0` has no strategy that
    finalizes `c0` with an outcome in `G`. -/
theorem not_finalizable_from (G : Outcome Bool → Prop) (A : Outcome Bool) (hA : ¬ G A)
    (n : NetworkState Bool p0) (hI : InvA A n) (hS : SafeA G (n.chain.statusOf c0)) :
    ¬ UnbeatableIn appsB T0 (fun _ => True) (fun n => ∃ Ω, n.Finalized c0 Ω ∧ G Ω) n := by
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
    obtain ⟨n', hseq, hI', hS', hnow, -⟩ :=
      roundA hA n.chain.now m.calls hcalls n hI (Or.inl hS) rfl (fun _ hr => hr)
    obtain ⟨hI'', hS''⟩ := hI'.applyHonest hS' m
    exact ih n' (mkRound hseq hnow) hI'' hS''

theorem invA_net1 (A : Outcome Bool) : InvA A net1 := by
  refine ⟨fun x hx _ => ?_, fun x hx => ?_, ⟨s1, List.mem_singleton_self _, rfl⟩⟩
  · rw [List.mem_singleton.1 hx]; exact Or.inl rfl
  · rw [List.mem_singleton.1 hx]; exact unforged_r0 _

theorem not_finalizable (Ω : Outcome Bool) : ¬ Finalizable appsB T0 c0 Ω net1 := fun h =>
  not_finalizable_from (· = Ω) (cutFor Ω) (cutFor_ne Ω) net1 (invA_net1 _) (Or.inl ⟨0, rfl⟩)
    (UnbeatableIn.imp (fun hf => ⟨Ω, hf, rfl⟩) h)

/-! ## Every outcome but `O1` is prevented

`p0` answers a challenge with the outcome `X ≠ O1` at turn `t`: it signs
`ansP t`, its own move at turn `t + 1`, which pays it 5 again, and then
checkpoints with it. A challenge has the deadline `now + 3 * ε`, and the
answer takes at most three rounds from the round in which the challenge
lands. -/

def ansP (t : Nat) : State Bool := st (t + 1) O1

/-- What `p0` holds of a challenge with the outcome `X` at turn `t`. -/
def XInfo (n : NetworkState Bool p0) (t : Nat) (ch : Challenge Bool) : Prop :=
  ch.state.turnNum = t ∧ t % 2 = 0 ∧ 2 ≤ t ∧ ch.state.isFinal = false ∧ ch.state.channel = c0 ∧
    ∃ x ∈ n.received, x.state = ch.state ∧ q0 ∈ x.signers

/-- Every state of `c0` that `p0` signs: the outcome `O1`, non-final, at an
    odd turn. -/
def SentOK (n : NetworkState Bool p0) : Prop :=
  ∀ s ∈ n.sent, s.state.channel = c0 →
    s.state.outcome = O1 ∧ s.state.isFinal = false ∧ s.state.turnNum % 2 = 1

/-- A support of `c0` with unforged states and an outcome other than `O1`:
    its candidate is a non-final move of `q0` at an even turn from 2 on. -/
theorem candX {n : NetworkState Bool p0} (hS : SentOK n) {P : SupportProof Bool}
    {cand : State Bool} (h : (appsB c0.appDef).supports c0 P cand = true)
    (hU : ∀ ss ∈ P, n.Unforged ss) (hne : cand.outcome ≠ O1) :
    cand.turnNum % 2 = 0 ∧ 2 ≤ cand.turnNum ∧ cand.isFinal = false ∧ cand.channel = c0 ∧
      ∃ m1 ∈ P, m1.state = cand ∧ q0 ∈ m1.signers := by
  obtain ⟨m0, m1, ⟨rfl, hlast, hc0, hc1, ht, hmv0, hmv1, hfin⟩⟩ := fm2 h
  subst hlast
  have hU0 := hU m0 (by simp)
  have hU1 := hU m1 (by simp)
  rcases Nat.mod_two_eq_zero_or_one m1.state.turnNum with he | ho
  · refine ⟨he, by omega, ?_, hc1, m1, by simp, rfl, byMover_even hc1 hmv1 he⟩
    cases hf : m1.state.isFinal with
    | false => rfl
    | true =>
      have ho0 : m0.state.turnNum % 2 = 1 := by omega
      obtain ⟨s, hs, hss⟩ := hU0.1 (byMover_odd hc0 hmv0 ho0)
      have := (hS s hs (by rw [hss]; exact hc0)).1
      rw [hss] at this
      exact absurd ((hfin hf).trans this) hne
  · obtain ⟨s, hs, hss⟩ := hU1.1 (byMover_odd hc1 hmv1 ho)
    have := (hS s hs (by rw [hss]; exact hc1)).1
    rw [hss] at this
    exact absurd this hne

theorem no_conclusion {n : NetworkState Bool p0} (hS : SentOK n) {ss : SignedState Bool}
    (hU : n.Unforged ss) (hcp : ConclusionProof c0 ss) : False := by
  obtain ⟨s, hs, hss⟩ := hU.1 (conclusion_p0 hcp)
  have := (hS s hs (by rw [hss]; exact hcp.1)).2.1
  rw [hss, hcp.2.1] at this
  cases this

/-- The invariant at the start of each round of `p0`'s strategy. -/
structure InvX (X : Outcome Bool) (n : NetworkState Bool p0) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sentOK : SentOK n
  noFin : ∀ t f o, n.chain.statusOf c0 ≠ .finalized t f o
  timing : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome = X →
    XInfo n t ch ∧ n.chain.now + 2 ≤ ch.deadline ∧
      ((¬ ∃ s ∈ n.sent, s.state = ansP t) → n.chain.now + 4 ≤ ch.deadline)

/-- The invariant inside a round that starts at `n0`; the turn record stays
    at least `R`. -/
structure KX (X : Outcome Bool) (n0 : NetworkState Bool p0) (R : Nat) (n : NetworkState Bool p0) :
    Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = n0.sent
  recv : ∀ r ∈ n0.received, r ∈ n.received
  now0 : n0.chain.now ≤ n.chain.now
  noFin : ∀ t f o, n.chain.statusOf c0 ≠ .finalized t f o
  chX : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ch.state.outcome = X →
    XInfo n t ch ∧ (n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ n0.chain.now + 6 ≤ ch.deadline)
  left : ∀ t0 ch0, n0.chain.statusOf c0 = .challenged t0 ch0 → ch0.state.outcome = X →
    n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ t0 < (n.chain.statusOf c0).turnNumRecord
  recR : R ≤ (n.chain.statusOf c0).turnNumRecord

theorem KX.start {X : Outcome Bool} {n0 : NetworkState Bool p0} (hI : InvX X n0) :
    KX X n0 (n0.chain.statusOf c0).turnNumRecord n0 :=
  ⟨hI.recvU, rfl, fun _ h => h, le_refl _, hI.noFin,
    fun t ch h hx => ⟨(hI.timing t ch h hx).1, Or.inl rfl⟩, fun _ _ _ _ => Or.inl rfl, le_refl _⟩

theorem XInfo.mono {n n' : NetworkState Bool p0} {t : Nat} {ch : Challenge Bool}
    (h : XInfo n t ch) (hr : ∀ r ∈ n.received, r ∈ n'.received) : XInfo n' t ch := by
  obtain ⟨h1, h2, h3, h4, h5, x, hx, hxs, hxq⟩ := h
  exact ⟨h1, h2, h3, h4, h5, x, hr x hx, hxs, hxq⟩

theorem apply_now_le {s s' : Adjudicator Bool} {caller : Participant} {op : Op Bool}
    (h : s.apply appsB caller op = some s') : s.now ≤ s'.now := by
  by_cases ht : ∃ dt, op = .tick dt
  · obtain ⟨dt, rfl⟩ := ht
    simp only [Adjudicator.apply_tick, Option.some.injEq] at h
    subst h
    exact Nat.le_add_right _ _
  · exact le_of_eq (Adjudicator.apply_now_eq_of_not_tick (fun dt h => ht ⟨dt, h⟩) h).symm

/-- One successful operation with unforged proof states keeps `KX`, inside
    a round whose clock stays below `n0`'s clock plus 2. -/
theorem stepK {X : Outcome Bool} (hX : X ≠ O1) {n0 n : NetworkState Bool p0} {R : Nat}
    (hI0 : InvX X n0) (hK : KX X n0 R n)
    {caller : Participant} {op : Op Bool} {s' : Adjudicator Bool}
    (h : n.chain.apply appsB caller op = some s') (hU : ∀ ss ∈ op.proofStates, n.Unforged ss)
    (hs'now : n.chain.now ≤ s'.now) :
    KX X n0 R { n with chain := s', received := op.proofStates ++ n.received } := by
  have hSn : SentOK n := by
    intro s hs hc; rw [hK.sent] at hs; exact hI0.sentOK s hs hc
  have hrec : ∀ r ∈ n.received, r ∈ op.proofStates ++ n.received :=
    fun r hr => List.mem_append_right _ hr
  have hRecU : ∀ r ∈ op.proofStates ++ n.received,
      ({ n with chain := s', received := op.proofStates ++ n.received } : NetworkState Bool p0).Unforged r := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact (hU r hr).of_sent rfl
    · exact (hK.recvU r hr).of_sent rfl
  rcases status_cases h with heq | ⟨P, cand, rfl, hsup, hcc, hmode, hst⟩ |
      ⟨P, cand, rfl, -, -, hlt, hst⟩ | ⟨ss, rfl, hcp⟩
  · refine ⟨hRecU, hK.sent, fun r hr => hrec r (hK.recv r hr), le_trans hK.now0 hs'now,
      fun t f o => by rw [heq]; exact hK.noFin t f o, fun t ch hc hx => ?_, fun t0 ch0 h0 hx => ?_,
      by rw [heq]; exact hK.recR⟩
    · rw [heq] at hc
      obtain ⟨hinfo, hor⟩ := hK.chX t ch hc hx
      exact ⟨hinfo.mono hrec, by rw [heq]; exact hor⟩
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
      obtain ⟨he, h2, hnf, hch, m1, hm1, hm1s, hm1q⟩ := candX hSn hsup hU
        (fun h => hX (hx.symm.trans h))
      refine ⟨⟨rfl, he, h2, hnf, hch, m1, List.mem_append_left _ hm1, hm1s, hm1q⟩,
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

/-- `KX` as a step invariant of a sub-round of pure adversary play. -/
theorem KX.stepInv {X : Outcome Bool} (hX : X ≠ O1) {n0 : NetworkState Bool p0} {R : Nat}
    (hI0 : InvX X n0) :
    T0.StepInvariant appsB (fun _ => True) (KX X n0 R) (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {n ss} _ hfe hK => by
    rw [NetworkState.applyAdv_deliver]
    refine ⟨fun r hr => ?_, hK.sent, fun r hr => List.mem_cons_of_mem _ (hK.recv r hr), hK.now0,
      hK.noFin, fun t ch hc hx => ?_, hK.left, hK.recR⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hfe.of_sent rfl
      · exact (hK.recvU r hr).of_sent rfl
    · obtain ⟨hinfo, hor⟩ := hK.chX t ch hc hx
      exact ⟨hinfo.mono (fun r hr => List.mem_cons_of_mem _ hr), hor⟩
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
  chain := fun {n caller op} _ hfe hK => by
    cases happ : n.chain.apply appsB caller op with
    | none => rw [NetworkState.applyAdv_chain_none appsB happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_chain_some appsB happ]
      exact stepK hX hI0 hK happ hfe.2 (apply_now_le happ)

open Classical in
/-- `p0`'s move against `X`: answer a challenge with the outcome `X`, first by
    signing `ansP t`, then by a checkpoint with it. -/
noncomputable def idealX (X : Outcome Bool) (n : NetworkState Bool p0) : HonestMove Bool :=
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
noncomputable def σX (X : Outcome Bool) : Strategy Bool p0 := fun n =>
  if (idealX X n).Feasible n then idealX X n else .wait 0

theorem σX_feasible (X : Outcome Bool) (n : NetworkState Bool p0) : (σX X n).Feasible n := by
  unfold σX
  split
  · assumption
  · trivial

theorem send_ansP_feasible {n : NetworkState Bool p0} {t : Nat} (ht : 2 ≤ t) :
    (HonestMove.send (ansP t)).Feasible n := by
  refine (HonestMove.Feasible_send n (ansP t)).mpr ⟨fun hlt => ?_, ?_, ?_⟩
  · exact absurd hlt (by simp only [ansP, st, c0, FixedPart.n, List.length_cons, List.length_nil]; omega)
  · show O1.entries.GuaranteesExternal
    decide
  · exact HonestSend.fundsCommitted_of_fundable (by show ∀ e ∈ O1.entries, _; decide)

theorem holds_ansP {n : NetworkState Bool p0} {t : Nat} (h : ∃ s ∈ n.sent, s.state = ansP t) :
    n.Holds ⟨ansP t, [p0]⟩ := by
  obtain ⟨s, hs, hss⟩ := h
  exact ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s, hs, hss⟩,
    fun v hv => by simp [ansP, st, State.voucher?] at hv⟩

/-- The three shapes of `σX X n`. -/
theorem σX_cases {X : Outcome Bool} {n : NetworkState Bool p0} (hI : InvX X n) :
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
  | finalized t f o => exact absurd hs (hI.noFin t f o)
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
        refine (HonestMove.Feasible_chain _ _).2 fun ss hss => ?_
        simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false] at hss
        rcases hss with rfl | rfl
        · exact holds_of_mem_received hx1
        · exact holds_ansP hd.1
      · right; left
        have hns : ¬ ∃ s ∈ n.sent, s.state = ansP t := fun h =>
          hd ⟨h, hinfo.2.2.2.2.2⟩
        refine ⟨t, ch, rfl, hx, hns, ?_⟩
        have hid : idealX X n = .send (ansP t) := by
          unfold idealX; rw [hs]; simp only [if_pos hx, dif_neg hd]
        unfold σX
        rw [hid, if_pos (send_ansP_feasible hinfo.2.2.1)]
    · exact Or.inl ⟨hwait (by unfold idealX; rw [hs]; simp only [if_neg hx]),
        fun t' ch' h => by cases h; exact hx⟩

/-- At the end of a round from `n0`, before `n0`'s clock plus 2, `X` is not
    finalized. -/
theorem notFinX {X : Outcome Bool} {n0 n : NetworkState Bool p0} {R : Nat} (hI0 : InvX X n0)
    (hK : KX X n0 R n) (hnow : n.chain.now < n0.chain.now + 2) : ¬ n.Finalized c0 X := by
  intro hf
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf
  cases hs : n.chain.statusOf c0 with
  | «open» t => rw [hs] at hf; simp at hf
  | finalized t f o => exact hK.noFin t f o hs
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
theorem KX.nil {X : Outcome Bool} (hX : X ≠ O1) {n0 n n' : NetworkState Bool p0} {R : Nat}
    {t : Time} (hI0 : InvX X n0) (hseq : T0.RoundSeq appsB t [] n n') (hK : KX X n0 R n) :
    KX X n0 R n' :=
  Threat.RoundSeq.nil_invariant hseq (KX.stepInv hX hI0).anyGuard hK

theorem KX.lower {X : Outcome Bool} {n0 n : NetworkState Bool p0} {R R' : Nat}
    (hK : KX X n0 R n) (hR : R' ≤ (n.chain.statusOf c0).turnNumRecord) : KX X n0 R' n :=
  ⟨hK.recvU, hK.sent, hK.recv, hK.now0, hK.noFin, hK.chX, hK.left, hR⟩

/-- The answer of `p0`: its checkpoint with `ansP t0` turns a standing
    challenge at `t0` into an open status at `t0 + 1`. -/
theorem checkpoint_apply {s : Adjudicator Bool} {t0 : Nat} {ch : Challenge Bool}
    {x : SignedState Bool} (hs : s.statusOf c0 = .challenged t0 ch) (hd : s.now < ch.deadline)
    (hxs : x.state = ch.state) (hxq : q0 ∈ x.signers) (hinfo : ch.state.turnNum = t0 ∧ t0 % 2 = 0 ∧
      ch.state.isFinal = false ∧ ch.state.channel = c0) :
    s.apply appsB p0 (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)) =
      some (s.setStatus c0 (.open (t0 + 1))) := by
  obtain ⟨ht, he, hf, hc⟩ := hinfo
  have hxc : x.state.channel = c0 := by rw [hxs]; exact hc
  have hb1 : x.byMover = true := (SignedState.byMover_iff _).2
    ⟨q0, by rw [mover_c0 hxc, if_pos (by rw [hxs, ht]; exact he)], hxq⟩
  have hm2 : (ansP t0).mover = some p0 := by
    rw [mover_c0 rfl, if_neg (by simp only [ansP, st]; omega)]
  have hb2 : (⟨ansP t0, [p0]⟩ : SignedState Bool).byMover = true := by
    simp [SignedState.byMover, hm2]
  have hsup : (appsB c0.appDef).supports c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0) = true := by
    simp only [appsB, forceMoveRules, validRun, validMove, hb2]
    simp [hxs, hc, hf, ht, ansP, st, vtAll, c0, FixedPart.n, hb1]
  show s.checkpoint appsB c0 _ _ = _
  unfold Adjudicator.checkpoint
  have hopen : (s.statusOf c0).IsOpen s.now := by
    rw [hs]
    simp only [ChannelStatus.IsOpen, ChannelStatus.mode, if_neg (not_le.mpr hd)]
    decide
  rw [if_pos ⟨hopen, hsup, rfl, by rw [hs]; simp [ansP, st]⟩]
  rfl

/-- One round of `σX`: `X` is not finalized at its end, and `InvX` holds at
    the start of the next round. -/
theorem roundX {X : Outcome Bool} (hX : X ≠ O1) {n0 n' : NetworkState Bool p0} (hI0 : InvX X n0)
    (hround : T0.Round appsB (σX X n0) n0 n') :
    ¬ n'.Finalized c0 X ∧ InvX X (n'.applyHonest (σX X n0)) := by
  have hbound := round_bound hround
  have hK0 := KX.start (X := X) hI0
  -- the start of the next round, from `KX` at the end and a fact about a
  -- standing challenge
  have hnext : ∀ {R : Nat} (hK : KX X n0 R n') (m : HonestMove Bool)
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
        exact ⟨rfl, rfl, by simp only [ansP, st]; omega⟩
    · rw [hchain.1]; exact hK.noFin t f o
    · rw [hchain.1] at hc
      obtain ⟨hinfo, hor⟩ := hK.chX t ch hc hx
      refine ⟨hinfo.mono (fun r hr => by rw [hrecv]; exact hr), ?_⟩
      rcases hor with h0 | h6
      · exact hS0 t ch hc hx h0
      · rw [hchain.2]
        have : n'.chain.now + 4 ≤ ch.deadline := le_trans (bound6 hbound) h6
        exact ⟨le_trans (Nat.add_le_add_left (by decide) _) this, fun _ => this⟩
  rcases σX_cases hI0 with ⟨hσ, hnx⟩ | ⟨t0, ch0, hs0, hx0, hns, hσ⟩ |
      ⟨t0, ch0, x, hs0, hx0, hsa, hx, hxs, hxq, hσ⟩
  · -- wait: a sub-round of pure adversary play
    rw [hσ] at hround ⊢
    have hK := KX.nil hX hI0 hround.1 hK0
    refine ⟨notFinX hI0 hK hbound, hnext hK _ (fun s hs => .inl hs) rfl ⟨by
      simp only [NetworkState.applyHonest, Adjudicator.tick_statusOf], by
      simp only [NetworkState.applyHonest, Adjudicator.tick_now]; rfl⟩ ?_⟩
    intro t ch hc hx h0
    rw [h0] at hc
    exact absurd hx (hnx t ch hc)
  · -- send `ansP t0`
    rw [hσ] at hround ⊢
    have hK := KX.nil hX hI0 hround.1 hK0
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
    have hK1 := KX.nil hX hI0 hA hK0
    have hnow1 : n1.chain.now ≤ n'.chain.now :=
      le_trans (NetworkState.applyAdv_now_le appsB n1 _) hB.now_le
    have hinfo0 := (hI0.timing _ _ hs0 hx0)
    -- the land of the checkpoint
    have hKL : KX X n0 (t0 + 1) (n1.applyAdv appsB (.land (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)))) := by
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
          ⟨hinfo0.1.1, hinfo0.1.2.1, hinfo0.1.2.2.2.1, hinfo0.1.2.2.2.2.1⟩
        rw [NetworkState.applyAdv_land_some appsB happ]
        exact (stepK hX hI0 hK1 happ hU (le_of_eq rfl)).lower (by simp)
      · have hK1' := hK1.lower hlt
        cases happ : n1.chain.apply appsB p0 (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)) with
        | none =>
          rw [NetworkState.applyAdv_land_none appsB happ]
          exact hK1'
        | some s' =>
          rw [NetworkState.applyAdv_land_some appsB happ]
          exact stepK hX hI0 hK1' happ hU (apply_now_le happ)
    have hK := KX.nil hX hI0 hB hKL
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

theorem prevents_other (X : Outcome Bool) (hX : X ≠ O1) :
    Prevents appsB T0 (fun n => n.Finalized c0 X) net1 := by
  have hI1 : InvX X net1 := by
    refine ⟨fun x hx => ?_, fun s hs _ => ?_,
      fun t f o h => (by simp [net1, Adjudicator.genesis, Adjudicator.statusOf] at h),
      fun t ch h => (by simp [net1, Adjudicator.genesis, Adjudicator.statusOf] at h)⟩
    · rw [List.mem_singleton.1 hx]; exact unforged_r0 _
    · rw [List.mem_singleton.1 hs]; exact ⟨rfl, rfl, rfl⟩
  have hrun : ∀ {n1}, Run appsB T0 (σX X) net1 n1 → InvX X n1 := by
    intro n1 h
    induction h with
    | refl => exact hI1
    | round _ hr ih => exact (roundX hX ih hr).2
  exact ⟨σX X, σX_feasible X, fun n1 n2 hr hround => (roundX hX (hrun hr) hround).1⟩

/-! ## The two statements fail -/

theorem finalizable_or_two_enabled_false : ¬ Spec.finalizable_or_two_enabled (E := Bool) := by
  intro h
  rcases h appsB T0 A0 ⟨net1, net1_reachable⟩ tc0 appsB_supportWindow (by decide)
      ⟨[r0, s1], st 1 O1, holds_r0s1, supports_r0s1, rfl⟩ with
    ⟨Ω, hΩ⟩ | ⟨Ω1, Ω2, hne, hE1, hE2⟩
  · exact not_finalizable Ω hΩ
  · by_cases h1 : Ω1 = O1
    · exact hE2 (prevents_other Ω2 (fun h2 => hne (h1.trans h2.symm)))
    · exact hE1 (prevents_other Ω1 h1)

theorem single_enabled_is_finalizable_false : ¬ Spec.single_enabled_is_finalizable (E := Bool) := by
  intro h
  refine not_finalizable O1 (h appsB T0 A0 ⟨net1, net1_reachable⟩ tc0 appsB_supportWindow
    (by decide) (fun t ht _ => ?_) O1 enabled_O1 (fun Ω' hE => ?_))
  · rw [List.mem_singleton.1 ht]
    exact ⟨[r0, s1], holds_r0s1, supports_r0s1⟩
  · by_contra hne
    exact hE (prevents_other Ω' hne)

#print axioms finalizable_or_two_enabled_false
#print axioms single_enabled_is_finalizable_false

/-! ## IR at every state (draft; no statement takes it)

armada-laconic `labbook/2026-10-30-app-classes-ic-ir.md` §2 (operator,
2026-10-30): "IR at every state: from any state, an online honest participant
can enforce at least what its holdings give it" (ForceMove:410-416,
125-130); "holdings: the signed states and vouchers a participant holds".
Assets leave a channel only through a finalized outcome of that channel
(`transfer_requires_finalized`), so "`p` takes its assets out" is "`p` can
finalize an outcome of `c` that pays `p` at least its share" (`CanTakeOut`).
The game itself need not end.

`AppIR` asks this from every reachable state where `p` holds a share
(`HoldsShare`). The channel must be open at a turn record no higher than the
held candidate: a reachable history can contain a stretch where `p` waited
and let a challenge it should have answered run or expire, and no app can
undo that.

Results, all proved in this section:
* `forceMove_IR`: a ForceMove app is IR when its game library takes nothing
  from a participant that does not move (`NoTakeFromNonMover`).
* `consensus_IR`: the consensus app is IR.
* `appsB_not_IR`, `vtAll_not_noTake`: the trivial game is not IR, and its
  library fails `NoTakeFromNonMover`.
The strategy (`TakeOut.takeout`): challenge an open channel with a held
support, answer a challenge below the held turn `Th` with the own support at
`Th`, and wait for a challenge at `Th` or above to end. Every support at a
turn from `Th` on pays `p` at least its share (`forceMove_pay`,
`consensus_pay`), and the window bounds every turn record by `Th + n`
(`Ctx.turn_lt`), so the rank `rk` falls in every round. -/

namespace TakeOut

section

variable {E : Type} [DecidableEq E]

/-- The amount that an outcome pays the external destination `d`. -/
def share (Ω : Outcome E) (d : E) : Coins := Ω.entries.owed (.external d)

/-- Every state of `proof` that `p` signed is a state in `sent`. -/
def SignedIn (sent : List (SignedState E)) (p : Participant) (proof : SupportProof E) : Prop :=
  ∀ ss ∈ proof, p ∈ ss.signers → ∃ s ∈ sent, s.state = ss.state

/-- The facts of the take-out strategy: `p` signed `sent0` only, every state
    of `c` in it is at most at turn `Th`, and every support of `c` at a turn
    from `Th` on, and every conclusion proof, pays `d` at least `x`. -/
structure Ctx (apps : Apps E) (p : Participant) (c : FixedPart) (d : E) (x Th : Nat)
    (sent0 : List (SignedState E)) : Prop where
  hp : p ∈ c.participants
  sw : (apps c.appDef).SupportWindow
  sentTurn : ∀ s ∈ sent0, s.state.channel = c → s.state.turnNum ≤ Th
  pay : ∀ proof cand, SignedIn sent0 p proof → (apps c.appDef).supports c proof cand = true →
    cand.channel = c → Th ≤ cand.turnNum → x ≤ share cand.outcome d
  payConc : ∀ ss, ConclusionProof c ss → (∃ s ∈ sent0, s.state = ss.state) →
    x ≤ share ss.state.outcome d

/-- Every supported candidate is below `Th + c.n`. -/
theorem Ctx.turn_lt {apps : Apps E} {p : Participant} {c : FixedPart} {d : E} {x Th : Nat}
    {sent0 : List (SignedState E)} (C : Ctx apps p c d x Th sent0) {proof : SupportProof E}
    {cand : State E} (hS : SignedIn sent0 p proof) (h : (apps c.appDef).supports c proof cand = true) :
    cand.turnNum < Th + c.n := by
  obtain ⟨ss, hss, hps, hch, -, hlt⟩ := C.sw c proof cand h p C.hp
  obtain ⟨s, hs, hse⟩ := hS ss hss hps
  have := C.sentTurn s hs (by rw [hse]; exact hch)
  rw [hse] at this
  omega

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
    | deposit a e x => simp [Op.targets] at ht
    | tick dt => simp [Op.targets] at ht
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
      exact Or.inr (Or.inl ⟨P, cand, rfl, hsup, hcc, hmode, by simp⟩)
    | checkpoint c' P cand =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨hopen, hsup, hcc, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
      exact Or.inr (Or.inr (Or.inl ⟨P, cand, rfl, hsup, hcc, hopen, hlt, by simp⟩))
    | conclude c' ss =>
      simp only [Op.targets] at ht; subst ht
      obtain ⟨⟨-, hcp⟩, rfl⟩ := Adjudicator.conclude_some h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ss, rfl, hcp, by simp⟩)))
  · exact Or.inl (statusOf_apply_of_not_targets h ht)

theorem apply_now_le {apps : Apps E} {s s' : Adjudicator E} {caller : Participant} {op : Op E}
    (h : s.apply apps caller op = some s') : s.now ≤ s'.now := by
  by_cases ht : ∃ dt, op = .tick dt
  · obtain ⟨dt, rfl⟩ := ht
    simp only [Adjudicator.apply_tick, Option.some.injEq] at h
    subst h
    exact Nat.le_add_right _ _
  · exact le_of_eq (Adjudicator.apply_now_eq_of_not_tick (fun dt h => ht ⟨dt, h⟩) h).symm

/-- The invariant inside a round that starts at `n0`. `R` is a lower bound of
    the turn record (or the status is finalized); the rank stays below `Kb`, or
    the status stays `S`. -/
structure K (apps : Apps E) {p : Participant} (c : FixedPart) (d : E) (x Th : Nat)
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
  recLt : (n.chain.statusOf c).turnNumRecord < Th + c.n
  lowK : ∀ t ch, n.chain.statusOf c = .challenged t ch → t < Th →
    n.chain.statusOf c = n0.chain.statusOf c ∨ n0.chain.now + c.challengeDuration ≤ ch.deadline
  recR : R ≤ (n.chain.statusOf c).turnNumRecord ∨ ∃ t f o, n.chain.statusOf c = .finalized t f o
  prog : rk (Th + c.n) (n.chain.statusOf c) < Kb ∨ n.chain.statusOf c = S

omit [DecidableEq E] in
theorem rk_step {M : Nat} {Kb : Nat} {S st st' : ChannelStatus E} (hpos : 0 < Kb)
    (hle : rk M S ≤ Kb) (hprev : rk M st < Kb ∨ st = S)
    (hstep : st' = st ∨ rk M st' < rk M st ∨ rk M st' = 0) : rk M st' < Kb ∨ st' = S := by
  rcases hstep with rfl | hlt | h0
  · exact hprev
  · rcases hprev with h | rfl
    · exact Or.inl (lt_trans hlt h)
    · exact Or.inl (lt_of_lt_of_le hlt hle)
  · exact Or.inl (by rw [h0]; exact hpos)

/-- One successful operation with unforged proof states keeps `K`. `E0`
    bounds the clock of the round; a low challenge standing at `n0` ends no
    sooner than `E0`. -/
theorem K.step {apps : Apps E} {p : Participant} {c : FixedPart} {d : E} {x Th : Nat}
    {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n0 m : NetworkState E p}
    {R Kb : Nat} {S : ChannelStatus E} (C : Ctx apps p c d x Th sent0)
    (hK : K apps c d x Th sent0 proof0 n0 R Kb S m) {E0 : Time}
    (hE0 : E0 ≤ n0.chain.now + c.challengeDuration) (hnow : m.chain.now < E0)
    (hlow0 : ∀ t ch, n0.chain.statusOf c = .challenged t ch → t < Th → E0 ≤ ch.deadline)
    (hpos : 0 < Kb) (hle : rk (Th + c.n) S ≤ Kb)
    {caller : Participant} {op : Op E} {s' : Adjudicator E}
    (h : m.chain.apply apps caller op = some s') (hU : ∀ ss ∈ op.proofStates, m.Unforged ss) :
    K apps c d x Th sent0 proof0 n0 R Kb S
      { m with chain := s', received := op.proofStates ++ m.received } := by
  have hS : SignedIn sent0 p op.proofStates := fun ss hss hps => by
    obtain ⟨s, hs, hse⟩ := (hU ss hss).1 hps
    exact ⟨s, by rw [← hK.sent]; exact hs, hse⟩
  have hrec : ∀ r ∈ m.received, r ∈ op.proofStates ++ m.received :=
    fun r hr => List.mem_append_right _ hr
  have hheld : ∀ {ss}, m.Holds ss →
      ({ m with chain := s', received := op.proofStates ++ m.received } : NetworkState E p).Holds ss :=
    fun h => NetworkState.Holds.mono (net := m) rfl hrec h
  have hnow' := apply_now_le h
  -- a low challenge at `m` has not expired
  have hlive : ∀ t ch, m.chain.statusOf c = .challenged t ch → t < Th → m.chain.now < ch.deadline := by
    intro t ch hc ht
    rcases hK.lowK t ch hc ht with h0 | h6
    · exact lt_of_lt_of_le hnow (hlow0 t ch (h0 ▸ hc) ht)
    · exact lt_of_lt_of_le hnow (le_trans hE0 h6)
  have hM : (m.chain.statusOf c).turnNumRecord < Th + c.n := hK.recLt
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
    have hlt' : cand.turnNum < Th + c.n := C.turn_lt hS hsup
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
    · refine rk_step hpos hle hK.prog (Or.inr (Or.inl ?_))
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
    have hlt' : cand.turnNum < Th + c.n := C.turn_lt hS hsup
    have hnotfin : ∀ t f o, m.chain.statusOf c ≠ .finalized t f o := fun t f o hf => by
      rw [hf] at hopen
      exact hopen (by simp [ChannelStatus.mode])
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
    · refine rk_step hpos hle hK.prog (Or.inr (Or.inl ?_))
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
    have hlt' : ss.state.turnNum < Th + c.n := by
      obtain ⟨s, hs, hse⟩ := hpss
      have := C.sentTurn s hs (by rw [hse]; exact hcp.1)
      rw [hse] at this
      have := List.length_pos_of_mem C.hp
      unfold FixedPart.n; omega
    refine ⟨hRecU, hK.sent, le_trans hK.now0 hnow', fun r hr => hrec r (hK.recv0 r hr), fun ss hss => hheld (hK.held0 ss hss),
      fun t ht => (by rw [hst] at ht; cases ht), fun t ch hc => (by rw [hst] at hc; cases hc),
      fun t f o hc => ?_, by rw [hst]; exact hlt', fun t ch hc => (by rw [hst] at hc; cases hc),
      Or.inr ⟨_, _, _, hst⟩, rk_step hpos hle hK.prog (Or.inr (Or.inr (by rw [hst]; rfl)))⟩
    rw [hst] at hc
    obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hc
    exact C.payConc ss hcp hpss
  · -- a payout: the status was already final
    cases hs : m.chain.statusOf c with
    | «open» r => rw [hs] at hfo; simp [ChannelStatus.finalOutcome] at hfo
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
        Or.inr ⟨_, _, _, hst⟩, rk_step hpos hle hK.prog (Or.inr (Or.inr (by rw [hst]; rfl)))⟩
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
        Or.inr ⟨_, _, _, hst⟩, rk_step hpos hle hK.prog (Or.inr (Or.inr (by rw [hst]; rfl)))⟩
      rw [hst] at hc
      obtain ⟨-, rfl, -⟩ := ChannelStatus.finalized.inj hc
      exact hpay

/-- `K` as a step invariant of a sub-round of pure adversary play that ends
    no later than `Eend < E0`. -/
theorem K.stepInv {apps : Apps E} {p : Participant} {T : Threat E p} {c : FixedPart} {d : E}
    {x Th : Nat} {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n0 : NetworkState E p}
    {R Kb : Nat} {S : ChannelStatus E} (C : Ctx apps p c d x Th sent0) (B : Bounds apps p T)
    {E0 Eend : Time} (hE0 : E0 ≤ n0.chain.now + c.challengeDuration) (hEend : Eend < E0)
    (hlow0 : ∀ t ch, n0.chain.statusOf c = .challenged t ch → t < Th → E0 ≤ ch.deadline)
    (hpos : 0 < Kb) (hle : rk (Th + c.n) S ≤ Kb) :
    T.StepInvariant apps (fun n => n.chain.now ≤ Eend)
      (K apps c d x Th sent0 proof0 n0 R Kb S) (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {n ss} _ hfe hK => by
    rw [NetworkState.applyAdv_deliver]
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
  tick := fun {n dt} _ _ hK => by
    rw [NetworkState.applyAdv_tick]
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
  chain := fun {n caller op} hg hfe hK => by
    cases happ : n.chain.apply apps caller op with
    | none => rw [NetworkState.applyAdv_chain_none apps happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_chain_some apps happ]
      exact K.step C hK hE0 (lt_of_le_of_lt hg hEend) hlow0 hpos hle happ (B.unforgeable n caller op hfe)

/-- The invariant at the start of each round. -/
structure TI (apps : Apps E) {p : Participant} (ε : Time) (c : FixedPart) (d : E) (x Th : Nat)
    (sent0 : List (SignedState E)) (proof0 : SupportProof E) (n : NetworkState E p) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = sent0
  held0 : ∀ ss ∈ proof0, n.Holds ss
  openW : ∀ t, n.chain.statusOf c = .open t → t ≤ Th ∨
    ∃ proof cand, (∀ ss ∈ proof, n.Holds ss) ∧ (apps c.appDef).supports c proof cand = true ∧
      cand.channel = c ∧ t ≤ cand.turnNum
  chPay : ∀ t ch, n.chain.statusOf c = .challenged t ch → Th ≤ t → x ≤ share ch.state.outcome d
  finPay : ∀ t f o, n.chain.statusOf c = .finalized t f o → x ≤ share f d
  recLt : (n.chain.statusOf c).turnNumRecord < Th + c.n
  chLow : ∀ t ch, n.chain.statusOf c = .challenged t ch → t < Th → n.chain.now + ε ≤ ch.deadline

theorem TI.toK {apps : Apps E} {p : Participant} {ε : Time} {c : FixedPart} {d : E} {x Th : Nat}
    {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n : NetworkState E p}
    (hI : TI apps ε c d x Th sent0 proof0 n) :
    K apps c d x Th sent0 proof0 n (n.chain.statusOf c).turnNumRecord (rk (Th + c.n) (n.chain.statusOf c))
      (n.chain.statusOf c) n :=
  ⟨hI.recvU, hI.sent, le_refl _, fun _ h => h, hI.held0, hI.openW, hI.chPay, hI.finPay, hI.recLt,
    fun _ _ _ _ => Or.inl rfl, Or.inl (le_refl _), Or.inr rfl⟩

theorem K.reS {apps : Apps E} {p : Participant} {c : FixedPart} {d : E} {x Th : Nat}
    {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n0 n : NetworkState E p}
    {R R' Kb : Nat} {S S' : ChannelStatus E} (hK : K apps c d x Th sent0 proof0 n0 R Kb S n)
    (hlt : rk (Th + c.n) (n.chain.statusOf c) < Kb)
    (hR : R' ≤ (n.chain.statusOf c).turnNumRecord ∨ ∃ t f o, n.chain.statusOf c = .finalized t f o) :
    K apps c d x Th sent0 proof0 n0 R' Kb S' n :=
  ⟨hK.recvU, hK.sent, hK.now0, hK.recv0, hK.held0, hK.openW, hK.chPay, hK.finPay, hK.recLt, hK.lowK,
    hR, Or.inl hlt⟩

/-- The rank of one successful operation with proof states of `sent0`: the
    status stays, or its rank falls, or it becomes `0`. -/
theorem rank_step {apps : Apps E} {p : Participant} {c : FixedPart} {d : E} {x Th : Nat}
    {sent0 : List (SignedState E)} (C : Ctx apps p c d x Th sent0) {s s' : Adjudicator E}
    {caller : Participant} {op : Op E} (h : s.apply apps caller op = some s')
    (hS : SignedIn sent0 p op.proofStates) (hM : (s.statusOf c).turnNumRecord < Th + c.n) :
    s'.statusOf c = s.statusOf c ∨ rk (Th + c.n) (s'.statusOf c) < rk (Th + c.n) (s.statusOf c) ∨
      rk (Th + c.n) (s'.statusOf c) = 0 := by
  rcases status_cases (c := c) h with heq | ⟨P, cand, rfl, hsup, -, hmode, hst⟩ |
      ⟨P, cand, rfl, hsup, -, hopen, hlt, hst⟩ | ⟨ss, rfl, -, hst⟩ | ⟨o0, o', hfo, hst⟩
  · exact Or.inl heq
  · right; left
    have hlt' : cand.turnNum < Th + c.n := C.turn_lt hS hsup
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
    have hlt' : cand.turnNum < Th + c.n := C.turn_lt hS hsup
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
      exact absurd (by simp [ChannelStatus.mode]) hopen
  · right; right; rw [hst]; rfl
  · right; right
    rw [hst]
    cases s.statusOf c <;> rfl

/-- The goal: `c` is finalized with an outcome that pays `d` at least `x`. -/
def Goal {p : Participant} (c : FixedPart) (d : E) (x : Nat) (n : NetworkState E p) : Prop :=
  ∃ Ω, n.Finalized c Ω ∧ x ≤ share Ω d

theorem two_eps {ε cd : Time} (h : 2 * ε ≤ cd) : ε ≤ cd := by
  have : ε ≤ 2 * ε := Nat.le_mul_of_pos_left ε (by decide)
  exact le_trans this h

/-- `K` at the end of a round from `n`, with a rank below `n`'s, gives `TI`. -/
theorem K.toTI {apps : Apps E} {p : Participant} {ε : Time} {c : FixedPart} {d : E} {x Th : Nat}
    {sent0 : List (SignedState E)} {proof0 : SupportProof E} {n n1 : NetworkState E p} {R Kb : Nat}
    {S : ChannelStatus E} (hK : K apps c d x Th sent0 proof0 n R Kb S n1)
    (hdur : 2 * ε ≤ c.challengeDuration) (hbound : n1.chain.now < n.chain.now + ε)
    (hne : n1.chain.statusOf c ≠ n.chain.statusOf c) : TI apps ε c d x Th sent0 proof0 n1 := by
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
    {x Th : Nat} {sent0 : List (SignedState E)} {proof0 : SupportProof E}
    (C : Ctx apps p c d x Th sent0) (A : Assumptions apps p T)
    (hdur : 2 * T.ε ≤ c.challengeDuration) {n n1 : NetworkState E p}
    (hI : TI apps T.ε c d x Th sent0 proof0 n) {P : SupportProof E} {cand : State E}
    (hH : ∀ ss ∈ P, n.Holds ss)
    (hok : ∀ s : Adjudicator E, s.statusOf c = n.chain.statusOf c → s.now < n.chain.now + T.ε →
      ∃ s', s.apply apps p (.challenge c P cand) = some s' ∧
        rk (Th + c.n) (s'.statusOf c) < rk (Th + c.n) (n.chain.statusOf c))
    (hpos : 0 < rk (Th + c.n) (n.chain.statusOf c))
    (hround : T.Round apps (HonestMove.chain (.challenge c P cand)) n n1) :
    TI apps T.ε c d x Th sent0 proof0 n1 ∧
      rk (Th + c.n) (n1.chain.statusOf c) < rk (Th + c.n) (n.chain.statusOf c) := by
  have hbound : n1.chain.now < n.chain.now + T.ε := hround.2
  have hE0 : n.chain.now + T.ε ≤ n.chain.now + c.challengeDuration :=
    Nat.add_le_add_left (two_eps hdur) _
  obtain ⟨na, hA, hB⟩ := Threat.Round.single hround
  have hnaend : na.chain.now ≤ n1.chain.now :=
    le_trans (NetworkState.applyAdv_now_le apps na _) hB.now_le
  have hnow_a : na.chain.now < n.chain.now + T.ε := lt_of_le_of_lt hnaend hbound
  have hKa := Threat.RoundSeq.nil_invariant hA
      (K.stepInv (R := (n.chain.statusOf c).turnNumRecord) C A.toBounds hE0 hnow_a hI.chLow hpos
        (le_refl _)) hI.toK
  have hHa : ∀ ss ∈ P, na.Holds ss := fun ss hss =>
    NetworkState.Holds.mono (by rw [hKa.sent, hI.sent]) hKa.recv0 (hH ss hss)
  have hUa : ∀ ss ∈ (Op.challenge c P cand).proofStates, na.Unforged ss := fun ss hss =>
    (hHa ss hss).unforged hKa.recvU
  have hSa : SignedIn sent0 p (Op.challenge c P cand).proofStates := fun ss hss hps => by
    obtain ⟨s, hs, hse⟩ := (hUa ss hss).1 hps
    exact ⟨s, by rw [← hKa.sent]; exact hs, hse⟩
  -- after the land, the rank is below `n`'s
  have hKL : K apps c d x Th sent0 proof0 n (n.chain.statusOf c).turnNumRecord
      (rk (Th + c.n) (n.chain.statusOf c)) (.finalized 0 cand.outcome cand.outcome)
      (na.applyAdv apps (.land (.challenge c P cand))) := by
    cases happ : na.chain.apply apps p (.challenge c P cand) with
    | none =>
      rw [NetworkState.applyAdv_land_none apps happ]
      rcases hKa.prog with h | h
      · exact hKa.reS h hKa.recR
      · obtain ⟨s', hs', -⟩ := hok na.chain h hnow_a
        rw [happ] at hs'; cases hs'
    | some s' =>
      rw [NetworkState.applyAdv_land_some apps happ]
      have hK' := K.step C hKa hE0 hnow_a hI.chLow hpos (le_refl _) happ hUa
      have hlt : rk (Th + c.n) (s'.statusOf c) < rk (Th + c.n) (n.chain.statusOf c) := by
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
      (K.stepInv C A.toBounds hE0 hbound hI.chLow hpos (Nat.zero_le _)) hKL
  have hlt1 : rk (Th + c.n) (n1.chain.statusOf c) < rk (Th + c.n) (n.chain.statusOf c) := by
    rcases hK1.prog with h | h
    · exact h
    · rw [h]; exact hpos
  exact ⟨hK1.toTI hdur hbound (fun h => by rw [h] at hlt1; exact lt_irrefl _ hlt1), hlt1⟩

theorem le_wait {a b d : Nat} (h : a ≤ b) : d ≤ b + (d - a) := by omega

/-- A successful challenge of `p` from a status `st`: the new status. -/
theorem challenge_apply {apps : Apps E} {p : Participant} {c : FixedPart} {s : Adjudicator E}
    {P : SupportProof E} {cand : State E} (hp : p ∈ c.participants)
    (hsup : (apps c.appDef).supports c P cand = true) (hcc : cand.channel = c)
    (hmode : (s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ cand.turnNum) ∨
      (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < cand.turnNum)) :
    s.apply apps p (.challenge c P cand) =
      some (s.setStatus c (.challenged cand.turnNum ⟨cand, s.now + c.challengeDuration⟩)) := by
  show s.challenge apps p c P cand = _
  unfold Adjudicator.challenge
  rw [if_pos ⟨hp, hsup, hcc, hmode⟩]

/-- **The take-out strategy.** From a state with `TI`, `p` finalizes `c`
    with an outcome that pays `d` at least `x`: it challenges an open `c`
    with a support it holds, answers a challenge below `Th` with its own
    support at `Th`, and waits for a challenge at `Th` or above to end. Each
    round lowers the rank or reaches the goal. -/
theorem takeout {apps : Apps E} {p : Participant} {T : Threat E p} {c : FixedPart} {d : E}
    {x Th : Nat} {sent0 : List (SignedState E)} {proof0 : SupportProof E} {cand0 : State E}
    (C : Ctx apps p c d x Th sent0) (A : Assumptions apps p T)
    (hdur : 2 * T.ε ≤ c.challengeDuration)
    (hsup0 : (apps c.appDef).supports c proof0 cand0 = true) (hch0 : cand0.channel = c)
    (hturn0 : cand0.turnNum = Th) :
    ∀ μ (n : NetworkState E p), TI apps T.ε c d x Th sent0 proof0 n →
      rk (Th + c.n) (n.chain.statusOf c) ≤ μ →
      UnbeatableIn apps T (fun _ => True) (Goal c d x) n := by
  have hn : 0 < c.n := List.length_pos_of_mem C.hp
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
  intro n hI hμ
  -- one challenge round, then the induction
  have hround : ∀ {P : SupportProof E} {cand : State E}, (∀ ss ∈ P, n.Holds ss) →
      (∀ ss ∈ P, n.Holds ss → True) →
      (∀ s : Adjudicator E, s.statusOf c = n.chain.statusOf c → s.now < n.chain.now + T.ε →
        ∃ s', s.apply apps p (.challenge c P cand) = some s' ∧
          rk (Th + c.n) (s'.statusOf c) < rk (Th + c.n) (n.chain.statusOf c)) →
      0 < rk (Th + c.n) (n.chain.statusOf c) →
      UnbeatableIn apps T (fun _ => True) (Goal c d x) n := by
    intro P cand hH _ hok hpos
    refine UnbeatableIn.move (.chain (.challenge c P cand)) trivial
      ((HonestMove.Feasible_chain _ _).2 hH) fun n1 hr => ?_
    rw [NetworkState.applyHonest_chain]
    obtain ⟨hI1, hlt⟩ := challenge_round C A hdur hI hH hok hpos hr
    exact ih _ (lt_of_lt_of_le hlt hμ) n1 hI1 (le_refl _)
  cases hs : n.chain.statusOf c with
  | finalized t f o =>
    apply UnbeatableIn.done
    refine ⟨f, ?_, hI.finPay t f o hs⟩
    simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hs,
      ChannelStatus.finalizedWith_finalized]
  | «open» t =>
    have hpos : 0 < rk (Th + c.n) (n.chain.statusOf c) := by rw [hs]; simp only [rk]; omega
    have hok : ∀ {P : SupportProof E} {cand : State E}, (apps c.appDef).supports c P cand = true →
        cand.channel = c → t ≤ cand.turnNum →
        ∀ s : Adjudicator E, s.statusOf c = n.chain.statusOf c → s.now < n.chain.now + T.ε →
          ∃ s', s.apply apps p (.challenge c P cand) = some s' ∧
            rk (Th + c.n) (s'.statusOf c) < rk (Th + c.n) (n.chain.statusOf c) := by
      intro P cand hsup hcc hle s hss _
      rw [hs] at hss ⊢
      refine ⟨_, challenge_apply C.hp hsup hcc (Or.inl ⟨by rw [Adjudicator.mode_eq, hss]; rfl,
        by rw [hss]; exact hle⟩), ?_⟩
      simp only [Adjudicator.statusOf_setStatus, if_true, rk]
      omega
    rcases hI.openW t hs with hle | ⟨P, cand, hH, hsup, hcc, hle⟩
    · exact hround hI.held0 (fun _ _ _ => trivial) (hok hsup0 hch0 (by rw [hturn0]; exact hle)) hpos
    · exact hround hH (fun _ _ _ => trivial) (hok hsup hcc hle) hpos
  | challenged t ch =>
    have hpos : 0 < rk (Th + c.n) (n.chain.statusOf c) := by rw [hs]; simp only [rk]; omega
    by_cases hlow : t < Th
    · -- answer with the own support at `Th`
      refine hround (cand := cand0) hI.held0 (fun _ _ _ => trivial) (fun s hss hsnow => ?_) hpos
      rw [hs] at hss ⊢
      have hdl := hI.chLow t ch hs hlow
      have hmode : s.mode c = .challenge := by
        rw [Adjudicator.mode_eq, hss]
        simp only [ChannelStatus.mode, if_neg (not_le.mpr (lt_of_lt_of_le hsnow hdl))]
      refine ⟨_, challenge_apply C.hp hsup0 hch0 (Or.inr ⟨hmode, by rw [hss, hturn0]; exact hlow⟩), ?_⟩
      simp only [Adjudicator.statusOf_setStatus, if_true, rk, hturn0]
      omega
    · -- wait for the challenge to end
      have hpay := hI.chPay t ch hs (by omega)
      by_cases hexp : ch.deadline ≤ n.chain.now
      · apply UnbeatableIn.done
        refine ⟨ch.state.outcome, ?_, hpay⟩
        simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hs,
          ChannelStatus.finalizedWith_challenged, if_pos hexp]
      · refine UnbeatableIn.move (.wait (ch.deadline - n.chain.now)) trivial trivial fun n1 hr => ?_
        have hbound : n1.chain.now < n.chain.now + T.ε := hr.2
        have hE0 : n.chain.now + T.ε ≤ n.chain.now + c.challengeDuration :=
          Nat.add_le_add_left (two_eps hdur) _
        have hK1 := Threat.RoundSeq.nil_invariant hr.1
          (K.stepInv (R := t) C A.toBounds hE0 hbound hI.chLow hpos (le_refl _))
          (by have := hI.toK; rw [hs] at this ⊢; exact this)
        have hTI : TI apps T.ε c d x Th sent0 proof0
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
        · exact ih _ (lt_of_lt_of_le (by simpa [NetworkState.applyHonest] using hlt) hμ) _ hTI
            (le_refl _)
        · apply UnbeatableIn.done
          refine ⟨ch.state.outcome, ?_, hpay⟩
          have hle : n.chain.now ≤ n1.chain.now := hr.1.now_le
          have hge : ch.deadline ≤ n1.chain.now + (ch.deadline - n.chain.now) := le_wait hle
          simp only [NetworkState.applyHonest, NetworkState.Finalized, FixedPart.address_eq,
            Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, heq, hs, Adjudicator.tick_now,
            ChannelStatus.finalizedWith_challenged, if_pos hge]

/-! ## The holdings, and the two apps -/

/-- The facts about the states `p` signed that `HoldsShare` gives: every
    state of `c` is at most at turn `Th`, and pays `d` at least `x` when it is
    in the window of `Th` or final. -/
def SentBelow (sent : List (SignedState E)) (c : FixedPart) (d : E) (x Th : Nat) : Prop :=
  ∀ s ∈ sent, s.state.channel = c → s.state.turnNum ≤ Th ∧
    ((Th < s.state.turnNum + c.n ∨ s.state.isFinal = true) → x ≤ share s.state.outcome d)

theorem payConc_of {sent : List (SignedState E)} {c : FixedPart} {d : E} {x Th : Nat}
    (h : SentBelow sent c d x Th) (ss : SignedState E) (hcp : ConclusionProof c ss)
    (hs : ∃ s ∈ sent, s.state = ss.state) : x ≤ share ss.state.outcome d := by
  obtain ⟨s, hs, hse⟩ := hs
  have := (h s hs (by rw [hse]; exact hcp.1)).2 (Or.inr (by rw [hse]; exact hcp.2.1))
  rwa [hse] at this

/-- A sufficient condition on a ForceMove game library: no valid transition
    reduces the payment to a participant that does not move. -/
def NoTakeFromNonMover (vt : State E → State E → Bool) (dest : Participant → E) : Prop :=
  ∀ s s', vt s s' = true → ∀ q, s'.mover ≠ some q → share s.outcome (dest q) ≤ share s'.outcome (dest q)

/-- Under `NoTakeFromNonMover`, every ForceMove support of `c` at a turn from
    `Th` on pays `p` at least `x`: the run holds a move of `p` in the window
    of `Th`, which pays `p` at least `x`, and no later move of another
    participant reduces it. -/
theorem forceMove_pay {vt : State E → State E → Bool} {dest : Participant → E} {p : Participant}
    (hNT : NoTakeFromNonMover vt dest) {c : FixedPart} (hp : p ∈ c.participants)
    {sent : List (SignedState E)} {x Th : Nat} (hB : SentBelow sent c (dest p) x Th)
    {proof : SupportProof E} {cand : State E} (hS : SignedIn sent p proof)
    (h : (forceMoveRules vt).supports c proof cand = true) (hTh : Th ≤ cand.turnNum) :
    x ≤ share cand.outcome (dest p) := by
  obtain ⟨hlen, hstep, ml, hml, hmls⟩ := forceMove_supports_valid_run vt c proof cand h
  have hkeep := forceMove_conclude_keeps_outcome vt c proof cand h
  have h' := h
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨-, hhead⟩, -⟩, hchAll⟩, -⟩ := h'
  have hn : 0 < c.n := List.length_pos_of_mem hp
  obtain ⟨m0, hm0⟩ : ∃ m0, proof[0]? = some m0 := by
    cases proof with
    | nil => simp at hlen; omega
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

/-- Every consensus support of `c` at a turn from `Th` on pays `p` at least
    `x`: its one state is the candidate, and `p` signed it. -/
theorem consensus_pay {p : Participant} {c : FixedPart} (hp : p ∈ c.participants) {d : E}
    {sent : List (SignedState E)} {x Th : Nat} (hB : SentBelow sent c d x Th)
    {proof : SupportProof E} {cand : State E} (hS : SignedIn sent p proof)
    (h : (consensusRules : Rules E).supports c proof cand = true) (hTh : Th ≤ cand.turnNum) :
    x ≤ share cand.outcome d := by
  match proof, h, hS with
  | [ss], h, hS =>
    simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hst, hch⟩, hall⟩ := h
    obtain ⟨s, hs, hse⟩ := hS ss (List.mem_singleton_self ss) (hall p (by rw [hch]; exact hp))
    obtain ⟨hle, hpay⟩ := hB s hs (by rw [hse]; exact hch)
    have hn : 0 < c.n := List.length_pos_of_mem hp
    rw [← hst, ← hse]
    refine hpay (Or.inl ?_)
    rw [hse, hst]; omega
  | [], h, _ => simp [consensusRules] at h
  | _ :: _ :: _, h, _ => simp [consensusRules] at h

/-- What `p`'s holdings give it at the destination `d`: at least `x`, the
    payment of a supported candidate of `c` that `p` holds. Every state of `c`
    that `p` signed is at most at the candidate's turn, and pays `d` at least
    `x` when it is in the candidate's window or final (`SentBelow`): the later
    and alternative moves of `p` are part of what its holdings give it. The
    channel is open, at a turn record no higher than the candidate's: `p` was
    online, so no challenge it should have answered is running. -/
def HoldsShare {p : Participant} (apps : Apps E) (net : NetworkState E p) (c : FixedPart) (d : E)
    (x : Coins) : Prop :=
  ∃ proof cand, (∀ ss ∈ proof, net.Holds ss) ∧ (apps c.appDef).supports c proof cand = true ∧
    cand.channel = c ∧ x ≤ share cand.outcome d ∧ SentBelow net.sent c d x cand.turnNum ∧
    ∃ t, net.chain.statusOf c = .open t ∧ t ≤ cand.turnNum

/-- `p` can take out `x` at `d`: it has an unbeatable strategy that finalizes
    `c` with an outcome that pays `d` at least `x`. -/
def CanTakeOut {p : Participant} (apps : Apps E) (T : Threat E p) (c : FixedPart) (d : E)
    (x : Coins) (net : NetworkState E p) : Prop :=
  Unbeatable apps T (Goal c d x) net

/-- IR at every state of the app `a`, for the destination map `dest`: from
    every reachable state, `p` can take out what its holdings give it. -/
def AppIR (apps : Apps E) (a : AppId) (dest : Participant → E) : Prop :=
  ∀ {p : Participant} (T : Threat E p), Assumptions apps p T →
    ∀ (net : Nitro.ReachableParticipant apps T) (c : TimedChannel T.ε) (x : Coins),
      (c : FixedPart).appDef = a → p ∈ (c : FixedPart).participants →
      HoldsShare apps net.state c (dest p) x → CanTakeOut apps T c (dest p) x net.state

/-- An app whose supports from the held turn on pay `p` at least `x` lets `p`
    take out `x` (`takeout`). -/
theorem canTakeOut_of {apps : Apps E} {p : Participant} {T : Threat E p}
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T) (c : TimedChannel T.ε)
    {d : E} {x : Coins} (hp : p ∈ (c : FixedPart).participants)
    (hsw : (apps (c : FixedPart).appDef).SupportWindow)
    (hpay : ∀ Th proof cand, SentBelow net.state.sent c d x Th → SignedIn net.state.sent p proof →
      (apps (c : FixedPart).appDef).supports c proof cand = true → Th ≤ cand.turnNum →
      x ≤ share cand.outcome d)
    (hH : HoldsShare apps net.state c d x) : CanTakeOut apps T c d x net.state := by
  obtain ⟨proof0, cand0, hH0, hsup0, hch0, -, hB, t, hst, hle⟩ := hH
  have C : Ctx apps p c d x cand0.turnNum net.state.sent :=
    ⟨hp, hsw, fun s hs hc => (hB s hs hc).1, fun pr cd hS hsu _ hTh => hpay _ pr cd hB hS hsu hTh,
      payConc_of hB⟩
  have hn : 0 < (c : FixedPart).n := List.length_pos_of_mem hp
  have hI : TI apps T.ε c d x cand0.turnNum net.state.sent proof0 net.state :=
    ⟨Nitro.participant_received_unforged A.toBounds net, rfl, hH0,
      fun t' ht' => (by rw [hst] at ht'; cases ht'; exact Or.inl hle),
      fun _ _ h => (by rw [hst] at h; cases h), fun _ _ _ h => (by rw [hst] at h; cases h),
      (by rw [hst]; simp only [ChannelStatus.turnNumRecord_open]; omega),
      fun _ _ h => (by rw [hst] at h; cases h)⟩
  exact takeout C A c.dur_le hsup0 hch0 rfl _ net.state hI (le_refl _)

/-- **ForceMove apps whose game library takes nothing from a non-mover are
    IR.** -/
theorem forceMove_IR {apps : Apps E} {a : AppId} {vt : State E → State E → Bool}
    {dest : Participant → E} (ha : apps a = forceMoveRules vt) (hNT : NoTakeFromNonMover vt dest) :
    AppIR apps a dest := by
  intro p T A net c x hca hp hH
  have happ : apps (c : FixedPart).appDef = forceMoveRules vt := by rw [hca, ha]
  refine canTakeOut_of A net c hp (by rw [happ]; exact forceMoveRules_supportWindow vt)
    (fun Th proof cand hB hS hsu hTh => ?_) hH
  rw [happ] at hsu
  exact forceMove_pay hNT hp hB hS hsu hTh

/-- **The consensus app is IR.** -/
theorem consensus_IR {apps : Apps E} {a : AppId} {dest : Participant → E}
    (ha : apps a = consensusRules) : AppIR apps a dest := by
  intro p T A net c x hca hp hH
  have happ : apps (c : FixedPart).appDef = consensusRules := by rw [hca, ha]
  refine canTakeOut_of A net c hp (by rw [happ]; exact consensusRules_supportWindow)
    (fun Th proof cand hB hS hsu hTh => ?_) hH
  rw [happ] at hsu
  exact consensus_pay hp hB hS hsu hTh


end

end TakeOut

open TakeOut in
/-- `p0` is paid at `true`, `q0` at `false`. -/
def destB (q : Participant) : Bool := decide (q = p0)

open TakeOut in
/-- The trivial game fails IR: at `net1`, `p0` holds `s1`, which pays it 5,
    the channel is open at turn 0, and `p0` cannot finalize any outcome that
    pays it 5. -/
theorem appsB_not_IR : ¬ AppIR appsB ⟨0⟩ destB := by
  intro h
  have hS : HoldsShare appsB net1 c0 (destB p0) 5 := by
    refine ⟨[r0, s1], st 1 O1, holds_r0s1, supports_r0s1, rfl, by decide, fun s hs _ => ?_,
      0, rfl, Nat.zero_le _⟩
    rw [List.mem_singleton.1 hs]
    exact ⟨le_refl _, fun _ => by decide⟩
  have hU := h T0 A0 ⟨net1, net1_reachable⟩ tc0 5 rfl (by decide) hS
  exact not_finalizable_from (fun Ω => 5 ≤ share Ω true) cut1 (by decide) net1 (invA_net1 _)
    (Or.inl ⟨0, rfl⟩) (UnbeatableIn.imp (fun ⟨Ω, hf, hs⟩ => ⟨Ω, hf, by simpa [destB] using hs⟩) hU)

open TakeOut in
/-- The trivial game fails `NoTakeFromNonMover`: `q0`'s move at turn 2 cuts
    `p0`'s payment from 5 to 0. -/
theorem vtAll_not_noTake : ¬ NoTakeFromNonMover vtAll destB := by
  intro h
  have := h (st 1 O1) (st 2 cut1) rfl p0 (by rw [mover_c0 rfl]; decide)
  exact absurd this (by decide)

#print axioms appsB_not_IR
#print axioms TakeOut.forceMove_IR
#print axioms TakeOut.consensus_IR

end ArmadaLean.Nitro.CounterexampleIRGame
