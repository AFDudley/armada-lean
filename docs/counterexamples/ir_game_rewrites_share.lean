/-
  Failure test: a game whose rules let the opponent rewrite `p`'s share
  undesirable apps. See an internal design note on app classes
  §5.

  The app is a real ForceMove app: `forceMoveRules vtAll`, whose game
  library accepts every transition (`vtAll`). It meets `Rules.SupportWindow`
  (`forceMoveRules_supportWindow`). It refutes both Nitro-24 statements in
  their form before the `AppIR` premise (`Old_finalizable_or_two_enabled`,
  `Old_single_enabled_is_finalizable`: `finalizable_or_two_enabled_false`,
  `single_enabled_is_finalizable_false`).

  The app is not IR in the standard sense:
  "from any state, an online honest participant can enforce at least what
  its holdings give it" (ForceMove:410-416, 125-130). `appsB_not_IR` proves
  `¬ AppIR appsB ⟨0⟩ destB` (`AppIR`, `ArmadaLean/Types/App.lean`). So the
  app fails the premise `hir` that was added on 2026-11-01 to
  both statements, and this file does not refute the current statements.
  The violating step is exact: the opponent's valid move can cut `p`'s
  share, so `p` must answer every challenge and can never let one expire
  (`vtAll_not_noTake`: `vtAll` fails `NoTakeFromNonMover`). This is not §5
  "unbound griefing": that case re-posts a stale outcome at a higher turn, a
  support-rule failure that `SupportWindow` excludes. Here every move of the
  opponent is a valid game move, signed at its own turn.

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
    (HonestMove.send (st 1 O1)).Feasible appsB (⟨Adjudicator.genesis, [r0], []⟩ : NetworkState Bool p0) :=
  (HonestMove.Feasible_send _ _ _).mpr
    ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide), fun h => absurd h (by decide), by decide, by decide⟩

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
    (hfeas : m.Feasible appsB n) :
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
theorem roundE_first {m : HonestMove Bool} (hfeas : m.Feasible appsB net1) :
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

`p0` answers a challenge whose outcome is in a set `B` (with `O1 ∉ B`) at turn `t`: it signs
`ansP t`, its own move at turn `t + 1`, which pays it 5 again, and then
checkpoints with it. A challenge has the deadline `now + 3 * ε`, and the
answer takes at most three rounds from the round in which the challenge
lands. -/

def ansP (t : Nat) : State Bool := st (t + 1) O1

/-- What `p0` holds of a challenge with the outcome `X` at turn `t`, and a
    support of the challenge state that `p0` holds (the call's proof states
    reach `received`). -/
def XInfo (n : NetworkState Bool p0) (t : Nat) (ch : Challenge Bool) : Prop :=
  ch.state.turnNum = t ∧ t % 2 = 0 ∧ 2 ≤ t ∧ ch.state.isFinal = false ∧ ch.state.channel = c0 ∧
    (∃ x ∈ n.received, x.state = ch.state ∧ q0 ∈ x.signers) ∧ n.HoldsSupportAt appsB c0 t

/-- Every state of `c0` that `p0` signs: the outcome `O1`, non-final, at an
    odd turn. -/
def SentOK (n : NetworkState Bool p0) : Prop :=
  ∀ s ∈ n.sent, s.state.channel = c0 →
    s.state.outcome = O1 ∧ s.state.isFinal = false ∧ s.state.turnNum % 2 = 1 ∧
      s.state = st s.state.turnNum O1

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
structure InvX (B : Outcome Bool → Prop) (n : NetworkState Bool p0) : Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sentOK : SentOK n
  noFin : ∀ t f o, n.chain.statusOf c0 ≠ .finalized t f o
  timing : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → B ch.state.outcome →
    XInfo n t ch ∧ n.chain.now + 2 ≤ ch.deadline ∧
      ((¬ ∃ s ∈ n.sent, s.state = ansP t) → n.chain.now + 4 ≤ ch.deadline)

/-- The invariant inside a round that starts at `n0`; the turn record stays
    at least `R`. -/
structure KX (B : Outcome Bool → Prop) (n0 : NetworkState Bool p0) (R : Nat) (n : NetworkState Bool p0) :
    Prop where
  recvU : ∀ r ∈ n.received, n.Unforged r
  sent : n.sent = n0.sent
  recv : ∀ r ∈ n0.received, r ∈ n.received
  now0 : n0.chain.now ≤ n.chain.now
  noFin : ∀ t f o, n.chain.statusOf c0 ≠ .finalized t f o
  chX : ∀ t ch, n.chain.statusOf c0 = .challenged t ch → B ch.state.outcome →
    XInfo n t ch ∧ (n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ n0.chain.now + 6 ≤ ch.deadline)
  left : ∀ t0 ch0, n0.chain.statusOf c0 = .challenged t0 ch0 → B ch0.state.outcome →
    n.chain.statusOf c0 = n0.chain.statusOf c0 ∨ t0 < (n.chain.statusOf c0).turnNumRecord
  recR : R ≤ (n.chain.statusOf c0).turnNumRecord

theorem KX.start {B : Outcome Bool → Prop} {n0 : NetworkState Bool p0} (hI : InvX B n0) :
    KX B n0 (n0.chain.statusOf c0).turnNumRecord n0 :=
  ⟨hI.recvU, rfl, fun _ h => h, le_refl _, hI.noFin,
    fun t ch h hx => ⟨(hI.timing t ch h hx).1, Or.inl rfl⟩, fun _ _ _ _ => Or.inl rfl, le_refl _⟩

theorem XInfo.mono {n n' : NetworkState Bool p0} {t : Nat} {ch : Challenge Bool}
    (h : XInfo n t ch) (hs : ∀ s ∈ n.sent, s ∈ n'.sent) (hr : ∀ r ∈ n.received, r ∈ n'.received) :
    XInfo n' t ch := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨x, hx, hxs, hxq⟩, P, cd, hH, hsP, hcd, hk⟩ := h
  exact ⟨h1, h2, h3, h4, h5, ⟨x, hr x hx, hxs, hxq⟩, P, cd, fun ss h => (hH ss h).of_subset hs hr, hsP, hcd, hk⟩

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
theorem stepK {B : Outcome Bool → Prop} (hX : ¬ B O1) {n0 n : NetworkState Bool p0} {R : Nat}
    (hI0 : InvX B n0) (hK : KX B n0 R n)
    {caller : Participant} {op : Op Bool} {s' : Adjudicator Bool}
    (h : n.chain.apply appsB caller op = some s') (hU : ∀ ss ∈ op.proofStates, n.Unforged ss)
    (hs'now : n.chain.now ≤ s'.now) :
    KX B n0 R { n with chain := s', received := op.proofStates ++ n.received } := by
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
      obtain ⟨he, h2, hnf, hch, m1, hm1, hm1s, hm1q⟩ := candX hSn hsup hU
        (fun h => hX (h ▸ hx))
      refine ⟨⟨rfl, he, h2, hnf, hch, ⟨m1, List.mem_append_left _ hm1, hm1s, hm1q⟩,
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

/-- `KX` as a step invariant of a sub-round of pure adversary play. -/
theorem KX.stepInv {B : Outcome Bool → Prop} (hX : ¬ B O1) {n0 : NetworkState Bool p0} {R : Nat}
    (hI0 : InvX B n0) :
    T0.StepInvariant appsB (fun _ => True) (KX B n0 R) (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {n ss} _ hfe hK => by
    rw [NetworkState.applyAdv_deliver]
    refine ⟨fun r hr => ?_, hK.sent, fun r hr => List.mem_cons_of_mem _ (hK.recv r hr), hK.now0,
      hK.noFin, fun t ch hc hx => ?_, hK.left, hK.recR⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hfe.of_sent rfl
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
  chain := fun {n caller op} _ hfe hK => by
    cases happ : n.chain.apply appsB caller op with
    | none => rw [NetworkState.applyAdv_chain_none appsB happ]; exact hK
    | some s' =>
      rw [NetworkState.applyAdv_chain_some appsB happ]
      exact stepK hX hI0 hK happ hfe.2 (apply_now_le happ)

open Classical in
/-- `p0`'s move against `X`: answer a challenge with the outcome `X`, first by
    signing `ansP t`, then by a checkpoint with it. -/
noncomputable def idealX (B : Outcome Bool → Prop) (n : NetworkState Bool p0) : HonestMove Bool :=
  match n.chain.statusOf c0 with
  | .challenged t ch =>
    if B ch.state.outcome then
      if h : (∃ s ∈ n.sent, s.state = ansP t) ∧
          (∃ x ∈ n.received, x.state = ch.state ∧ q0 ∈ x.signers) then
        .chain (.checkpoint c0 [Classical.choose h.2, ⟨ansP t, [p0]⟩] (ansP t))
      else .send (ansP t)
    else .wait 0
  | _ => .wait 0

open Classical in
/-- The strategy: `idealX` where it is feasible, a wait otherwise. -/
noncomputable def σX (B : Outcome Bool → Prop) : Strategy Bool p0 := fun n =>
  if (idealX B n).Feasible appsB n then idealX B n else .wait 0

theorem σX_feasible (B : Outcome Bool → Prop) (n : NetworkState Bool p0) :
    (σX B n).Feasible appsB n := by
  unfold σX
  split
  · assumption
  · trivial

/-- `p0`'s move `ansP t0` after `q0`'s challenge state `x` at `t0` is a
    support of `ansP t0`. -/
theorem supports_ansP {ch : Challenge Bool} {t0 : Nat} {x : SignedState Bool}
    (hxs : x.state = ch.state) (hxq : q0 ∈ x.signers) (hinfo : ch.state.turnNum = t0 ∧ t0 % 2 = 0 ∧
      ch.state.isFinal = false ∧ ch.state.channel = c0) :
    (appsB c0.appDef).supports c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0) = true := by
  obtain ⟨ht, he, hf, hc⟩ := hinfo
  have hxc : x.state.channel = c0 := by rw [hxs]; exact hc
  have hb1 : x.byMover = true := (SignedState.byMover_iff _).2
    ⟨q0, by rw [mover_c0 hxc, if_pos (by rw [hxs, ht]; exact he)], hxq⟩
  have hm2 : (ansP t0).mover = some p0 := by
    rw [mover_c0 rfl, if_neg (by simp only [ansP, st]; omega)]
  have hb2 : (⟨ansP t0, [p0]⟩ : SignedState Bool).byMover = true := by
    simp [SignedState.byMover, hm2]
  simp only [appsB, forceMoveRules, validRun, validMove, hb2]
  simp [hxs, hc, hf, ht, ansP, st, vtAll, c0, FixedPart.n, hb1]

/-- `p0` may sign `ansP t`: every state it signed carries `O1` (`SentOK`), so
    the send commits no own-violation of kind (a) (`HonestSend.noConflict`),
    and `p0` moves by the rules from the challenge state at turn `t`, whose
    support it holds (`HonestSend.movesFrom`). -/
theorem send_ansP_feasible {n : NetworkState Bool p0} {t : Nat} {ch : Challenge Bool}
    (hS : SentOK n) (hinfo : XInfo n t ch) : (HonestMove.send (ansP t)).Feasible appsB n := by
  obtain ⟨ht, he, -, hf, hc, ⟨x, hx, hxs, hxq⟩, hsup⟩ := hinfo
  refine (HonestMove.Feasible_send appsB n (ansP t)).mpr
    ⟨fun ⟨s, hs, hc, _, hne⟩ => ?_, ?_, ?_, fun _ => ⟨hsup, [x, ⟨ansP t, [p0]⟩], fun ss hss => ?_,
      supports_ansP hxs hxq ⟨ht, he, hf, hc⟩⟩, fun ⟨s, hs, hc, htn, hne⟩ => ?_, fun ⟨s, hs, hc, hfb⟩ => ?_⟩
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

theorem holds_ansP {n : NetworkState Bool p0} {t : Nat} (h : ∃ s ∈ n.sent, s.state = ansP t) :
    n.Holds ⟨ansP t, [p0]⟩ := by
  obtain ⟨s, hs, hss⟩ := h
  exact ⟨fun q hq => .inl ⟨List.mem_singleton.1 hq, s, hs, hss⟩,
    fun v hv => by simp [ansP, st, State.voucher?] at hv⟩

/-- The three shapes of `σX B n`. -/
theorem σX_cases {B : Outcome Bool → Prop} {n : NetworkState Bool p0} (hI : InvX B n) :
    (σX B n = .wait 0 ∧ ∀ t ch, n.chain.statusOf c0 = .challenged t ch → ¬ B ch.state.outcome) ∨
    (∃ t ch, n.chain.statusOf c0 = .challenged t ch ∧ B ch.state.outcome ∧
      (¬ ∃ s ∈ n.sent, s.state = ansP t) ∧ σX B n = .send (ansP t)) ∨
    (∃ t ch x, n.chain.statusOf c0 = .challenged t ch ∧ B ch.state.outcome ∧
      (∃ s ∈ n.sent, s.state = ansP t) ∧ x ∈ n.received ∧ x.state = ch.state ∧ q0 ∈ x.signers ∧
      σX B n = .chain (.checkpoint c0 [x, ⟨ansP t, [p0]⟩] (ansP t))) := by
  have hwait : idealX B n = .wait 0 → σX B n = .wait 0 := fun h => by
    unfold σX; rw [h]; exact ite_self _
  cases hs : n.chain.statusOf c0 with
  | «open» t =>
    exact Or.inl ⟨hwait (by unfold idealX; rw [hs]), fun t ch h => by cases h⟩
  | finalized t f o => exact absurd hs (hI.noFin t f o)
  | challenged t ch =>
    by_cases hx : B ch.state.outcome
    · have hinfo := (hI.timing t ch hs hx).1
      by_cases hd : (∃ s ∈ n.sent, s.state = ansP t) ∧
          (∃ x ∈ n.received, x.state = ch.state ∧ q0 ∈ x.signers)
      · right; right
        obtain ⟨hx1, hx2, hx3⟩ := Classical.choose_spec hd.2
        refine ⟨t, ch, Classical.choose hd.2, rfl, hx, hd.1, hx1, hx2, hx3, ?_⟩
        have hid : idealX B n = .chain (.checkpoint c0 [Classical.choose hd.2, ⟨ansP t, [p0]⟩] (ansP t)) := by
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
          hd ⟨h, hinfo.2.2.2.2.2.1⟩
        refine ⟨t, ch, rfl, hx, hns, ?_⟩
        have hid : idealX B n = .send (ansP t) := by
          unfold idealX; rw [hs]; simp only [if_pos hx, dif_neg hd]
        unfold σX
        rw [hid, if_pos (send_ansP_feasible hI.sentOK hinfo)]
    · exact Or.inl ⟨hwait (by unfold idealX; rw [hs]; simp only [if_neg hx]),
        fun t' ch' h => by cases h; exact hx⟩

/-- At the end of a round from `n0`, before `n0`'s clock plus 2, no outcome in
    `B` is finalized. -/
theorem notFinX {B : Outcome Bool → Prop} {n0 n : NetworkState Bool p0} {R : Nat} (hI0 : InvX B n0)
    (hK : KX B n0 R n) (hnow : n.chain.now < n0.chain.now + 2) :
    ∀ Ω, B Ω → ¬ n.Finalized c0 Ω := by
  intro Ω hB hf
  simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf
  cases hs : n.chain.statusOf c0 with
  | «open» t => rw [hs] at hf; simp at hf
  | finalized t f o => exact hK.noFin t f o hs
  | challenged t ch =>
    rw [hs] at hf
    simp only [ChannelStatus.finalizedWith_challenged] at hf
    split at hf
    · rename_i hd
      have hx : B ch.state.outcome := by rw [Option.some.inj hf]; exact hB
      rcases (hK.chX t ch hs hx).2 with h0 | h6
      · rw [hs] at h0
        have := (hI0.timing t ch h0.symm hx).2.1
        exact absurd hd (not_le.mpr (lt_of_lt_of_le hnow this))
      · exact absurd hd (not_le.mpr (lt_of_lt_of_le hnow (le_trans (Nat.add_le_add_left (by decide) _) h6)))
    · cases hf

theorem bound6 {a b : Nat} (h : a < b + 2) : a + 4 ≤ b + 6 := by omega
theorem bound4 {a b : Nat} (h : a < b + 2) : a + 2 ≤ b + 4 := by omega

/-- `KX` over a sub-round of pure adversary play. -/
theorem KX.nil {B : Outcome Bool → Prop} (hX : ¬ B O1) {n0 n n' : NetworkState Bool p0} {R : Nat}
    {t : Time} (hI0 : InvX B n0) (hseq : T0.RoundSeq appsB t [] n n') (hK : KX B n0 R n) :
    KX B n0 R n' :=
  Threat.RoundSeq.nil_invariant hseq (KX.stepInv hX hI0).anyGuard hK

theorem KX.lower {B : Outcome Bool → Prop} {n0 n : NetworkState Bool p0} {R R' : Nat}
    (hK : KX B n0 R n) (hR : R' ≤ (n.chain.statusOf c0).turnNumRecord) : KX B n0 R' n :=
  ⟨hK.recvU, hK.sent, hK.recv, hK.now0, hK.noFin, hK.chX, hK.left, hR⟩

/-- The answer of `p0`: its checkpoint with `ansP t0` turns a standing
    challenge at `t0` into an open status at `t0 + 1`. -/
theorem checkpoint_apply {s : Adjudicator Bool} {t0 : Nat} {ch : Challenge Bool}
    {x : SignedState Bool} (hs : s.statusOf c0 = .challenged t0 ch) (hd : s.now < ch.deadline)
    (hxs : x.state = ch.state) (hxq : q0 ∈ x.signers) (hinfo : ch.state.turnNum = t0 ∧ t0 % 2 = 0 ∧
      ch.state.isFinal = false ∧ ch.state.channel = c0) :
    s.apply appsB p0 (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)) =
      some (s.setStatus c0 (.open (t0 + 1))) := by
  have hsup := supports_ansP hxs hxq hinfo
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
theorem roundX {B : Outcome Bool → Prop} (hX : ¬ B O1) {n0 n' : NetworkState Bool p0} (hI0 : InvX B n0)
    (hround : T0.Round appsB (σX B n0) n0 n') :
    (∀ Ω, B Ω → ¬ n'.Finalized c0 Ω) ∧ InvX B (n'.applyHonest (σX B n0)) := by
  have hbound := round_bound hround
  have hK0 := KX.start (B := B) hI0
  -- the start of the next round, from `KX` at the end and a fact about a
  -- standing challenge
  have hnext : ∀ {R : Nat} (hK : KX B n0 R n') (m : HonestMove Bool)
      (hsent : ∀ s ∈ (n'.applyHonest m).sent, s ∈ n'.sent ∨ ∃ t0 ch0,
        n0.chain.statusOf c0 = .challenged t0 ch0 ∧ B ch0.state.outcome ∧ s = ⟨ansP t0, [p0]⟩)
      (hrecv : (n'.applyHonest m).received = n'.received)
      (hchain : (n'.applyHonest m).chain.statusOf c0 = n'.chain.statusOf c0 ∧
        (n'.applyHonest m).chain.now = n'.chain.now)
      (hS0 : ∀ t ch, n'.chain.statusOf c0 = .challenged t ch → B ch.state.outcome →
        n'.chain.statusOf c0 = n0.chain.statusOf c0 →
        (n'.applyHonest m).chain.now + 2 ≤ ch.deadline ∧
          ((¬ ∃ s ∈ (n'.applyHonest m).sent, s.state = ansP t) →
            (n'.applyHonest m).chain.now + 4 ≤ ch.deadline)),
      InvX B (n'.applyHonest m) := by
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
    have hKL : KX B n0 (t0 + 1) (n1.applyAdv appsB (.land (.checkpoint c0 [x, ⟨ansP t0, [p0]⟩] (ansP t0)))) := by
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

/-- `p0` prevents every outcome in a set `B` that does not hold `O1`. -/
theorem prevents_bad (B : Outcome Bool → Prop) (hX : ¬ B O1) :
    Prevents appsB T0 (fun n => ∃ Ω, n.Finalized c0 Ω ∧ B Ω) net1 := by
  have hI1 : InvX B net1 := by
    refine ⟨fun x hx => ?_, fun s hs _ => ?_,
      fun t f o h => (by simp [net1, Adjudicator.genesis, Adjudicator.statusOf] at h),
      fun t ch h => (by simp [net1, Adjudicator.genesis, Adjudicator.statusOf] at h)⟩
    · rw [List.mem_singleton.1 hx]; exact unforged_r0 _
    · rw [List.mem_singleton.1 hs]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hrun : ∀ {n1}, Run appsB T0 (σX B) net1 n1 → InvX B n1 := by
    intro n1 h
    induction h with
    | refl => exact hI1
    | round _ hr ih => exact (roundX hX ih hr).2
  exact ⟨σX B, σX_feasible B, fun n1 n2 hr hround ⟨Ω, hf, hB⟩ =>
    (roundX hX (hrun hr) hround).1 Ω hB hf⟩

theorem prevents_other (X : Outcome Bool) (hX : X ≠ O1) :
    Prevents appsB T0 (fun n => n.Finalized c0 X) net1 := by
  obtain ⟨σ, hσ, hprev⟩ := prevents_bad (· = X) (fun h => hX h.symm)
  exact ⟨σ, hσ, fun n1 n2 hr hround hf => hprev n1 n2 hr hround ⟨X, hf, rfl⟩⟩

/-! ## The two statements fail, in their form before `AppIR` -/

/-- `Spec.finalizable_or_two_enabled` before the IR premise
    `hir : AppIR apps c.appDef dest` was added on 2026-11-01. -/
def Old_finalizable_or_two_enabled : Prop :=
  ∀ (apps : Apps Bool) {p : Participant} (T : Threat Bool p)
    (_A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε)
    (_happ : (apps (c : FixedPart).appDef).SupportWindow)
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof candidate = true ∧
      candidate.channel = (c : FixedPart)),
    (∃ Ω, Finalizable apps T (c : FixedPart) Ω net.state) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T (c : FixedPart) Ω1 net.state ∧
      Enabled apps T (c : FixedPart) Ω2 net.state)

/-- `Spec.single_enabled_is_finalizable` before the IR premise
    `hir : AppIR apps c.appDef dest` was added on 2026-11-01. -/
def Old_single_enabled_is_finalizable : Prop :=
  ∀ (apps : Apps Bool) {p : Participant} (T : Threat Bool p)
    (_A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε)
    (_happ : (apps (c : FixedPart).appDef).SupportWindow)
    (_hp : p ∈ (c : FixedPart).participants)
    (_hsupp : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) →
      ∃ proof, (∀ ss ∈ proof, net.state.Holds ss) ∧
      (apps (c : FixedPart).appDef).supports (c : FixedPart) proof t.state = true)
    (Ω : Outcome Bool) (_hΩ : Enabled apps T (c : FixedPart) Ω net.state)
    (_huniq : ∀ Ω', Enabled apps T (c : FixedPart) Ω' net.state → Ω' = Ω),
    Finalizable apps T (c : FixedPart) Ω net.state

theorem finalizable_or_two_enabled_false : ¬ Old_finalizable_or_two_enabled := by
  intro h
  rcases h appsB T0 A0 ⟨net1, net1_reachable⟩ tc0 appsB_supportWindow (by decide)
      ⟨[r0, s1], st 1 O1, holds_r0s1, supports_r0s1, rfl⟩ with
    ⟨Ω, hΩ⟩ | ⟨Ω1, Ω2, hne, hE1, hE2⟩
  · exact not_finalizable Ω hΩ
  · by_cases h1 : Ω1 = O1
    · exact hE2 (prevents_other Ω2 (fun h2 => hne (h1.trans h2.symm)))
    · exact hE1 (prevents_other Ω1 h1)

theorem single_enabled_is_finalizable_false : ¬ Old_single_enabled_is_finalizable := by
  intro h
  refine not_finalizable O1 (h appsB T0 A0 ⟨net1, net1_reachable⟩ tc0 appsB_supportWindow
    (by decide) (fun t ht _ => ?_) O1 enabled_O1 (fun Ω' hE => ?_))
  · rw [List.mem_singleton.1 ht]
    exact ⟨[r0, s1], holds_r0s1, supports_r0s1⟩
  · by_contra hne
    exact hE (prevents_other Ω' hne)

#print axioms finalizable_or_two_enabled_false
#print axioms single_enabled_is_finalizable_false

/-! ## The game is not IR

`AppIR`, `HoldsShare` and `NoTakeFromNonMover` are the library's
(`ArmadaLean/Types/App.lean`). -/

/-- `p0` is paid at `true`, `q0` at `false`. -/
def destB (q : Participant) : Bool := decide (q = p0)

/-- The trivial game fails IR: at `net1`, `p0` holds `s1`, which pays it 5,
    the channel is open at turn 0, and `p0` cannot finalize any outcome that
    pays it 5. So `appsB` fails the premise `hir` of both Nitro-24
    statements. -/
theorem appsB_not_IR : ¬ AppIR appsB ⟨0⟩ destB := by
  intro h
  have hS : HoldsShare appsB net1 c0 (destB p0) 5 := by
    refine ⟨[r0, s1], st 1 O1, holds_r0s1, supports_r0s1, rfl, by decide, fun s hs _ => ?_,
      0, rfl, Nat.zero_le _⟩
    rw [List.mem_singleton.1 hs]
    exact ⟨le_refl _, fun _ => by decide⟩
  have hU := h.takeOut T0 A0 ⟨net1, net1_reachable⟩ tc0 5 rfl (by decide) hS
  exact not_finalizable_from (fun Ω => 5 ≤ share Ω true) cut1 (by decide) net1 (invA_net1 _)
    (Or.inl ⟨0, rfl⟩) (UnbeatableIn.imp (fun ⟨Ω, hf, hs⟩ => ⟨Ω, hf, by simpa [destB] using hs⟩) hU)

/-- The trivial game is not desirable: it fails IR (`appsB_not_IR`). -/
theorem appsB_not_desirable : ¬ Desirable appsB ⟨0⟩ destB := fun h => appsB_not_IR h.ir

/-- The trivial game fails `NoTakeFromNonMover`: `q0`'s move at turn 2 cuts
    `p0`'s payment from 5 to 0. -/
theorem vtAll_not_noTake : ¬ NoTakeFromNonMover vtAll destB := by
  intro h
  have := h (st 1 O1) (st 2 cut1) rfl p0 (by rw [mover_c0 rfl]; decide)
  exact absurd this (by decide)

#print axioms appsB_not_IR
#print axioms appsB_not_desirable
#print axioms vtAll_not_noTake

end ArmadaLean.Nitro.CounterexampleIRGame
