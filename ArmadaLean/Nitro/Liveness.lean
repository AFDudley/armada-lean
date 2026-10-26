/-
  Nitro protocol theorems: unbeatable strategies, finalizability, value
  algorithms, ledger and virtual channel constructions, and the SATP
  protocol guarantees. Every proof is `sorry`. Each doc comment cites the
  source lines and the property ids of `docs/nitro-theorems.md`.
-/
import ArmadaLean.Nitro.Safety

namespace ArmadaLean.Nitro

open Classical

/-- S2-31. S2:779-781: "We will restrict ourselves to looking at strategies
    and counter-strategies involving transfer operations only, ignoring
    deposits and withdrawals." An adversary that plays only transfers and
    lets time pass. -/
def Threat.TransfersOnly {p : Participant} (T : Threat p) : Prop :=
  ∀ net m, T.feasible net m →
    (∃ caller a b x, m = .chain caller (.transfer a b x)) ∨ (∃ dt, m = .tick dt)

/-- An adversary that plays only transfers and claims. S2:1147-1151 reasons
    about Nitro redistribution with these two operations. -/
def Threat.RedistributionOnly {p : Participant} (T : Threat p) : Prop :=
  ∀ net m, T.feasible net m →
    (∃ caller op, m = .chain caller op ∧ op.isRedistribution = true) ∨ (∃ dt, m = .tick dt)

/-- An honest move that does not let time pass. -/
def HonestMove.NoWait : HonestMove → Prop
  | .wait _ => False
  | _ => True

/-- `Unbeatable` with no `wait` move: the goal is reached "instantly", with
    no challenge period (S2:1046-1047: "A was able to withdraw their funds
    instantly, without having to wait for the channel timeout"). -/
inductive UnbeatableNoWait (apps : Apps) {p : Participant} (T : Threat p)
    (G : NetworkState p → Prop) : NetworkState p → Prop
  | done {net} : G net → UnbeatableNoWait apps T G net
  | move {net} (m : HonestMove) : m.Feasible net → m.NoWait →
      (∀ advs net', T.FeasibleSeq apps net advs net' →
        UnbeatableNoWait apps T G (net'.applyHonest apps m)) →
      UnbeatableNoWait apps T G net

/-- S1-A06, S1-A07. S1:1092-1125 and S1:1150-1184: through the
    PreFundSetup and PostFundSetup phases (the first `2n` states) every
    transition keeps the resolution. -/
def SetupPhaseKeepsOutcome (vt : State → State → Prop) (c : FixedPart) : Prop :=
  ∀ s1 s2, vt s1 s2 → s1.channel = c → s1.turnNum + 1 < 2 * c.n → s2.outcome = s1.outcome

/-- A list of claims only. -/
def OnlyClaims (ops : List (Participant × Op)) : Prop :=
  ∀ e ∈ ops, ∃ g a x, e.2 = Op.claim g a x

/-- S2-16, S2-21, S1-B01, S1-C03, S4-0070-05, S4-0080-06. S2:395-398: "where
    the channel L itself has enough coins in the adjudicator to cover the
    entire allocation ... A will receive all x coins allocated to them in ω."
    The strategy is one transfer. -/
theorem directly_funded_pays (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (o : Allocation)
    (hf : net.Finalized c (.allocation o)) (hfund : net.chain.DirectlyFunded c) :
    UnbeatableNoWait apps T
      (fun net' => net.chain.balances.get p.address + o.owed p.address ≤
        net'.chain.balances.get p.address) net := by
  sorry

/-- S2-17, S2-21, S2-16. S2:480-481 and S2:590-593: a finalizable allocation
    in a channel funded for `p` pays `p` its allocation. -/
theorem finalizable_funded_pays (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (o : Allocation)
    (hf : Finalizable apps T c (.allocation o) net) (hfund : FundedFor apps T c o.total net) :
    CanObtain apps T p.address (net.chain.balances.get p.address + o.owed p.address) net := by
  sorry

/-- S2-13, S2-21, S2-23, S4-0070-05, S1-A14. S2:296-299: a participant who
    holds a conclusion proof can register it. Under the consensus app no
    other participant can finalize a different outcome without `p`'s
    signature, so the outcome is finalizable for `p`. -/
theorem conclusion_proof_finalizable (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState)
    (Ω : Outcome) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hchain : net.chain.finalOutcome c.address = none ∨ net.chain.finalOutcome c.address = some Ω) :
    UnbeatableNoWait apps T (fun net' => net'.Finalized c Ω) net := by
  sorry

/-- S2-12, S1-B01, S1-B03, S4-0070-06, S1-C02. S2:292-296: "one participant
    launches an on-chain challenge, starting a timeout period; if no other
    participant responds during the timeout period, then the challenge times
    out and the outcome corresponding to the challenge state is finalized."
    Under the consensus app, a participant who holds a supported state and
    has signed no higher state can finalize that state's outcome. -/
theorem latest_state_finalizable (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState)
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hlatest : ∀ t ∈ net.sent, t.state.channel = c → t.state.turnNum ≤ ss.state.turnNum)
    (hfinal : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = ss.state.outcome)
    (hdur : 0 < c.challengeDuration)
    (hrec : (net.chain.statusOf c).turnNumRecord ≤ ss.state.turnNum)
    (hchain : net.chain.finalOutcome c.address = none ∨
      net.chain.finalOutcome c.address = some ss.state.outcome) :
    Finalizable apps T c ss.state.outcome net := by
  sorry

/-- S1-B05. S1:1511-1529: "as long as Alice notices Bob's challenge within
    the timeout period, she cannot hurt her position by playing on as though
    still in Collaborative mode ... all the moves made in Collaborative still
    stand." A participant who holds a supported state above the challenge
    state can reopen the channel at or above that turn before the deadline. -/
theorem late_observer_can_respond (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState)
    (t : Nat) (ch : Challenge) (hc : apps c.appDef = consensusRules)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hst : net.chain.statusOf c = .challenged t ch) (hgt : t < ss.state.turnNum)
    (hnow : net.chain.now < ch.deadline) :
    UnbeatableNoWait apps T
      (fun net' => net'.chain.mode c = .open ∧
        ss.state.turnNum ≤ (net'.chain.statusOf c).turnNumRecord) net := by
  sorry

/-- S2-22. S2:612-614: "The definition of finalizability excludes the case
    where two different finalizable outcomes are held by different
    participants, as in this case at least one participant's strategy would
    be beatable by the other participant's strategy." -/
theorem finalizable_unique (apps : Apps) (Ts : Threats apps) (v : Views) (hv : v.Consistent)
    (c : FixedPart) (p q : Participant) (hpq : p ≠ q) (Ω Ω' : Outcome)
    (hp : Finalizable apps (Ts.T p) c Ω (v p)) (hq : Finalizable apps (Ts.T q) c Ω' (v q)) :
    Ω = Ω' := by
  sorry

/-- S2-22. S2:597-611: "exactly one of the following statements is true
    about a channel χ at any point in time: 1. Finalized outcome ... 2. One
    participant has multiple finalizable outcomes ... 3. Multiple participants
    share one finalizable outcome ... 4. No finalizable outcomes." -/
theorem channel_finalizability_cases (apps : Apps) (Ts : Threats apps) (v : Views)
    (hv : v.Consistent) (c : FixedPart) (p0 : Participant) :
    (∃ Ω, (v p0).Finalized c Ω) ∨
    (∃ p, p ∈ c.participants ∧ (∃ Ω, Finalizable apps (Ts.T p) c Ω (v p)) ∧
      ∀ q, q ∈ c.participants → q ≠ p → ∀ Ω, ¬ Finalizable apps (Ts.T q) c Ω (v q)) ∨
    (∃ Ω p q, p ∈ c.participants ∧ q ∈ c.participants ∧ p ≠ q ∧
      Finalizable apps (Ts.T p) c Ω (v p) ∧ Finalizable apps (Ts.T q) c Ω (v q) ∧
      ∀ r, r ∈ c.participants → ∀ Ω', Finalizable apps (Ts.T r) c Ω' (v r) → Ω' = Ω) ∨
    (∀ p, p ∈ c.participants → ∀ Ω, ¬ Finalizable apps (Ts.T p) c Ω (v p)) := by
  sorry

/-- S2-24. S2:653-656: "For any participant, p, in a channel, χ, exactly one
    of the following statements is true at a given point in time: 1. p has at
    least one finalizable outcome. 2. p has at least two enabled outcomes." -/
theorem finalizable_or_two_enabled (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (hp : p ∈ c.participants) :
    (∃ Ω, Finalizable apps T c Ω net) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T c Ω1 net ∧ Enabled apps T c Ω2 net) := by
  sorry

/-- S2-24. S2:657-658: "if a participant has only enabled a single outcome,
    that outcome must be finalizable for them." -/
theorem single_enabled_is_finalizable (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (hp : p ∈ c.participants)
    (Ω : Outcome) (hΩ : Enabled apps T c Ω net)
    (huniq : ∀ Ω', Enabled apps T c Ω' net → Ω' = Ω) :
    Finalizable apps T c Ω net := by
  sorry

/-- S2-24, S2-21. A finalizable outcome is enabled: `p` cannot prevent what
    `p` can force. -/
theorem finalizable_is_enabled (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (Ω : Outcome)
    (h : Finalizable apps T c Ω net) : Enabled apps T c Ω net := by
  sorry

/-- S2-23, S1-B06, S1-A06, S1-A07. S2:635-636, S2:639-640: at the funding
    point, "After the first n states have been broadcast", the outcome is
    universally finalizable. S1:862-871: the prefund states are "exactly what
    they need to launch a challenge on-chain to recover their funds". The
    setup phase keeps the outcome (S1:1092-1125, S1:1150-1184). -/
theorem funding_point_universally_finalizable (apps : Apps) (Ts : Threats apps) (v : Views)
    (hv : v.Consistent) (c : FixedPart) (Ω : Outcome) (vt : State → State → Prop)
    (hc : apps c.appDef = forceMoveRules vt) (hsetup : SetupPhaseKeepsOutcome vt c)
    (hn : 0 < c.n) (hdur : 0 < c.challengeDuration) (h : AtFundingPoint v c Ω)
    (hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) :
    UniversallyFinalizable apps Ts v c Ω := by
  sorry

/-- S2-23, S1-A14. S2:637-640: "When a single conclusion proof is known to
    each participant ... the channel is in the concluded state." The
    concluded outcome is universally finalizable. -/
theorem concluded_universally_finalizable (apps : Apps) (Ts : Threats apps) (v : Views)
    (hv : v.Consistent) (c : FixedPart) (Ω : Outcome) (hc : apps c.appDef = consensusRules)
    (h : Concluded v c Ω)
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = Ω)
    (hchain : ∀ p, (v p).chain.finalOutcome c.address = none ∨
      (v p).chain.finalOutcome c.address = some Ω) :
    UniversallyFinalizable apps Ts v c Ω := by
  sorry

/-- S2-49 (consensus game, S2:660-688), S3-08, S4-0020-01. S2:684-688:
    "Throughout the only enabled outcomes for any participant are Ω1 and Ω2.
    In particular, a participant has the finalizable outcome [χ ↦ Ω1]_p
    until they approve the transition, and then enabled outcomes
    [χ ↦ Ω1, Ω2]_(p) until they receive the final state." Under the
    consensus app: a participant who holds an all-signed state with `Ω1` and
    has signed at most one higher state, with `Ω2`, has only `Ω1` and `Ω2`
    enabled. -/
theorem consensus_enabled_outcomes (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (c : FixedPart) (ss : SignedState)
    (Ω1 Ω2 : Outcome) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hΩ1 : ss.state.outcome = Ω1)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c →
      t.state.turnNum ≤ ss.state.turnNum ∨ t.state.outcome = Ω2)
    (hchain : net.chain.finalOutcome c.address = none) (Ω : Outcome)
    (hen : Enabled apps T c Ω net) : Ω = Ω1 ∨ Ω = Ω2 := by
  sorry

/-- S2-30, S2-16. S2:775-777: "reasoning about redistribution is easy in
    Turbo: if you can find one strategy to move a certain amount into an
    address, then no-one else can prevent this from occurring." A transfer
    sequence that reaches balance `x` at `a` gives an unbeatable strategy
    against a transfer-only adversary. -/
theorem turbo_redistribution_unbeatable (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p)
    (hturbo : net.chain.TurboOnly) (hdag : net.chain.IsDAG)
    (ops : List (Participant × Op)) (hops : OnlyTransfers ops) (a : Address) (x : Coins)
    (hgoal : x ≤ (Adjudicator.applyAll apps ops net.chain).balances.get a) :
    CanObtain apps T a x net := by
  sorry

/-- S2-31. S2:785-787: "a deposit into the system cannot reduce the value of
    any address and cannot increase the value of any address by more than the
    value of the deposit." -/
theorem deposit_bounds_value (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (a : Address) (y x x' : Coins)
    (hv : Value apps T net x)
    (hv' : Value apps T { net with chain := net.chain.deposit a y } x') :
    x ≤ x' ∧ x' ≤ x + y := by
  sorry

/-- S2-31. S2:787-789: "Withdrawals can only occur from participant
    addresses and are the only way funds can leave these addresses, so cannot
    affect values elsewhere." A withdrawal by another participant leaves
    `p`'s value unchanged. -/
theorem withdrawal_affects_only_owner (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p) (q : Participant) (hq : q ≠ p) (y : Coins)
    (s' : Adjudicator) (h : net.chain.withdraw q q y = some s') (x : Coins) :
    Value apps T net x ↔ Value apps T { net with chain := s' } x := by
  sorry

/-- S2-32. S2:792-794: "While it is technically possible to create outcomes
    with cycles, it is also possible for any participant in the channel to
    prevent this from happening." Under the consensus app a participant who
    signs no state can keep the outcome network acyclic. -/
theorem participant_can_prevent_cycles (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (net : NetworkState p)
    (hc : ∀ c : FixedPart, p ∈ c.participants → apps c.appDef = consensusRules)
    (hdag : net.chain.IsDAG) (hsent : net.sent = []) :
    Prevents apps T (fun net' => ¬ net'.chain.IsDAG) net := by
  sorry

/-- S2-33, S2-34, S2-32. S2:836-837: "it is impossible to find a strategy
    that gives any node a value higher than allocated by this algorithm."
    Against a transfer-only adversary, on a DAG of allocation outcomes. -/
theorem turbo_value_upper_bound (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p)
    (hturbo : net.chain.TurboOnly) (order : List Address)
    (ho : net.chain.IsTopologicalOrder order) (n : Address) (x : Coins)
    (h : CanObtain apps T n x net) : x ≤ net.chain.turboValue order n := by
  sorry

/-- S2-33, S2-35, S2-18. S2:837-839: "It is also not hard to construct a
    strategy for a node to obtain the value allocated by the algorithm, if
    necessary by actually implementing the algorithm up until that node." -/
theorem turbo_value_achievable (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p)
    (hturbo : net.chain.TurboOnly) (order : List Address)
    (ho : net.chain.IsTopologicalOrder order) (n : Address) :
    CanObtain apps T n (net.chain.turboValue order n) net := by
  sorry

/-- S2-18, S2-33, S2-34, S2-35. S2:482-484 with S2:835-839: on a Turbo DAG
    the value of `p`'s network state is the algorithm's value of `p`'s
    address. -/
theorem turbo_value_is_value (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (hT : T.TransfersOnly) (net : NetworkState p)
    (hturbo : net.chain.TurboOnly) (order : List Address)
    (ho : net.chain.IsTopologicalOrder order) :
    Value apps T net (net.chain.turboValue order p.address) := by
  sorry

/-- S2-36. S2:842-843: "calling transfers out of order does not affect the
    ultimate result." Two exhausted transfer sequences from one Turbo state
    give the same balances. -/
theorem turbo_order_independent (apps : Apps) (s : Adjudicator) (hturbo : s.TurboOnly)
    (hdag : s.IsDAG) (ops1 ops2 : List (Participant × Op)) (h1 : OnlyTransfers ops1)
    (h2 : OnlyTransfers ops2) (hx1 : (Adjudicator.applyAll apps ops1 s).TransferExhausted)
    (hx2 : (Adjudicator.applyAll apps ops2 s).TransferExhausted) (a : Address) :
    (Adjudicator.applyAll apps ops1 s).balances.get a =
      (Adjudicator.applyAll apps ops2 s).balances.get a := by
  sorry

/-- S2-33, S2-36. S2:819 "Choose a topological ordering": the algorithm's
    value does not depend on which topological ordering is chosen. -/
theorem turbo_value_order_choice_irrelevant (s : Adjudicator) (hturbo : s.TurboOnly)
    (o1 o2 : List Address) (h1 : s.IsTopologicalOrder o1) (h2 : s.IsTopologicalOrder o2)
    (n : Address) : s.turboValue o1 n = s.turboValue o2 n := by
  sorry

/-- S2-37, S4-0060-07, S4-0080-08. S2:859-865: "χ is funded with 6 coins by
    L for both A and B ... Once it is on-chain, the transfer operation
    T(L, χ, 6) is all that is required to make χ directly funded. From the
    Turbo redistribution result, we know that this redistribution strategy is
    unbeatable." -/
theorem ledger_offload_funds_subchannel (apps : Apps) (Ts : Threats apps) (v : Views)
    (hv : v.Consistent) (w : LedgerWithSub) (hw : w.Holds apps Ts v) :
    FundedFor apps (Ts.T w.A) w.χ w.c (v w.A) ∧ FundedFor apps (Ts.T w.B) w.χ w.c (v w.B) := by
  sorry

/-- S2-49 (S2:891-922, §5.4.1 Opening a Sub-channel), S4-0060-07. From
    `⟦L : x⟧, [L ↦ (A : a, B : b)]_{A,B}` and `[χ ↦ (A : a', B : b')]_{A,B}`
    with `a' ≤ a`, `b' ≤ b`, the update
    `[L ↦ (A : a − a', B : b − b', χ : a' + b')]_{A,B}` preserves the value
    of `A` and `B`. -/
theorem subchannel_open_value_preserving (apps : Apps) (Ts : Threats apps) (v v' : Views)
    (hv : v.Consistent) (hv' : v'.Consistent) (A B : Participant) (L χ : FixedPart)
    (a b a' b' : Coins) (ha : a' ≤ a) (hb : b' ≤ b)
    (hL : IsLedgerChannel apps L) (hLp : L.participants = [A, B]) (hχp : χ.participants = [A, B])
    (hbal : v.HoldsBalance L.address (a + b)) (hbal' : v'.HoldsBalance L.address (a + b))
    (h1 : v.FinalizableBy apps Ts L (.allocation [alloc A.address a, alloc B.address b]) [A, B])
    (h2 : v.FinalizableBy apps Ts χ (.allocation [alloc A.address a', alloc B.address b']) [A, B])
    (h3 : v'.FinalizableBy apps Ts L
      (.allocation [alloc A.address (a - a'), alloc B.address (b - b'), alloc χ.address (a' + b')])
      [A, B])
    (h4 : v'.FinalizableBy apps Ts χ (.allocation [alloc A.address a', alloc B.address b']) [A, B])
    (hother : ∀ p, p = A ∨ p = B → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T A) (v A) (v' A) ∧ SameValue apps (Ts.T B) (v B) (v' B) := by
  sorry

/-- S2-49 (S2:939-957, §5.4.2 Closing a Sub-channel), S4-0080-07. From
    `[L ↦ (A : a, B : b, χ : c)]_{A,B}` and the concluded
    `[χ ↦ (A : a', B : b')]_{A,B}` with `a' + b' = c`, the update
    `[L ↦ (A : a + a', B : b + b')]_{A,B}` preserves the value of `A` and
    `B`. -/
theorem subchannel_close_value_preserving (apps : Apps) (Ts : Threats apps) (v v' : Views)
    (hv : v.Consistent) (hv' : v'.Consistent) (w : LedgerWithSub) (a' b' : Coins)
    (hc : a' + b' = w.c) (hw : w.Holds apps Ts v)
    (hχ : v.FinalizableBy apps Ts w.χ
      (.allocation [alloc w.A.address a', alloc w.B.address b']) [w.A, w.B])
    (h3 : v'.FinalizableBy apps Ts w.L
      (.allocation [alloc w.A.address (w.a + a'), alloc w.B.address (w.b + b')]) [w.A, w.B])
    (hbal' : v'.HoldsBalance w.L.address (w.a + w.b + w.c))
    (hother : ∀ p, p = w.A ∨ p = w.B → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T w.A) (v w.A) (v' w.A) ∧ SameValue apps (Ts.T w.B) (v w.B) (v' w.B) := by
  sorry

/-- S2-49 (S2:959-995, §5.4.3 Topping Up a Ledger Channel), S4-0060-05.
    S2:982-985: moving `A`'s entry to the end with the larger total
    `a + a'` "is a safe operation due to the precedence rules: as the channel
    is currently underfunded A would still only receive a if the outcome went
    to chain." The reordered outcome affords `A` exactly `a`. -/
theorem ledger_topup_reorder_safe (A B χ : Address) (a b c a' : Coins) (hAB : A ≠ B)
    (hAχ : A ≠ χ) (hBχ : B ≠ χ) :
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] A = a ∧
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] B = b ∧
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] χ = c := by
  sorry

/-- S2-49 (S2:989-995, §5.4.3 steps 3-4), S2-04. After the deposit
    `D_L(a')` the reordered outcome is fully funded: every entry, including
    `A`'s raised one, is affordable in full. -/
theorem ledger_topup_deposit_funds (A B χ : Address) (a b c a' : Coins) (hAB : A ≠ B)
    (hAχ : A ≠ χ) (hBχ : B ≠ χ) :
    Allocation.paidTo (a + b + c + a') [alloc B b, alloc χ c, alloc A (a + a')] A = a + a' ∧
    Allocation.paidTo (a + b + c + a') [alloc A (a + a'), alloc B b, alloc χ c] A = a + a' := by
  sorry

/-- S2-49 (S2:997-1047, §5.4.4 Partial Withdrawal from a Ledger Channel).
    S2:1046-1047: "A was able to withdraw their funds instantly, without
    having to wait for the channel timeout." With the conclusion proof for
    `[L ↦ (L' : a + b + c, A : a')]_{A,B}` and `⟦L : x⟧`, `A` obtains `a'`
    with no wait, and `L'` is funded with `a + b + c` for `A` and `B`. -/
theorem ledger_partial_withdrawal (apps : Apps) (Ts : Threats apps) (v : Views)
    (hv : v.Consistent) (A B : Participant) (L L' χ : FixedPart) (a b c a' : Coins)
    (hL : IsLedgerChannel apps L) (hL' : IsLedgerChannel apps L') (hLp : L.participants = [A, B])
    (hL'p : L'.participants = [A, B]) (hLL' : L ≠ L')
    (hbal : v.HoldsBalance L.address (a + b + c + a'))
    (hconc : Concluded v L (.allocation [alloc L'.address (a + b + c), alloc A.address a']))
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L → t.state.isFinal = true →
      t.state.outcome = .allocation [alloc L'.address (a + b + c), alloc A.address a'])
    (hopen : ∀ p, (v p).chain.finalOutcome L.address = none)
    (hL'out : v.FinalizableBy apps Ts L'
      (.allocation [alloc A.address a, alloc B.address b, alloc χ.address c]) [A, B]) :
    UnbeatableNoWait apps (Ts.T A)
      (fun net' => (v A).chain.balances.get A.address + a' ≤ net'.chain.balances.get A.address)
      (v A) ∧
    FundedFor apps (Ts.T A) L' (a + b + c) (v A) ∧ FundedFor apps (Ts.T B) L' (a + b + c) (v B) := by
  sorry

/-- S2-44. S2:1148-1151: "it is possible to construct situations where the
    same outcome can lead to different values, depending on the order in
    which guarantees are claimed." Figure 23: two guarantees `G1 = (J|I, A)`
    and `G2 = (J|I, B)` of 5 coins each on `J ↦ (I : 5, A : 5, B : 5)`. -/
theorem claim_order_dependent (apps : Apps) :
    ∃ (s : Adjudicator) (ops1 ops2 : List (Participant × Op)) (a : Address),
      OnlyClaims ops1 ∧ OnlyClaims ops2 ∧
      (Adjudicator.applyAll apps ops1 s).balances.get a ≠
        (Adjudicator.applyAll apps ops2 s).balances.get a := by
  sorry

/-- S2-45, S2-18. S2:1152-1154, S2:1178-1193: the Nitro Lower-bound Value
    Algorithm gives a value every node can obtain against a redistribution
    adversary. -/
theorem nitro_lower_bound_achievable (apps : Apps) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (hT : T.RedistributionOnly) (net : NetworkState p)
    (minPayout : GuaranteeGroup → Address → Coins) (hmp : MinPayoutCorrect minPayout)
    (order : List Address) (ho : net.chain.IsTopologicalOrder order)
    (hg : ∀ c pr, net.chain.finalOutcome (.channel c) = some (.guarantee (.channel c) pr) → False)
    (n : Address) :
    CanObtain apps T n (net.chain.nitroValue minPayout order n) net := by
  sorry

/-- S2-45. S2:1194-1196: "by taking the minimum independently on different
    allocation/guarantee groupings, we end up with an algorithm that strictly
    underestimates the actual value in some cases." -/
theorem nitro_lower_bound_underestimates (apps : Apps) (p : Participant) :
    ∃ (T : Threat p) (net : NetworkState p) (minPayout : GuaranteeGroup → Address → Coins)
      (order : List Address) (n : Address) (x : Coins),
      Assumptions apps p T ∧ MinPayoutCorrect minPayout ∧ net.chain.IsTopologicalOrder order ∧
      CanObtain apps T n x net ∧ net.chain.nitroValue minPayout order n < x := by
  sorry

/-- S2-46. S2:1216-1218: "If Σ v_i > Σ a_j, then we say the system is
    overfunded. In this case, we know that all destinations will receive
    their allocations, so p_i = a_i regardless of the order of payout." -/
theorem overfunded_min_payout (g : GuaranteeGroup) (h : g.Overfunded) (d : Address)
    (hd : ∃ e ∈ g.target, e.dest = d) : g.IsMinPayout d (g.target.owed d) := by
  sorry

/-- S2-46. S2:1251-1253: "In the fully funded case, where Σ v_i = Σ a_j, it
    is easy to see that p_i = a_i, just as in the overfunded case." -/
theorem fully_funded_min_payout (g : GuaranteeGroup) (h : g.FullyFunded) (d : Address)
    (hd : ∃ e ∈ g.target, e.dest = d) : g.IsMinPayout d (g.target.owed d) := by
  sorry

/-- S2-46. S2:1253-1255: "In the single guarantee case, the payouts are fully
    determined." Every exhausted claim order pays each destination the same
    amount. -/
theorem single_guarantee_determined (g : GuaranteeGroup) (h : g.guarantees.length = 1)
    (cs1 cs2 : List (Nat × Address × Coins)) (h1 : (g.applyClaims cs1).Exhausted)
    (h2 : (g.applyClaims cs2).Exhausted) (d : Address) :
    g.paidTo (g.applyClaims cs1) d = g.paidTo (g.applyClaims cs2) d := by
  sorry

/-- S2-45, S2-44. S2:1173-1176, Figure 23: "participant I will receive their
    5 coins, even though we cannot say anything about how the remaining 5
    coins will be distributed between A and B." -/
theorem figure23_lower_bound (I A B : Address) (hIA : I ≠ A) (hIB : I ≠ B) (hAB : A ≠ B) :
    GuaranteeGroup.IsMinPayout
      { target := [alloc I 5, alloc A 5, alloc B 5], guarantees := [(5, [I, A]), (5, [I, B])] }
      I 5 ∧
    GuaranteeGroup.IsMinPayout
      { target := [alloc I 5, alloc A 5, alloc B 5], guarantees := [(5, [I, A]), (5, [I, B])] }
      A 0 ∧
    GuaranteeGroup.IsMinPayout
      { target := [alloc I 5, alloc A 5, alloc B 5], guarantees := [(5, [I, A]), (5, [I, B])] }
      B 0 := by
  sorry

/-- S2-47, S2-37, S4-0060-08. S2:1299-1316: `A` finalizes `L`, `G` and `J`,
    calls `T(L, G, x)` and `C(G, χ, x)`; "As G has χ as top priority, the
    operation is successful. By symmetry, the previous case also covers the
    case where B wants to offload." The virtual channel construction funds
    `χ` with `x` for `A` and for `B`. -/
theorem end_participant_offloads (apps : Apps) (Ts : Threats apps) (v : Views)
    (hv : v.Consistent) (w : VirtualSetup) (hw : w.Holds apps Ts v) :
    FundedFor apps (Ts.T w.A) w.χ w.x (v w.A) ∧ FundedFor apps (Ts.T w.B) w.χ w.x (v w.B) := by
  sorry

/-- S2-48. S2:1317-1343: "the case where I wants to offload the channel and
    reclaim their funds. This is important to ensure that A and B cannot lock
    I's funds indefinitely in the channel ... The virtual channel became a
    direct channel and the intermediary was able to recover their
    collateral." `I` can reach a state where `χ` holds `x` and `I`'s balance
    rose by `x`. -/
theorem intermediary_recovers_collateral (apps : Apps) (Ts : Threats apps) (v : Views)
    (hv : v.Consistent) (w : VirtualSetup) (hw : w.Holds apps Ts v) :
    Unbeatable apps (Ts.T w.I)
      (fun net' => net'.chain.DirectlyFundedWith w.χ w.x ∧
        (v w.I).chain.balances.get w.I.address + w.x ≤ net'.chain.balances.get w.I.address)
      (v w.I) := by
  sorry

/-- S2-49 (S2:1364-1394, §6.5.1 Opening a Virtual Channel), S4-0060-08. The
    construction is reached from equation 22 by single-channel updates that
    preserve the value of `A`, `B` and `I`. -/
theorem virtual_open_value_preserving (apps : Apps) (Ts : Threats apps) (v v' : Views)
    (hv : v.Consistent) (hv' : v'.Consistent) (w : VirtualSetup) (a b : Coins)
    (hstart : w.Start apps Ts v a b) (hend : w.Holds apps Ts v')
    (hχ : v'.FinalizableBy apps Ts w.χ
      (.allocation [alloc w.A.address a, alloc w.B.address b]) [w.A, w.B])
    (hother : ∀ p, p = w.A ∨ p = w.B ∨ p = w.I → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T w.A) (v w.A) (v' w.A) ∧ SameValue apps (Ts.T w.B) (v w.B) (v' w.B) ∧
    SameValue apps (Ts.T w.I) (v w.I) (v' w.I) := by
  sorry

/-- S2-49 (S2:1412-1431, §6.5.2 Closing a Virtual Channel), S4-0080-07.
    S2:1418-1420: "I will accept this update, provided that their allocation
    of x coins remains the same." The reverse sequence preserves the value of
    `A`, `B` and `I`, and `I` ends with `b' + a' = x` across the ledgers. -/
theorem virtual_close_value_preserving (apps : Apps) (Ts : Threats apps) (v v' : Views)
    (hv : v.Consistent) (hv' : v'.Consistent) (w : VirtualSetup) (a' b' : Coins)
    (hx : a' + b' = w.x) (hstart : w.Holds apps Ts v)
    (hχ : v.FinalizableBy apps Ts w.χ
      (.allocation [alloc w.A.address a', alloc w.B.address b']) [w.A, w.B])
    (hend : w.Closed apps Ts v' a' b')
    (hother : ∀ p, p = w.A ∨ p = w.B ∨ p = w.I → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T w.A) (v w.A) (v' w.A) ∧ SameValue apps (Ts.T w.B) (v w.B) (v' w.B) ∧
    SameValue apps (Ts.T w.I) (v w.I) (v' w.I) := by
  sorry

/-- S3-19, S3-18. S3:707-709, S3:734: "The following two requirements
    guarantee that intermediary's funds are invariant:
    `voucher1.alice + voucher1.bob == x`" and the same for `voucher2`. Every
    state that `validateOutcomeChange` supports keeps the funded total of the
    start state. -/
theorem satp_outcome_change_keeps_total (decode : Decode) (c : FixedPart) (alice bob : Participant)
    (proof : SupportProof) (candidate : State)
    (h : ValidateOutcomeChange decode c alice bob proof candidate) (s0 : SignedState)
    (h0 : proof.head? = some s0) :
    candidate.outcome.fundedTotal = s0.state.outcome.fundedTotal ∧
    (candidate ≠ s0.state → ∃ a b, PairOutcome alice bob candidate.outcome a b ∧
      a + b = s0.state.outcome.fundedTotal) := by
  sorry

/-- S3-21, S3-19 (Lemma 3.1, S3:511-513; Lemma A.1, S3:746-753). "Suppose V
    finalizes on-chain. Either V is finalized with version = 0 and its
    original outcome {A : A(a0), B : A(b0)} or it is finalized with an
    outcome {A : A(a), B : A(b)}, where a0 + b0 = a + b." The hypotheses are
    what an honest signer controls: every all-signed setup state carries the
    original outcome, and every all-signed final state keeps the total
    (S3:751-753). -/
theorem satp_lemma_3_1 (apps : Apps) (decode : Decode) (r : Route) (alice bob : Participant)
    (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules decode)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hsetup : ∀ ss : SignedState, ss.ByAll → ss.state.channel = r.V → ss.state.turnNum ≤ 1 →
      ss.state.outcome = originalOutcome alice bob r.a0 r.b0)
    (hfinal : ∀ ss : SignedState, ss.ByAll → ss.state.channel = r.V → ss.state.isFinal = true →
      ∃ a b, PairOutcome alice bob ss.state.outcome a b ∧ a + b = r.a0 + r.b0)
    (s : Adjudicator) (hs : Reachable apps s) (Ω : Outcome)
    (hfin : s.finalOutcome r.V.address = some Ω) :
    ∃ Ω0, Redistributed Ω0 Ω ∧
      (((s.statusOf r.V).turnNumRecord = 0 ∧ Ω0 = originalOutcome alice bob r.a0 r.b0) ∨
       (∃ a b, PairOutcome alice bob Ω0 a b ∧ a + b = r.a0 + r.b0)) := by
  sorry

/-- S3-21 (Lemma A.1, S3:747-750, liveness half). "every party has signed a
    None state with version 1, in which case peers can take unilateral
    actions to ensure V finalized with an outcome {A : a, B : b}, where
    a0 + b0 = a + b." A peer who holds the all-signed post-fund state and
    signed no state that breaks the total can force such a finalization. -/
theorem satp_peers_can_finalize (apps : Apps) (decode : Decode) {p : Participant} (T : Threat p)
    (A : Assumptions apps p T) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules decode) (hp : p ∈ r.peers)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hdur : 0 < r.V.challengeDuration) (net : NetworkState p) (s1 : SignedState)
    (hh : net.Holds s1) (hall : s1.ByAll) (hchan : s1.state.channel = r.V)
    (hv1 : s1.state.turnNum = 1) (h1 : s1.state.outcome = originalOutcome alice bob r.a0 r.b0)
    (hsent : ∀ t ∈ net.sent, t.state.channel = r.V →
      t.state.outcome.fundedTotal = r.a0 + r.b0)
    (hchain : net.chain.finalOutcome r.V.address = none) :
    Unbeatable apps T (fun net' => ∃ Ω a b, net'.Finalized r.V Ω ∧
      PairOutcome alice bob Ω a b ∧ a + b = r.a0 + r.b0) net := by
  sorry

/-- S3-20 (Theorem 3.2, S3:503-507). "Let d(V, Pi) be the amount debited to
    V from Pi's balances, across Li and Li−1 in Protocol 3.1. Let c(V, Pi) be
    the amount credited to Pi's balance from guarantees targeting V across Li
    and Li−1 in both Protocol 3.2 and 3.3. For all V, for all i = 1, ..., n,
    if Pi follows Protocols 3.1-3.3, then c(Pi) = d(Pi)." An intermediary
    that completed Round 2 (S3:411-418) and holds the latest ledger states
    has an unbeatable strategy (Protocol 3.3, S3:480-485) to finalize both
    ledgers with no guarantee for `V` and its pre-protocol balances
    restored. -/
theorem satp_theorem_3_2 (apps : Apps) (decode : Decode) {P : Participant} (T : Threat P)
    (A : Assumptions apps P T) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules decode)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Pprev Pnext : Participant) (hprev : r.peers[i - 1]? = some Pprev)
    (hnext : r.peers[i + 1]? = some Pnext)
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 0 < Lm.challengeDuration ∧ 0 < Lp.challengeDuration ∧ 0 < r.V.challengeDuration)
    (om op : Allocation) (balm balp : Coins)
    (hom : r.LedgerAfterRound2 om Pprev P balm r.b0)
    (hop : r.LedgerAfterRound2 op P Pnext balp r.a0)
    (net : NetworkState P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hVs : HoldsVirtualSetup net r alice bob true)
    (hsetup : ∀ ss : SignedState, ss.ByAll → ss.state.channel = r.V → ss.state.turnNum ≤ 1 →
      ss.state.outcome = originalOutcome alice bob r.a0 r.b0)
    (hchain : net.chain.finalOutcome Lm.address = none ∧ net.chain.finalOutcome Lp.address = none ∧
      net.chain.finalOutcome r.V.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp) net := by
  sorry

/-- S3-20 (Theorem 3.2, Case 1-2, S3:522-537). An intermediary that has not
    signed any ledger update with a guarantee for `V` keeps its ledger
    balances: "Without Pi's signature on such an update, the consensus app
    guarantees there is no risk to Pi's balances". -/
theorem satp_intermediary_before_round2 (apps : Apps) {P : Participant} (T : Threat P)
    (A : Assumptions apps P T) (r : Route) (hr : r.WellFormed apps) (i : Nat) (hi : 1 ≤ i)
    (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 0 < Lm.challengeDuration ∧ 0 < Lp.challengeDuration)
    (om op : Allocation) (balm balp : Coins)
    (hom : r.LedgerBeforeRound2 om P balm) (hop : r.LedgerBeforeRound2 op P balp)
    (net : NetworkState P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hchain : net.chain.finalOutcome Lm.address = none ∧
      net.chain.finalOutcome Lp.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp) net := by
  sorry

/-- S3-20 (S3:500-501): "We omit the analogous statement that can be stated
    for the end-users Alice and Bob." The analogue for Alice (`P0`, ledger
    `L0`): if `V` finalizes with `{A : A(a), B : A(b)}` Alice can finalize
    `L0` with no guarantee for `V` and her entry raised by `a` from its
    Round 2 level, so she is owed her pre-protocol balance minus `a0` plus
    `a`. -/
theorem satp_end_user_recovers (apps : Apps) (decode : Decode) {P : Participant} (T : Threat P)
    (A : Assumptions apps P T) (r : Route) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules decode)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hPA : P = alice) (P1 : Participant) (hP1 : r.peers[1]? = some P1)
    (L0 : FixedPart) (hL0 : r.ledgers[0]? = some L0)
    (hdur : 0 < L0.challengeDuration ∧ 0 < r.V.challengeDuration)
    (o : Allocation) (bal : Coins) (ho : r.LedgerAfterRound2 o P P1 bal r.a0)
    (net : NetworkState P) (hH : HoldsLatestLedger net L0 o)
    (hVs : HoldsVirtualSetup net r alice bob true)
    (a b : Coins) (hfin : net.Finalized r.V (.allocation [alloc alice.address a, alloc bob.address b]))
    (hchain : net.chain.finalOutcome L0.address = none) :
    Unbeatable apps T (EndUserRecovered r L0 bal a) net := by
  sorry

/-- S3-15, S3-20 (Protocol 3.3 step 3, S3:484-485; S3:550-553). After both
    ledgers and `V` are finalized, one reclaim on each ledger credits `Pi`
    with `a` in `L_{i-1}` and `b` in `L_i`: "implying Pi's balance increases
    by a + b = a0 + b0 across both Li and Li−1." -/
theorem satp_reclaim_credits_intermediary (s : Adjudicator) (r : Route) (alice bob P Pprev Pnext : Participant)
    (Lm Lp : FixedPart) (om op : Allocation) (a b : Coins)
    (hdist : P ≠ Pprev ∧ P ≠ Pnext ∧ Pprev ≠ Pnext)
    (hV : s.finalOutcome r.V.address = some (.allocation [alloc alice.address a, alloc bob.address b]))
    (hLm : s.finalOutcome Lm.address = some (.allocation om))
    (hLp : s.finalOutcome Lp.address = some (.allocation op))
    (hgm : om.find r.V.address = some (r.guarantee Pprev P))
    (hgp : op.find r.V.address = some (r.guarantee P Pnext)) (hne : Lm ≠ Lp) :
    ∃ s1 s2 om' op', s.reclaim Lm r.V = some s1 ∧ s1.reclaim Lp r.V = some s2 ∧
      s2.finalOutcome Lm.address = some (.allocation om') ∧
      s2.finalOutcome Lp.address = some (.allocation op') ∧
      om'.owed P.address = om.owed P.address + b ∧ op'.owed P.address = op.owed P.address + a ∧
      om'.find r.V.address = none ∧ op'.find r.V.address = none := by
  sorry

end ArmadaLean.Nitro
