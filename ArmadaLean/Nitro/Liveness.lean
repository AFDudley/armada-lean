/-
  Nitro protocol theorems: unbeatable strategies, finalizability, value
  algorithms, ledger and virtual channel constructions, and the SATP
  protocol guarantees. Every proof is `sorry`, except the theorems that read
  no game definition. Each doc comment cites the source lines and the
  property ids of `docs/nitro-theorems.md`. The repair of 2026-10-27 (every
  changed type, with its reason) is `docs/nitro-repair-2026-10-27.md`.
-/
import ArmadaLean.Nitro.Safety

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- An honest move that does not let time pass. -/
def HonestMove.NoWait : HonestMove E → Prop
  | .wait _ => False
  | _ => True

/-- `Unbeatable` with no `wait` move: the goal is reached "instantly", with
    no challenge period (Nitro:1046-1047: "A was able to withdraw their funds
    instantly, without having to wait for the channel timeout"). -/
def UnbeatableNoWait (apps : Apps E) {p : Participant} (T : Threat E p)
    (G : NetworkState E p → Prop) (net : NetworkState E p) : Prop :=
  UnbeatableIn apps T HonestMove.NoWait G net

/-- ForceMove-A06, ForceMove-A07. ForceMove:1092-1125 and ForceMove:1150-1184: through the
    PreFundSetup and PostFundSetup phases (the first `2n` states) every
    transition keeps the resolution. -/
def SetupPhaseKeepsOutcome (vt : State E → State E → Bool) (c : FixedPart) : Prop :=
  ∀ s1 s2, vt s1 s2 = true → s1.channel = c → s1.turnNum + 1 < 2 * c.n → s2.outcome = s1.outcome

/-- ForceMove:1092-1125: the game library accepts every setup transition of
    `c` (one step up in turn, below the funding point, same outcome, not
    final). -/
def SetupPhaseAccepted (vt : State E → State E → Bool) (c : FixedPart) : Prop :=
  ∀ s1 s2, s1.channel = c → s2.channel = c → s2.turnNum = s1.turnNum + 1 → s2.turnNum < c.n →
    s2.outcome = s1.outcome → s2.isFinal = false → vt s1 s2 = true

/-- Nitro-16, Nitro-21, ForceMove-B01, ForceMove-C03, docs-0070-05, docs-0080-06. Nitro:395-398: "where
    the channel L itself has enough coins in the adjudicator to cover the
    entire allocation ... A will receive all x coins allocated to them in ω."
    The strategy is one transfer. The entry of `d` is an allocation item:
    go-nitro refuses to transfer a guarantee (MultiAssetHolder.sol:169-170). -/
theorem directly_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.chain.finalOutcome c.address = some (.allocation o))
    (hfund : net.chain.DirectlyFunded c) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    UnbeatableNoWait apps T
      (fun net' => net.chain.balances.get (.external d) + o.owed (.external d) ≤
        net'.chain.balances.get (.external d)) net := by
  sorry

/-- Nitro-17, Nitro-21, Nitro-16. Nitro:480-481 and Nitro:590-593: a finalized allocation
    in a channel funded for `p` pays `d` its allocation. The channel is
    finalized already: a strategy to finalize and a strategy to fund do not
    compose, because the second one starts from `net`. -/
theorem finalizable_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.chain.finalOutcome c.address = some (.allocation o))
    (hfund : FundedFor apps T c o.total net) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    CanObtain apps T (.external d) (net.chain.balances.get (.external d) + o.owed (.external d))
      net := by
  sorry

/-- Nitro-13, Nitro-21, Nitro-23, docs-0070-05, ForceMove-A14. SATP:286-289: a
    final state supported by all finalizes "without delay"; Nitro:296-299: a
    participant who holds a conclusion proof can register it; go-nitro
    `_conclude` accepts it from any caller. Under the consensus app no other
    participant can finalize a different outcome without `p`'s signature
    before `p`'s conclude lands, because a challenge lasts at least `2 * ε`
    and no running challenge ends within `ε` (Nitro:537-539). -/
theorem conclusion_proof_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
    (Ω : Outcome E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hchain : net.chain.finalizedWith c.address = none ∨ net.Finalized c Ω)
    (hdur : 2 * T.ε ≤ c.challengeDuration) (hpend : net.DeadlineAfter c T.ε) :
    UnbeatableNoWait apps T (fun net' => net'.Finalized c Ω) net := by
  sorry

/-- Nitro-12, ForceMove-B01, ForceMove-B03, docs-0070-06, ForceMove-C02.
    SATP:290-292: "an adjudicator implements a challenge operation, enabling
    peers to recover funds from the channel after a timeout"; Nitro:292-296:
    "if no other participant responds during the timeout period, then the
    challenge times out and the outcome corresponding to the challenge state
    is finalized." go-nitro: a later challenge or checkpoint needs a strictly
    higher turn (ForceMove.sol:48-50, 95), so the holder of the highest
    supported state wins.
    Under the consensus app, a participant who holds a supported state, has
    signed no other state at that turn or above, and sees no chain record
    above it, can finalize that state's outcome. -/
theorem latest_state_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hlatest : ∀ t ∈ net.sent, t.state.channel = c →
      t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state)
    (hfinal : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = ss.state.outcome)
    (hdur : 2 * T.ε ≤ c.challengeDuration)
    (hst : net.Finalized c ss.state.outcome ∨
      (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + T.ε ≤ ch.deadline)) :
    Finalizable apps T c ss.state.outcome net := by
  sorry

/-- ForceMove-B05. ForceMove:1511-1529: "as long as Alice notices Bob's challenge within
    the timeout period, she cannot hurt her position by playing on as though
    still in Collaborative mode ... all the moves made in Collaborative still
    stand." A participant who holds a supported state above the challenge
    state, and signed nothing above it, can bring the record to that turn
    before the deadline, with go-nitro `checkpoint`, and the channel is not
    finalized. The adversary can register that same state as a challenge, so
    the goal does not ask for Open mode. -/
theorem late_observer_can_checkpoint (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
    (t : Nat) (ch : Challenge E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hsent : ∀ u ∈ net.sent, u.state.channel = c →
      (u.state.turnNum < ss.state.turnNum ∨ u.state = ss.state) ∧ u.state.isFinal = false)
    (hst : net.chain.statusOf c = .challenged t ch) (hgt : t < ss.state.turnNum)
    (hnow : net.chain.now + T.ε ≤ ch.deadline) (hdur : 2 * T.ε ≤ c.challengeDuration) :
    UnbeatableNoWait apps T
      (fun net' => net'.chain.mode c ≠ .finalized ∧
        ss.state.turnNum ≤ (net'.chain.statusOf c).turnNumRecord) net := by
  sorry

/-- Nitro-22. Nitro:612-614: "The definition of finalizability excludes the case
    where two different finalizable outcomes are held by different
    participants, as in this case at least one participant's strategy would
    be beatable by the other participant's strategy." -/
theorem finalizable_unique (apps : Apps E) (Ts : Threats E apps) (v : Views E) (hv : v.Consistent)
    (c : FixedPart) (p q : Participant) (hpq : p ≠ q) (Ω Ω' : Outcome E)
    (hp : Finalizable apps (Ts.T p) c Ω (v p)) (hq : Finalizable apps (Ts.T q) c Ω' (v q)) :
    Ω = Ω' := by
  sorry

/-- Nitro-22. Nitro:597-611: "exactly one of the following statements is true
    about a channel χ at any point in time: 1. Finalized outcome ... 2. One
    participant has multiple finalizable outcomes ... 3. Multiple participants
    share one finalizable outcome ... 4. No finalizable outcomes." -/
theorem channel_finalizability_cases (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (c : FixedPart) (p0 : Participant) :
    (∃ Ω, (v p0).Finalized c Ω) ∨
    (∃ p, p ∈ c.participants ∧ (∃ Ω, Finalizable apps (Ts.T p) c Ω (v p)) ∧
      ∀ q, q ∈ c.participants → q ≠ p → ∀ Ω, ¬ Finalizable apps (Ts.T q) c Ω (v q)) ∨
    (∃ Ω p q, p ∈ c.participants ∧ q ∈ c.participants ∧ p ≠ q ∧
      Finalizable apps (Ts.T p) c Ω (v p) ∧ Finalizable apps (Ts.T q) c Ω (v q) ∧
      ∀ r, r ∈ c.participants → ∀ Ω', Finalizable apps (Ts.T r) c Ω' (v r) → Ω' = Ω) ∨
    (∀ p, p ∈ c.participants → ∀ Ω, ¬ Finalizable apps (Ts.T p) c Ω (v p)) := by
  sorry

/-- Nitro-24. Nitro:653-656: "For any participant, p, in a channel, χ, exactly one
    of the following statements is true at a given point in time: 1. p has at
    least one finalizable outcome. 2. p has at least two enabled outcomes."
    The channel is past its setup: `p` holds a supported state of it. -/
theorem finalizable_or_two_enabled (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (hp : p ∈ c.participants)
    (hsupp : ∃ proof candidate, (∀ ss ∈ proof, net.Holds ss) ∧
      (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    (∃ Ω, Finalizable apps T c Ω net) ∨
    (∃ Ω1 Ω2, Ω1 ≠ Ω2 ∧ Enabled apps T c Ω1 net ∧ Enabled apps T c Ω2 net) := by
  sorry

/-- Nitro-24. Nitro:657-658: "if a participant has only enabled a single outcome,
    that outcome must be finalizable for them." `p` holds a support for every
    state of `c` it signed. -/
theorem single_enabled_is_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (hp : p ∈ c.participants)
    (hsupp : ∀ t ∈ net.sent, t.state.channel = c → ∃ proof, (∀ ss ∈ proof, net.Holds ss) ∧
      (apps c.appDef).supports c proof t.state = true)
    (hdur : 2 * T.ε ≤ c.challengeDuration)
    (Ω : Outcome E) (hΩ : Enabled apps T c Ω net)
    (huniq : ∀ Ω', Enabled apps T c Ω' net → Ω' = Ω) :
    Finalizable apps T c Ω net := by
  sorry

/-- Nitro-24, Nitro-21. A finalizable outcome is enabled: `p` cannot prevent what
    `p` can force. -/
theorem finalizable_is_enabled (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (Ω : Outcome E)
    (h : Finalizable apps T c Ω net) : Enabled apps T c Ω net := by
  sorry

/-- Nitro-23, ForceMove-B06, ForceMove-A06, ForceMove-A07. Nitro:635-636, Nitro:639-640: at the funding
    point, "After the first n states have been broadcast", the outcome is
    universally finalizable. ForceMove:862-871: the prefund states are "exactly what
    they need to launch a challenge on-chain to recover their funds". The
    setup phase keeps the outcome (ForceMove:1092-1125, ForceMove:1150-1184),
    and the game library accepts its transitions. -/
theorem funding_point_universally_finalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (c : FixedPart) (Ω : Outcome E) (vt : State E → State E → Bool)
    (hc : apps c.appDef = forceMoveRules vt) (hsetup : SetupPhaseKeepsOutcome vt c)
    (hvt : SetupPhaseAccepted vt c)
    (hn : 0 < c.n) (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration) (h : AtFundingPoint v c Ω)
    (hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) :
    UniversallyFinalizable apps Ts v c Ω := by
  sorry

/-- Nitro-23, ForceMove-A14. Nitro:637-640: "When a single conclusion proof is known to
    each participant ... the channel is in the concluded state." The
    concluded outcome is universally finalizable. -/
theorem concluded_universally_finalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (c : FixedPart) (Ω : Outcome E) (hc : apps c.appDef = consensusRules)
    (h : Concluded v c Ω)
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = Ω)
    (hchain : ∀ p, (v p).chain.finalizedWith c.address = none ∨ (v p).Finalized c Ω)
    (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration)
    (hpend : ∀ p, (v p).DeadlineAfter c (Ts.T p).ε) :
    UniversallyFinalizable apps Ts v c Ω := by
  sorry

/-- Nitro-49 (consensus game, Nitro:660-688), SATP-08, docs-0020-01. Nitro:684-688:
    "Throughout the only enabled outcomes for any participant are Ω1 and Ω2.
    In particular, a participant has the finalizable outcome [χ ↦ Ω1]_p
    until they approve the transition, and then enabled outcomes
    [χ ↦ Ω1, Ω2]_(p) until they receive the final state." Under the
    consensus app: a participant who holds an all-signed state with `Ω1`,
    signed no other state at that turn or above except with `Ω2`, and signed
    final states only with `Ω1` or `Ω2`, has only `Ω1` and `Ω2` enabled. -/
theorem consensus_enabled_outcomes (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (ss : SignedState E)
    (Ω1 Ω2 : Outcome E) (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hh : net.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = c)
    (hΩ1 : ss.state.outcome = Ω1)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c →
      (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
      (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2))
    (hdur : 2 * T.ε ≤ c.challengeDuration)
    (hst : (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + T.ε ≤ ch.deadline))
    (Ω : Outcome E) (hen : Enabled apps T c Ω net) : Ω = Ω1 ∨ Ω = Ω2 := by
  sorry

/-- Nitro-30, Nitro-16. Nitro:775-777: "reasoning about redistribution is easy
    in Turbo: if you can find one strategy to move a certain amount into an
    address, then no-one else can prevent this from occurring." A transfer
    sequence that reaches balance `x` at the external destination `d` gives
    an unbeatable transfer-only strategy against a transfer-only adversary
    (Nitro:779-781). A channel target is excluded: the adversary can pay a
    finalized channel's coins onward in the same round. -/
theorem turbo_redistribution_unbeatable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG)
    (ops : List (Participant × Op E)) (hops : OnlyTransfers ops) (d : E) (x : Coins)
    (hgoal : x ≤ (Adjudicator.applyAll apps ops net.chain).balances.get (.external d)) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) x net := by
  sorry

/-- Nitro-31. Nitro:785-787: "a deposit into the system cannot reduce the value of
    any address and cannot increase the value of any address by more than the
    value of the deposit." -/
theorem deposit_bounds_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (c : FixedPart) (d : E) (y x x' : Coins)
    (s' : Adjudicator E) (e : Coins) (hd : net.chain.deposit c.address e y = some s')
    (hv : Value apps T d net x) (hv' : Value apps T d { net with chain := s' } x') :
    x ≤ x' ∧ x' ≤ x + y := by
  sorry

/-- Nitro-31. Nitro:787-789: "Withdrawals can only occur from participant
    addresses and are the only way funds can leave these addresses, so cannot
    affect values elsewhere." go-nitro has no withdrawal: a payout is the
    transfer of a finalized entry to an external destination. A payout to
    another destination `q` leaves the value at `d` unchanged. -/
theorem payout_to_other_affects_only_owner (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) (d q : E) (hq : q ≠ d)
    (a : FixedPart) (s' : Adjudicator E) (h : net.chain.transfer a (.external q) = some s')
    (x : Coins) :
    Value apps T d net x ↔ Value apps T d { net with chain := s' } x := by
  sorry

/-- Nitro-32. Nitro:792-794: "While it is technically possible to create outcomes
    with cycles, it is also possible for any participant in the channel to
    prevent this from happening." Under the consensus app a participant who
    signs no state can keep every cycle away from its open channels. -/
theorem participant_can_prevent_cycles (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p)
    (hc : ∀ c : FixedPart, p ∈ c.participants → apps c.appDef = consensusRules)
    (hopen : ∀ c : FixedPart, p ∈ c.participants → ∃ t, net.chain.statusOf c = .open t)
    (hdag : net.chain.IsDAG) (hsent : net.sent = []) :
    Prevents apps T (fun net' => ∃ c : FixedPart, p ∈ c.participants ∧
      Relation.TransGen net'.chain.Edge c.address c.address) net := by
  sorry

/-- Nitro-33, Nitro-34, Nitro-32. Nitro:836-837: "it is impossible to find a strategy
    that gives any node a value higher than allocated by this algorithm."
    In the transfer-only game (Nitro:779-781), on a DAG of outcomes. -/
theorem turbo_value_upper_bound (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG) (n : Address E) (v x : Coins)
    (hv : net.chain.TurboValue n v)
    (h : CanObtainIn apps T HonestMove.IsTransfer n x net) : x ≤ v := by
  sorry

/-- Nitro-33, Nitro-35, Nitro-18. Nitro:837-839: "It is also not hard to construct a
    strategy for a node to obtain the value allocated by the algorithm, if
    necessary by actually implementing the algorithm up until that node." In
    the transfer-only game, for an external destination. -/
theorem turbo_value_achievable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG) (d : E) (v : Coins)
    (hv : net.chain.TurboValue (.external d) v) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) v net := by
  sorry

/-- Nitro-18, Nitro-33, Nitro-34, Nitro-35. Nitro:482-484 with Nitro:835-839: on a Turbo DAG
    the value at `d` in the transfer-only game is the algorithm's value of
    `d`. -/
theorem turbo_value_is_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : NetworkState E p) (hdag : net.chain.IsDAG) (d : E) (v : Coins)
    (hv : net.chain.TurboValue (.external d) v) :
    ValueIn apps T HonestMove.IsTransfer d net v := by
  sorry

/-- Nitro-36. Nitro:842-843: "calling transfers out of order does not affect the
    ultimate result." Two exhausted transfer sequences from one Turbo state
    give the same balances. -/
theorem turbo_order_independent (apps : Apps E) (s : Adjudicator E) (hdag : s.IsDAG)
    (ops1 ops2 : List (Participant × Op E)) (h1 : OnlyTransfers ops1)
    (h2 : OnlyTransfers ops2) (hx1 : (Adjudicator.applyAll apps ops1 s).TransferExhausted)
    (hx2 : (Adjudicator.applyAll apps ops2 s).TransferExhausted) (a : Address E) :
    (Adjudicator.applyAll apps ops1 s).balances.get a =
      (Adjudicator.applyAll apps ops2 s).balances.get a := by
  sorry

/-- Nitro-33, Nitro-36, Nitro-32. Nitro:819 "Choose a topological ordering":
    on a DAG a topological ordering exists (Nitro:798-799) and the
    algorithm's value does not depend on which one is chosen, so
    `TurboValue` is a function. -/
theorem turbo_value_exists_unique (s : Adjudicator E) (hdag : s.IsDAG) (n : Address E) :
    (∃ v, s.TurboValue n v) ∧ ∀ v w, s.TurboValue n v → s.TurboValue n w → v = w := by
  sorry

/-- Nitro-37, Nitro-47, docs-0060-07, docs-0080-08. Nitro:859-865: "χ is funded with 6 coins by
    L for both A and B ... Once it is on-chain, the transfer operation
    T(L, χ, 6) is all that is required to make χ directly funded. From the
    Turbo redistribution result, we know that this redistribution strategy is
    unbeatable." -/
theorem ledger_offload_funds_subchannel (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (w : LedgerWithSub E) (hw : w.Holds apps Ts v) :
    FundedFor apps (Ts.T w.A) w.χ w.c (v w.A) ∧ FundedFor apps (Ts.T w.B) w.χ w.c (v w.B) := by
  sorry

/-- Nitro-49 (Nitro:891-922, §5.4.1 Opening a Sub-channel), docs-0060-07. From
    `⟦L : x⟧, [L ↦ (A : a, B : b)]_{A,B}` and `[χ ↦ (A : a', B : b')]_{A,B}`
    with `a' ≤ a`, `b' ≤ b`, the update
    `[L ↦ (A : a − a', B : b − b', χ : a' + b')]_{A,B}` preserves the value
    of `A` and `B` at their destinations `dA` and `dB`. -/
theorem subchannel_open_value_preserving (apps : Apps E) (Ts : Threats E apps) (v v' : Views E)
    (hv : v.Consistent) (hv' : v'.Consistent) (A B : Participant) (dA dB : E) (L χ : FixedPart)
    (a b a' b' : Coins) (ha : a' ≤ a) (hb : b' ≤ b)
    (hL : IsLedgerChannel apps L) (hLp : L.participants = [A, B]) (hχp : χ.participants = [A, B])
    (hbal : v.HoldsBalance L.address (a + b)) (hbal' : v'.HoldsBalance L.address (a + b))
    (h1 : v.FinalizableBy apps Ts L (.allocation [alloc (.external dA) a, alloc (.external dB) b])
      [A, B])
    (h2 : v.FinalizableBy apps Ts χ
      (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B])
    (h3 : v'.FinalizableBy apps Ts L
      (.allocation [alloc (.external dA) (a - a'), alloc (.external dB) (b - b'),
        alloc χ.address (a' + b')]) [A, B])
    (h4 : v'.FinalizableBy apps Ts χ
      (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B])
    (hother : ∀ p, p = A ∨ p = B → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T A) dA (v A) (v' A) ∧ SameValue apps (Ts.T B) dB (v B) (v' B) := by
  sorry

/-- Nitro-49 (Nitro:939-957, §5.4.2 Closing a Sub-channel), docs-0080-07. From
    `[L ↦ (A : a, B : b, χ : c)]_{A,B}` and the concluded
    `[χ ↦ (A : a', B : b')]_{A,B}` with `a' + b' = c`, the update
    `[L ↦ (A : a + a', B : b + b')]_{A,B}` preserves the value of `A` and
    `B`. -/
theorem subchannel_close_value_preserving (apps : Apps E) (Ts : Threats E apps) (v v' : Views E)
    (hv : v.Consistent) (hv' : v'.Consistent) (w : LedgerWithSub E) (a' b' : Coins)
    (hc : a' + b' = w.c) (hw : w.Holds apps Ts v)
    (hχ : v.FinalizableBy apps Ts w.χ
      (.allocation [alloc (.external w.dA) a', alloc (.external w.dB) b']) [w.A, w.B])
    (h3 : v'.FinalizableBy apps Ts w.L
      (.allocation [alloc (.external w.dA) (w.a + a'), alloc (.external w.dB) (w.b + b')])
      [w.A, w.B])
    (hbal' : v'.HoldsBalance w.L.address (w.a + w.b + w.c))
    (hother : ∀ p, p = w.A ∨ p = w.B → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T w.A) w.dA (v w.A) (v' w.A) ∧
      SameValue apps (Ts.T w.B) w.dB (v w.B) (v' w.B) := by
  sorry

/-- Nitro-49 (Nitro:959-995, §5.4.3 Topping Up a Ledger Channel), docs-0060-05.
    Nitro:982-985: moving `A`'s entry to the end with the larger total
    `a + a'` "is a safe operation due to the precedence rules: as the channel
    is currently underfunded A would still only receive a if the outcome went
    to chain." The reordered outcome affords `A` exactly `a`. -/
theorem ledger_topup_reorder_safe (A B χ : Address E) (a b c a' : Coins) (hAB : A ≠ B)
    (hAχ : A ≠ χ) (hBχ : B ≠ χ) :
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] A = a ∧
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] B = b ∧
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] χ = c := by
  sorry

/-- Nitro-49 (Nitro:989-995, §5.4.3 steps 3-4), Nitro-04, docs-0060-05.
    After the deposit `D_L(a')`, made with `expectedHeld = a + b + c` (the
    ledger's holding `A` saw), the reordered outcome is fully funded: every
    entry, including `A`'s raised one, is affordable in full. -/
theorem ledger_topup_deposit_funds (s s' : Adjudicator E) (L : FixedPart) (A B χ : Address E)
    (a b c a' : Coins) (hAB : A ≠ B) (hAχ : A ≠ χ) (hBχ : B ≠ χ)
    (hheld : s.balances.get L.address = a + b + c)
    (hd : s.deposit L.address (a + b + c) a' = some s') :
    s'.balances.get L.address = a + b + c + a' ∧
    Allocation.paidTo (s'.balances.get L.address) [alloc B b, alloc χ c, alloc A (a + a')] A =
      a + a' ∧
    Allocation.paidTo (s'.balances.get L.address) [alloc A (a + a'), alloc B b, alloc χ c] A =
      a + a' := by
  sorry

/-- Nitro-49 (Nitro:997-1047, §5.4.4 Partial Withdrawal from a Ledger Channel).
    Nitro:1046-1047: "A was able to withdraw their funds instantly, without
    having to wait for the channel timeout." With the conclusion proof for
    `[L ↦ (L' : a + b + c, A : a')]_{A,B}` and `⟦L : x⟧`, `A` obtains `a'`
    at `dA` with no wait, and `L'` is funded with `a + b + c` for `A` and
    `B`. `L'` cannot finalize before `L` pays it: no running challenge of
    `L'` ends within `2 * ε`, no participant signed a final state of `L'`,
    and a challenge of `L'` lasts at least `2 * ε`. -/
theorem ledger_partial_withdrawal (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (hv : v.Consistent) (A B : Participant) (dA dB : E) (L L' χ : FixedPart) (a b c a' : Coins)
    (hL : IsLedgerChannel apps L) (hL' : IsLedgerChannel apps L') (hLp : L.participants = [A, B])
    (hL'p : L'.participants = [A, B]) (hLL' : L ≠ L')
    (hbal : v.HoldsBalance L.address (a + b + c + a'))
    (hconc : Concluded v L (.allocation [alloc L'.address (a + b + c), alloc (.external dA) a']))
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L → t.state.isFinal = true →
      t.state.outcome = .allocation [alloc L'.address (a + b + c), alloc (.external dA) a'])
    (hopen : ∀ p, (v p).chain.finalizedWith L.address = none)
    (hdur : ∀ p, 2 * (Ts.T p).ε ≤ L.challengeDuration ∧ 2 * (Ts.T p).ε ≤ L'.challengeDuration)
    (hpend : ∀ p, (v p).DeadlineAfter L (Ts.T p).ε ∧ (v p).DeadlineAfter L' (2 * (Ts.T p).ε))
    (hL'open : ∀ p, (v p).chain.finalOutcome L'.address = none)
    (hL'sent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = L' → t.state.isFinal = false)
    (hL'out : v.FinalizableBy apps Ts L'
      (.allocation [alloc (.external dA) a, alloc (.external dB) b, alloc χ.address c]) [A, B]) :
    UnbeatableNoWait apps (Ts.T A)
      (fun net' => (v A).chain.balances.get (.external dA) + a' ≤
        net'.chain.balances.get (.external dA))
      (v A) ∧
    FundedFor apps (Ts.T A) L' (a + b + c) (v A) ∧ FundedFor apps (Ts.T B) L' (a + b + c) (v B) := by
  sorry

/-- SATP-19, SATP-18. SATP:707-709, SATP:734: "The following two requirements
    guarantee that intermediary's funds are invariant:
    `voucher1.alice + voucher1.bob == x`" and the same for `voucher2`. Every
    state that `validateOutcomeChange` supports keeps the funded total of the
    start state, and a changed outcome pays the start state's first two
    destinations. -/
theorem satp_outcome_change_keeps_total (c : FixedPart) (alice bob : Participant)
    (proof : SupportProof E) (candidate : State E)
    (h : validateOutcomeChange c alice bob proof candidate = true) (s0 : SignedState E)
    (h0 : proof.head? = some s0) :
    candidate.outcome.fundedTotal = s0.state.outcome.fundedTotal ∧
    (candidate ≠ s0.state → ∃ da db a b, s0.state.outcome.pairDests = some (da, db) ∧
      candidate.outcome = .allocation [⟨da, .alloc a⟩, ⟨db, .alloc b⟩] ∧
      a + b = s0.state.outcome.fundedTotal) := by
  sorry

/-- SATP-21, SATP-19 (Lemma 3.1, SATP:511-513; Lemma A.1, SATP:746-753). "Suppose V
    finalizes on-chain. Either V is finalized with version = 0 and its
    original outcome {A : A(a0), B : A(b0)} or it is finalized with an
    outcome {A : A(a), B : A(b)}, where a0 + b0 = a + b." `signed` lists the
    signatures that exist (`(q, st)`: `q` signed `st`), and the chain uses no
    other (SATP:168). The hypothesis is what honest peers sign
    (SATP:407-421, SATP:751-753): every state of `V` that every peer signed is
    a setup state with the original outcome, or a final state that keeps the
    total. -/
theorem satp_lemma_3_1 (apps : Apps E) (r : Route E) (alice bob : Participant)
    (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (signed : List (Participant × State E))
    (hsigned : ∀ st : State E, (∀ q ∈ r.V.participants, (q, st) ∈ signed) → st.channel = r.V →
      (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (st.isFinal = true ∧ ∃ a b, PairOutcome (r.dest alice) (r.dest bob) st.outcome a b ∧
        a + b = r.a0 + r.b0))
    (s : Adjudicator E) (hs : ReachableSigned apps signed s) (Ω : Outcome E)
    (hfin : s.finalOutcome r.V.address = some Ω) :
    ∃ Ω0, Redistributed Ω0 Ω ∧
      (((s.statusOf r.V).turnNumRecord = 0 ∧
        Ω0 = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
       (∃ a b, PairOutcome (r.dest alice) (r.dest bob) Ω0 a b ∧ a + b = r.a0 + r.b0)) := by
  sorry

/-- SATP-21 (Lemma A.1, SATP:747-750, liveness half). "every party has signed a
    None state with version 1, in which case peers can take unilateral
    actions to ensure V finalized with an outcome {A : a, B : b}, where
    a0 + b0 = a + b." A peer who holds the all-signed post-fund state, signed
    only setup states and pair outcomes that keep the total, and sees `V`
    open at or below version 1, can force such a finalization. -/
theorem satp_peers_can_finalize (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules) (hp : p ∈ r.peers)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hdur : 2 * T.ε ≤ r.V.challengeDuration) (net : NetworkState E p) (s1 : SignedState E)
    (hh : net.Holds s1) (hall : s1.ByAll) (hchan : s1.state.channel = r.V)
    (hv1 : s1.state.turnNum = 1)
    (h1 : s1.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0)
    (hsent : ∀ t ∈ net.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0))
    (hst : ∃ t, net.chain.statusOf r.V = .open t ∧ t ≤ 1) :
    Unbeatable apps T (fun net' => ∃ Ω a b, net'.Finalized r.V Ω ∧
      PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧ a + b = r.a0 + r.b0) net := by
  sorry

/-- SATP-20 (Theorem 3.2, SATP:503-507). "Let d(V, Pi) be the amount debited to
    V from Pi's balances, across Li and Li−1 in Protocol 3.1. Let c(V, Pi) be
    the amount credited to Pi's balance from guarantees targeting V across Li
    and Li−1 in both Protocol 3.2 and 3.3. For all V, for all i = 1, ..., n,
    if Pi follows Protocols 3.1-3.3, then c(Pi) = d(Pi)." An intermediary
    that completed Round 2 (SATP:411-418) and holds the latest ledger states
    has an unbeatable strategy (Protocol 3.3, SATP:480-485) to finalize both
    ledgers with no guarantee for `V` and its pre-protocol balances
    restored. `Pi`'s own signatures on `V` are the setup states
    (`HoldsVirtualSetup`); the game rule `Bounds.unforgeable` bounds the
    rest. -/
theorem satp_theorem_3_2 (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Pprev Pnext : Participant) (hprev : r.peers[i - 1]? = some Pprev)
    (hnext : r.peers[i + 1]? = some Pnext)
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration ∧
      2 * T.ε ≤ r.V.challengeDuration)
    (om op : Allocation E) (balm balp : Coins)
    (hom : r.LedgerAfterRound2 om Pprev P balm r.b0)
    (hop : r.LedgerAfterRound2 op P Pnext balp r.a0)
    (net : NetworkState E P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hVs : HoldsVirtualSetup net r alice bob true)
    (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε ∧ net.DeadlineAfter r.V T.ε)
    (hchain : net.chain.finalizedWith Lm.address = none ∧
      net.chain.finalizedWith Lp.address = none ∧ net.chain.finalizedWith r.V.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp
      (net.chain.balances.get (.external (r.dest P)))) net := by
  sorry

/-- SATP-20 (Theorem 3.2, Case 1-2, SATP:522-537). An intermediary that has not
    signed any ledger update with a guarantee for `V` keeps its ledger
    balances: "Without Pi's signature on such an update, the consensus app
    guarantees there is no risk to Pi's balances". -/
theorem satp_intermediary_before_round2 (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (hr : r.WellFormed apps) (i : Nat) (hi : 1 ≤ i)
    (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Lm Lp : FixedPart) (hLm : r.ledgers[i - 1]? = some Lm) (hLp : r.ledgers[i]? = some Lp)
    (hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration)
    (om op : Allocation E) (balm balp : Coins)
    (hom : r.LedgerBeforeRound2 om P balm) (hop : r.LedgerBeforeRound2 op P balp)
    (net : NetworkState E P) (hHm : HoldsLatestLedger net Lm om) (hHp : HoldsLatestLedger net Lp op)
    (hpend : net.DeadlineAfter Lm T.ε ∧ net.DeadlineAfter Lp T.ε)
    (hchain : net.chain.finalizedWith Lm.address = none ∧
      net.chain.finalizedWith Lp.address = none) :
    Unbeatable apps T (IntermediaryRecovered r Lm Lp balm balp
      (net.chain.balances.get (.external (r.dest P)))) net := by
  sorry

/-- SATP-20 (SATP:500-501): "We omit the analogous statement that can be stated
    for the end-users Alice and Bob." The analogue for Alice (`P0`, ledger
    `L0`): if `V` finalizes with `{A : A(a), B : A(b)}` and `a + b = a0 + b0`
    (go-nitro `reclaim` needs it, MultiAssetHolder.sol:365), Alice can
    finalize `L0` with no guarantee for `V` and her entry raised by `a` from
    its Round 2 level, so she is owed her pre-protocol balance minus `a0`
    plus `a`. -/
theorem satp_end_user_recovers (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hPA : P = alice) (P1 : Participant) (hP1 : r.peers[1]? = some P1)
    (L0 : FixedPart) (hL0 : r.ledgers[0]? = some L0)
    (hdur : 2 * T.ε ≤ L0.challengeDuration ∧ 2 * T.ε ≤ r.V.challengeDuration)
    (o : Allocation E) (bal : Coins) (ho : r.LedgerAfterRound2 o P P1 bal r.a0)
    (net : NetworkState E P) (hH : HoldsLatestLedger net L0 o)
    (hVs : HoldsVirtualSetup net r alice bob true)
    (a b : Coins) (hab : a + b = r.a0 + r.b0)
    (hfin : net.chain.finalOutcome r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]))
    (hpend : net.DeadlineAfter L0 T.ε)
    (hchain : net.chain.finalizedWith L0.address = none) :
    Unbeatable apps T (EndUserRecovered r L0 bal a
      (net.chain.balances.get (.external (r.dest P)))) net := by
  sorry

/-- SATP-15, SATP-20 (Protocol 3.3 step 3, SATP:484-485; SATP:550-553). After
    both ledgers and `V` are finalized, one reclaim on each ledger credits
    `Pi` with `a` in `L_{i-1}` and `b` in `L_i`: "implying Pi's balance
    increases by a + b = a0 + b0 across both Li and Li−1." go-nitro
    `compute_reclaim_effects` needs the peers' entries present and
    `a + b = a0 + b0`; both hold after Protocol 3.1 Round 2 (SATP:411-418). -/
theorem satp_reclaim_credits_intermediary (s : Adjudicator E) (r : Route E)
    (alice bob P Pprev Pnext : Participant)
    (Lm Lp : FixedPart) (om op : Allocation E) (a b : Coins)
    (hdist : r.dest P ≠ r.dest Pprev ∧ r.dest P ≠ r.dest Pnext ∧ r.dest Pprev ≠ r.dest Pnext)
    (hV : s.finalOutcome r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]))
    (hLm : s.finalOutcome Lm.address = some (.allocation om))
    (hLp : s.finalOutcome Lp.address = some (.allocation op))
    (hgm : om.find r.V.address = some (r.guarantee Pprev P))
    (hgp : op.find r.V.address = some (r.guarantee P Pnext)) (hne : Lm ≠ Lp)
    (hem : om.find (.external (r.dest Pprev)) ≠ none ∧ om.find (.external (r.dest P)) ≠ none)
    (hep : op.find (.external (r.dest P)) ≠ none ∧ op.find (.external (r.dest Pnext)) ≠ none)
    (hab : a + b = r.a0 + r.b0) :
    ∃ s1 s2 om' op', s.reclaim Lm r.V = some s1 ∧ s1.reclaim Lp r.V = some s2 ∧
      s2.finalOutcome Lm.address = some (.allocation om') ∧
      s2.finalOutcome Lp.address = some (.allocation op') ∧
      om'.owed (.external (r.dest P)) = om.owed (.external (r.dest P)) + b ∧
      op'.owed (.external (r.dest P)) = op.owed (.external (r.dest P)) + a ∧
      om'.find r.V.address = none ∧ op'.find r.V.address = none := by
  sorry

end ArmadaLean.Nitro
