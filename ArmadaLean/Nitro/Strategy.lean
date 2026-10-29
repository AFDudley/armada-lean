/-
  Nitro protocol specification: network states, strategies, unbeatable
  strategies, finalizable and enabled outcomes, funding and value. Source:
  Nitro §4 (lines 359-709); SATP:164-168 gives the two security assumptions
  and SATP:393-399 the commit step. go-nitro has no off-chain model. See
  `Address.lean` for the source list. The repair of 2026-10-27 is recorded in
  `docs/nitro-repair-2026-10-27.md`.

  Modelling choice (the game). Nitro:460-461: "we assume that all other
  participants are controlled by a single adversary, pooling their resources
  and commitments." The honest participant `p` plays against that adversary.
  One round is: `p` chooses one move, the adversary applies any finite list
  of feasible moves, then `p`'s move is applied. This encodes Nitro:540-542:
  "Transactions can be front-run". The clock follows Nitro:537-539:
  "Transactions are unimpeded: given that the current time is t and ε > 0,
  then it is possible for any party to apply any operation, O, on-chain before
  time t + ε." The adversary may move the clock, but in each round `p`'s move
  lands before `ε` has passed since `p` chose it (`Threat.Round`). The
  liveness theorems assume challenge durations of at least `2 * ε`: a
  challenge that the adversary registers just after `p` chose a move is seen
  at the next round, and `p`'s answer lands before `2 * ε` has passed.
-/
import ArmadaLean.Nitro.Adjudicator

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- Nitro:446-454: "The network state, Σ, for a participant, A, consists of:
    1. The state of the adjudicator ... 2. For each channel A is a participant
    of: (a) Signed commitments that A has received (b) Signed commitments that
    A has sent (c) Private information held by A". The private information is
    the signing key; it is implicit in `p`. -/
structure NetworkState (E : Type) (p : Participant) where
  chain : Adjudicator E
  received : List (SignedState E)
  sent : List (SignedState E)

/-- The signed states `p` can assemble. Every signer is `p` on a state `p`
    sent, or a participant whose signature `p` received on that state. Every
    signer listed in the state's voucher (SATP:703) is `p` on a voucher `p`
    sent, or a participant who signed a received state that carries the
    voucher. -/
def NetworkState.Holds {p : Participant} (net : NetworkState E p) (ss : SignedState E) : Prop :=
  (∀ q ∈ ss.signers,
    (q = p ∧ ∃ s ∈ net.sent, s.state = ss.state) ∨
    (∃ r ∈ net.received, r.state = ss.state ∧ q ∈ r.signers)) ∧
  ∀ v, ss.state.voucher? = some v → ∀ q ∈ v.signers,
    (q = p ∧ ∃ s ∈ net.sent, s.state.voucher? = some v) ∨
    (∃ r ∈ net.received, r.state.voucher? = some v ∧ q ∈ r.signers)

/-- A move of the honest participant. Nitro:485-488: "signing commitments,
    refusing to sign commitments, launching/responding to on-chain challenges
    and calling on-chain operations". SATP:393-399 (Definition 3.1): a peer
    commits by signing and sending a state. `wait` lets the chain clock
    advance. -/
inductive HonestMove (E : Type)
  | chain (op : Op E)
  | send (st : State E)
  | wait (dt : Time)

/-- A move of the adversary: an on-chain operation by some other participant,
    a signed state delivered to `p`, or the clock moving. -/
inductive AdvMove (E : Type)
  | chain (caller : Participant) (op : Op E)
  | deliver (ss : SignedState E)
  | tick (dt : Time)

/-- The honest participant may submit only states it holds. It does not
    deposit: Nitro:779-781 analyses strategies "ignoring deposits and
    withdrawals", and `p` has no wallet, so a deposit by `p` would create
    coins. -/
def HonestMove.Feasible {p : Participant} (net : NetworkState E p) : HonestMove E → Prop
  | .chain (.deposit ..) => False
  | .chain op => ∀ ss ∈ op.proofStates, net.Holds ss
  | .send _ => True
  | .wait _ => True

/-- Apply an honest move. A failed on-chain operation changes nothing
    (ForceMove:685-686). -/
def NetworkState.applyHonest (apps : Apps E) {p : Participant}
    (m : HonestMove E) (net : NetworkState E p) : NetworkState E p :=
  match m with
  | .chain op => { net with chain := (net.chain.apply apps p op).getD net.chain }
  | .send st => { net with sent := ⟨st, [p]⟩ :: net.sent }
  | .wait dt => { net with chain := net.chain.tick dt }

/-- Apply an adversary move. D9 repair (`docs/nitro-repair-2026-10-27.md`):
    go-nitro emits the signed states of a challenge (`ChallengeRegistered`)
    and a checkpoint is calldata, so every on-chain call makes its proof
    states public. A successful chain operation adds `op.proofStates` to
    `received`: the honest participant can then answer a challenge or
    checkpoint it did not see delivered, closing the gap that let the
    adversary register an undeliverable state (theorems
    `funding_point_universally_finalizable`, `satp_peers_can_finalize`,
    `satp_theorem_3_2` in the re-audit). -/
def NetworkState.applyAdv (apps : Apps E) {p : Participant}
    (m : AdvMove E) (net : NetworkState E p) : NetworkState E p :=
  match m with
  | .chain caller op =>
    match net.chain.apply apps caller op with
    | some s' => { net with chain := s', received := op.proofStates ++ net.received }
    | none => net
  | .deliver ss => { net with received := ss :: net.received }
  | .tick dt => { net with chain := net.chain.tick dt }

/-- What the adversary can do. `feasible net m` holds when the adversary can
    play `m` from `net`. `ε` is the inclusion bound of Nitro:537-539: a
    transaction lands before `ε` has passed; the type carries `0 < ε`
    (Nitro:537 "ε > 0"). The structures `Bounds` and `Capable` bound it. -/
structure Threat (E : Type) (p : Participant) where
  feasible : NetworkState E p → AdvMove E → Prop
  ε : Time
  ε_pos : 0 < ε

/-- A list of adversary moves, each feasible where it is applied. -/
inductive Threat.FeasibleSeq (apps : Apps E) {p : Participant} (T : Threat E p) :
    NetworkState E p → List (AdvMove E) → NetworkState E p → Prop
  | nil {net} : T.FeasibleSeq apps net [] net
  | cons {net net' m rest} : T.feasible net m →
      T.FeasibleSeq apps (net.applyAdv apps m) rest net' → T.FeasibleSeq apps net (m :: rest) net'

/-- The adversary's part of one round: a feasible prefix that ends before `ε`
    has passed since the round began (Nitro:537-539, "before time t + ε"). -/
def Threat.Round (apps : Apps E) {p : Participant} (T : Threat E p) (net : NetworkState E p)
    (advs : List (AdvMove E)) (net' : NetworkState E p) : Prop :=
  T.FeasibleSeq apps net advs net' ∧ net'.chain.now < net.chain.now + T.ε

/-- The signatures of `p` that a state carries are genuine: `p` signed the
    state, and `p` signed a state that carries the state's voucher, if `p` is
    one of its signers. SATP:168: "(Safety) Forging cryptographic signatures
    is infeasible."; Nitro:158-160; ForceMove:683. -/
def NetworkState.Unforged {p : Participant} (net : NetworkState E p) (ss : SignedState E) : Prop :=
  (p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state) ∧
  ∀ v, ss.state.voucher? = some v → p ∈ v.signers → ∃ s ∈ net.sent, s.state.voucher? = some v

/-- The bounds on the adversary `T`, as named hypotheses. -/
structure Bounds (apps : Apps E) (p : Participant) (T : Threat E p) : Prop where
  /-- SATP:168, Nitro:158-160, ForceMove:683: the adversary submits a
      signature of `p` only where `p` signed. -/
  unforgeable : ∀ net caller op, T.feasible net (.chain caller op) →
    ∀ ss ∈ op.proofStates, net.Unforged ss
  /-- The same bound for delivered states. -/
  unforgeableDeliver : ∀ net ss, T.feasible net (.deliver ss) → net.Unforged ss
  /-- The adversary never acts as `p`. -/
  notHonest : ∀ net caller op, T.feasible net (.chain caller op) → caller ≠ p

/-- The capabilities of the adversary `T`. Nitro:460-461: the adversary
    controls every other participant. -/
structure Capable (apps : Apps E) (p : Participant) (T : Threat E p) : Prop where
  /-- Any operation by another caller that carries no forged signature of
      `p` is feasible. -/
  capable : ∀ net caller op, caller ≠ p → (∀ ss ∈ op.proofStates, net.Unforged ss) →
    T.feasible net (.chain caller op)
  /-- The adversary can deliver any state it can sign. -/
  capableDeliver : ∀ net ss, net.Unforged ss → T.feasible net (.deliver ss)
  /-- The adversary can move the clock; `Threat.Round` bounds each round. -/
  capableTick : ∀ net dt, T.feasible net (.tick dt)

/-- The chain and cryptography assumptions of the full game. Each theorem
    that speaks about a strategy takes an `Assumptions` value. -/
structure Assumptions (apps : Apps E) (p : Participant) (T : Threat E p) : Prop
    extends Bounds apps p T, Capable apps p T

/-- Nitro:526-530: "having an unbeatable strategy for obtaining some state
    on-chain. The means that whatever actions (or lack of actions) other
    participants and external parties might take, the target state is still
    obtainable." `UnbeatableIn apps T allowed G net`: `p` has a strategy from
    `net`, using only moves in `allowed`, that reaches a state in `G` against
    every feasible adversary play. The strategy is the finite tree of honest
    moves. -/
inductive UnbeatableIn (apps : Apps E) {p : Participant} (T : Threat E p)
    (allowed : HonestMove E → Prop) (G : NetworkState E p → Prop) : NetworkState E p → Prop
  | done {net} : G net → UnbeatableIn apps T allowed G net
  | move {net} (m : HonestMove E) : allowed m → m.Feasible net →
      (∀ advs net', T.Round apps net advs net' →
        UnbeatableIn apps T allowed G (net'.applyHonest apps m)) →
      UnbeatableIn apps T allowed G net

/-- `UnbeatableIn` with every honest move allowed. -/
def Unbeatable (apps : Apps E) {p : Participant} (T : Threat E p)
    (G : NetworkState E p → Prop) (net : NetworkState E p) : Prop :=
  UnbeatableIn apps T (fun _ => True) G net

/-- A strategy of `p`: the next move, in every network state. -/
def Strategy (E : Type) (p : Participant) := NetworkState E p → HonestMove E

/-- The states at the start of each round of a play of `σ`: each round is an
    adversary prefix (`Threat.Round`) followed by the move `σ` chose at the
    start of the round. -/
inductive Run (apps : Apps E) {p : Participant} (T : Threat E p) (σ : Strategy E p) :
    NetworkState E p → NetworkState E p → Prop
  | refl {net} : Run apps T σ net net
  | round {net n1 n2 advs} : Run apps T σ net n1 → T.Round apps n1 advs n2 →
      Run apps T σ net (n2.applyHonest apps (σ n1))

/-- Nitro:641-644: `p` "has a strategy to prevent" `G`: a strategy whose
    every move is feasible keeps every state of every play outside `G`,
    within the rounds too. -/
def Prevents (apps : Apps E) {p : Participant} (T : Threat E p)
    (G : NetworkState E p → Prop) (net : NetworkState E p) : Prop :=
  ∃ σ : Strategy E p, (∀ n, (σ n).Feasible n) ∧
    ∀ n1 advs n2, Run apps T σ net n1 → T.Round apps n1 advs n2 → ¬ G n2

/-- Nitro:602-603 `⟦χ ↦ Ω⟧`: `χ` finalized with the outcome `Ω`. A later
    payout does not change it. -/
def NetworkState.Finalized {p : Participant} (net : NetworkState E p) (c : FixedPart)
    (Ω : Outcome E) : Prop :=
  net.chain.finalizedWith c.address = some Ω

/-- A running challenge of `c` ends no sooner than `δ` from now. With
    `δ = ε`, `p` can answer it before it ends (Nitro:537-539). -/
def NetworkState.DeadlineAfter {p : Participant} (net : NetworkState E p) (c : FixedPart)
    (δ : Time) : Prop :=
  ∀ t ch, net.chain.statusOf c = .challenged t ch → net.chain.now + δ ≤ ch.deadline

/-- Nitro:590-593: "an outcome, Ω, is finalizable for participant A, if A has an
    unbeatable strategy for finalizing this outcome in the adjudicator. We use
    the notation `[χ ↦ Ω]_A`". -/
def Finalizable (apps : Apps E) {p : Participant} (T : Threat E p) (c : FixedPart) (Ω : Outcome E)
    (net : NetworkState E p) : Prop :=
  Unbeatable apps T (fun net' => net'.Finalized c Ω) net

/-- Nitro:641-652: "The enabled outcomes for a participant, p, is defined as the
    set of outcomes that p has no strategy to prevent from being finalized." -/
def Enabled (apps : Apps E) {p : Participant} (T : Threat E p) (c : FixedPart) (Ω : Outcome E)
    (net : NetworkState E p) : Prop :=
  ¬ Prevents apps T (fun net' => net'.Finalized c Ω) net

/-- Nitro:480-481: "A channel χ is funded for participant A with x coins, if A
    has an unbeatable strategy for obtaining a state where χ is directly
    funded with x coins." -/
def FundedFor (apps : Apps E) {p : Participant} (T : Threat E p) (c : FixedPart) (x : Coins)
    (net : NetworkState E p) : Prop :=
  Unbeatable apps T (fun net' => net'.chain.DirectlyFundedWith c x) net

/-- `p` has an unbeatable strategy, with moves in `allowed`, for a balance of
    at least `x` at address `a`. -/
def CanObtainIn (apps : Apps E) {p : Participant} (T : Threat E p)
    (allowed : HonestMove E → Prop) (a : Address E) (x : Coins) (net : NetworkState E p) : Prop :=
  UnbeatableIn apps T allowed (fun net' => x ≤ net'.chain.balances.get a) net

/-- `CanObtainIn` with every honest move allowed. -/
def CanObtain (apps : Apps E) {p : Participant} (T : Threat E p) (a : Address E) (x : Coins)
    (net : NetworkState E p) : Prop :=
  CanObtainIn apps T (fun _ => True) a x net

/-- Nitro:482-484: "The value for participant A of a network state net is the
    maximum x for which A has an unbeatable strategy for obtaining a state
    where the balance of A's address in the adjudicator is x coins." The
    address is the external destination `d` (operator ruling 2026-10-27:
    destinations are not participants). -/
def ValueIn (apps : Apps E) {p : Participant} (T : Threat E p) (allowed : HonestMove E → Prop)
    (d : E) (net : NetworkState E p) (x : Coins) : Prop :=
  CanObtainIn apps T allowed (.external d) x net ∧
  ∀ y, CanObtainIn apps T allowed (.external d) y net → y ≤ x

/-- `ValueIn` with every honest move allowed. -/
def Value (apps : Apps E) {p : Participant} (T : Threat E p) (d : E) (net : NetworkState E p)
    (x : Coins) : Prop :=
  ValueIn apps T (fun _ => True) d net x

/-- A family of network states, one per participant. Nitro:632-633: "the outcome
    of a channel is finalizable by all its participants". -/
def Views (E : Type) := ∀ p : Participant, NetworkState E p

/-- The views agree: they share one chain, a state `p` sends reaches its
    channel's other participants (operator ruling 2026-10-29: the network
    is synchronous by construction, `State.recipients`), and a signature
    of `q` that `p` received is on a state `q` sent (SATP:168). The
    asynchronous system — where sending and delivery are separate steps,
    so a sent state need not yet have reached its recipients — is future
    work; this file models only the synchronous one. -/
def Views.Consistent (v : Views E) : Prop :=
  (∀ p q, (v p).chain = (v q).chain) ∧
  (∀ p, ∀ ss ∈ (v p).sent, ∀ q ∈ ss.state.recipients p, ss ∈ (v q).received) ∧
  (∀ p q, p ≠ q → ∀ r ∈ (v p).received, q ∈ r.signers → ∃ s ∈ (v q).sent, s.state = r.state)

/-- A family of threats, one per participant, and their assumptions. -/
structure Threats (E : Type) [DecidableEq E] (apps : Apps E) where
  T : ∀ p : Participant, Threat E p
  ok : ∀ p, Assumptions apps p (T p)

/-- Nitro:632-633: "In the special case where the outcome of a channel is
    finalizable by all its participants, we say that the outcome is
    universally finalizable." -/
def UniversallyFinalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E) (c : FixedPart)
    (Ω : Outcome E) : Prop :=
  ∀ p ∈ c.participants, Finalizable apps (Ts.T p) c Ω (v p)

/-- Nitro:635-636: "After the first n states have been broadcast. In this state,
    we say the channel is at the funding point." Each participant holds the
    first `n` states, each signed by its mover, with outcome `Ω`, and no
    participant has signed any later state. -/
def AtFundingPoint (v : Views E) (c : FixedPart) (Ω : Outcome E) : Prop :=
  (∀ p ∈ c.participants, ∀ k, k < c.n →
    ∃ ss, (v p).Holds ss ∧ ss.state.channel = c ∧ ss.state.turnNum = k ∧
      ss.state.outcome = Ω ∧ ss.state.isFinal = false ∧ ss.ByMover) ∧
  (∀ p ∈ c.participants, ∀ ss ∈ (v p).sent, ss.state.channel = c → ss.state.turnNum < c.n)

/-- Nitro:637-638: "When a single conclusion proof is known to each participant.
    In this state, we say the channel is in the concluded state." -/
def Concluded (v : Views E) (c : FixedPart) (Ω : Outcome E) : Prop :=
  ∀ p ∈ c.participants, ∃ ss, (v p).Holds ss ∧ ConclusionProof c ss ∧ ss.state.outcome = Ω

end ArmadaLean.Nitro
