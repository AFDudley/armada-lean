/-
  Nitro protocol specification: network states, strategies, unbeatable
  strategies, finalizable and enabled outcomes, funding and value. Source:
  Nitro §4 (lines 359-709); SATP:164-168 gives the two security assumptions
  and SATP:393-399 the commit step. go-nitro has no off-chain model. See
  `Address.lean` for the source list.

  Modelling choice (the game). Nitro:460-461: "we assume that all other
  participants are controlled by a single adversary, pooling their resources
  and commitments." The honest participant `p` plays against that adversary.
  One round is: the adversary applies any finite list of feasible moves, then
  `p` applies one move. This encodes Nitro:537-542: the adversary can front-run
  any single move of `p` (Nitro:540-542), and `p`'s move is applied before the
  adversary can move time past a deadline (Nitro:537-539, `Assumptions.unimpeded`).
  Only `p` lets time pass by `HonestMove.wait`. The adversary may move time
  only short of every pending deadline of a channel of `p`.
-/
import ArmadaLean.Nitro.Adjudicator

namespace ArmadaLean.Nitro

/-- Nitro:446-454: "The network state, Σ, for a participant, A, consists of:
    1. The state of the adjudicator ... 2. For each channel A is a participant
    of: (a) Signed commitments that A has received (b) Signed commitments that
    A has sent (c) Private information held by A". The private information is
    the signing key; it is implicit in `p`. -/
structure NetworkState (p : Participant) where
  chain : Adjudicator
  received : List SignedState
  sent : List SignedState

/-- The signed states `p` can assemble: every signer is `p` on a state `p`
    sent, or a participant whose signature `p` received. -/
def NetworkState.Holds {p : Participant} (net : NetworkState p) (ss : SignedState) : Prop :=
  ∀ q ∈ ss.signers,
    (q = p ∧ ∃ s ∈ net.sent, s.state = ss.state) ∨
    (∃ r ∈ net.received, r.state = ss.state ∧ q ∈ r.signers)

/-- A move of the honest participant. Nitro:485-488: "signing commitments,
    refusing to sign commitments, launching/responding to on-chain challenges
    and calling on-chain operations". SATP:393-399 (Definition 3.1): a peer
    commits by signing and sending a state. `wait` lets the chain clock
    advance. -/
inductive HonestMove
  | chain (op : Op)
  | send (st : State)
  | wait (dt : Time)

/-- A move of the adversary: an on-chain operation by some other participant,
    a signed state delivered to `p`, or the clock moving. -/
inductive AdvMove
  | chain (caller : Participant) (op : Op)
  | deliver (ss : SignedState)
  | tick (dt : Time)

/-- The honest participant may submit only states it holds. -/
def HonestMove.Feasible {p : Participant} (net : NetworkState p) : HonestMove → Prop
  | .chain op => ∀ ss ∈ op.proofStates, net.Holds ss
  | .send _ => True
  | .wait _ => True

/-- Apply an honest move. A failed on-chain operation changes nothing
    (ForceMove:685-686). -/
noncomputable def NetworkState.applyHonest (apps : Apps) {p : Participant}
    (m : HonestMove) (net : NetworkState p) : NetworkState p :=
  match m with
  | .chain op => { net with chain := (net.chain.apply apps p op).getD net.chain }
  | .send st => { net with sent := ⟨st, [p]⟩ :: net.sent }
  | .wait dt => { net with chain := net.chain.tick dt }

/-- Apply an adversary move. -/
noncomputable def NetworkState.applyAdv (apps : Apps) {p : Participant}
    (m : AdvMove) (net : NetworkState p) : NetworkState p :=
  match m with
  | .chain caller op => { net with chain := (net.chain.apply apps caller op).getD net.chain }
  | .deliver ss => { net with received := ss :: net.received }
  | .tick dt => { net with chain := net.chain.tick dt }

/-- What the adversary can do. `feasible net m` holds when the adversary can
    play `m` from `net`. The structure `Assumptions` bounds it. -/
structure Threat (p : Participant) where
  feasible : NetworkState p → AdvMove → Prop

/-- A list of adversary moves, each feasible where it is applied. -/
inductive Threat.FeasibleSeq (apps : Apps) {p : Participant} (T : Threat p) :
    NetworkState p → List AdvMove → NetworkState p → Prop
  | nil {net} : T.FeasibleSeq apps net [] net
  | cons {net net' m rest} : T.feasible net m →
      T.FeasibleSeq apps (net.applyAdv apps m) rest net' → T.FeasibleSeq apps net (m :: rest) net'

/-- The deadlines of pending challenges in channels of `p`. -/
def NetworkState.PendingDeadline {p : Participant} (net : NetworkState p) (d : Time) : Prop :=
  ∃ c st ch, (c, st) ∈ net.chain.status ∧ p ∈ c.participants ∧
    st = .challenged st.turnNumRecord ch ∧ ch.deadline = d ∧ net.chain.now < d

/-- The chain and cryptography assumptions, as named hypotheses on the
    adversary `T`. Each theorem that speaks about a strategy takes an
    `Assumptions` value. -/
structure Assumptions (apps : Apps) (p : Participant) (T : Threat p) : Prop where
  /-- SATP:168: "(Safety) Forging cryptographic signatures is infeasible.";
      Nitro:158-160: "impossible to find a private key for A"; ForceMove:683:
      "From the signature you can deduce the signer". The adversary submits
      `p`'s signature only on a state `p` sent. -/
  unforgeable : ∀ net caller op, T.feasible net (.chain caller op) →
    ∀ ss ∈ op.proofStates, p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state
  /-- The same bound for delivered states. -/
  unforgeableDeliver : ∀ net ss, T.feasible net (.deliver ss) →
    p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state
  /-- The adversary never acts as `p`. -/
  notHonest : ∀ net caller op, T.feasible net (.chain caller op) → caller ≠ p
  /-- SATP:166-167 "(Liveness) Any peer can successfully record transactions
      on the blockchain in O(1) time"; Nitro:537-539 "Transactions are
      unimpeded". The adversary cannot move the clock to a pending deadline
      of `p`. -/
  unimpeded : ∀ net dt, T.feasible net (.tick dt) →
    ∀ d, net.PendingDeadline d → net.chain.now + dt < d
  /-- Nitro:460-461: the adversary controls every other participant. Any
      operation by another caller that carries no forged signature of `p` is
      feasible. -/
  capable : ∀ net caller op, caller ≠ p →
    (∀ ss ∈ op.proofStates, p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state) →
    T.feasible net (.chain caller op)
  /-- The adversary can deliver any state it can sign. -/
  capableDeliver : ∀ net ss, (p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state) →
    T.feasible net (.deliver ss)
  /-- The adversary can let time pass short of every pending deadline. -/
  capableTick : ∀ net dt, (∀ d, net.PendingDeadline d → net.chain.now + dt < d) →
    T.feasible net (.tick dt)

/-- Nitro:526-530: "having an unbeatable strategy for obtaining some state
    on-chain. The means that whatever actions (or lack of actions) other
    participants and external parties might take, the target state is still
    obtainable." `Unbeatable apps p T G net`: `p` has a strategy from `net` that
    reaches a state in `G` against every feasible adversary play. The
    strategy is the finite tree of honest moves. -/
inductive Unbeatable (apps : Apps) {p : Participant} (T : Threat p)
    (G : NetworkState p → Prop) : NetworkState p → Prop
  | done {net} : G net → Unbeatable apps T G net
  | move {net} (m : HonestMove) : m.Feasible net →
      (∀ advs net', T.FeasibleSeq apps net advs net' →
        Unbeatable apps T G (net'.applyHonest apps m)) →
      Unbeatable apps T G net

/-- A strategy of `p`: the next move, or nothing. -/
def Strategy (p : Participant) := NetworkState p → Option HonestMove

/-- A run consistent with a strategy `σ`: adversary moves and `σ`'s moves,
    in any order. -/
inductive Run (apps : Apps) {p : Participant} (T : Threat p) (σ : Strategy p) :
    NetworkState p → NetworkState p → Prop
  | refl {net} : Run apps T σ net net
  | adv {net net' m} : Run apps T σ net net' → T.feasible net' m →
      Run apps T σ net (net'.applyAdv apps m)
  | honest {net net' m} : Run apps T σ net net' → σ net' = some m → m.Feasible net' →
      Run apps T σ net (net'.applyHonest apps m)

/-- Nitro:641-644: `p` "has a strategy to prevent" `G`: some strategy keeps
    every run outside `G`. -/
def Prevents (apps : Apps) {p : Participant} (T : Threat p)
    (G : NetworkState p → Prop) (net : NetworkState p) : Prop :=
  ∃ σ : Strategy p, ∀ net', Run apps T σ net net' → ¬ G net'

/-- Nitro:602-603 `⟦χ ↦ Ω⟧`: the outcome of `χ` is finalized on-chain as `Ω`. -/
def NetworkState.Finalized {p : Participant} (net : NetworkState p) (c : FixedPart)
    (Ω : Outcome) : Prop :=
  net.chain.finalOutcome c.address = some Ω

/-- Nitro:590-593: "an outcome, Ω, is finalizable for participant A, if A has an
    unbeatable strategy for finalizing this outcome in the adjudicator. We use
    the notation `[χ ↦ Ω]_A`". -/
def Finalizable (apps : Apps) {p : Participant} (T : Threat p) (c : FixedPart) (Ω : Outcome)
    (net : NetworkState p) : Prop :=
  Unbeatable apps T (fun net' => net'.Finalized c Ω) net

/-- Nitro:641-652: "The enabled outcomes for a participant, p, is defined as the
    set of outcomes that p has no strategy to prevent from being finalized." -/
def Enabled (apps : Apps) {p : Participant} (T : Threat p) (c : FixedPart) (Ω : Outcome)
    (net : NetworkState p) : Prop :=
  ¬ Prevents apps T (fun net' => net'.Finalized c Ω) net

/-- Nitro:480-481: "A channel χ is funded for participant A with x coins, if A
    has an unbeatable strategy for obtaining a state where χ is directly
    funded with x coins." -/
def FundedFor (apps : Apps) {p : Participant} (T : Threat p) (c : FixedPart) (x : Coins)
    (net : NetworkState p) : Prop :=
  Unbeatable apps T (fun net' => net'.chain.DirectlyFundedWith c x) net

/-- `p` has an unbeatable strategy for a balance of at least `x` at address
    `a`. -/
def CanObtain (apps : Apps) {p : Participant} (T : Threat p) (a : Address) (x : Coins)
    (net : NetworkState p) : Prop :=
  Unbeatable apps T (fun net' => x ≤ net'.chain.balances.get a) net

/-- Nitro:482-484: "The value for participant A of a network state net is the
    maximum x for which A has an unbeatable strategy for obtaining a state
    where the balance of A's address in the adjudicator is x coins." -/
def Value (apps : Apps) {p : Participant} (T : Threat p) (net : NetworkState p) (x : Coins) :
    Prop :=
  CanObtain apps T (.participant p) x net ∧
  ∀ y, CanObtain apps T (.participant p) y net → y ≤ x

/-- A family of network states, one per participant. Nitro:632-633: "the outcome
    of a channel is finalizable by all its participants". -/
def Views := ∀ p : Participant, NetworkState p

/-- The views agree: they share one chain, and what one participant sent the
    others received. -/
def Views.Consistent (v : Views) : Prop :=
  (∀ p q, (v p).chain = (v q).chain) ∧
  (∀ p q, p ≠ q → ∀ ss ∈ (v p).sent, ss ∈ (v q).received)

/-- A family of threats, one per participant, and their assumptions. -/
structure Threats (apps : Apps) where
  T : ∀ p : Participant, Threat p
  ok : ∀ p, Assumptions apps p (T p)

/-- Nitro:632-633: "In the special case where the outcome of a channel is
    finalizable by all its participants, we say that the outcome is
    universally finalizable." -/
def UniversallyFinalizable (apps : Apps) (Ts : Threats apps) (v : Views) (c : FixedPart)
    (Ω : Outcome) : Prop :=
  ∀ p ∈ c.participants, Finalizable apps (Ts.T p) c Ω (v p)

/-- Nitro:635-636: "After the first n states have been broadcast. In this state,
    we say the channel is at the funding point." Each participant holds the
    first `n` states, each signed by its mover, with outcome `Ω`, and no
    participant has signed any later state. -/
def AtFundingPoint (v : Views) (c : FixedPart) (Ω : Outcome) : Prop :=
  (∀ p ∈ c.participants, ∀ k, k < c.n →
    ∃ ss, (v p).Holds ss ∧ ss.state.channel = c ∧ ss.state.turnNum = k ∧
      ss.state.outcome = Ω ∧ ss.state.isFinal = false ∧ ss.ByMover) ∧
  (∀ p ∈ c.participants, ∀ ss ∈ (v p).sent, ss.state.channel = c → ss.state.turnNum < c.n)

/-- Nitro:637-638: "When a single conclusion proof is known to each participant.
    In this state, we say the channel is in the concluded state." -/
def Concluded (v : Views) (c : FixedPart) (Ω : Outcome) : Prop :=
  ∀ p ∈ c.participants, ∃ ss, (v p).Holds ss ∧ ConclusionProof c ss ∧ ss.state.outcome = Ω

end ArmadaLean.Nitro
