/-
  Armada adjudicator: the game of Nitro §4 over the Armada system. Nitro
  `Strategy.lean` defines the game over the Nitro chain (`Adjudicator`). Its
  chain moves are functions. An Armada call is a relation, because the pool
  chooses the keys of the created notes. So this module states the same game
  with relational chain moves. The message part is Nitro's own: `Net.view t`
  is a Nitro `NetworkState`, and every Nitro predicate on network states
  (`NetworkState.Holds`, `Finalized`, `PendingDeadline`, `HoldsLatestLedger`,
  `IntermediaryRecovered`, ...) applies to it.

  An honest chain move carries the whole call, with the notes that it spends,
  as a submitted pool proof does. The adversary moves first, any finite number
  of times (Nitro:540-542, front-running). A move whose call cannot execute
  any more is a failed call and changes nothing (ForceMove:685-686). So a
  pending call that a concurrent call makes stale is part of the game.

  The adversary is every other pool user and every other participant
  (Nitro:460-461). Its pool steps cannot spend the adjudicator's notes
  (`OtherUserStep`). There is no separate clock move: time moves by the call
  `Call.tick`.
-/
import ArmadaLean.ArmadaNitro.Operations

namespace ArmadaLean.ArmadaNitro

set_option autoImplicit false

open ArmadaLean.Nitro (Coins Time Participant FixedPart Outcome Apps SignedState NetworkState
  LedgerWithSub IsLedgerChannel)

/-- The network state of participant `p` (Nitro:446-454) over the Armada
    system: the chain, and the signed states `p` received and sent. -/
structure Net (p : Participant) where
  chain : ArmadaState
  received : List SignedState
  sent : List SignedState

/-- The Nitro network state of token `t`: the abstraction of the chain, with
    the same messages. -/
def Net.view {p : Participant} (net : Net p) (t : Token) : NetworkState p :=
  { chain := toNitro net.chain t, received := net.received, sent := net.sent }

/-- `p` can assemble the signed state `ss` (Nitro `NetworkState.Holds`). That
    predicate reads only the messages, so every token gives the same view. -/
def Net.Holds {p : Participant} (net : Net p) (ss : SignedState) : Prop :=
  ∀ t, (net.view t).Holds ss

/-- A move of the honest participant (Nitro `HonestMove`): a call, or a signed
    state sent. -/
inductive HonestMove
  | chain (call : Call)
  | send (st : Nitro.State)

/-- A move of the adversary (Nitro `AdvMove`): a call, or a signed state
    delivered to `p`. -/
inductive AdvMove
  | chain (call : Call)
  | deliver (ss : SignedState)

/-- The honest participant submits only states it holds, and challenges only
    as itself. -/
def HonestMove.Feasible {p : Participant} (net : Net p) : HonestMove → Prop
  | .chain call => (∀ ss ∈ call.proofStates, net.Holds ss) ∧ ∀ q, call.challenger = some q → q = p
  | .send _ => True

/-- A move that does not let time pass (Nitro `HonestMove.NoWait`). -/
def HonestMove.NoWait : HonestMove → Prop
  | .chain (.tick _) => False
  | _ => True

/-- The results of a call: a successful step, or no change when the call cannot
    execute. -/
inductive CallResult (cfg : Config) (apps : Apps) {p : Participant} (call : Call) :
    Net p → Net p → Prop
  | ok {net : Net p} {s' : ArmadaState} (h : ArmadaStep cfg apps call net.chain s') :
      CallResult cfg apps call net { net with chain := s' }
  | fail {net : Net p} (h : ¬ CallEnabled cfg apps net.chain call) :
      CallResult cfg apps call net net

/-- The results of an honest move (Nitro `NetworkState.applyHonest`). -/
def HonestResult (cfg : Config) (apps : Apps) {p : Participant} :
    HonestMove → Net p → Net p → Prop
  | .chain call, net, net' => CallResult cfg apps call net net'
  | .send st, net, net' => net' = { net with sent := ⟨st, [p]⟩ :: net.sent }

/-- The results of an adversary move (Nitro `NetworkState.applyAdv`). -/
def AdvResult (cfg : Config) (apps : Apps) {p : Participant} : AdvMove → Net p → Net p → Prop
  | .chain call, net, net' => CallResult cfg apps call net net'
  | .deliver ss, net, net' => net' = { net with received := ss :: net.received }

/-- What the adversary can do (Nitro `Threat`). -/
structure Threat (p : Participant) where
  feasible : Net p → AdvMove → Prop

/-- A list of adversary moves, each feasible where it is played. -/
inductive Threat.FeasibleSeq (cfg : Config) (apps : Apps) {p : Participant} (T : Threat p) :
    Net p → List AdvMove → Net p → Prop
  | nil {net : Net p} : T.FeasibleSeq cfg apps net [] net
  | cons {net net1 net' : Net p} {m : AdvMove} {rest : List AdvMove} :
      T.feasible net m → AdvResult cfg apps m net net1 →
      T.FeasibleSeq cfg apps net1 rest net' → T.FeasibleSeq cfg apps net (m :: rest) net'

/-- The chain and cryptography assumptions (Nitro `Assumptions`; SATP:164-168),
    for the Armada system. -/
structure Assumptions (cfg : Config) (apps : Apps) (p : Participant) (T : Threat p) : Prop where
  /-- SATP:168: the adversary submits `p`'s signature only on a state `p`
      sent. -/
  unforgeable : ∀ net call, T.feasible net (.chain call) →
    ∀ ss ∈ call.proofStates, p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state
  /-- The same bound for delivered states. -/
  unforgeableDeliver : ∀ net ss, T.feasible net (.deliver ss) →
    p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state
  /-- The adversary never challenges as `p`. -/
  notHonest : ∀ net call, T.feasible net (.chain call) → call.challenger ≠ some p
  /-- SATP:166-167; Nitro:537-539: the adversary cannot move the clock to a
      pending deadline of `p`, in any token. -/
  unimpeded : ∀ net dt, T.feasible net (.chain (.tick dt)) →
    ∀ t d, (net.view t).PendingDeadline d → net.chain.now + dt < d
  /-- Nitro:460-461: every call by another party that carries no forged
      signature of `p` and moves no clock is feasible. This includes every
      pool step of another pool user. -/
  capable : ∀ net call, call.challenger ≠ some p → (∀ dt, call ≠ .tick dt) →
    (∀ ss ∈ call.proofStates, p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state) →
    T.feasible net (.chain call)
  /-- The adversary can deliver any state it can sign. -/
  capableDeliver : ∀ net ss, (p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state) →
    T.feasible net (.deliver ss)
  /-- The adversary can let time pass short of every pending deadline. -/
  capableTick : ∀ net dt, (∀ t d, (net.view t).PendingDeadline d → net.chain.now + dt < d) →
    T.feasible net (.chain (.tick dt))

/-- Nitro:526-530 (Nitro `Unbeatable`), with relational moves: `p` has a finite
    strategy tree, using only moves in `allowed`, that reaches `G` against
    every feasible adversary play and every result of each call. -/
inductive UnbeatableBy (cfg : Config) (apps : Apps) {p : Participant} (T : Threat p)
    (allowed : HonestMove → Prop) (G : Net p → Prop) : Net p → Prop
  | done {net : Net p} : G net → UnbeatableBy cfg apps T allowed G net
  | move {net : Net p} (m : HonestMove) : m.Feasible net → allowed m →
      (∀ advs net', T.FeasibleSeq cfg apps net advs net' →
        ∀ net'', HonestResult cfg apps m net' net'' → UnbeatableBy cfg apps T allowed G net'') →
      UnbeatableBy cfg apps T allowed G net

/-- Nitro `Unbeatable` over the Armada system. -/
def Unbeatable (cfg : Config) (apps : Apps) {p : Participant} (T : Threat p) (G : Net p → Prop)
    (net : Net p) : Prop :=
  UnbeatableBy cfg apps T (fun _ => True) G net

/-- Nitro `UnbeatableNoWait` (Liveness.lean:27-33) over the Armada system. -/
def UnbeatableNoWait (cfg : Config) (apps : Apps) {p : Participant} (T : Threat p)
    (G : Net p → Prop) (net : Net p) : Prop :=
  UnbeatableBy cfg apps T HonestMove.NoWait G net

/-- Nitro `Finalizable` (Nitro:590-593) for token `t`. -/
def Finalizable (cfg : Config) (apps : Apps) {p : Participant} (T : Threat p) (t : Token)
    (c : FixedPart) (Ω : Outcome) (net : Net p) : Prop :=
  Unbeatable cfg apps T (fun net' => (net'.view t).Finalized c Ω) net

/-- Nitro `FundedFor` (Nitro:480-481) at note level: `p` can obtain a state in
    which the notes of channel `c` in token `t` total at least `x`. -/
def FundedFor (cfg : Config) (apps : Apps) {p : Participant} (T : Threat p) (t : Token)
    (c : FixedPart) (x : Coins) (net : Net p) : Prop :=
  Unbeatable cfg apps T (fun net' => x ≤ net'.chain.balance t c) net

/-- A family of network states, one per participant (Nitro `Views`). -/
def Views := ∀ p : Participant, Net p

/-- The views share one chain, and what one participant sent the others
    received (Nitro `Views.Consistent`). -/
def Views.Consistent (v : Views) : Prop :=
  (∀ p q, (v p).chain = (v q).chain) ∧
  (∀ p q, p ≠ q → ∀ ss ∈ (v p).sent, ss ∈ (v q).received)

/-- The Nitro views of token `t`. -/
def Views.nitro (v : Views) (t : Token) : Nitro.Views := fun p => (v p).view t

/-- One threat per participant, with its assumptions (Nitro `Threats`). -/
structure Threats (cfg : Config) (apps : Apps) where
  T : ∀ p : Participant, Threat p
  ok : ∀ p, Assumptions cfg apps p (T p)

/-- Nitro `Views.FinalizableBy` over the Armada system. -/
def Views.FinalizableBy (cfg : Config) (apps : Apps) (Ts : Threats cfg apps) (v : Views)
    (t : Token) (c : FixedPart) (Ω : Outcome) (ps : List Participant) : Prop :=
  ∀ p ∈ ps, Finalizable cfg apps (Ts.T p) t c Ω (v p)

/-- Nitro `LedgerWithSub.Holds` (Nitro:945, eq 6) at note level: the ledger
    `L`'s notes total `a + b + c`, and its outcome is finalizable by `A` and
    `B`. -/
def HoldsLedgerWithSub (cfg : Config) (apps : Apps) (Ts : Threats cfg apps) (v : Views)
    (t : Token) (w : LedgerWithSub) : Prop :=
  IsLedgerChannel apps w.L ∧ w.L.participants = [w.A, w.B] ∧
  (∀ p, (v p).chain.balance t w.L = w.a + w.b + w.c) ∧
  v.FinalizableBy cfg apps Ts t w.L w.outcome [w.A, w.B]

end ArmadaLean.ArmadaNitro
