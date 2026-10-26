/-
  Nitro protocol specification: channel states, signatures, application rules
  and the per-channel adjudication status. See `Address.lean` for the source
  list.

  Modelling choice (signatures). A signature is symbolic. A signed state
  carries the list of participants who signed it. The adjudicator reads that
  list. Who can produce a signature is a game rule in `Strategy.lean`
  (`Assumptions.unforgeable`), not a property of the data.
-/
import ArmadaLean.Nitro.Outcome

namespace ArmadaLean.Nitro

/-- A channel state. S1:699-715: every state carries `channel`, `turnNum`,
    `resolution`. S3:205-211 `ChannelVars { version, isFinal, outcome,
    appData, signatures }`. S3 calls the counter `version`; S1 calls it
    `turnNum`. S1:1006-1011 marks a conclude state by its type; S3 marks it
    by `isFinal`. `appData` is S1:932-938 `gameAttributes`, opaque here. -/
structure State where
  channel : FixedPart
  turnNum : Nat
  outcome : Outcome
  isFinal : Bool
  appData : Nat
  deriving DecidableEq, Repr

/-- S1:714 `State::mover: s ↦ s.channel.participants[s.turnNum % n]`. -/
def State.mover (s : State) : Option Participant :=
  s.channel.participants[s.turnNum % s.channel.n]?

/-- A state with its signatures. S1:674-683 `Move { state, signature }`,
    "From the signature you can deduce the signer." S3:244-245: "each state
    containing one or more signatures from the channel's peer list." -/
structure SignedState where
  state : State
  signers : List Participant
  deriving DecidableEq, Repr

/-- S3:264 `signedByEveryone(vars[0], consts.peers)`; S2:297-298 "all the
    participants sign a special conclude state". -/
def SignedState.ByAll (ss : SignedState) : Prop :=
  ∀ p ∈ ss.state.channel.participants, p ∈ ss.signers

/-- S1:750 `toMove.state.mover == toMove.signer`. -/
def SignedState.ByMover (ss : SignedState) : Prop :=
  ∃ m, ss.state.mover = some m ∧ m ∈ ss.signers

/-- A support proof. S3:247-250 `SupportProof { consts, vars : ChannelVars[] }`.
    S1:1030-1058 and S1:1340-1354 pass a list of signed moves. -/
abbrev SupportProof := List SignedState

/-- Application rules. S3:254-259: an application maps a support proof to
    "the most recent version of the channel's state to be supported by all
    peers in the channel, even if not explicitly signed by every peer."
    `supports c proof candidate` holds when the proof supports `candidate` in
    channel `c`. S1:963-966: the rules are pure. They read only the states.
    That holds by construction: `Rules` has no access to chain state. -/
structure Rules where
  supports : FixedPart → SupportProof → State → Prop

/-- S1:761-778: a valid transition keeps the channel and increments the
    turn number by exactly one. -/
def UniversalTransition (s1 s2 : State) : Prop :=
  s2.channel = s1.channel ∧ s2.turnNum = s1.turnNum + 1

/-- S1:971-980, S1:1017-1022, S1:1187-1208: a transition into a conclude
    state keeps the resolution. From a conclude state only a conclude state
    follows. -/
def ConclusionTransition (s1 s2 : State) : Prop :=
  (s2.isFinal = true → s2.outcome = s1.outcome) ∧
  (s1.isFinal = true → s2.isFinal = true)

/-- S1:744-751 `validMove(fromMove, toMove)`: a valid transition, and the
    signer of `toMove` is its mover. `vt` is the game library's
    `validTransition` (S1:971-973). -/
def ValidMove (vt : State → State → Prop) (m1 m2 : SignedState) : Prop :=
  UniversalTransition m1.state m2.state ∧
  ConclusionTransition m1.state m2.state ∧
  (m2.state.isFinal = false → vt m1.state m2.state) ∧
  m2.ByMover

/-- A run of valid moves. -/
def ValidRun (vt : State → State → Prop) : SupportProof → Prop
  | [] => True
  | [_] => True
  | m1 :: m2 :: rest => ValidMove vt m1 m2 ∧ ValidRun vt (m2 :: rest)

/-- The ForceMove rules. S1:1340-1354 `forceMove(moves)`: a run of `n` valid
    moves, one per participant, whose last state is the candidate. S1:724-727:
    "players must take turns in a cyclical order." -/
def forceMoveRules (vt : State → State → Prop) : Rules where
  supports c proof candidate :=
    proof.length = c.n ∧
    ValidRun vt proof ∧
    (∀ m ∈ proof, m.state.channel = c) ∧
    (∃ m, proof.getLast? = some m ∧ m.state = candidate)

/-- The consensus app. S3:262-266: exactly one state, signed by everyone.
    S2:660-688 calls it the consensus game. -/
def consensusRules : Rules where
  supports c proof candidate :=
    ∃ ss, proof = [ss] ∧ ss.state = candidate ∧ ss.state.channel = c ∧ ss.ByAll

/-- S1:1030-1058 `validConclusionProof`: in S2:296-299 and S3:286-289 the
    form is "a state with `isFinal = true`" supported by all participants.
    S1's `n` consecutive conclude moves are superseded by this form
    (S1-A09). -/
def ConclusionProof (c : FixedPart) (ss : SignedState) : Prop :=
  ss.state.channel = c ∧ ss.state.isFinal = true ∧ ss.ByAll

/-- An on-chain challenge. S1:1292-1297 `Challenge { endState, endTime }`.
    S3:234-238 stores `version`, `outcome`, `finalizationTime`. -/
structure Challenge where
  state : State
  deadline : Time
  deriving DecidableEq, Repr

/-- The adjudication status of one channel. S1:1237-1247 (Figure 5) has five
    modes. S2:281-290 (Figure 4) has Setup, Running, Challenge, Concluded,
    Finalized. S3:234-241 stores `version`, `outcome`, `finalizationTime`.
    The explicit constructors replace a time sentinel. `turnNumRecord` is the
    stored turn of S1:1543-1545 ("store the turnNum of the response state in
    the adjudicator") and the `version` of S3:235. -/
inductive ChannelStatus
  | open (turnNumRecord : Nat)
  | challenged (turnNumRecord : Nat) (ch : Challenge)
  | finalized (turnNumRecord : Nat) (outcome : Outcome)
  deriving DecidableEq, Repr

/-- The modes a caller can observe. S2:288-290: Challenge, Finalized;
    S1:1504-1507: "a game concluded with a conclusion proof behaves exactly
    the same as one that was terminated by an expired challenge." So
    Concluded and Terminated are one mode here. -/
inductive Mode
  | open
  | challenge
  | finalized
  deriving DecidableEq, Repr

/-- S1:1295-1296: a challenge is in progress while `endTime > now()`; it is
    terminated when the end time passed. S3:294-298 `isOpen`. The timeout is
    a passive transition: only `now` moves. -/
def ChannelStatus.mode (st : ChannelStatus) (now : Time) : Mode :=
  match st with
  | .open _ => .open
  | .challenged _ ch => if ch.deadline ≤ now then .finalized else .challenge
  | .finalized _ _ => .finalized

/-- S3:294-298 `isOpen`: no active challenge, or the challenge has not
    expired. -/
def ChannelStatus.IsOpen (st : ChannelStatus) (now : Time) : Prop :=
  st.mode now ≠ .finalized

instance (st : ChannelStatus) (now : Time) : Decidable (st.IsOpen now) :=
  inferInstanceAs (Decidable (st.mode now ≠ .finalized))

/-- The stored turn number. -/
def ChannelStatus.turnNumRecord : ChannelStatus → Nat
  | .open t => t
  | .challenged t _ => t
  | .finalized t _ => t

/-- The finalized outcome, if the channel is finalized at `now`. S2:263-264:
    "the outcome of the channel is stored on the blockchain." -/
def ChannelStatus.finalOutcome (st : ChannelStatus) (now : Time) : Option Outcome :=
  match st with
  | .open _ => none
  | .challenged _ ch => if ch.deadline ≤ now then some ch.state.outcome else none
  | .finalized _ o => some o

/-- Replace the finalized outcome. The redistribution operations rewrite the
    stored outcome (S2:770, S2:1144, S3:363). -/
def ChannelStatus.withOutcome (st : ChannelStatus) (o : Outcome) : ChannelStatus :=
  .finalized st.turnNumRecord o

end ArmadaLean.Nitro
