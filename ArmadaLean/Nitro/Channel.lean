/-
  Nitro protocol specification: channel states, signatures, application rules
  and the per-channel adjudication status. See `Address.lean` for the source
  list.

  Modelling choice (signatures). A signature is symbolic. A signed state
  carries the list of participants who signed it; this is go-nitro's
  `RecoveredVariablePart.signedBy` (INitroTypes.sol:32-35) as a list instead
  of a bitmask. Who can produce a signature is a game rule in `Strategy.lean`
  (`Assumptions.unforgeable`), not a property of the data.
-/
import ArmadaLean.Nitro.Outcome

namespace ArmadaLean.Nitro

/-- SATP:630-637 `Voucher { virtualChannelId, version, alice, bob,
    signatures }`. -/
structure Voucher where
  virtualChannelId : FixedPart
  version : Nat
  alice : Coins
  bob : Coins
  signers : List Participant
  deriving DecidableEq, Repr

/-- SATP:616-620: "The setup states are given type None. Alice can move from a
    state with type None to a state with type A, or a state with type B to a
    state with type AB. Bob can move from ... None to ... B, or ... A to
    AB." -/
inductive VType
  | none
  | A
  | B
  | AB
  deriving DecidableEq, Repr

/-- The app data of a virtual channel state: its type and its voucher.
    Operator ruling 2026-10-27: the state carries this value, not bytes;
    ABI encoding, decoding and the round-trip theorem belong to the
    refinement layer. -/
structure VirtualAppData where
  type : VType
  voucher : Voucher
  deriving DecidableEq, Repr

/-- Application data in a state. SATP:209 `appData : bytes // parsed by
    custom app logic`; go-nitro INitroTypes.sol:22. The SATP virtual channel
    app reads `VirtualAppData`; every other app reads an opaque label. The
    state carries the parsed value (operator ruling 2026-10-27). -/
inductive AppData
  | satpVirtual (d : VirtualAppData)
  | opaque (label : Nat)
  deriving DecidableEq, Repr

/-- A channel state. SATP:205-211 `ChannelVars { version, isFinal, outcome,
    appData, signatures }` with the constants of SATP:218-221; go-nitro
    INitroTypes.sol:20-25 `VariablePart { outcome, appData, turnNum,
    isFinal }`. SATP calls the counter `version`; go-nitro and ForceMove:699-715
    call it `turnNum`. The code name is used. -/
structure State where
  channel : FixedPart
  turnNum : Nat
  outcome : Outcome
  isFinal : Bool
  appData : AppData
  deriving DecidableEq, Repr

/-- ForceMove:714 `State::mover: s ↦ s.channel.participants[s.turnNum % n]`
    (ForceMove only; SATP and Nitro leave turn-taking to the application;
    go-nitro StrictTurnTaking.sol has the same rule as a library). -/
def State.mover (s : State) : Option Participant :=
  s.channel.participants[s.turnNum % s.channel.n]?

/-- A state with its signatures. SATP:244-245: "each state containing one or
    more signatures from the channel's peer list"; go-nitro
    INitroTypes.sol:27-35 `SignedVariablePart`/`RecoveredVariablePart`. -/
structure SignedState where
  state : State
  signers : List Participant
  deriving DecidableEq, Repr

/-- SATP:264 `signedByEveryone(vars[0], consts.peers)`; go-nitro
    Consensus.sol `getClaimedSignersNum(candidate.signedBy) ==
    participants.length`. -/
def SignedState.ByAll (ss : SignedState) : Prop :=
  ∀ p ∈ ss.state.channel.participants, p ∈ ss.signers

instance (ss : SignedState) : Decidable ss.ByAll :=
  inferInstanceAs (Decidable (∀ p ∈ ss.state.channel.participants, p ∈ ss.signers))

/-- ForceMove:750 `toMove.state.mover == toMove.signer` (ForceMove only). -/
def SignedState.ByMover (ss : SignedState) : Prop :=
  ∃ m, ss.state.mover = some m ∧ m ∈ ss.signers

/-- `ByMover` as a decision. -/
def SignedState.byMover (ss : SignedState) : Bool :=
  match ss.state.mover with
  | some m => decide (m ∈ ss.signers)
  | none => false

/-- A support proof. SATP:247-250 `SupportProof { consts, vars :
    ChannelVars[] }`; go-nitro ForceMove.sol `proof :
    SignedVariablePart[]`. -/
abbrev SupportProof := List SignedState

/-- Application rules. SATP:254-259: an application maps a support proof to
    "the most recent version of the channel's state to be supported by all
    peers in the channel, even if not explicitly signed by every peer".
    go-nitro IForceMoveApp.sol `stateIsSupported(fixedPart, proof,
    candidate)` returns a boolean; the model follows the code and keeps the
    candidate separate from the proof. `supports c proof candidate = true`
    when the proof supports `candidate` in channel `c`. Operator ruling
    2026-10-27: the rules are a computable `Bool` function, as in the code.
    ForceMove:963-966: the rules are pure; go-nitro declares
    `stateIsSupported` `pure`. That holds by construction: `Rules` has no
    access to chain state. -/
structure Rules where
  supports : FixedPart → SupportProof → State → Bool

/-- ForceMove:761-778 (ForceMove only): a valid transition keeps the channel
    and increments the turn number by exactly one. -/
def UniversalTransition (s1 s2 : State) : Prop :=
  s2.channel = s1.channel ∧ s2.turnNum = s1.turnNum + 1

/-- ForceMove:971-980, 1017-1022, 1187-1208 (ForceMove only): a transition
    into a conclude state keeps the resolution. From a conclude state only a
    conclude state follows. -/
def ConclusionTransition (s1 s2 : State) : Prop :=
  (s2.isFinal = true → s2.outcome = s1.outcome) ∧
  (s1.isFinal = true → s2.isFinal = true)

/-- ForceMove:744-751 `validMove(fromMove, toMove)` (ForceMove only): a valid
    transition, and the signer of `toMove` is its mover. `vt` is the game
    library's `validTransition` (ForceMove:971-973). -/
def ValidMove (vt : State → State → Prop) (m1 m2 : SignedState) : Prop :=
  UniversalTransition m1.state m2.state ∧
  ConclusionTransition m1.state m2.state ∧
  (m2.state.isFinal = false → vt m1.state m2.state) ∧
  m2.ByMover

/-- `ValidMove` as a decision, for a `Bool` game library `vt`. -/
def validMove (vt : State → State → Bool) (m1 m2 : SignedState) : Bool :=
  decide (m2.state.channel = m1.state.channel) && decide (m2.state.turnNum = m1.state.turnNum + 1) &&
  (!m2.state.isFinal || decide (m2.state.outcome = m1.state.outcome)) &&
  (!m1.state.isFinal || m2.state.isFinal) &&
  (m2.state.isFinal || vt m1.state m2.state) &&
  m2.byMover

/-- A run of valid moves. -/
def validRun (vt : State → State → Bool) : SupportProof → Bool
  | [] => true
  | [_] => true
  | m1 :: m2 :: rest => validMove vt m1 m2 && validRun vt (m2 :: rest)

/-- The ForceMove rules as an application. ForceMove:1340-1354 `forceMove`: a
    run of `n` valid moves, one per participant, whose last state is the
    candidate; ForceMove:724-727: "players must take turns in a cyclical
    order." go-nitro StrictTurnTaking.sol is the same rule. -/
def forceMoveRules (vt : State → State → Bool) : Rules where
  supports c proof candidate :=
    decide (proof.length = c.n) &&
    validRun vt proof &&
    proof.all (fun m => decide (m.state.channel = c)) &&
    decide ((proof.getLast?.map SignedState.state) = some candidate)

/-- The consensus app. SATP:262-266: exactly one state, signed by everyone.
    go-nitro Consensus.sol: `proof.length == 0` and the candidate is
    unanimous. The two agree: the one signed state is the candidate.
    Nitro:660-688 calls it the consensus game. -/
def consensusRules : Rules where
  supports c proof candidate :=
    match proof with
    | [ss] => decide (ss.state = candidate) && decide (ss.state.channel = c) && decide ss.ByAll
    | _ => false

/-- A conclusion proof. go-nitro ForceMove.sol `_conclude`: `isFinal` and
    unanimous signatures, with no call to the application. SATP:286-289:
    "supporting a state with isFinal = true"; Nitro:297-298: "all the
    participants sign a special conclude state, called a conclusion proof".
    The code form is used: every participant signs, for every application.
    ForceMove:1030-1058's `n` consecutive conclude moves are superseded. -/
def ConclusionProof (c : FixedPart) (ss : SignedState) : Prop :=
  ss.state.channel = c ∧ ss.state.isFinal = true ∧ ss.ByAll

instance (c : FixedPart) (ss : SignedState) : Decidable (ConclusionProof c ss) :=
  inferInstanceAs (Decidable (ss.state.channel = c ∧ ss.state.isFinal = true ∧ ss.ByAll))

/-- An on-chain challenge. SATP:234-238 stores `version`, `outcome`,
    `finalizationTime`; go-nitro stores the turn record, the finalization
    time and a fingerprint of the state and outcome (StatusManager.sol). The
    model stores the state itself; the hash is an encoding. -/
structure Challenge where
  state : State
  deadline : Time
  deriving DecidableEq, Repr

/-- The adjudication status of one channel. go-nitro StatusManager.sol:5-14
    `_mode`: Open, Challenge, Finalized, read from the stored finalization
    time and
    `block.timestamp`; SATP:234-241 `AdjudicationState` per channel id. The
    explicit constructors replace the zero sentinel of the code.
    `turnNumRecord` is go-nitro's name (ForceMove.sol:22) for SATP's
    `version` (SATP:235). -/
inductive ChannelStatus
  | open (turnNumRecord : Nat)
  | challenged (turnNumRecord : Nat) (ch : Challenge)
  | finalized (turnNumRecord : Nat) (outcome : Outcome)
  deriving DecidableEq, Repr

/-- The modes a caller can observe. go-nitro IStatusManager `ChannelMode
    { Open, Challenge, Finalized }`. ForceMove:1504-1507: "a game concluded
    with a conclusion proof behaves exactly the same as one that was
    terminated by an expired challenge", so Concluded and Terminated are one
    mode. -/
inductive Mode
  | open
  | challenge
  | finalized
  deriving DecidableEq, Repr

/-- go-nitro StatusManager.sol:5-14: Open when there is no challenge,
    Finalized when the finalization time is at or before `block.timestamp`,
    Challenge otherwise.
    SATP:294-298 `isOpen`. The timeout is passive: only `now` moves. -/
def ChannelStatus.mode (st : ChannelStatus) (now : Time) : Mode :=
  match st with
  | .open _ => .open
  | .challenged _ ch => if ch.deadline ≤ now then .finalized else .challenge
  | .finalized _ _ => .finalized

/-- SATP:294-298 `isOpen`: no active challenge, or the challenge has not
    expired. go-nitro `_requireChannelNotFinalized` (ForceMove.sol). -/
def ChannelStatus.IsOpen (st : ChannelStatus) (now : Time) : Prop :=
  st.mode now ≠ .finalized

instance (st : ChannelStatus) (now : Time) : Decidable (st.IsOpen now) :=
  inferInstanceAs (Decidable (st.mode now ≠ .finalized))

/-- The stored turn number. go-nitro `_unpackStatus` `turnNumRecord`. -/
def ChannelStatus.turnNumRecord : ChannelStatus → Nat
  | .open t => t
  | .challenged t _ => t
  | .finalized t _ => t

/-- The finalized outcome, if the channel is finalized at `now`.
    Nitro:263-264: "the outcome of the channel is stored on the blockchain." -/
def ChannelStatus.finalOutcome (st : ChannelStatus) (now : Time) : Option Outcome :=
  match st with
  | .open _ => none
  | .challenged _ ch => if ch.deadline ≤ now then some ch.state.outcome else none
  | .finalized _ o => some o

/-- Replace the finalized outcome. go-nitro `_updateFingerprint`
    (MultiAssetHolder.sol) rewrites the stored outcome after a transfer or a
    reclaim; SATP:363. -/
def ChannelStatus.withOutcome (st : ChannelStatus) (o : Outcome) : ChannelStatus :=
  .finalized st.turnNumRecord o

end ArmadaLean.Nitro
