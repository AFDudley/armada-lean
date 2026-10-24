/-
  ArmadaLean.Adjudicator.Channel — a channel's identity, its state, who
  supports a state, and who can finalize an outcome.

  This file translates S1-S4's state-channel vocabulary into Lean, one
  definition per source quote, plus the operator's addition: "finalizable
  outcome" and "enabled outcome" (Nitro-2019-219.pdf §4.4), formalizing
  "who gets paid" the way the papers define it, not by invented rules.
  `Outcome.lean` holds the payout pieces these definitions carry as data;
  `Operations.lean` holds the state TRANSITIONS (challenge, checkpoint,
  conclude) that this file's definitions describe the shape of.
-/
import ArmadaLean.Adjudicator.Assumptions
import ArmadaLean.Adjudicator.Outcome

namespace ArmadaLean.Adjudicator

/-!
## State: FixedPart and VariablePart

S4 `0010-states-channels.md`, "States": "In Nitro protocol, a state is
broken up into fixed and variable parts: `struct FixedPart { address[]
participants; uint48 channelNonce; address appDefinition; uint48
challengeDuration; } struct VariablePart { Outcome.SingleAssetExit[]
outcome; bytes appData; uint48 turnNum; bool isFinal; }`" (clauses 1, 2).

S3 §2.1 names the same two parts `ChannelConsts` (`peers`, `appDef`,
`nonce`, `challengeDuration`) and `ChannelVars` (`version`, `isFinal`,
`outcome`, `appData`, `signatures`) — S3's `version` is S4's `turnNum`
under a different name; S3 bundles `signatures` into the variable part
where S4 keeps them in a separate `SignedVariablePart` wrapper (below).

S1 (ForceMove, 2018) has no `FixedPart`/`VariablePart` split at all: its
`PreFundsetupState`/`GameState`/`ConcludeState` (§3.2.2-3.2.4) each carry
`channel`, `turnNum` and `resolution` (S1's name for `outcome`) inline,
with no `appDefinition` or `challengeDuration` field — those two only
appear in S4/the code, not in S1. `clauses.md` §2 item 1 records why: S1
fixes `mover = participants[turnNum % n]` and a per-state-type
`validTransition`; the code (and S4) instead delegate ALL execution rules
to the deployed app contract `fixedPart.appDefinition`
(`stateIsSupported`, see the "Application rules and state support"
section below), so `appDefinition` is new infrastructure S1 has no field
for. S1's vocabulary is otherwise a strict subset of S4's: this model
follows S4 (the code's own vocabulary).
-/

/-- `FixedPart`: the channel properties that never change across states
    (S4 `0010-states-channels.md`, "States", quoted above; clause 1). -/
structure FixedPart where
  participants : List Nat
  channelNonce : Nat
  appDefinition : Nat
  challengeDuration : Nat

/-- `VariablePart`: the properties a state update may change (S4
    `0010-states-channels.md`, "States", quoted above; clause 2). -/
structure VariablePart where
  outcome : Outcome
  appData : Nat
  turnNum : Nat
  isFinal : Bool

/-- The channel id (S4 `0010-states-channels.md`, "Channel IDs"; clause 3).
    `Assumptions.lean`'s `channelIdOf`/`channelIdOf_inj` state what a
    caller cannot do to it. -/
noncomputable def channelId (fp : FixedPart) : Nat :=
  channelIdOf fp.participants fp.channelNonce fp.appDefinition fp.challengeDuration

/-- The state hash (S4 `0010-states-channels.md`, "State commitments";
    clause 4). -/
noncomputable def stateHash (fp : FixedPart) (vp : VariablePart) : Nat :=
  stateHashOf (channelId fp) vp.appData vp.outcome vp.turnNum vp.isFinal

/-!
## Signed state and support proof

S4 `0010-states-channels.md`, "`SignedVariableParts`": "Signatures on a
state hash by different participants are often bundled up with the
variable part of the state when being submitted to chain: `struct
SignedVariablePart { VariablePart variablePart; Signature[] sigs; }`."

S4 `0010-states-channels.md`, "Support proofs": "A support proof is any
bundle of information sufficient for the chain to verify that a given
channel state is legitimate. They usually consist of `FixedPart`, plus a
singular `SignedVariablePart` named `candidate`, plus an array of
`SignedVariableParts` named `proof`."

S3 §2.2 names the same thing a `SupportProof { consts: ChannelConsts,
vars: ChannelVars[] }` and states the rule it must satisfy: "a function
accepting an arbitrary number of states and signatures and returning the
latest single state which is deemed to be supported by those inputs."

A state is "signed by participant p" iff p produced an authorization over
its hash — assumption 2 (`Assumptions.lean`'s `SignatureAssumptions.
contractAuthorizes`, for a contract participant, combined with the
EXECUTION-tracked `signedBy` relation, for an EOA participant, gated on
an `Actor` matching the signer — `Operations.lean`'s module comment).
The combined notion, `AuthorizedBy`, and `SignedByAll` (used by
`conclude`, below — S3 §2.2's `signedByEveryone`; S4
`0020-execution-rules.md`, `ConsensusApp`, "a state must be unanimously
countersigned — that is, signed by all of the channel participants") are
defined in `State.lean`, not here: both need `AdjudicatorState` (for its
`signedBy` field), which is not defined until that file. -/

/-!
## Application rules and state support

S4 `0020-execution-rules.md`, "Core protocol rules": "Nitro is a very open
protocol: ...very little is stipulated at the core protocol level. Each
application gets full control over when a state can be considered
supported. The only things enforced by the core protocol are: the rule
that higher turn numbers take precedence over lower ones; an escape hatch
for an 'instant checkout'..." (clause 7).

S4 `0020-execution-rules.md`, "Application rules": each channel's app
contract implements `function stateIsSupported(FixedPart calldata
fixedPart, RecoveredVariablePart[] calldata proof, RecoveredVariablePart
calldata candidate) external view returns (bool, string memory);`.

S3 §2.2 states the same function, `latestSupportedState(proof) :
ChannelState`, and names two concrete instances: the `consensus app`
("require(signedByEveryone(vars[0], consts.peers))") and a more
sophisticated virtual-channel app (S3 §3.2, Listing 3).

A gap between S1 and S3/S4: S1 §3.1.3/§3.2 fixes `mover =
participants[turnNum % n]` with one `validTransition` per state TYPE
(PREFUNDSETUP/POSTFUNDSETUP/GAME/CONCLUDE), enforced by the core protocol
itself. S3/S4 remove turn-taking from the core protocol entirely and let
EVERY application define its own `stateIsSupported`/`latestSupportedState`
(`clauses.md` clause 10, `StrictTurnTaking`), not a rule S3/S4's core
protocol states. This model follows S3/S4: the application rule below is
the one hook the core protocol core exposes, with no built-in
turn-taking or consensus rule, matching clause 7's "very little is
stipulated at the core protocol level". -/

/-!
Application rule: whether `candidate` is supported by `proof`, AT STATE
`s` (S4 `0020-execution-rules.md`, "Application rules", quoted above; S3
§2.2's `latestSupportedState`; clause 7). A PARAMETER of the model
(`Operations.lean`'s `Step`, `appRel : AdjudicatorState → FixedPart →
List VariablePart → VariablePart → Prop`), not a bare global axiom
(coordinator correction, this session: "the app relation is a parameter
of the model") — safety theorems (`Safety.lean`, sections A-C) quantify
it for ANY app; the can-happen theorems (section D) use the real,
deployed `ConsensusApp`'s own relation in its place. Defined in
`Operations.lean`, not here: it takes `AdjudicatorState`, which is not
defined until `State.lean`. Takes the CURRENT state `s`, not only
`(fp, proof, candidate)`: this model's `candidate` carries no inline
signature array the way the real `RecoveredVariablePart` does
(`State.lean`'s `SignedByAll` already reads the execution-tracked
`signedBy` for the same reason), so a concrete consensus-style rule can
only be evaluated against the execution's own signing record. Pluggable
per `fixedPart.appDefinition`, fixed at channel-creation time in the
real protocol; this model uses ONE relation per execution/theorem, the
simplification Nitro-2019-219.pdf §4.4's own Figure 11 discussion
already makes (a single hook, not per-channel dispatch).
-/

/-!
## Channel modes

S4 `0040-lifecycle-of-a-channel.md`, "Channel Modes": "A channel is in one
or the other of three modes... `Open --> Challenge: challenge`, `Open -->
Open: checkpoint`, `Open --> Finalized: conclude`, `Challenge -->
Challenge: challenge`, `Challenge --> Open: checkpoint`, `Challenge -->
Finalized: conclude`, `Challenge --> Finalized': timeout`." And
"`finalizesAt`": "the channel mode is determined by the relation between
the timestamp of the current block and the `finalizesAt` timestamp stored
on chain. When `finalizesAt` is in the past, the channel is `Finalized`;
when it is in the future, the channel is in `Challenge`. When it is (the
magic and initial value of) `0`, the channel is `Open`." (clause 11,
quoting the identical code comment at `StatusManager.sol:17-30`.)

S3 §2.3, `isOpen`: "`return status.finalizesAt == 0 || status.finalizesAt >
now`" — the same rule stated as the negation of `Finalized`.

The `timeout` transition is passive (S4, "The remaining transition
`timeout` is a passive transition which happens when a block is produced
with a sufficiently large timestamp."; clause 18's [INFERENCE]: "no
separate function" needed). This model's `mode` function below computes it
directly from `finalizesAt` and the current time, with no step needed to
"apply" a timeout — matching the quote. -/
inductive ChannelMode where
  | open
  | challenge
  | finalized
  deriving DecidableEq

/-- Adjudicator storage per channel (S4 `0040-lifecycle-of-a-channel.md`,
    "Adjudicator storage": `turnNumRecord` (48 bits), `finalizesAt` (48
    bits), and a `fingerprint` built from `stateHash` and `outcomeHash`;
    clause 12). This model stores `stateHash`/`outcomeHash` directly rather
    than the 160-bit keccak "fingerprint" of the two: the fingerprint
    exists only to fit three values into one 32-byte storage slot (S4: "the
    most significant 48 bits... the next most significant 48 bits...
    the next most significant 160 bits"), a gas-storage encoding with no
    semantic content beyond what the three unpacked fields already carry.
    No caller influences that packing, so removing it removes nothing this
    model needs. -/
structure ChannelStatus where
  turnNumRecord : Nat
  finalizesAt : Nat
  stateHash : Nat
  outcomeHash : Nat

/-- The empty status every channel starts at (S4 `0040-lifecycle-of-a-
    channel.md`, `_mode`'s code comment, quoted in `Operations.lean`:
    "`_unpackStatus(someRandomChannelId)` returns `(0,0,0)`, which is
    correct when nobody has written to storage yet."). -/
def emptyStatus : ChannelStatus := ⟨0, 0, 0, 0⟩

/-- A channel's mode, derived from `finalizesAt` and the current time (S4
    `0040-lifecycle-of-a-channel.md`, "Channel Modes"/"`finalizesAt`",
    quoted above; S3 §2.3 `isOpen`; clause 11). -/
def ChannelStatus.mode (c : ChannelStatus) (now : Nat) : ChannelMode :=
  if c.finalizesAt = 0 then .open
  else if c.finalizesAt ≤ now then .finalized
  else .challenge

/-!
## Finalizable and enabled outcomes (Nitro-2019-219.pdf §4.4)

"We say an outcome, ω, is finalizable for participant A, if A has an
unbeatable strategy for finalizing this outcome in the adjudicator. We use
the notation [Γ ↦ ω]_A, to represent a state of a channel, Γ, where the
outcome, ω, is finalizable by A. A's unbeatable strategy [Γ ↦ ω]_A ⟹
⟦Γ ↦ ω⟧" (§4.4, eq. 1).

"If a participant has no finalizable outcomes, their analysis of the
network needs to be performed in terms of their enabled outcomes. The
enabled outcomes for a participant, p, is defined as the set of outcomes
that p has no strategy to prevent from being finalized." (§4.4).

"For any participant, p, in a channel, Γ, exactly one of the following
statements is true at a given point in time: 1. p has at least one
finalizable outcome. 2. p has at least two enabled outcomes. Note that if
a participant has only enabled a single outcome, that outcome must be
finalizable for them." (§4.4).

§4.3 defines "unbeatable strategy" through two named assumptions about the
chain: "1. Transactions are unimpeded: given that the current time is t
and Δ > 0, then it is possible for any party to apply any operation, O, on
chain before time t + Δ. 2. Transactions can be front-run: given two
parties, p1 and p2, and two operations, O1 and O2, there is no way for p1
to ensure that they can apply O1 to the chain before p2 applies O2."

§3.3 is the Nitro-protocol-independent statement most of this model's
call layer already follows without being told to: "There is no
restriction on who can trigger the operations." This is why
`Operations.lean`'s `Step` relation carries no `actor` check for any
call EXCEPT `.sign`/`.signNote` (whose own effect IS the restriction —
`Operations.lean`'s module comment) — matching §4.3 assumption 1 (anyone
can apply any operation) and assumption 2 (no one can block another's
operation), which together are exactly the premise "unbeatable strategy"
needs: a participant's strategy is a fixed sequence of calls they can
always append, `Finalizable`/`unbeatable_pays` state this concretely for
this adjudicator's two concrete unbeatable cases: the "concluded" point
(S2 §4.4 point 2, unanimous signatures reached — `SignedByAll`,
`State.lean`) and the "timeout" point (ForceMove-2018.pdf §1.2: "the
adjudicator releases funds according to the resolution specified by the
most recently known state at the time of the dispute", after
`challengeDuration` with no higher-turn response). Full strategy-space
reasoning over an arbitrary application's `appRel` is out of this
phase's scope (see `Safety.lean`'s header); this model instantiates
finalizability at the two points every ForceMove channel is guaranteed
to reach (Nitro-2019-219.pdf §4.4, Figure 11: "Every ForceMove channel
has at least two points when the outcome is universally finalizable:
one at the funding point and one when the channel has concluded."),
which is what `Operations.lean`'s `conclude` and the challenge-timeout
mechanics model.
-/

end ArmadaLean.Adjudicator
