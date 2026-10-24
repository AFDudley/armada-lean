/-
  ArmadaLean.Adjudicator.State — the adjudicator's full on-chain state.

  Combines `Channel.lean`'s per-channel status (the S1-S4 layer) with
  `Notes.lean`'s pool state (the Armada layer) into one record every
  `Operations.lean` call transitions. Armada layer: the armada-nitro
  rule (`AdjudicatorState`'s `holdings` field, below, states and cites
  it) — `holdings` are references to one Armada pool commitment per
  `(asset, channelId)`, never a raw token-unit balance.
-/
import ArmadaLean.Adjudicator.Channel
import ArmadaLean.Adjudicator.Notes

namespace ArmadaLean.Adjudicator

/-- Pointwise function update: `update f a v` agrees with `f` everywhere
    except at `a`, where it is `v`. Lean's `Function.update` lives in
    mathlib, which this repo does not depend on (root `README.md`: "No
    dependencies (no mathlib)"), so `Operations.lean` uses this minimal
    local replacement for every `holdings`/`channels` write. -/
def update {α : Type} [DecidableEq α] {β : Type} (f : α → β) (a : α) (v : β) : α → β :=
  fun x => if x = a then v else f x

/-- The adjudicator's full state: the pool (`Notes.lean`), one
    `ChannelStatus` per channel id (S4 `0040-lifecycle-of-a-channel.md`,
    "Adjudicator storage"), one live collateral commitment per `(asset,
    channelId)` (`holdings`) — THE ARMADA-NITRO RULE, named and cited
    here, and only here: a channel's holding is a NOTE in the pool,
    owned by the adjudicator; it is never a NUMBER the adjudicator
    stores. Lab book decision 9
    (`labbook/2026-10-18-contract-owned-notes-and-zk-channel-apps.md`):
    "The adjudicator owns its channel collateral as notes, so the
    collateral never leaves the pool and there is no public `deposit`
    path, no raw-transfer surplus, and no `sweep`." §3a of the same
    entry states the pool-wide invariant this specializes: "The pool's
    core invariant is that value in the pool exists only as notes:
    every token the pool holds backs exactly one unspent note, and the
    only moves are shield, transact and unshield." `holdings` is
    modeled as `Option Nat`, `none` for no collateral — see
    `heldValue`'s doc comment for how the armada-nitro rule fixes the
    rest of this field's encoding. Every other comment in this model
    that relies on the armada-nitro rule cites it by name, not this
    quote a second time. The
    hub's configured asset list (`ArmadaNitroAdjudicator.configuredAssets`),
    the adjudicator contract's own note-owner identity (`self` — the
    `address(this)` every self-owned `npk` derivation in `Notes.lean`
    reads), the current time (`block.timestamp`, read by `ChannelStatus.
    mode` and advanced by passing calls — `Operations.lean`'s `tick`), and
    `signedBy` — the EOA half of assumption 2 (`Assumptions.lean`'s module
    comment): which `(participant, digest)` pairs this EXECUTION has
    recorded a genuine signature for. Grows only through
    `Operations.lean`'s `.sign` `Call`, whose `Step` case both requires
    the taking `Actor` to BE the named participant and only ever adds to
    that participant's OWN row — "authority comes from the knowledge of
    the corresponding private key" (Nitro-2019-219.pdf §3.1),
    "Forging cryptographic signatures is infeasible" (SATP §1.4). -/
structure AdjudicatorState where
  pool : PoolState
  channels : Nat → ChannelStatus
  holdings : Nat → Nat → Option Nat
  configuredAssets : Nat → Prop
  self : Nat
  now : Nat
  signedBy : Nat → Nat → Prop
  /-- The pool layer's own EOA signing record (the SAME kind of
      execution-tracked fact `signedBy` is for the Nitro layer, above):
      which `(babyjubjubPublicKey, msgHash)` pairs this execution has
      recorded a genuine EdDSA signature for. Grows only through
      `Operations.lean`'s `.signNote` `Call`, which only ever adds to the
      signing key's OWN row. Kept at the ADJUDICATOR level, not inside the
      shared `ArmadaLean.PoolState` (`Pool.lean`): it is this execution's
      own record of who it has seen sign what, not part of the pool
      contract's own storage. -/
  poolSignedBy : (Nat × Nat) → Nat → Prop

/-!
The armada-nitro rule (`AdjudicatorState`'s `holdings` field, above),
applied to a ZERO balance. Nitro-2019-219.pdf §3.1: "We model the
adjudicator as having a simple mapping that stores the quantity of
coins for an address. If an address does not appear in the table we
take the balance to be zero." Under the armada-nitro rule a balance
only exists AS a note — there is no number to read instead — so a
zero balance has no note to point `holdings` at: `holdings asset
channelId = none`, never `some c` for a `c` recorded with value `0`.

This "never value `0`" half is the ADJUDICATOR's OWN invariant over
REACHABLE states, not a pool guarantee: `TransactOwned.circom:117-120`
only range-checks each output value to 120 bits (`Num2Bits(120)`),
with no further constraint, so a `0`-valued output commitment is a
VALID owned-spend output — `ArmadaLean.OwnedConstrained`
(`TransactOwned.lean`) permits it, and the pool will happily mint and
hold such a note. The rule that NO channel's `holdings` entry ever
POINTS AT one is the adjudicator's own rule, kept by every `Step`
case that writes `holdings` (`Safety.lean`'s `holdings_never_zero_
valued` states and grounds this precisely, checking `.deposit`/
`.transfer`/`.reclaim` each keep it).
-/

/-- `heldValue`: `0` for no collateral (`none`, the armada-nitro
    rule's zero-balance case, stated above), else the pool's own
    recorded value for the live commitment — the note's value read
    from the pool's own record, which `ArmadaLean.preimageOf_
    consistent` (`PoolOwned.lean`) proves trustworthy: every preimage
    the pool records hashes to the commitment it is recorded for, so
    no caller can make a commitment read back a value the pool did
    not itself attest. The `match ... | none => 0` branch below is
    where the rule becomes a value-level fact: a caller cannot make
    an empty commitment read as a positive holding, and (over
    REACHABLE states, `holdings_never_zero_valued`) no reachable
    holding's own preimage reads back as a `0`-value note either. -/
def heldValue (s : AdjudicatorState) (asset channelId : Nat) : Nat :=
  match s.holdings asset channelId with
  | none => 0
  | some c => (s.pool.preimageOf c).map CommitmentPreimage.value |>.getD 0

/-- Whether `asset` is on the hub's configured list
    (`ArmadaNitroAdjudicator.isAsset`). Stated as a field of
    `AdjudicatorState` rather than derived from a fixed list, because
    the deployed asset list is itself part of the state a reachability
    argument must track (set once at construction, `Operations.lean`
    never mutates it — `Safety.lean`'s `configuredAssets_invariant`,
    statement 20, states and cites this). -/
abbrev isAsset (s : AdjudicatorState) (asset : Nat) : Prop := s.configuredAssets asset

/-- Assumption 2, combined (`Assumptions.lean`'s module comment): `p`
    authorized `d` iff `p` signed `d` in THIS execution (the EOA path,
    `s.signedBy`, grown only through `Operations.lean`'s `.sign`, whose
    `Step` case requires the ACTOR to be `p` — Nitro-2019-219.pdf §3.1,
    "authority comes from the knowledge of the corresponding private
    key"; SATP §1.4, "Forging cryptographic signatures is infeasible";
    ForceMove-2018.pdf §3.1.3, "From the signature you can deduce the
    signer – the participant who signed the move"), OR `p` is a contract
    whose own code accepts `d` (the EIP-1271 path, `sig.
    contractAuthorizes`, fixed and caller-independent). Matches
    `NitroUtils.isAuthorizedBy`'s own two-branch union
    (`NitroUtils.sol:101-126`). -/
def AuthorizedBy (sig : SignatureAssumptions) (s : AdjudicatorState) (p d : Nat) : Prop :=
  s.signedBy p d ∨ sig.contractAuthorizes p d

/-- `candidate` is signed by every participant of `fp` (used by `conclude`,
    `Operations.lean` — S3 §2.2's `signedByEveryone`; S4
    `0020-execution-rules.md`, `ConsensusApp`, "a state must be
    unanimously countersigned — that is, signed by all of the channel
    participants"). -/
def SignedByAll (sig : SignatureAssumptions) (s : AdjudicatorState)
    (fp : FixedPart) (vp : VariablePart) : Prop :=
  ∀ p ∈ fp.participants, AuthorizedBy sig s p (stateHash fp vp)

/-- The state at deployment: no channel ever touched, no collateral, no
    digest signed yet, the deploy-time asset list and the adjudicator's
    own identity, clock at `0`. A safety statement holds at every state
    reachable from deployment by any sequence of calls by any caller, so
    `genesis` is THE deployment state every reachability claim anchors
    to (`Reachability.lean`'s `Reachable`), not an arbitrary starting
    state a theorem could otherwise leave unconstrained. `assets`/`self`
    stay
    parameters: the deploy-time asset list and the adjudicator's own
    address are themselves constructor arguments
    (`ArmadaNitroAdjudicator`'s constructor), fixed once per deployment.
    `pool` is ALSO a parameter, not empty: the Armada pool (`Notes.lean`)
    is a shared, already-running contract this adjudicator is deployed
    alongside, not created by it — a depositor's note (`DepositStep`,
    `Notes.lean`) must already be live in the pool before this adjudicator
    ever sees a call, so the pool's state at deployment is whatever it
    already was, not `[]`. `signedBy` is NOT a parameter: no Nitro-layer
    digest is signed before the first `.sign` call in the execution:
    signing is an action the execution carries, not a deploy-time
    given. -/
def genesis (assets : Nat → Prop) (self : Nat) (pool : PoolState) : AdjudicatorState where
  pool := pool
  channels := fun _ => emptyStatus
  holdings := fun _ _ => none
  configuredAssets := assets
  self := self
  now := 0
  signedBy := fun _ _ => False
  poolSignedBy := fun _ _ => False

end ArmadaLean.Adjudicator
