/-
  ArmadaLean.Adjudicator.State — the adjudicator's full on-chain state.

  Combines `Channel.lean`'s per-channel status (the S1-S4 layer) with
  `Notes.lean`'s pool state (the Armada layer) into one record every
  `Operations.lean` call transitions. Armada layer, lab book decision 9:
  "The adjudicator owns its channel collateral as notes" — `holdings`
  are references to one Armada pool commitment per `(asset, channelId)`,
  never a raw token-unit balance.
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
    channelId)` (`holdings` — lab book decision 9, "the adjudicator owns
    its channel collateral as notes": the field holds a live commitment,
    not a raw token amount — modeled as `Option Nat`, `none` for no
    collateral; see `heldValue`'s doc comment for the full encoding
    rule), the
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

/-!
Armada encoding rule (stated once here; `Safety.lean`'s statements 19
("`heldValue_zero_iff_no_collateral`"), 21 ("`zero_payout_mints_
nothing`") and 22 ("`full_payout_leaves_no_remainder`") cite it by
name, not a second time). Nitro-2019-219.pdf §3.1: "We model the
adjudicator as having a simple mapping that stores the quantity of
coins for an address. If an address does not appear in the table we
take the balance to be zero." This model's note-backed balance
specializes that rule: A BALANCE IS HELD AS ONE NOTE, AND A ZERO
BALANCE IS HELD AS NO NOTE. A positive balance is exactly one live
commitment (`holdings asset channelId = some c`, `s.pool.isLive c`); a
zero balance is no commitment at all (`holdings asset channelId =
none`), never a commitment recorded with value `0` — the pool itself
enforces this half (it never mints a `0`-value commitment, N1a husband
review's third bullet, armada-nitro@5519526c:docs/tasks/
N1a-multiassetholder-commitment-storage.md, the only source recording
this specific pool-level guarantee). No paper covers a note-backed
balance representation at all; this is Armada's own encoding, with no
dedicated lab book section.
-/

/-- `heldValue`: `0` for no collateral (`none`, the Armada encoding
    rule's "zero balance is held as no note" half, stated above), else
    the pool's own recorded value for the live commitment — never a
    cached or caller-asserted amount (lab book decision 11: the
    adjudicator reads only what the pool itself attests through
    `preimageOf`). The `match ... | none => 0` branch below is where
    the encoding rule becomes a value-level fact: a caller cannot make
    an empty commitment read as a positive holding, nor can the pool's
    own `0`-value-commitment prohibition make a REAL note read as
    empty. -/
def heldValue (s : AdjudicatorState) (asset channelId : Nat) : Nat :=
  match s.holdings asset channelId with
  | none => 0
  | some c => (s.pool.preimageOf c).map NotePreimage.value |>.getD 0

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
    own identity, clock at `0`. Phase 1 brief: "A safety statement holds
    at every state reachable from deployment by any sequence of calls by
    any caller" — `genesis` is THE deployment state every reachability
    claim anchors to (`Reachability.lean`'s `Reachable`), not an arbitrary
    starting state a theorem could otherwise leave unconstrained
    (coordinator correction, prior session). `assets`/`self` stay
    parameters: the deploy-time asset list and the adjudicator's own
    address are themselves constructor arguments
    (`ArmadaNitroAdjudicator`'s constructor), fixed once per deployment.
    `pool` is ALSO a parameter, not empty: the Armada pool (`Notes.lean`)
    is a shared, already-running contract this adjudicator is deployed
    alongside, not created by it — a depositor's note (`DepositTransacted`,
    `Notes.lean`) must already be live in the pool before this adjudicator
    ever sees a call, so the pool's state at deployment is whatever it
    already was, not `[]`. `signedBy` is NOT a parameter: no Nitro-layer
    digest is signed before the first `.sign` call in the execution
    (coordinator correction, this session: signing is an action the
    execution carries, not a deploy-time given). -/
def genesis (assets : Nat → Prop) (self : Nat) (pool : PoolState) : AdjudicatorState where
  pool := pool
  channels := fun _ => emptyStatus
  holdings := fun _ _ => none
  configuredAssets := assets
  self := self
  now := 0
  signedBy := fun _ _ => False

end ArmadaLean.Adjudicator
