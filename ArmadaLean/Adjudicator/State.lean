/-
  ArmadaLean.Adjudicator.State — the adjudicator's full on-chain state.

  Combines `Channel.lean`'s per-channel status (the S1-S4 layer) with
  `Notes.lean`'s pool state (the Armada layer) into one record every
  `Operations.lean` call transitions. Armada layer: N1a brief ("`holdings`
  stop being raw token-unit balances... They become references to one
  Armada pool commitment per `(asset, channelId)`").
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
    channelId)` (`holdings`, N1a brief S1: "Replace `mapping(address =>
    mapping(bytes32 => uint256)) public holdings;` with `mapping(address =>
    mapping(bytes32 => bytes32)) public holdings;`, where the value is the
    live commitment for that asset and channel (`bytes32(0)` means no
    collateral)" — modeled as `Option Nat`, `none` for `bytes32(0)`), the
    hub's configured asset list (`ArmadaNitroAdjudicator.configuredAssets`),
    the adjudicator contract's own note-owner identity (`self` — the
    `address(this)` every self-owned `npk` derivation in `Notes.lean`
    reads), and the current time (`block.timestamp`, read by
    `ChannelStatus.mode` and advanced by passing calls —
    `Operations.lean`'s `tick`). -/
structure AdjudicatorState where
  pool : PoolState
  channels : Nat → ChannelStatus
  holdings : Nat → Nat → Option Nat
  configuredAssets : Nat → Prop
  self : Nat
  now : Nat

/-- `heldValue`: `0` for no collateral, else the pool's own recorded value
    for the live commitment (N1a brief S2: "it returns `0` for an empty
    commitment, else `pool.preimageOf(holdings[asset][channelId]).value`");
    never a cached or caller-asserted amount (N1a husband review: "`
    heldValue` never trusts a value the pool did not attest: it always
    reads `preimageOf`"). The R1 mutant this closes
    (`R1-adjudicator-rewrite.md`, "`heldValue`'s `commitment == 0` check...
    1/17 mutants missed") is the `match ... | none => 0` branch below: a
    caller cannot make an empty commitment read as a positive holding, nor
    can the pool's own `0`-value-commitment prohibition (N1a husband
    review, third bullet) make a REAL note read as empty. -/
def heldValue (s : AdjudicatorState) (asset channelId : Nat) : Nat :=
  match s.holdings asset channelId with
  | none => 0
  | some c => (s.pool.preimageOf c).map NotePreimage.value |>.getD 0

/-- Whether `asset` is on the hub's configured list (`ArmadaNitroAdjudicator
    .isAsset`; the R1 mutant this closes, `R1-adjudicator-rewrite.md`:
    "the constructor's `configuredAssets[...] = true`... 1/3 mutants
    missed"). Stated as a field of `AdjudicatorState` rather than derived
    from a fixed list, because the deployed asset list is itself part of
    the state a reachability argument must track (set once at construction,
    `Operations.lean` never mutates it). -/
abbrev isAsset (s : AdjudicatorState) (asset : Nat) : Prop := s.configuredAssets asset

/-- The state at deployment: no channel ever touched, no collateral, the
    deploy-time asset list and the adjudicator's own identity, clock at
    `0`. Phase 1 brief: "A safety statement holds at every state reachable
    from deployment by any sequence of calls by any caller" — `genesis` is
    THE deployment state every reachability claim anchors to
    (`Reachability.lean`'s `Reachable`), not an arbitrary starting state a
    theorem could otherwise leave unconstrained (coordinator correction,
    this session). `assets`/`self` stay parameters: the deploy-time asset
    list and the adjudicator's own address are themselves constructor
    arguments (`ArmadaNitroAdjudicator`'s constructor), fixed once per
    deployment. `pool` is ALSO a parameter, not empty: the Armada pool
    (`Notes.lean`) is a shared, already-running contract this adjudicator
    is deployed alongside, not created by it — a depositor's note
    (`DepositTransacted`, `Notes.lean`) must already be live in the pool
    before this adjudicator ever sees a call, so the pool's state at
    deployment is whatever it already was, not `[]`. -/
def genesis (assets : Nat → Prop) (self : Nat) (pool : PoolState) : AdjudicatorState where
  pool := pool
  channels := fun _ => emptyStatus
  holdings := fun _ _ => none
  configuredAssets := assets
  self := self
  now := 0

end ArmadaLean.Adjudicator
