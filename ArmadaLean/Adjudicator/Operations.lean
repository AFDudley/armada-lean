/-
  ArmadaLean.Adjudicator.Operations — every call the adjudicator accepts,
  and what it does.

  Each case below cites the S1-S4 source for its MECHANICS (challenge,
  checkpoint, conclude, timeout) and the Armada source for its VALUE
  MOVEMENT (deposit, transfer, reclaim — N1a/N1b/N2a/N2b/N3/R1 briefs, the
  INTENDED design, not the current buggy Solidity; see the departures
  report, `Safety.lean`'s closing section). Nitro-2019-219.pdf §3.3: "There
  is no restriction on who can trigger the operations" — so `Step` below
  carries no caller-identity check beyond what a call's own signed or
  owned data supplies.
-/
import ArmadaLean.Adjudicator.State

namespace ArmadaLean.Adjudicator

/-- Every entry point this model's adjudicator exposes, with the public
    parameters a caller supplies (mirroring each function's own signature,
    quoted at its `Step` case below). `bulkTransferAllAssets` and
    `bulkConcludeAndTransferAllAssets` are included and always fail — see
    their `Step` case — to state N3's "revert" behavior as a positive fact
    about the call, not an omission a reader might mistake for an
    oversight. -/
inductive Call where
  | deposit (channelId expectedHeld asset amount : Nat)
  | challenge (fp : FixedPart) (proof : List VariablePart) (candidate : VariablePart)
      (challenger : Nat)
  | checkpoint (fp : FixedPart) (proof : List VariablePart) (candidate : VariablePart)
  | conclude (fp : FixedPart) (candidate : VariablePart)
  | transfer (assetIndex channelId claimedStateHash : Nat) (outcome : Outcome)
  | reclaim (sourceChannelId : Nat) (sourceOutcome : Outcome)
      (sourceAssetIndex indexOfTargetInSource : Nat) (targetOutcome : Outcome)
      (targetAssetIndex claimedTargetStateHash : Nat)
  | bulkTransferAllAssets (channelId : Nat) (outcome : Outcome) (claimedStateHash : Nat)
  | bulkConcludeAndTransferAllAssets (fp : FixedPart) (candidate : VariablePart)
  | tick (newNow : Nat)

/-- One call's effect: `s` steps to `s'` under `call`. Each case is a
    conjunction of the call's checks (citing its source) and its effect on
    `s'`'s fields, stated as equations rather than a record update so every
    untouched field is named explicitly. -/
def Step (s : AdjudicatorState) : Call → AdjudicatorState → Prop
  /-
  ### `deposit` — N2a brief, intended design

  N2a brief, "Goal": "`depositFromNote` funds a channel by having the
  depositor spend their own note into a fresh contract-owned note at the
  adjudicator, inside the pool, instead of unshielding ERC-20 out to the
  adjudicator's raw balance. The deposited value never leaves the pool (lab
  book decision 9)." S3 (N2a's own check) "Keep the reentrancy guard and
  the `held == expectedHeld` check." DEPARTURE (`departures-found.md` item
  1, "Deposit leaves the pool"): the current `depositFromNote` still
  requires `UnshieldType.NORMAL` and pays real ERC-20 out via
  `TransactModule._transferTokenOut`; this model follows N2a's stated
  intent, not the current code.
  -/
  | .deposit channelId expectedHeld asset amount => fun s' =>
      s.configuredAssets asset ∧
      heldValue s asset channelId = expectedHeld ∧
      ¬ isExternal channelId ∧
      (∃ N M : Nat, ∃ (w : TransactWitness N M) (pub : TransactPublic N M)
          (idx : Fin M),
        DepositPoolStep s.pool s.self asset amount w pub idx s'.pool ∧
        s'.holdings = update s.holdings asset
          (update (s.holdings asset) channelId (some (pub.commitmentsOut idx)))) ∧
      s'.channels = s.channels ∧
      s'.configuredAssets = s.configuredAssets ∧
      s'.self = s.self ∧
      s'.now = s.now
  /-
  ### `challenge` — ForceMove.sol:39-81; S4 `0070-finalizing-a-channel.md`

  "The `challenge` function allows anyone holding the appropriate off-chain
  state(s) to register a challenge state on chain... Once these are
  submitted... an `outcome` is registered against the `channelId`, with a
  finalization time set at some delay after the transaction is processed."
  "Call `challenge`": the challenger "needs to sign...
  `keccak256(abi.encode(challengeStateHash, 'forceMove'))`... This
  mechanism allows the challenge to be authorized only by a channel
  participant." S4 `0040-lifecycle-of-a-channel.md`, "Channel Modes":
  `Open --challenge--> Challenge`, `Challenge --challenge--> Challenge`.
  Turn-number rule: clause 15 ("when Open, the candidate turn must not
  decrease; when already in Challenge, it must strictly increase",
  `ForceMove.sol:48-55`).

  Simplification: the challenger's digest is modeled as `stateHash fp
  candidate` directly, folding in the `'forceMove'` domain-separation
  string the quote names — the string distinguishes a challenge
  authorization from a plain state signature, which this model does not
  need to distinguish because it only ever checks `AuthorizedBy challenger
  (stateHash fp candidate)` for the challenge call, never for both uses
  at once.
  -/
  | .challenge fp proof candidate challenger => fun s' =>
      let cid := channelId fp
      (match (s.channels cid).mode s.now with
        | .open => candidate.turnNum ≥ (s.channels cid).turnNumRecord
        | .challenge => candidate.turnNum > (s.channels cid).turnNumRecord
        | .finalized => False) ∧
      AppSupports fp proof candidate ∧
      challenger ∈ fp.participants ∧
      AuthorizedBy challenger (stateHash fp candidate) ∧
      s'.channels = update s.channels cid
        { turnNumRecord := candidate.turnNum
          finalizesAt := s.now + fp.challengeDuration
          stateHash := stateHash fp candidate
          outcomeHash := outcomeHashOf candidate.outcome } ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now
  /-
  ### `checkpoint` — ForceMove.sol:90-119; S4 `0070-finalizing-a-channel.md`

  "The `checkpoint` method allows anyone with a supported off-chain state
  to establish a new and higher `turnNumRecord` on chain, and leave the
  resulting channel in the 'Open' mode. It can be used to clear a
  challenge." S4 `0040-lifecycle-of-a-channel.md`: `Open
  --checkpoint--> Open`, `Challenge --checkpoint--> Open`. The stored
  `stateHash`/`outcomeHash` are cleared to the zero value
  (`ForceMove.sol:109-111`, `ChannelData(candidateTurnNum, 0, bytes32(0),
  bytes32(0))`): checkpoint records only that a higher turn number is now
  known, not a finalizable outcome — `transfer`/`reclaim` require a
  `.finalized` channel, so the cleared hashes are never read as a payout
  outcome.
  -/
  | .checkpoint fp proof candidate => fun s' =>
      let cid := channelId fp
      (s.channels cid).mode s.now ≠ .finalized ∧
      candidate.turnNum > (s.channels cid).turnNumRecord ∧
      AppSupports fp proof candidate ∧
      s'.channels = update s.channels cid
        { turnNumRecord := candidate.turnNum, finalizesAt := 0, stateHash := 0, outcomeHash := 0 } ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now
  /-
  ### `conclude` — ForceMove.sol:127-170; S4 `0070-finalizing-a-channel.md`

  "A participant wishing to end the state channel will sign a state with
  `isFinal = true`. Then, the other participants may support that state.
  Once a full set of `n` such signatures exists (a 'finalization proof')
  the channel is said to be 'closed' or 'finalized'... anyone in possession
  of a finalization proof may use it to finalize the `outcome` on-chain...
  by calling `conclude`." The stored `stateHash` is ALSO cleared to zero on
  conclude (`ForceMove.sol:160-167`, `ChannelData(0, uint48(block.
  timestamp), bytes32(0), NitroUtils.hashOutcome(...))`): only `
  outcomeHash` survives. N3 brief + R1 brief, "Behavior (unchanged)":
  "`conclude` finalizes without moving value" — this `Step` case touches
  only `s'.channels`; `s'.pool` and `s'.holdings` are UNCHANGED, matching
  N3's wording exactly. A caller who wants a payout calls `transfer`
  separately afterward (N3 brief S1).
  -/
  | .conclude fp candidate => fun s' =>
      let cid := channelId fp
      (s.channels cid).mode s.now ≠ .finalized ∧
      candidate.isFinal = true ∧
      SignedByAll fp candidate ∧
      s'.channels = update s.channels cid
        { turnNumRecord := 0, finalizesAt := s.now, stateHash := 0
          outcomeHash := outcomeHashOf candidate.outcome } ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now
  /-
  ### `transfer` — MultiAssetHolder.sol:59-109,135-191 (trusted, vendored
  `src/nitro`), settled via N1b/N2b's owned-spend (Armada layer)

  S2 §5.1, "Allocations and Transfer": priority-order payout, `afford`
  (`Outcome.lean`). Clause 24: `transfer(assetIndex, fromChannelId,
  outcomeBytes, stateHash, indices)`. Clause 25: "`transfer` must refuse a
  guarantee allocation" (`MultiAssetHolder.sol:169-170`, `revert 'cannot
  transfer a guarantee'`). N1b brief S1/S2: the exit becomes one `
  transactOwned` spend — nullify the channel's old collateral commitment,
  mint one fresh owned note per non-zero payout (npk = the allocation's own
  destination, N2b: "the recipient's own note key, not contract-owned"),
  plus a remainder note owned by `self` when the payout is partial. N2b
  brief, "Goal": "There is no protocol fee on a payout... a payout is a
  plain output, with no fee tag and no `cumulativeFees` coupling" — no fee
  field appears anywhere in this case, which is the Lean statement of "no
  fee".

  Simplification: this model pays the FULL allocation list in priority
  order (the `indices == []`, "pay out to all" case,
  `MultiAssetHolder.sol:149`), not an arbitrary caller-chosen subset —
  the general `indices` feature is established by clause 24 and not
  re-derived bit-for-bit here, since the safety theorems this phase states
  do not depend on which subset a caller names.
  -/
  | .transfer assetIndex cid claimedStateHash outcome => fun s' =>
      ∃ h : assetIndex < outcome.length,
      let assetOutcome := outcome.get ⟨assetIndex, h⟩
      (s.channels cid).mode s.now = .finalized ∧
      (s.channels cid).stateHash = claimedStateHash ∧
      (s.channels cid).outcomeHash = outcomeHashOf outcome ∧
      (∀ a ∈ assetOutcome.allocations, a.allocationType ≠ .guarantee) ∧
      (let paid := afford assetOutcome.allocations (heldValue s assetOutcome.asset cid)
       let remainder := heldValue s assetOutcome.asset cid - listSum paid
       let payouts := (assetOutcome.allocations.zip paid).filterMap
         (fun (a, amt) => if amt = 0 then none
           else some (⟨a.destination, assetOutcome.asset, amt⟩ : NotePreimage))
       let outputs := payouts ++
         (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : NotePreimage)])
       PoolOwnedSpendStep s.pool s.self assetOutcome.asset (s.holdings assetOutcome.asset cid)
         outputs s'.pool ∧
       s'.holdings = update s.holdings assetOutcome.asset
         (update (s.holdings assetOutcome.asset) cid
           (if remainder = 0 then none
            else some (commitment s.self assetOutcome.asset remainder))) ∧
       s'.channels = update s.channels cid
         { s.channels cid with
           outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
             if i ≠ assetIndex then exit
             else { exit with
               allocations := (exit.allocations.zip paid).map
                 fun (a, amt) => { a with amount := a.amount - amt } }) }) ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now
  /-
  ### `reclaim` — MultiAssetHolder.sol:237-390 (trusted, vendored
  `src/nitro`); S3 §2.4 Listing 2; clause 28

  S3 §2.4, Listing 2, "Reclaim": "`o_target = statusOf(targetChannelId).
  outcome; o_ledger[left] += o_target[0]; o_ledger[right] += o_target[1];
  delete statusOf(ledgerChannelId).outcome[targetChannelId]`." Guarantees
  are not pool commitments — they are a bookkeeping entry inside the
  SOURCE channel's own outcome, reprioritizing value already backed by the
  source's own collateral note (S4 `0030-outcomes.md`, "Guarantees": funds
  "may be moved to another channel on chain using the `reclaim` method").
  The base `MultiAssetHolder._settleReclaimExit` is correspondingly a no-op
  (`MultiAssetHolder.sol:419-431`'s doc comment: "go-nitro's target channel
  already settled independently of the guarantee, so there is no raw
  balance to credit here"). This `Step` case therefore touches only
  `s'.channels` — `s'.pool` and `s'.holdings` are UNCHANGED. DEPARTURE
  (`departures-found.md` item 2, "Reclaim creates value"): the current
  `ArmadaNitroAdjudicator._settleReclaimExit` instead mints a brand-new
  commitment worth `priorHeld + guaranteeAmount` to the target with
  nothing debited anywhere, which this model does not follow.
  -/
  | .reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource
      targetOutcome targetAssetIndex claimedTargetStateHash => fun s' =>
      (s.channels sourceChannelId).mode s.now = .finalized ∧
      (s.channels sourceChannelId).outcomeHash = outcomeHashOf sourceOutcome ∧
      ∃ hsa : sourceAssetIndex < sourceOutcome.length,
      ∃ hidx : indexOfTargetInSource < (sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.length,
      let guarantee := (sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get ⟨indexOfTargetInSource, hidx⟩
      guarantee.allocationType = .guarantee ∧
      (let (left, right) := decodeGuarantee guarantee.metadata
       let targetChannelId := guarantee.destination
       (s.channels targetChannelId).mode s.now = .finalized ∧
       (s.channels targetChannelId).stateHash = claimedTargetStateHash ∧
       (s.channels targetChannelId).outcomeHash = outcomeHashOf targetOutcome ∧
       ∃ hta : targetAssetIndex < targetOutcome.length,
       (targetOutcome.get ⟨targetAssetIndex, hta⟩).asset = (sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).asset ∧
       ∃ a0 a1 : Nat,
         (targetOutcome.get ⟨targetAssetIndex, hta⟩).allocations.length ≥ 2 ∧
         a0 = ((targetOutcome.get ⟨targetAssetIndex, hta⟩).allocations.getD 0 Allocation.default).amount ∧
         a1 = ((targetOutcome.get ⟨targetAssetIndex, hta⟩).allocations.getD 1 Allocation.default).amount ∧
         a0 + a1 = guarantee.amount ∧
         s'.channels = update s.channels sourceChannelId
           { s.channels sourceChannelId with
             outcomeHash := outcomeHashOf
               (reallocateGuarantee sourceOutcome sourceAssetIndex indexOfTargetInSource left right a0 a1) }) ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now
  /-
  ### `bulkTransferAllAssets`, `bulkConcludeAndTransferAllAssets` — N3
  brief, "revert"

  N3 brief S2: "Override `transferAllAssets` in `ArmadaNitroAdjudicator` to
  `revert('Use transfer(assetIndex, ...)')`." N3/R1, "Behavior (unchanged)":
  "`transferAllAssets` and `concludeAndTransferAllAssets` revert with a
  use-`transfer` message instead of running the inherited bulk path."
  DEPARTURE (`departures-found.md` item 5, "N3 absent"): the current
  `ArmadaNitroAdjudicator.sol` has NO such override — `transferAllAssets`
  and `concludeAndTransferAllAssets` are inherited unchanged and run the
  base `_transferAllAssetsBody`, which subtracts from a `bytes32`
  commitment as if it were a raw `uint256` AND mints brand-new owned
  commitments via `PoolSpend.mintPayoutCommitmentsNoChannel` with no
  nullifier at all — pure value creation with no debit anywhere. This
  model does not give these two calls any way to succeed, matching the
  INTENDED N3 design, not the current code.
  -/
  | .bulkTransferAllAssets _ _ _ => fun _ => False
  | .bulkConcludeAndTransferAllAssets _ _ => fun _ => False
  /-
  ### `tick` — the passive timeout transition

  ForceMove-2018.pdf §4.1: "the game transitions into the Terminated mode"
  when "no response is received within the timeout period" — no call is
  needed. S4 `0040-lifecycle-of-a-channel.md`: "The remaining transition
  `timeout` is a passive transition which happens when a block is produced
  with a sufficiently large timestamp." `tick` advances `now`
  monotonically and changes nothing else; `ChannelStatus.mode` then reads
  `Finalized` once `finalizesAt ≤ now`, with no separate "apply timeout"
  step — matching the quote.
  -/
  | .tick newNow => fun s' =>
      newNow ≥ s.now ∧
      s'.now = newNow ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧ s'.channels = s.channels ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self

end ArmadaLean.Adjudicator
