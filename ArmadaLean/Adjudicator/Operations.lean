/-
  ArmadaLean.Adjudicator.Operations — every call the adjudicator accepts,
  and what it does.

  Each case below cites the S1-S4 source for its MECHANICS (challenge,
  checkpoint, conclude, timeout) and the Armada source for its VALUE
  MOVEMENT (deposit, transfer, reclaim — N1a/N1b/N2a/N2b/N3/R1 briefs, the
  INTENDED design, not the current buggy Solidity; see the departures
  report, `Safety.lean`'s closing section). Nitro-2019-219.pdf §3.3: "There
  is no restriction on who can trigger the operations" — so `Step` places
  no restriction on `actor` for any call EXCEPT `.sign`/`.signNote`, whose
  own effect IS the fact that only a key's holder can produce (`Actor`
  below, `Assumptions.lean`'s module comment).

  `Step` takes `SignatureAssumptions` and `ProofAssumptions`
  (`Assumptions.lean`, `Notes.lean`) as explicit arguments, because
  `.challenge`/`.conclude` need to ask whether a digest was authorized and
  `.deposit`/`.transfer` need to ask whether an owned proof was accepted —
  both are explicit structure arguments, never a bare global axiom
  (coordinator correction, prior session). `appRel` is the application
  rule (`Channel.lean`'s module comment on `.challenge`/`.checkpoint`): a
  PARAMETER of the model, like `sig`/`proofA`, not a bare global axiom —
  `Safety.lean`'s safety theorems quantify it for any app; its can-happen
  theorems use the real `ConsensusApp`'s own relation in its place
  (`Safety.lean`'s "concrete app" section). Two `Call`s, `.sign` and
  `.signNote`, are how an EOA participant's half of assumption 2 enters
  the execution: `actor` names who is really taking the step — the
  identity `ecrecover`/the pool's own witness check would recover, not a
  caller-asserted claim — and `.sign p d`/`.signNote pk msgHash` succeed
  only when `actor` IS the key holder the step names. Every OTHER case
  places no constraint on `actor` and leaves `s'.signedBy = s.signedBy`,
  so only `.sign` ever grows it, and only when its own actor check passes.
-/
import ArmadaLean.Adjudicator.State

namespace ArmadaLean.Adjudicator

/-- Who actually produced this step's authorization — the identity
    `ecrecover` (Nitro layer) or the pool's own EdDSA check (pool layer)
    would recover from a genuine signature, not a caller-asserted claim.
    Two spaces, because this model spans two signature primitives
    (`Assumptions.lean`'s module comment: "the Nitro layer hashes with
    keccak256 and signs with ECDSA/EIP-1271... the pool's
    Poseidon/EdDSA"): a Nitro-layer address, or a pool-layer babyjubjub
    public key. Every `Step` case below takes an `actor`; only `.sign`
    and `.signNote` constrain it. -/
inductive Actor where
  | nitro (p : Nat)
  | pool (pk : Nat × Nat)
  deriving DecidableEq

/-- Every entry point this model's adjudicator exposes, with the public
    parameters a caller supplies (mirroring each function's own signature,
    quoted at its `Step` case below). `bulkTransferAllAssets` and
    `bulkConcludeAndTransferAllAssets` are included and always fail — see
    their `Step` case — to state N3's "revert" behavior as a positive fact
    about the call, not an omission a reader might mistake for an
    oversight. `transfer` carries `indices` (clause 24: `transfer(
    assetIndex, fromChannelId, outcomeBytes, stateHash, indices)`), since a
    caller chooses which destinations to pay out now. `sign`/`signNote`
    are not go-nitro/Armada entry points — they name the off-chain act of
    producing a signature (`Step`'s `actor` parameter is how this model
    restricts who may take them; see the module comment). -/
inductive Call where
  | deposit (channelId expectedHeld asset amount : Nat)
  | challenge (fp : FixedPart) (proof : List VariablePart) (candidate : VariablePart)
      (challenger : Nat)
  | checkpoint (fp : FixedPart) (proof : List VariablePart) (candidate : VariablePart)
  | conclude (fp : FixedPart) (candidate : VariablePart)
  | transfer (assetIndex channelId claimedStateHash : Nat) (outcome : Outcome)
      (indices : List Nat)
  | reclaim (sourceChannelId : Nat) (sourceOutcome : Outcome)
      (sourceAssetIndex indexOfTargetInSource : Nat) (targetOutcome : Outcome)
      (targetAssetIndex claimedTargetStateHash : Nat)
  | bulkTransferAllAssets (channelId : Nat) (outcome : Outcome) (claimedStateHash : Nat)
  | bulkConcludeAndTransferAllAssets (fp : FixedPart) (candidate : VariablePart)
  | tick (newNow : Nat)
  | sign (p d : Nat)
  | signNote (pk : Nat × Nat) (msgHash : Nat)

/-- One call's effect: `s` steps to `s'` under `call`, taken by `actor`,
    given the signature and proof assumptions (`sig`, `proofA`) and the
    application rule (`appRel`) the call's checks may need. Each case is
    a conjunction of the call's checks (citing its source) and its effect
    on `s'`'s fields, stated as equations rather than a record update so
    every untouched field is named explicitly. -/
def Step (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s : AdjudicatorState) : Call → AdjudicatorState → Prop
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
  intent, not the current code. Deposit is authorized by the depositor's
  own EdDSA signature on the spent note (the pool layer's `EdDSAVerify`,
  reused via `Constrained`/`DepositTransacted`, `Notes.lean`), not by
  `sig`/`proofA`/`actor`, so this case does not use any of the three.
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
      s'.now = s.now ∧
      s'.signedBy = s.signedBy
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
  `ForceMove.sol:48-55`). `actor` is unconstrained: the challenger's own
  authorization is `AuthorizedBy sig s challenger ...` below, which only a
  prior `.sign challenger ...` step by `challenger` themselves could have
  established — `actor` here is whoever submits the transaction, which
  ForceMove-2018.pdf §2.2's worked example already allows to be anyone
  holding the signature bytes ("Bob ... provides both the last state
  signed by Alice and the last state he signed").

  Simplification: the challenger's digest is modeled as `stateHash fp
  candidate` directly, folding in the `'forceMove'` domain-separation
  string the quote names — the string distinguishes a challenge
  authorization from a plain state signature, which this model does not
  need to distinguish because it only ever checks `AuthorizedBy sig s
  challenger (stateHash fp candidate)` for the challenge call, never for
  both uses at once.
  -/
  | .challenge fp proof candidate challenger => fun s' =>
      let cid := channelId fp
      (match (s.channels cid).mode s.now with
        | .open => candidate.turnNum ≥ (s.channels cid).turnNumRecord
        | .challenge => candidate.turnNum > (s.channels cid).turnNumRecord
        | .finalized => False) ∧
      appRel s fp proof candidate ∧
      challenger ∈ fp.participants ∧
      AuthorizedBy sig s challenger (stateHash fp candidate) ∧
      s'.channels = update s.channels cid
        { turnNumRecord := candidate.turnNum
          finalizesAt := s.now + fp.challengeDuration
          stateHash := stateHash fp candidate
          outcomeHash := outcomeHashOf candidate.outcome } ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now ∧
      s'.signedBy = s.signedBy
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
  outcome. No signature or proof check beyond `appRel`, so this case does
  not use `sig`/`proofA`, and `actor` is unconstrained ("anyone with a
  supported off-chain state", quoted above).
  -/
  | .checkpoint fp proof candidate => fun s' =>
      let cid := channelId fp
      (s.channels cid).mode s.now ≠ .finalized ∧
      candidate.turnNum > (s.channels cid).turnNumRecord ∧
      appRel s fp proof candidate ∧
      s'.channels = update s.channels cid
        { turnNumRecord := candidate.turnNum, finalizesAt := 0, stateHash := 0, outcomeHash := 0 } ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now ∧
      s'.signedBy = s.signedBy
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
  separately afterward (N3 brief S1). `actor` is unconstrained ("anyone in
  possession of a finalization proof", quoted above); `SignedByAll`
  requires every participant's OWN prior `.sign` step, which `actor` here
  cannot substitute for.
  -/
  | .conclude fp candidate => fun s' =>
      let cid := channelId fp
      (s.channels cid).mode s.now ≠ .finalized ∧
      candidate.isFinal = true ∧
      SignedByAll sig s fp candidate ∧
      s'.channels = update s.channels cid
        { turnNumRecord := 0, finalizesAt := s.now, stateHash := 0
          outcomeHash := outcomeHashOf candidate.outcome } ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now ∧
      s'.signedBy = s.signedBy
  /-
  ### `transfer` — MultiAssetHolder.sol:135-191 (trusted, vendored
  `src/nitro`), settled via N1b/N2b's owned-spend (Armada layer)

  S2 §5.1, "Allocations and Transfer": priority-order payout, `afford`
  (`Outcome.lean`). Clause 24: `transfer(assetIndex, fromChannelId,
  outcomeBytes, stateHash, indices)`. `_requireIncreasingIndices`
  (`:528-535`): indices strictly increasing. `compute_transfer_effects_
  and_interactions` (`:135-191`, `Outcome.lean`'s `transferEffects`):
  surplus is consumed in priority order for every allocation, but only a
  SELECTED index (`indices`, or all when `indices = []`) is paid now and
  has its recorded amount reduced. Clause 25: "`transfer` must refuse a
  guarantee allocation" (`MultiAssetHolder.sol:169-170`, `revert 'cannot
  transfer a guarantee'`) — checked only for SELECTED allocations, matching
  the code (the `revert` sits inside the `if (selected)` branch,
  `:168-171`). N1b brief S1/S2: the exit becomes one `transactOwned` spend
  — nullify the channel's old collateral commitment, mint one fresh owned
  note per non-zero SELECTED payout (npk = the allocation's own
  destination, N2b: "the recipient's own note key, not contract-owned"),
  plus a remainder note owned by `self` for whatever is left of
  `heldValue` after the selected payouts (`:228`, `holdings[asset][
  channelId] = ... - totalPayouts`, where `totalPayouts` sums only the
  selected amounts). N2b brief, "Goal": "There is no protocol fee on a
  payout... a payout is a plain output, with no fee tag and no
  `cumulativeFees` coupling" — no fee field appears anywhere in this case,
  which is the Lean statement of "no fee".
  -/
  | .transfer assetIndex cid claimedStateHash outcome indices => fun s' =>
      ∃ h : assetIndex < outcome.length,
      let assetOutcome := outcome.get ⟨assetIndex, h⟩
      (s.channels cid).mode s.now = .finalized ∧
      (s.channels cid).stateHash = claimedStateHash ∧
      (s.channels cid).outcomeHash = outcomeHashOf outcome ∧
      StrictlyIncreasing indices ∧
      (let (newAllocs, exitAllocs, totalPayouts) :=
         transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices
       (∀ a ∈ exitAllocs, a.allocationType ≠ .guarantee) ∧
       (let remainder := heldValue s assetOutcome.asset cid - totalPayouts
        let payoutOutputs := exitAllocs.filterMap (fun a =>
          if a.amount = 0 then none
          else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : NotePreimage))
        let outputs := payoutOutputs ++
          (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : NotePreimage)])
        PoolOwnedSpendStep proofA s.pool s.self assetOutcome.asset
          (s.holdings assetOutcome.asset cid) outputs s'.pool ∧
        s'.holdings = update s.holdings assetOutcome.asset
          (update (s.holdings assetOutcome.asset) cid
            (if remainder = 0 then none
             else some (commitment s.self assetOutcome.asset remainder))) ∧
        s'.channels = update s.channels cid
          { s.channels cid with
            outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
              if i ≠ assetIndex then exit else { exit with allocations := newAllocs }) })) ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now ∧
      s'.signedBy = s.signedBy
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
  nothing debited anywhere, which this model does not follow. No
  signature or proof check, so this case does not use `sig`/`proofA`, and
  `actor` is unconstrained (clause 28 names no caller restriction).
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
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now ∧
      s'.signedBy = s.signedBy
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
  step — matching the quote. `actor` is unconstrained: advancing the clock
  is not an authorization act.
  -/
  | .tick newNow => fun s' =>
      newNow ≥ s.now ∧
      s'.now = newNow ∧
      s'.pool = s.pool ∧ s'.holdings = s.holdings ∧ s'.channels = s.channels ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧
      s'.signedBy = s.signedBy
  /-
  ### `sign` — the EOA half of assumption 2 (`Assumptions.lean`'s module
  comment)

  Not a go-nitro or Armada entry point: it names the off-chain act of a
  participant producing a signature. Nitro-2019-219.pdf §3.1: "Given an
  address, A, we assume that the properties of the signature scheme and
  hashing algorithm make it impossible to find a private key for A... if
  they are not previously known"; the withdrawal operation "can be used
  to withdraw coins held at participant address, A, by any party with the
  knowledge of the corresponding private key" — authority comes from
  HOLDING the key, which is exactly what `actor = .nitro p` requires
  below. ForceMove-2018.pdf §3.1.3: "A move consists of a State and a
  (cryptographic) signature... From the signature you can deduce the
  signer – the participant who signed the move." This `Step` case is
  where that deduction is made STRUCTURAL: it succeeds only when `actor`
  IS `p`, and its effect only ever adds `d` to `p`'s OWN row — no `Call`
  exists, and no value of `actor`, that adds a digest to a DIFFERENT
  participant's row.
  -/
  | .sign p d => fun s' =>
      actor = .nitro p ∧
      s'.signedBy = (fun p' d' => (p' = p ∧ d' = d) ∨ s.signedBy p' d') ∧
      s'.pool = s.pool ∧ s'.channels = s.channels ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now
  /-
  ### `signNote` — the pool layer's own EdDSA signing action
  (`Notes.lean`'s `PoolSignatureLiveness`)

  The exact same idea as `.sign`, for the root pool layer's EdDSA check
  `Constrained.sig` relies on (`Transact.lean:119`): names the off-chain
  act of the holder of babyjubjub key `pk` signing `msgHash`. SATP §1.4,
  "Our contribution": "(Safety) Forging cryptographic signatures is
  infeasible" — applies to BOTH signature schemes this model spans, not
  only the Nitro layer's ECDSA. Succeeds only when `actor` IS the holder
  of `pk`, and only ever adds `(pk, msgHash)` to `pk`'s OWN row of
  `PoolState.poolSignedBy`.
  -/
  | .signNote pk msgHash => fun s' =>
      actor = .pool pk ∧
      s'.pool.poolSignedBy = (fun pk' m' => (pk' = pk ∧ m' = msgHash) ∨ s.pool.poolSignedBy pk' m') ∧
      s'.pool.liveNotes = s.pool.liveNotes ∧ s'.pool.usedNullifiers = s.pool.usedNullifiers ∧
      s'.channels = s.channels ∧ s'.holdings = s.holdings ∧
      s'.configuredAssets = s.configuredAssets ∧ s'.self = s.self ∧ s'.now = s.now ∧
      s'.signedBy = s.signedBy

end ArmadaLean.Adjudicator
