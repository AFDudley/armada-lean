/-
  ArmadaLean.Adjudicator.Safety — the theorem STATEMENTS stage A asks for.
  Every proof is `sorry`; the operator reviews the statements before any
  proof work starts (Phase 1 brief, "What to produce now (stage A)").

  Phase 1 brief, "Why this model exists": the adjudicator holds other
  people's money, so this model must show three things: (1) no caller can
  take money they are not owed; (2) no caller can stop someone from
  getting money they are owed; (3) no caller can create or destroy value in
  the pool. Every theorem below is grounded in one of these three, stated
  over the REACHABLE set (`Reachability.lean`), never over one step from a
  chosen state, per the brief: "A safety statement holds at every state
  reachable from deployment by any sequence of calls by any caller."

  Operator addition (coordinator message, prior session): "every
  finalizable outcome is paid out as notes, with no fee, with pool value
  conserved; and no caller can make the adjudicator pay an outcome that is
  not finalizable", using Nitro-2019-219.pdf §4.4's own definitions of
  "finalizable" and "enabled" outcome, not an invented rule. Sections A and
  B below are the two halves of that sentence.

  Every theorem that reasons about a call sequence takes
  `SignatureAssumptions` and `ProofAssumptions` (`Assumptions.lean`,
  `Notes.lean`) as explicit arguments — `Step`/`AppliesAll`/`Reachable` are
  themselves parameterized by them, so a reader sees on the theorem's own
  type which cryptographic facts it relies on, never a hidden global axiom
  (coordinator correction, prior session). Every theorem that reasons
  about the reachable set takes the deploy-time asset list (`assets`), the
  adjudicator's own identity (`self`), and the pool's state at deployment
  (`pool0`) as explicit arguments and anchors `Reachable` at `genesis
  assets self pool0` (`State.lean`) — the one true deployment state, not
  an arbitrary unconstrained starting state (same correction).

  Signing is now an ACTION, not a bare relation (coordinator correction,
  this session): `AuthorizedBy sig s p d` (`State.lean`) and `SignedByAll
  sig s fp vp` take the CURRENT state `s`, so they read the digests `s`'s
  execution has actually recorded as signed, through `AdjudicatorState.
  signedBy` (grown only by `Operations.lean`'s `.sign`, in the signer's
  own row). Signing is monotone (`.sign` only ever adds, never removes a
  recorded digest), so a fact `SignedByAll sig s fp vp` established at
  some point in an execution survives to every LATER reachable state too —
  the safety theorems below state it at the theorem's own `s`, the current
  or final state, with no loss of generality.
-/
import ArmadaLean.Adjudicator.Reachability

namespace ArmadaLean.Adjudicator

/-- A channel is finalized, right now, with exactly this `stateHash`/
    `outcomeHash` pair (S4 `0040-lifecycle-of-a-channel.md`, "Channel
    Modes"). A convenience predicate so the theorems below read as
    statements about the protocol's own storage fields, not about
    `ChannelStatus`'s internal shape. -/
def ChannelFinalizedWith (s : AdjudicatorState) (cid stateH outcomeH : Nat) : Prop :=
  (s.channels cid).mode s.now = .finalized ∧
  (s.channels cid).stateHash = stateH ∧ (s.channels cid).outcomeHash = outcomeH

/-!
## A. No caller can take money they are not owed

Nitro-2019-219.pdf §4.4: "we say an outcome, ω, is finalizable for
participant A, if A has an unbeatable strategy for finalizing this outcome
in the adjudicator"; a channel is finalized "(i) through a challenge that
times out before anyone responds, and (ii) through the registration of a
conclusion proof" (§3.2, Figure 4). `finalized_outcome_was_concluded_or_
challenged` is the converse fact "no caller can take money they are not
owed" needs: a payout always traces back to one of those two
protocol-recognized paths, never to a bare caller assertion.
-/

/-- Which harm this rules out: a caller cannot invent a finalized outcome
    out of thin air and have `transfer` pay it out. Formalizes
    Nitro-2019-219.pdf §3.2's "two ways for an outcome to be finalized" as
    the ONLY ways a reachable state can show a channel finalized with a
    given `(stateHash, outcomeHash)` pair. Simplification: this statement
    names the call that PRODUCED the finalized status (`conclude` with
    `SignedByAll`, or `challenge` with `AppSupports`+`AuthorizedBy`) but
    does not additionally require that no later, higher-turn challenge or
    checkpoint overwrote it before the timeout — that refinement belongs to
    the proof stage, not to this statement. -/
theorem finalized_outcome_was_concluded_or_challenged
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (cid stateH outcomeH : Nat)
    (hreach : Reachable sig proofA (genesis assets self pool0) s)
    (hfin : ChannelFinalizedWith s cid stateH outcomeH) :
    (∃ fp candidate, channelId fp = cid ∧ SignedByAll sig s fp candidate ∧
      outcomeHashOf candidate.outcome = outcomeH) ∨
    (∃ fp proof candidate challenger, channelId fp = cid ∧
      AppSupports fp proof candidate ∧ challenger ∈ fp.participants ∧
      AuthorizedBy sig s challenger (stateHash fp candidate) ∧
      stateHash fp candidate = stateH ∧
      outcomeHashOf candidate.outcome = outcomeH) := by
  sorry

/-- Which harm this rules out: a caller cannot name an `outcome`/`indices`
    to `transfer` that pays a destination the finalized outcome did not
    name, or more than the finalized outcome allocated. This is `Step`'s
    `transfer` case made explicit as a theorem: the `outcome`/
    `claimedStateHash` a `transfer` call supplies must already equal the
    channel's stored `(stateHash, outcomeHash)` (`Operations.lean`'s
    `.transfer` case, mirroring `MultiAssetHolder._requireMatchingFingerprint`,
    `MultiAssetHolder.sol:506-516`), and every allocation this call actually
    pays now (`transferEffects`'s `exitAllocations`, clause 24,
    `MultiAssetHolder.sol:135-191`) shares its destination with, and is paid
    no more than, some allocation already recorded in that outcome. -/
theorem transfer_pays_only_the_finalized_outcome
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig proofA s (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    ChannelFinalizedWith s cid claimedStateHash (outcomeHashOf outcome) ∧
    ∀ paid ∈ (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.1,
      ∃ original ∈ (outcome.get ⟨assetIndex, h⟩).allocations,
        paid.destination = original.destination ∧ paid.amount ≤ original.amount := by
  sorry

/-!
## B. No caller can stop someone from getting money they are owed

Nitro-2019-219.pdf §4.4 eq. (1): "A's unbeatable strategy [Γ ↦ ω]_A ⟹
⟦Γ ↦ ω⟧." §4.3: "Transactions are unimpeded: ... it is possible for any
party to apply any operation, O, on-chain before time t + Δ"; "Transactions
can be front-run: ... there is no way for p1 to ensure that they can apply
O1 to the chain before p2 applies O2" — together these state that no
caller can BLOCK another caller's operation, only interleave with it.
-/

/-- Which harm this rules out: once all participants have signed a final
    state (Nitro-2019-219.pdf §4.4's "concluded" universally finalizable
    point, Figure 11), no other caller's actions — in any number, in any
    order, before this theorem's own calls run — can prevent a named
    participant from obtaining a spendable note worth their allocation.
    This is the Lean statement of "A's unbeatable strategy ⟹ the
    finalized outcome": the fixed strategy is `conclude` (if not already
    concluded) then `transfer`, and it succeeds after ANY interleaving
    (`interleaved`) another caller runs first — formalizing §4.3's two
    assumptions (unimpeded, cannot be front-run) as "no interleaving can
    make the strategy's own `Step` preconditions false". `hsigned` reads
    unanimous signing at `s`; since `.sign` only ever adds to `signedBy`
    (`State.lean`'s module comment), `interleaved` cannot UN-sign anything,
    so `SignedByAll` still holds at `mid`. "Getting money owed" is a live
    note in the pool, matching this model's note-based payment
    (`Notes.lean`): `p` can later spend it with their own key, which is
    the Armada-layer meaning of "paid" (lab book decision 9: the
    collateral "never leaves the pool"). -/
theorem unbeatable_pays
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (p assetIndex : Nat) (hAssetIdx : assetIndex < candidate.outcome.length)
    (owed : Nat) (dest : Allocation)
    (hreach : Reachable sig proofA (genesis assets self pool0) s) (hp : p ∈ fp.participants)
    (hsigned : SignedByAll sig s fp candidate)
    (hdest : dest ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations)
    (hp_dest : dest.destination = p) (howed : dest.amount = owed) :
    ∀ (interleaved : List Call) (mid : AdjudicatorState),
      AppliesAll sig proofA s interleaved mid →
      ∃ (payCalls : List Call) (final : AdjudicatorState),
        AppliesAll sig proofA mid payCalls final ∧
        ∃ pre : NotePreimage, pre.npk = p ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          pre.value = owed ∧
          final.pool.isLive (commitment pre.npk pre.token pre.value) := by
  sorry

/-- Which harm this rules out: the same guarantee for the "sad path"
    (ForceMove-2018.pdf §1.2: "the adjudicator releases funds according to
    the resolution specified by the most recently known state at the time
    of the dispute" — timeout, not cooperation, decides the payout). Once a
    challenge is registered naming `candidate` and no higher-turn state is
    presented before `finalizesAt`, a participant's strategy — `tick` to
    `finalizesAt`, then `transfer` — succeeds after any interleaving,
    matching `unbeatable_pays` for the non-cooperative case
    (Nitro-2019-219.pdf §4.4 Figure 11's other universally finalizable
    point and S4 `0040-lifecycle-of-a-channel.md`'s `Challenge --timeout-->
    Finalized'`). -/
theorem unbeatable_pays_after_timeout
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (proof : List VariablePart)
    (candidate : VariablePart) (challenger p assetIndex : Nat)
    (hAssetIdx : assetIndex < candidate.outcome.length) (owed : Nat) (dest : Allocation)
    (hreach : Reachable sig proofA (genesis assets self pool0) s) (hp : p ∈ fp.participants)
    (hsupported : AppSupports fp proof candidate)
    (hchallenger : challenger ∈ fp.participants)
    (hauth : AuthorizedBy sig s challenger (stateHash fp candidate))
    (hfinalizing : (s.channels (channelId fp)).finalizesAt > 0)
    (hdest : dest ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations)
    (hp_dest : dest.destination = p) (howed : dest.amount = owed) :
    ∀ (interleaved : List Call) (mid : AdjudicatorState),
      AppliesAll sig proofA s interleaved mid →
      (∀ highTurn, highTurn ≤ candidate.turnNum ∨
        ¬ ∃ s'', Step sig proofA mid
          (.challenge fp proof ⟨candidate.outcome, candidate.appData, highTurn, candidate.isFinal⟩
            challenger) s'') →
      ∃ (payCalls : List Call) (final : AdjudicatorState),
        AppliesAll sig proofA mid payCalls final ∧
        ∃ pre : NotePreimage, pre.npk = p ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          pre.value = owed ∧
          final.pool.isLive (commitment pre.npk pre.token pre.value) := by
  sorry

/-!
## C. No caller can create or destroy value in the pool

Lab book §3a: "The pool's core invariant is that value in the pool exists
only as notes: every token the pool holds backs exactly one unspent note,
and the only moves are shield, transact and unshield." This adjudicator
calls only `transact`/`transactOwned` (every `Step` case in
`Operations.lean`), never `shield`/`unshield`, so the quoted invariant
specializes to pure conservation for every call this adjudicator accepts.
-/

/-- Which harm this rules out: no single call can mint value into the pool
    or burn value out of it — every call only moves WHICH note backs a
    given token's value, never how much. One-step form; `Reachability.lean`
    lifts it to the full reachable set in `notedValue_conserved_reachable`
    below. -/
theorem notedValue_conserved
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s s' : AdjudicatorState) (call : Call) (token : Nat)
    (hstep : Step sig proofA s call s') :
    s'.pool.notedValue token = s.pool.notedValue token := by
  sorry

/-- The reachable-set form of `notedValue_conserved` (Phase 1 brief: "state
    it over that reachable set, not over one step from a chosen state"):
    every reachable state's `notedValue` per token equals the DEPLOYED
    pool's — the adjudicator only ever reassigns which note backs a
    token's value, starting from whatever the shared Armada pool already
    held when this adjudicator was deployed (`State.lean`'s `genesis`). -/
theorem notedValue_conserved_reachable
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (token : Nat)
    (hreach : Reachable sig proofA (genesis assets self pool0) s) :
    s.pool.notedValue token = pool0.notedValue token := by
  sorry

/-- Which harm this rules out: `holdings` can never point to a commitment
    the pool itself does not back with a live note — there is no path by
    which a channel's recorded collateral becomes a dangling reference a
    caller could exploit (N1a husband review: "No code path sets `holdings[
    asset][channelId]` to a commitment whose preimage the adjudicator has
    not itself verified"). This is the formal content of lab book decision
    9's "value in the pool exists only as notes" at the adjudicator's own
    storage layer, not only the pool's. -/
theorem holdings_point_to_live_notes
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (asset cid c : Nat)
    (hreach : Reachable sig proofA (genesis assets self pool0) s)
    (hholds : s.holdings asset cid = some c) :
    s.pool.isLive c := by
  sorry

/-!
## A concrete app, for the can-happen theorems only

Safety stays stated for ANY `AppSupports` (coordinator instruction, this
session: "Safety stays stated for any app" — sections A-C above take no
stance on which app a channel uses, and none of them is touched below).
The can-happen theorems in section D need to WITNESS a channel whose
`.challenge` actually succeeds, which needs `AppSupports` satisfiable for
SOME input — so for THESE theorems only, this model uses the REAL,
deployed `ConsensusApp` (`ConsensusApp.sol:18-25`): "`Consensus.
requireConsensus(fixedPart, proof, candidate); return (true, '');`" and
`Consensus.requireConsensus` (`Consensus.sol:18-28`): "`require(proof.
length == 0, '|proof|!=0'); require(NitroUtils.getClaimedSignersNum(
candidate.signedBy) == fixedPart.participants.length, '!unanimous');`" —
empty proof, unanimous signatures, nothing else.
-/

/-- A distinguished `appDefinition` value standing for the address where
    the real `ConsensusApp` is deployed. -/
def consensusApp : Nat := 1

/-- `ConsensusApp.stateIsSupported` implements EXACTLY `Consensus.
    requireConsensus` (quoted above): a fact about what the real, already
    -written, deployed bytecode computes, not a new cryptographic
    assumption — the same status this model already gives `channelIdOf`
    (a deterministic function of its inputs, `Assumptions.lean`). Used
    only by the can-happen theorems, to replace the opaque `AppSupports`
    with the real app's rule for a channel that actually runs it. -/
axiom AppSupports_consensusApp (sig : SignatureAssumptions) (s : AdjudicatorState)
    (fp : FixedPart) (proof : List VariablePart) (candidate : VariablePart)
    (happ : fp.appDefinition = consensusApp) :
    AppSupports fp proof candidate ↔ (proof = [] ∧ SignedByAll sig s fp candidate)

/-!
## D. "Can happen": the adjudicator's reason for existing

Phase 1 brief: "Also state, for each thing the adjudicator is for (a
deposit, a payout, a top-up, a reclaim, a conclude, a challenge that times
out), that it can actually happen. A model in which nothing can happen
satisfies every safety statement, and proves nothing." Every statement
below quantifies `HashAssumptions`, `SignatureAssumptions`,
`ProofAssumptions` and `ProofLiveness` UNIVERSALLY ("for all assumptions
(hash, signature unforgeability, proof soundness, proof completeness)"),
with only the EXECUTION (the deployment parameters and the call sequence)
existentially chosen (coordinator instruction, this session). The
execution starts from `genesis assets self pool0` and includes whatever
`.sign`/`.signNote` calls are needed for the honest participants it names
to sign what the later calls require — this is what "honest participants
sign what is needed" means concretely: the witness call sequence contains
the signing actions, not an assumption that signs on their behalf.

All seven restate this way; none needed a further, unauthorized
assumption. The pool layer's `EdDSAVerify` gap and the app layer's
`AppSupports` gap the PRIOR correction reported as blocking are both
closed here: `EdDSAVerify` by `Notes.lean`'s `eddsaCompleteness`, gated on
`.signNote`; `AppSupports` by `AppSupports_consensusApp` above, gated on
`.sign` for every participant plus `fp.appDefinition = consensusApp`.
-/

/-- A deposit can happen: for all `HashAssumptions`, `SignatureAssumptions`,
    `ProofAssumptions`, `ProofLiveness`, there is an execution from
    `genesis` — with a pool state `pool0` that already holds the
    depositor's spendable note, and a `.signNote` call recording that the
    depositor's key signed the deposit's message hash — in which a deposit
    succeeds (N2a brief, "Goal"). `eddsaCompleteness` turns the recorded
    signing fact into the `EdDSAVerify` witness `Constrained`
    (`DepositTransacted`, `Notes.lean`) needs. -/
theorem deposit_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (channelId expectedHeld asset amount : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.deposit channelId expectedHeld asset amount) s' := by
  sorry

/-- A top-up can happen: the same construction as `deposit_can_happen`,
    run twice from a `pool0` holding both notes, against a channel that
    already holds collateral from the first deposit — `heldValue`
    increases by the second deposit's amount (`depositBinding`'s own
    purpose, `ArmadaNitroAdjudicator.sol:60-72`: binds the proof to
    `(channelId, expectedHeld)` so a deposit always adds to, never
    replaces, the prior holding). -/
theorem topup_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s mid s' : AdjudicatorState) (cid a1 a2 asset amt1 amt2 : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.deposit cid a1 asset amt1) mid ∧
      Step sig proofA mid (.deposit cid a2 asset amt2) s' ∧
      heldValue s' asset cid = heldValue mid asset cid + amt2 := by
  sorry

/-- A challenge can happen: for all four assumptions, there is an
    execution from `genesis` — naming a channel `fp` whose `appDefinition`
    is the real `ConsensusApp` (`consensusApp`), and a `.sign` call for
    every one of `fp`'s participants on `stateHash fp candidate` — in
    which a `.challenge` call succeeds and advances the channel to
    `.challenge` mode (ForceMove.sol:39-81; clause 13).
    `AppSupports_consensusApp` turns the recorded unanimous signing into
    `AppSupports fp [] candidate`; the challenger, being one of the
    participants who signed, is also authorized. -/
theorem challenge_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (proof : List VariablePart)
      (candidate : VariablePart) (challenger : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.challenge fp proof candidate challenger) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .challenge := by
  sorry

/-- A challenge can time out: starting from `challenge_can_happen`'s own
    construction, a reachable state with a registered, unanswered
    challenge, a `tick` to `finalizesAt` reaches `.finalized` mode with no
    further call (clause 18, S4 `0040-lifecycle-of-a-channel.md`: "timeout
    is a passive transition"). -/
theorem challenge_timeout_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (cid : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      (s.channels cid).finalizesAt > 0 ∧
      Step sig proofA s (.tick (s.channels cid).finalizesAt) s' ∧
      (s'.channels cid).mode s'.now = .finalized := by
  sorry

/-- A conclude can happen: for all four assumptions, there is an execution
    from `genesis` — a `.sign` call for every one of `fp`'s participants on
    `stateHash fp candidate` — in which a `.conclude` call finalizes the
    channel instantly (clause 17, S4 `0070-finalizing-a-channel.md`: "the
    `conclude` method allows anyone... to immediately finalize an
    outcome... without having to wait for a challenge to expire"). Needs
    no `AppSupports`/`ConsensusApp` machinery: `.conclude`'s `Step` case
    checks only `SignedByAll`, which the `.sign` calls establish directly. -/
theorem conclude_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.conclude fp candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .finalized := by
  sorry

/-- A payout can happen: starting from `deposit_can_happen`'s construction
    to fund a channel, a `.sign` sequence to `.conclude` it (as in
    `conclude_can_happen`), a `.transfer` call pays a nonzero amount to
    some destination (N1b/N2b briefs). -/
theorem payout_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
      (outcome : Outcome) (indices : List Nat) (h : assetIndex < outcome.length)
      (dest : Allocation),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.transfer assetIndex cid claimedStateHash outcome indices) s' ∧
      dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations ∧
      0 < dest.amount ∧
      s'.pool.isLive
        (commitment dest.destination (outcome.get ⟨assetIndex, h⟩).asset dest.amount) := by
  sorry

/-- A reclaim can happen: for all four assumptions, there is an execution
    from `genesis` — `.sign` sequences unanimously concluding both the
    source and the target channel — in which a guarantee allocation can be
    reclaimed, reallocating the source channel's own outcome (S3 §2.4,
    Listing 2). `.reclaim`'s `Step` case never calls `AppSupports` or
    `PoolOwnedSpendStep`, so no `ConsensusApp`/`ProofLiveness` machinery is
    needed beyond the `.sign` calls that finalize both channels. -/
theorem reclaim_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (sourceChannelId : Nat) (sourceOutcome : Outcome)
      (sourceAssetIndex indexOfTargetInSource : Nat) (targetOutcome : Outcome)
      (targetAssetIndex claimedTargetStateHash : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.reclaim sourceChannelId sourceOutcome sourceAssetIndex
        indexOfTargetInSource targetOutcome targetAssetIndex claimedTargetStateHash) s' ∧
      s'.channels sourceChannelId ≠ s.channels sourceChannelId := by
  sorry

/-!
## E. Behavior-brief statements, on top of the three questions

Phase 1 brief: "The behavior briefs add rules on top of the three
questions. State them too: the only fee is the shield-in fee, so a payout
takes no fee; `conclude` finalizes without moving value, and the bulk
paths `transferAllAssets` and `concludeAndTransferAllAssets` revert (N3);
value in the pool exists only as notes."
-/

/-- A payout takes no fee: `transfer` mints exactly as much as it debits —
    the paid allocations' total plus the remainder equals the pre-call
    `heldValue`, with no amount withheld anywhere (N2b brief, "Goal":
    "There is no protocol fee on a payout... a payout is a plain output,
    with no fee tag and no `cumulativeFees` coupling."). The only fee
    ANYWHERE in the Armada design is the shield-in fee, charged by the
    pool's `ShieldModule` on a DIFFERENT entry point this adjudicator
    never calls (`ArmadaLean.Fee`, the root pool model's `fee_conservation`
    theorem, which this model does not restate — it belongs to the pool,
    not the adjudicator). -/
theorem payout_takes_no_fee
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig proofA s (.transfer assetIndex cid claimedStateHash outcome indices) s') :
    ∀ h : assetIndex < outcome.length,
      let (_, _, totalPayouts) := transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices
      totalPayouts + (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid - totalPayouts)
        = heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid := by
  sorry

/-- `conclude` finalizes without moving value: `conclude`'s `Step` case
    touches only `s'.channels`; `s'.pool` and `s'.holdings` are provably
    unchanged (N3/R1 briefs, "Behavior (unchanged)": "`conclude` finalizes
    a channel... without the inherited... bulk payout path"). -/
theorem conclude_moves_no_value
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (hstep : Step sig proofA s (.conclude fp candidate) s') :
    s'.pool = s.pool ∧ s'.holdings = s.holdings := by
  sorry

/-- The bulk paths revert: `transferAllAssets` and
    `concludeAndTransferAllAssets` have no successful `Step`, for any
    arguments (N3 brief S2; R1 brief, "Behavior (unchanged)": "`
    transferAllAssets` and `concludeAndTransferAllAssets` revert with a
    use-`transfer` message instead of running the inherited bulk path.").
    DEPARTURE (`departures-found.md` item 5): the current code has no such
    override and both calls succeed, which is the bug this statement rules
    out of the model. -/
theorem bulk_paths_never_succeed
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (cid : Nat) (outcome : Outcome) (claimedStateHash : Nat)
    (fp : FixedPart) (candidate : VariablePart) :
    (∀ s s', ¬ Step sig proofA s (.bulkTransferAllAssets cid outcome claimedStateHash) s') ∧
    (∀ s s', ¬ Step sig proofA s (.bulkConcludeAndTransferAllAssets fp candidate) s') := by
  sorry

/-- Value in the pool exists only as notes, at the adjudicator's own
    interface: `AdjudicatorState` has no raw-balance field anywhere, and
    `heldValue` (`State.lean`) is always a read of a live note's preimage,
    never a stored integer (lab book §3a; decision 9, "there is no public
    `deposit` path, no raw-transfer surplus, and no `sweep`"). This
    statement packages `holdings_point_to_live_notes` (C) and
    `notedValue_conserved_reachable` (C) as the single "value is notes"
    claim the brief names separately from plain conservation. -/
theorem value_exists_only_as_notes
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (asset cid : Nat)
    (hreach : Reachable sig proofA (genesis assets self pool0) s)
    (held : Nat) (hheld : heldValue s asset cid = held) (hpos : 0 < held) :
    ∃ c, s.holdings asset cid = some c ∧ s.pool.isLive c ∧
      (s.pool.preimageOf c).map NotePreimage.value = some held := by
  sorry

/-!
## F. R1 mutation-test misses (`R1-adjudicator-rewrite.md`)

"arn-7c4... found these mutation-test misses... Each rewrite chunk whose
new code covers the old mutated behavior closes the matching miss with a
strengthened test." These are the Lean statements of the same three
closed gaps.
-/

/-- Closes the `heldValue`'s `commitment == 0` miss (old offset 2549): an
    empty commitment reads as `0`, and — the mutant's blind spot — this
    cannot be confused with a REAL note the pool happens to value at `0`,
    because the pool never mints a `0`-value commitment (N1a husband
    review, third bullet). -/
theorem heldValue_zero_iff_no_collateral (s : AdjudicatorState) (asset cid : Nat) :
    heldValue s asset cid = 0 ↔
      s.holdings asset cid = none ∨
      ∃ c, s.holdings asset cid = some c ∧ s.pool.preimageOf c = none := by
  sorry

/-- Closes the constructor's `configuredAssets[...] = true` miss (old
    offset 2921): the configured-asset set never changes after deployment —
    every `Step` case leaves `s'.configuredAssets = s.configuredAssets`
    (`Operations.lean`), so it is exactly the deploy-time list for every
    reachable state. -/
theorem configuredAssets_invariant
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState)
    (hreach : Reachable sig proofA (genesis assets self pool0) s) :
    s.configuredAssets = assets := by
  sorry

/-- Closes two of the five `_mintTransferPayout` misses (old offsets
    11666, 11738): an allocation paid exactly `0` mints no note at all —
    `transferEffects`'s `exitAllocations` (`Outcome.lean`) carries a
    position's allocation through `afford` regardless of selection, but
    `.transfer`'s output list (`Operations.lean`, `payoutOutputs`) is built
    by `filterMap`, which drops a `0`-amount entry outright, not a `≤ 0`/
    `< 1` check a mutant could weaken unnoticed. -/
theorem zero_payout_mints_nothing
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig proofA s (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) (dest : Allocation)
    (hdest : dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations) (hzero : dest.amount = 0) :
    ¬ ∃ pre : NotePreimage, pre.npk = dest.destination ∧ pre.value = 0 ∧
        (commitment pre.npk pre.token pre.value, pre) ∈ s'.pool.liveNotes ∧
        (commitment pre.npk pre.token pre.value, pre) ∉ s.pool.liveNotes := by
  sorry

/-- Closes two more `_mintTransferPayout` misses (old offsets 11843,
    12171): a remainder note is minted only when the remainder is
    strictly positive — a full payout (every index selected, or
    `indices = []`, and `totalPayouts = heldValue`) leaves `holdings[
    asset][cid] = none`, never a dangling `0`-value commitment (N1b
    husband review: "`totalPayouts == initialAssetHoldings` (full payout)
    mints no remainder output, so `holdings[asset][channelId]` cannot be
    left pointing at a `0`-value commitment"). -/
theorem full_payout_leaves_no_remainder
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig proofA s (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length)
    (hfull :
      (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 =
      heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) :
    s'.holdings (outcome.get ⟨assetIndex, h⟩).asset cid = none := by
  sorry

/-- Closes the fifth `_mintTransferPayout` miss (old offset 12743): the
    old collateral commitment is nullified if and only if one existed —
    an unfunded channel's `transfer` call nullifies nothing
    (`PoolOwnedSpendStep`'s `N = (if nullifiedCommitment.isSome then 1 else
    0)` field, `Notes.lean`). -/
theorem nullify_iff_commitment_was_some
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig proofA s (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    (s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid = none) ↔
      s'.pool.usedNullifiers = s.pool.usedNullifiers := by
  sorry

end ArmadaLean.Adjudicator
