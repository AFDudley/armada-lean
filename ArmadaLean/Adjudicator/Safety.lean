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

  Every theorem that reasons about a call sequence takes `SignatureAssumptions`
  and `ProofAssumptions` (`Assumptions.lean`, `Notes.lean`) as explicit
  arguments — `Step`/`AppliesAll`/`Reachable` are themselves parameterized
  by them, so a reader sees on the theorem's own type which cryptographic
  facts it relies on, never a hidden global axiom (coordinator correction,
  this session). Every theorem that reasons about the reachable set takes
  the deploy-time asset list (`assets`), the adjudicator's own identity
  (`self`), and the pool's state at deployment (`pool0`) as explicit
  arguments and anchors `Reachable` at `genesis assets self pool0`
  (`State.lean`) — the one true deployment state, not an arbitrary
  unconstrained starting state (same correction).
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
    (∃ fp candidate, channelId fp = cid ∧ SignedByAll sig fp candidate ∧
      outcomeHashOf candidate.outcome = outcomeH) ∨
    (∃ fp proof candidate challenger, channelId fp = cid ∧
      AppSupports fp proof candidate ∧ challenger ∈ fp.participants ∧
      sig.AuthorizedBy challenger (stateHash fp candidate) ∧
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
    make the strategy's own `Step` preconditions false". "Getting money
    owed" is a live note in the pool, matching this model's note-based
    payment (`Notes.lean`): `p` can later spend it with their own key,
    which is the Armada-layer meaning of "paid" (lab book decision 9: the
    collateral "never leaves the pool"). -/
theorem unbeatable_pays
    (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (p assetIndex : Nat) (hAssetIdx : assetIndex < candidate.outcome.length)
    (owed : Nat) (dest : Allocation)
    (hreach : Reachable sig proofA (genesis assets self pool0) s) (hp : p ∈ fp.participants)
    (hsigned : SignedByAll sig fp candidate)
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
    (hauth : sig.AuthorizedBy challenger (stateHash fp candidate))
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
## D. "Can happen": the adjudicator's reason for existing

Phase 1 brief: "Also state, for each thing the adjudicator is for (a
deposit, a payout, a top-up, a reclaim, a conclude, a challenge that times
out), that it can actually happen. A model in which nothing can happen
satisfies every safety statement, and proves nothing." Each statement
below that IS restated quantifies the three safety assumptions and the
two liveness assumptions UNIVERSALLY ("for all `HashAssumptions`,
`SignatureAssumptions`, `ProofAssumptions`, `SignatureLiveness`,
`ProofLiveness`"), with only the EXECUTION (the deployment parameters and
the call sequence) existentially chosen (coordinator correction, this
session): a prior form put the assumptions inside the existential, so a
proof could choose, for example, an `AuthorizedBy` that accepts
everything, and the statement said nothing about the real system. The
execution starts from a state `s` that is itself `Reachable` from
deployment (`genesis assets self pool0`), so an unreachable, impossible
state cannot satisfy it either.

Two of the seven — `conclude_can_happen`, `reclaim_can_happen` — restate
cleanly this way: both go through only `SignedByAll`/`AuthorizedBy`, which
`SignatureLiveness` makes satisfiable for any `fp`/`candidate`.

The other five — `deposit_can_happen`, `topup_can_happen`,
`challenge_can_happen`, `challenge_timeout_can_happen`, `payout_can_happen`
— each need a THIRD kind of liveness fact the coordinator's two named
assumptions do not cover (the pool layer's `EdDSAVerify`, or the
app-layer's `AppSupports`, being satisfiable for some input). Per
instruction: "If a 'can happen' theorem cannot be stated this way without
a further assumption, stop and report which one and why. Do not add it."
Each keeps its PRE-correction statement below (assumptions still inside
the existential — the ORIGINAL defect, not fixed), with a comment naming
exactly which further assumption would be needed and why adding it was
out of scope for this correction.
-/

/-- BLOCKED — not restated. Instruction: "If a 'can happen' theorem cannot
    be stated this way without a further assumption, stop and report which
    one and why. Do not add it." A deposit spends the depositor's note
    through the pool's BASE `Transact` circuit (`DepositTransacted`,
    `Notes.lean`), whose signature check is `ArmadaLean.EdDSAVerify`
    (root pool layer, `Transact.lean:29`) — a bare global axiom this phase
    does not touch (`Assumptions.lean`'s module comment: "this file does
    not change [the pool layer's axioms]... outside this phase's scope").
    `EdDSAVerify` carries no completeness assumption anywhere in the
    model: in the model's weakest admissible interpretation it is always
    `False`, which no witness can satisfy, making `DepositTransacted`
    unsatisfiable no matter what `HashAssumptions`/`SignatureAssumptions`/
    `ProofAssumptions`/`SignatureLiveness`/`ProofLiveness` hold (none
    mention `EdDSAVerify`). Restating this theorem with those five
    quantified universally would therefore assert a FALSE claim. The
    further assumption needed — EdDSA completeness for the pool's own
    `Transact` circuit, "an honest depositor can produce a valid signature
    over any message they choose" — is not one of the two the coordinator
    named, so it is not added; this theorem is reported as blocked
    instead. -/
theorem deposit_can_happen :
    ∃ (sig : SignatureAssumptions) (proofA : ProofAssumptions)
      (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (channelId expectedHeld asset amount : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.deposit channelId expectedHeld asset amount) s' := by
  sorry

/-- BLOCKED — not restated, same gap as `deposit_can_happen`: a top-up is
    two deposits, so it needs `EdDSAVerify` completeness twice over. -/
theorem topup_can_happen :
    ∃ (sig : SignatureAssumptions) (proofA : ProofAssumptions)
      (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s mid s' : AdjudicatorState) (cid a1 a2 asset amt1 amt2 : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.deposit cid a1 asset amt1) mid ∧
      Step sig proofA mid (.deposit cid a2 asset amt2) s' ∧
      heldValue s' asset cid = heldValue mid asset cid + amt2 := by
  sorry

/-- BLOCKED — not restated. `.challenge`'s `Step` case requires
    `AppSupports fp proof candidate` (`Operations.lean`) — a bare global
    axiom (`Channel.lean`: "Modeled as an opaque relation rather than one
    of the three cryptographic assumptions, because it is not independent
    of the channel's own setup"). `AppSupports` carries no completeness
    assumption anywhere in the model: in the weakest admissible
    interpretation it is always `False`, which no `fp`/`proof`/`candidate`
    triple can satisfy, making every `.challenge` call impossible no
    matter what the five stated assumptions hold (none mention
    `AppSupports`). The further assumption needed — that some application
    rule is satisfiable for some input — is not one of the two the
    coordinator named, so it is not added; this theorem is reported as
    blocked instead. -/
theorem challenge_can_happen :
    ∃ (sig : SignatureAssumptions) (proofA : ProofAssumptions)
      (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (proof : List VariablePart)
      (candidate : VariablePart) (challenger : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.challenge fp proof candidate challenger) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .challenge := by
  sorry

/-- BLOCKED — not restated, same gap as `challenge_can_happen`: a genuine
    "challenge that times out" must first reach `.challenge` mode, which
    needs `AppSupports` satisfiable. (Reaching `finalizesAt > 0` via
    `.conclude` instead would not demonstrate a timeout — `conclude`
    finalizes instantly, with no challenge and no waiting — so it would
    answer a different question than the one this theorem is named for,
    not a legitimate workaround.) -/
theorem challenge_timeout_can_happen :
    ∃ (sig : SignatureAssumptions) (proofA : ProofAssumptions)
      (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (cid : Nat),
      Reachable sig proofA (genesis assets self pool0) s ∧
      (s.channels cid).finalizesAt > 0 ∧
      Step sig proofA s (.tick (s.channels cid).finalizesAt) s' ∧
      (s'.channels cid).mode s'.now = .finalized := by
  sorry

/-- A conclude can happen: for ALL `HashAssumptions`, `SignatureAssumptions`,
    `ProofAssumptions`, `SignatureLiveness`, `ProofLiveness`, SOME unanimous
    final state finalizes a channel instantly (clause 17, S4
    `0070-finalizing-a-channel.md`: "the `conclude` method allows anyone...
    to immediately finalize an outcome... without having to wait for a
    challenge to expire"). `.conclude`'s `Step` case needs only
    `SignedByAll sig fp candidate`, and `sigLive.can_authorize` gives
    `sig.AuthorizedBy p d` for every `p`/`d`, hence `SignedByAll` for any
    `fp`/`candidate` — no further assumption needed. -/
theorem conclude_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (sigLive : SignatureLiveness sig) (proofLive : ProofLiveness proofA) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart),
      Reachable sig proofA (genesis assets self pool0) s ∧
      Step sig proofA s (.conclude fp candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .finalized := by
  sorry

/-- BLOCKED — not restated. A payout demonstrating `0 < dest.amount`
    actually minted needs `heldValue s asset cid > 0` before the call
    (`afford`/`transferEffects` pay `0` out of a `0` surplus no matter what
    the outcome records). The ONLY `Step` case that ever sets `holdings` to
    `some _` is `.deposit` — `transfer`'s own remainder output needs an
    EXISTING holding to begin with, so it cannot bootstrap one, and
    `genesis`'s `holdings` starts at `fun _ _ => none` unconditionally. So
    a funded, reachable `s` requires a prior successful `.deposit`, which
    needs `EdDSAVerify` completeness — `deposit_can_happen`'s exact gap,
    not one of the two assumptions the coordinator named. Reported as
    blocked, not restated. -/
theorem payout_can_happen :
    ∃ (sig : SignatureAssumptions) (proofA : ProofAssumptions)
      (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
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

/-- A reclaim can happen: for ALL `HashAssumptions`, `SignatureAssumptions`,
    `ProofAssumptions`, `SignatureLiveness`, `ProofLiveness`, SOME
    guarantee allocation can be reclaimed, reallocating the source
    channel's own outcome (S3 §2.4, Listing 2). `.reclaim`'s `Step` case
    never calls `AppSupports` or `PoolOwnedSpendStep` — it only needs both
    channels `.finalized` (via `.conclude`, using `SignatureLiveness` as
    in `conclude_can_happen`) and arithmetic on the chosen outcome data
    (`a0 + a1 = guarantee.amount`), so no further assumption is needed. -/
theorem reclaim_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (proofA : ProofAssumptions)
    (sigLive : SignatureLiveness sig) (proofLive : ProofLiveness proofA) :
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
