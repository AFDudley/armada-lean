/-
  ArmadaLean.Adjudicator.Safety — the theorem STATEMENTS stage A asks for.
  Every theorem's proof is `sorry`; the proofs are not written yet.

  The adjudicator holds other people's money, so this model shows three
  things: (1) no caller can take money they are not owed; (2) no caller
  can stop someone from getting money they are owed; (3) no caller can
  create or destroy value in the pool. Every theorem below is grounded
  in one of these three, stated over the REACHABLE set
  (`Reachability.lean`), never over one step from a chosen state: a
  safety statement holds at every state reachable from deployment by
  any sequence of calls by any caller.

  This model also requires: every finalizable outcome is paid out as
  notes, with no fee, with pool value conserved; and no caller can make
  the adjudicator pay an outcome that is not finalizable — using
  Nitro-2019-219.pdf §4.4's own definitions of "finalizable" and
  "enabled" outcome, not an invented rule. Sections A and B below are
  the two halves of that requirement.

  Every theorem that reasons about a call sequence takes
  `SignatureAssumptions` (`Assumptions.lean`) as an explicit argument —
  `Step`/`AppliesAll`/`Reachable` are themselves parameterized by it, so a
  reader sees on the theorem's own type which cryptographic facts it
  relies on, never a hidden global axiom. Safety theorems (sections A-C)
  also take `appRel`
  (`Operations.lean`'s module comment) as an explicit UNIVERSAL parameter:
  "safety stays stated for any app." Every theorem that reasons about the
  reachable set takes the deploy-time asset list (`assets`), the
  adjudicator's own identity (`self`), and the pool's state at deployment
  (`pool0`) as explicit arguments and anchors `Reachable` at `genesis
  assets self pool0` (`State.lean`) — the one true deployment state, not
  an arbitrary unconstrained starting state.

  Signing is an ACTION taken by a named `Actor` (`Operations.lean`'s
  module comment): `AuthorizedBy sig s p d` (`State.lean`) and
  `SignedByAll sig s fp vp` take the CURRENT state `s`, so they read the
  digests `s`'s execution has actually recorded as signed, through
  `AdjudicatorState.signedBy` — grown only by `.sign`, and only when the
  acting `Actor` IS the participant the digest names (`Operations.lean`'s
  `.sign` case). Signing is monotone (`.sign` only ever adds, never
  removes a recorded digest), so a fact `SignedByAll sig s fp vp`
  established at some point in an execution survives to every LATER
  reachable state too — the safety theorems below state it at the
  theorem's own `s`, the current or final state, with no loss of
  generality. The two "unbeatable strategy" theorems (section B) name
  the strategy's own participant `h` (for "honest"): every step an
  `interleaved` sequence supplies may be taken by an actor OTHER than
  `h` (an attacker's own steps), and such a step cannot add to `h`'s row
  of `signedBy` — a direct consequence of `.sign`'s own actor check, not
  an extra hypothesis these theorems need to state.

  Contract-owned notes, and the soundness/completeness assumptions about
  the `TransactOwned` circuit's proof system, are a POOL feature, not an
  adjudicator feature: the adjudicator is an ordinary user of the pool,
  so owned-note rules come from the pool module. They live in
  `ArmadaLean.TransactOwned`/`ArmadaLean.PoolOwned` (root `ArmadaLean`
  modules, branch `owned-notes`), not here. `Operations.lean`'s `.transfer`
  case calls `ArmadaLean.PoolOwnedSpendStep` (`Notes.lean`), which reads
  `ArmadaLean.VerifyOwnedAccepts`/`ArmadaLean.OwnedConstrained` directly —
  no adjudicator-level `ProofAssumptions` wrapper is threaded through
  `Step`/`AppliesAll`/`Reachable` any more. `payout_can_happen` (section D)
  takes `ArmadaLean.OwnedProofCompleteness` as an explicit argument where
  it needs the pool's own completeness assumption; `ArmadaLean.
  owned_no_double_spend` grounds `nullify_iff_commitment_was_some`
  (section F).
-/
import ArmadaLean.Adjudicator.Lemmas

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
    `SignedByAll`, or `challenge` with `appRel`+`AuthorizedBy`) but does
    not additionally require that no later, higher-turn challenge or
    checkpoint overwrote it before the timeout — that refinement belongs
    to the proof stage, not to this statement. -/
theorem finalized_outcome_was_concluded_or_challenged
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (cid stateH outcomeH : Nat)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hfin : ChannelFinalizedWith s cid stateH outcomeH) :
    (∃ fp candidate, channelId fp = cid ∧ SignedByAll sig s fp candidate ∧
      outcomeHashOf candidate.outcome = outcomeH) ∨
    (∃ fp proof candidate challenger, channelId fp = cid ∧
      appRel s fp proof candidate ∧ challenger ∈ fp.participants ∧
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
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    ChannelFinalizedWith s cid claimedStateHash (outcomeHashOf outcome) ∧
    ∀ paid ∈ (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.1,
      ∃ original ∈ (outcome.get ⟨assetIndex, h⟩).allocations,
        paid.destination = original.destination ∧ paid.amount ≤ original.amount := by
  obtain ⟨_hidx, hmode, hsh, hoh, _hstrict, _hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  exact ⟨⟨hmode, hsh, hoh⟩,
    transferEffects_exit_provenance (outcome.get ⟨assetIndex, h⟩).allocations
      (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices⟩

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
    order, by any `Actor` OTHER than `h` themselves, before this
    theorem's own calls run — can prevent the honest participant `h` from
    obtaining a spendable note worth their allocation. This is the Lean
    statement of "A's unbeatable strategy ⟹ the finalized outcome": the
    fixed strategy is `conclude` (if not already concluded) then
    `transfer`, and it succeeds after ANY interleaving (`interleaved`)
    another caller runs first — formalizing §4.3's two assumptions
    (unimpeded, cannot be front-run) as "no interleaving can make the
    strategy's own `Step` preconditions false". `hnotActor` excludes `h`'s
    OWN actor identities (the Nitro identity `h`, and the pool key
    `hPoolKey` if `h` has one) from `interleaved`: without it,
    `interleaved` could contain a step only `h` themselves could take
    (`.sign h d` for an arbitrary `d` `h` never chose, `Operations.lean`'s
    actor check) and have it count as "the adversary's" doing, when it is
    really `h`'s own action. `h`'s own steps belong only
    in the witnessed `payCalls`, never in `interleaved`. `hsigned` reads
    unanimous signing at `s`; since `.sign` only ever adds to `signedBy`,
    and only in the ACTING participant's own row, `interleaved` (now
    excluding `h`'s own actor) cannot UN-sign anything, so `SignedByAll`
    still holds at `mid`. "Getting money owed" is a live note in the
    pool, matching this model's note-based payment (`Notes.lean`): `h`
    can later spend it with their own key, which is the Armada-layer
    meaning of "paid" — the armada-nitro rule (`State.lean`). -/
theorem unbeatable_pays
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (h : Nat) (hPoolKey : Option (Nat × Nat)) (assetIndex : Nat)
    (hAssetIdx : assetIndex < candidate.outcome.length)
    (owed : Nat) (dest : Allocation)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) (hp : h ∈ fp.participants)
    (hsigned : SignedByAll sig s fp candidate)
    (hdest : dest ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations)
    (hh_dest : dest.destination = h) (howed : dest.amount = owed) :
    ∀ (interleaved : List (Actor × Call)) (mid : AdjudicatorState),
      AppliesAll sig appRel s interleaved mid →
      (∀ actor call, (actor, call) ∈ interleaved →
        actor ≠ Actor.nitro h ∧ ∀ pk, hPoolKey = some pk → actor ≠ Actor.pool pk) →
      ∃ (payCalls : List (Actor × Call)) (final : AdjudicatorState),
        AppliesAll sig appRel mid payCalls final ∧
        ∃ pre : NotePreimage, pre.npk = h ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          pre.value = owed ∧
          final.pool.isLive (commitment pre.npk pre.token pre.value) := by
  sorry

/-- Which harm this rules out: the same guarantee for the "sad path"
    (ForceMove-2018.pdf §1.2: "the adjudicator releases funds according to
    the resolution specified by the most recently known state at the time
    of the dispute" — timeout, not cooperation, decides the payout). Once a
    challenge is registered naming `candidate` and no higher-turn state is
    presented before `finalizesAt`, the honest participant `h`'s strategy
    — `tick` to `finalizesAt`, then `transfer` — succeeds after any
    interleaving by any `Actor` OTHER than `h`, matching `unbeatable_pays`
    for the non-cooperative case (Nitro-2019-219.pdf §4.4 Figure 11's
    other universally finalizable point and S4
    `0040-lifecycle-of-a-channel.md`'s `Challenge --timeout--> Finalized'`).
    `hnotActor` excludes `h`'s own actor identities from `interleaved`,
    for the same reason `unbeatable_pays` does. -/
theorem unbeatable_pays_after_timeout
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (proof : List VariablePart)
    (candidate : VariablePart) (challenger h : Nat) (hPoolKey : Option (Nat × Nat))
    (assetIndex : Nat)
    (hAssetIdx : assetIndex < candidate.outcome.length) (owed : Nat) (dest : Allocation)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) (hp : h ∈ fp.participants)
    (hsupported : appRel s fp proof candidate)
    (hchallenger : challenger ∈ fp.participants)
    (hauth : AuthorizedBy sig s challenger (stateHash fp candidate))
    (hfinalizing : (s.channels (channelId fp)).finalizesAt > 0)
    (hdest : dest ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations)
    (hh_dest : dest.destination = h) (howed : dest.amount = owed) :
    ∀ (interleaved : List (Actor × Call)) (mid : AdjudicatorState),
      AppliesAll sig appRel s interleaved mid →
      (∀ actor call, (actor, call) ∈ interleaved →
        actor ≠ Actor.nitro h ∧ ∀ pk, hPoolKey = some pk → actor ≠ Actor.pool pk) →
      (∀ highTurn, highTurn ≤ candidate.turnNum ∨
        ¬ ∃ (anyActor : Actor) (s'' : AdjudicatorState), Step sig appRel anyActor mid
          (.challenge fp proof ⟨candidate.outcome, candidate.appData, highTurn, candidate.isFinal⟩
            challenger) s'') →
      ∃ (payCalls : List (Actor × Call)) (final : AdjudicatorState),
        AppliesAll sig appRel mid payCalls final ∧
        ∃ pre : NotePreimage, pre.npk = h ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          pre.value = owed ∧
          final.pool.isLive (commitment pre.npk pre.token pre.value) := by
  sorry

/-!
## C. No caller can create or destroy value in the pool

The armada-nitro rule (`State.lean`): a channel's holding is a note in
the pool, owned by the adjudicator. This adjudicator
calls only `transact`/`transactOwned` (every `Step` case in
`Operations.lean`), never `shield`/`unshield`, so value in the pool
can be reassigned between notes but neither created nor destroyed:
`ArmadaLean.transact_value_conserved` (`Transact.lean`) and
`ArmadaLean.transactOwned_value_conserved` (`TransactOwned.lean`)
prove this for each circuit's own spend.
-/

/-- Which harm this rules out: no single call can mint value into the pool
    or burn value out of it — every call only moves WHICH note backs a
    given token's value, never how much. One-step form; `Reachability.lean`
    lifts it to the full reachable set in `notedValue_conserved_reachable`
    below. -/
theorem notedValue_conserved
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call) (token : Nat)
    (hstep : Step sig appRel actor s call s') :
    s'.pool.notedValue token = s.pool.notedValue token := by
  sorry

/-- The reachable-set form of `notedValue_conserved`, stated over the
    REACHABLE set rather than over one step from a chosen state: every
    reachable state's `notedValue` per token equals the DEPLOYED
    pool's — the adjudicator only ever reassigns which note backs a
    token's value, starting from whatever the shared Armada pool already
    held when this adjudicator was deployed (`State.lean`'s `genesis`). -/
theorem notedValue_conserved_reachable
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (token : Nat)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) :
    s.pool.notedValue token = pool0.notedValue token := by
  sorry

/-- Which harm this rules out: `holdings` can never point to a commitment
    the pool itself does not back with a live note — there is no path by
    which a channel's recorded collateral becomes a dangling reference a
    caller could exploit. The held value is the note's value read from
    the pool's own record, which `ArmadaLean.preimageOf_consistent`
    (`PoolOwned.lean`) proves trustworthy; only the owner can ever
    spend the note the holding points at, by `ArmadaLean.
    owned_owner_binding` (`PoolOwned.lean`). This is the formal content
    of the armada-nitro rule at the adjudicator's own storage layer,
    not only the pool's. -/
theorem holdings_point_to_live_notes
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (asset cid c : Nat)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hholds : s.holdings asset cid = some c) :
    s.pool.isLive c := by
  sorry

/-!
## A concrete app, for the can-happen theorems only

Safety stays stated for ANY `appRel` (sections A-C above take no stance
on which app a channel uses, and none of them is touched below). The
can-happen theorems in section D need to WITNESS a channel whose
`.challenge` actually succeeds, which needs `appRel` satisfiable for SOME
input — so for THESE theorems only, this model uses the REAL, deployed
`ConsensusApp`'s own relation in `appRel`'s place (`appRel` is a
PARAMETER of the model, `Operations.lean`'s `Step`, not a bare global
axiom). `ConsensusApp.sol:18-25`: "`Consensus.requireConsensus(fixedPart,
proof, candidate); return (true, '');`" and `Consensus.requireConsensus`
(`Consensus.sol:18-28`): "`require(proof.length == 0, '|proof|!=0');
require(NitroUtils.getClaimedSignersNum(candidate.signedBy) ==
fixedPart.participants.length, '!unanimous');`" — empty proof, unanimous
signatures, nothing else.
-/

/-- The real ConsensusApp's rule (`ConsensusApp.sol`/`Consensus.sol`,
    quoted above): empty proof, and every participant has authorized the
    candidate's hash at the current state (`SignedByAll`). A `def`, not an
    axiom: a fact about what the already-deployed, already-audited
    bytecode computes, the same status this model already gives
    `channelIdOf` (a deterministic function of its inputs,
    `Assumptions.lean`). The can-happen theorems below SUBSTITUTE this
    relation for `appRel` directly, instead of reasoning about an
    arbitrary one. -/
def consensusRelation (sig : SignatureAssumptions) (s : AdjudicatorState)
    (fp : FixedPart) (proof : List VariablePart) (candidate : VariablePart) : Prop :=
  proof = [] ∧ SignedByAll sig s fp candidate

/-!
## D. "Can happen": the adjudicator's reason for existing

For each thing the adjudicator is for — a deposit, a payout, a top-up,
a reclaim, a conclude, a challenge that times out — this model also
states that it can actually happen. A model in which nothing can
happen satisfies every safety statement, and proves nothing. Every statement
below quantifies `HashAssumptions`, `SignatureAssumptions` and whichever
liveness assumptions its own call sequence needs UNIVERSALLY, with only
the EXECUTION (the deployment parameters and the call sequence)
existentially chosen. The execution starts from `genesis assets self
pool0`, uses `appRel := consensusRelation sig` (the preceding section),
and includes whatever `.sign`/`.signNote` calls are needed for the honest
participants it names to sign what the later calls require, EACH taken
by that participant's own `Actor` (`Operations.lean`'s `.sign`/
`.signNote` cases) — this is what "honest participants sign what is
needed" means concretely: the witness call sequence contains the signing
actions, taken by the right actors, not an assumption that signs on
their behalf.

All seven restate this way; none needed a further, unauthorized
assumption. The pool layer's `EdDSAVerify` gap, the app layer's `appRel`
gap, and (now that contract-owned notes moved to `ArmadaLean.
PoolOwned`) the owned circuit's `VerifyOwnedAccepts` gap are all
closed: `EdDSAVerify` by `Notes.lean`'s `PoolSignatureLiveness.
eddsaCompleteness`, gated on `.signNote`; `appRel` by substituting
`consensusRelation sig`, gated on `.sign` for every participant;
`VerifyOwnedAccepts` by `ArmadaLean.OwnedProofCompleteness`
(`PoolOwned.lean`), taken as an explicit argument by `payout_can_happen`
only (the one can-happen theorem whose witnessed execution includes a
`.transfer` call).
-/

/-- A deposit can happen: for all `HashAssumptions`, `SignatureAssumptions`,
    `PoolSignatureLiveness`, there is an execution from
    `genesis` — with a pool state `pool0` that already holds the
    depositor's spendable note, and a `.signNote` call recording that the
    depositor's key signed the deposit's message hash — in which a
    deposit succeeds (Nitro-2019-219.pdf §3.1: "There are no
    restrictions on who can deposit coins for an address"; the
    armada-nitro rule, `State.lean`, specializes the deposited coins to
    a note). `PoolSignatureLiveness.
    eddsaCompleteness` turns the recorded signing fact into the
    `EdDSAVerify` witness `Constrained` (`DepositTransacted`,
    `Notes.lean`) needs. Unrelated to owned notes: `.deposit` uses the
    BASE `Transact` circuit (EdDSA), not `ArmadaLean.OwnedConstrained`,
    so no `OwnedProofCompleteness` argument is needed here. -/
theorem deposit_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (channelId expectedHeld asset amount : Nat) (actor : Actor),
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.deposit channelId expectedHeld asset amount) s' := by
  sorry

/-- A top-up can happen: the same construction as `deposit_can_happen`,
    run twice from a `pool0` holding both notes, against a channel that
    already holds collateral from the first deposit — `heldValue`
    increases by the second deposit's amount (`depositBinding`'s own
    purpose, `ArmadaNitroAdjudicator.sol:60-72`: binds the proof to
    `(channelId, expectedHeld)` so a deposit always adds to, never
    replaces, the prior holding). -/
theorem topup_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s mid s' : AdjudicatorState) (cid a1 a2 asset amt1 amt2 : Nat) (actor1 actor2 : Actor),
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor1 s (.deposit cid a1 asset amt1) mid ∧
      Step sig (consensusRelation sig) actor2 mid (.deposit cid a2 asset amt2) s' ∧
      heldValue s' asset cid = heldValue mid asset cid + amt2 := by
  sorry

/-- A challenge can happen: for all `HashAssumptions`/`SignatureAssumptions`,
    there is an execution from `genesis` — a `.sign` call for every one of
    `fp`'s participants on `stateHash fp candidate` — in which a
    `.challenge` call succeeds and advances the channel to `.challenge`
    mode (ForceMove.sol:39-81; clause 13), using `consensusRelation sig`
    for `appRel`: the recorded unanimous signing directly satisfies it
    with `proof := []`; the challenger, being one of the participants who
    signed, is also authorized. -/
theorem challenge_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
      (challenger : Nat) (actor : Actor),
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.challenge fp [] candidate challenger) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .challenge := by
  sorry

/-- A challenge can time out: starting from `challenge_can_happen`'s own
    construction, a reachable state with a registered, unanswered
    challenge, a `tick` to `finalizesAt` reaches `.finalized` mode with no
    further call (clause 18, S4 `0040-lifecycle-of-a-channel.md`: "timeout
    is a passive transition"). -/
theorem challenge_timeout_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (cid : Nat) (actor : Actor),
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      (s.channels cid).finalizesAt > 0 ∧
      Step sig (consensusRelation sig) actor s (.tick (s.channels cid).finalizesAt) s' ∧
      (s'.channels cid).mode s'.now = .finalized := by
  sorry

/-- A conclude can happen: for all `HashAssumptions`/`SignatureAssumptions`,
    there is an execution from `genesis` — a `.sign` call for every one of
    `fp`'s participants on `stateHash fp candidate` — in which a
    `.conclude` call finalizes the channel instantly (clause 17, S4
    `0070-finalizing-a-channel.md`: "the `conclude` method allows anyone...
    to immediately finalize an outcome... without having to wait for a
    challenge to expire"). Needs no `appRel`/`ConsensusApp` machinery:
    `.conclude`'s `Step` case checks only `SignedByAll`, which the `.sign`
    calls establish directly. -/
theorem conclude_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart) (actor : Actor),
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s (.conclude fp candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .finalized := by
  sorry

/-- A payout can happen: starting from `deposit_can_happen`'s construction
    to fund a channel, a `.sign` sequence to `.conclude` it (as in
    `conclude_can_happen`), a `.transfer` call pays a nonzero amount to
    some destination (`Operations.lean`'s `.transfer` case). `.transfer`'s
    owned-spend (`ArmadaLean.PoolOwnedSpendStep`, `Notes.lean`) now needs
    an accepted `transactOwned` proof — `ownedComplete : ArmadaLean.
    OwnedProofCompleteness` (`PoolOwned.lean`) turns the channel's own
    collateral witness (satisfying `ArmadaLean.OwnedConstrained` by
    construction, since the adjudicator itself minted it) into the
    `VerifyOwnedAccepts` witness the pool's own check needs
    (`ArmadaLean.owned_spend_can_happen` proves the same bridge for a
    general owning caller; this theorem specializes it to the
    adjudicator). -/
theorem payout_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness)
    (ownedComplete : OwnedProofCompleteness) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
      (outcome : Outcome) (indices : List Nat) (h : assetIndex < outcome.length)
      (dest : Allocation) (actor : Actor),
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.transfer assetIndex cid claimedStateHash outcome indices) s' ∧
      dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations ∧
      0 < dest.amount ∧
      s'.pool.isLive
        (commitment dest.destination (outcome.get ⟨assetIndex, h⟩).asset dest.amount) := by
  sorry

/-- A reclaim can happen: for all `HashAssumptions`/`SignatureAssumptions`,
    there is an execution from `genesis` — `.sign` sequences unanimously
    concluding both the source and the target channel — in which a
    guarantee allocation can be reclaimed, reallocating the source
    channel's own outcome (S3 §2.4, Listing 2). `.reclaim`'s `Step` case
    never calls `appRel` or `PoolOwnedSpendStep`, so no
    `ConsensusApp`/owned-note machinery is needed beyond the `.sign` calls
    that finalize both channels. -/
theorem reclaim_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (sourceChannelId : Nat) (sourceOutcome : Outcome)
      (sourceAssetIndex indexOfTargetInSource : Nat) (targetOutcome : Outcome)
      (targetAssetIndex claimedTargetStateHash : Nat) (actor : Actor),
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s (.reclaim sourceChannelId sourceOutcome
        sourceAssetIndex indexOfTargetInSource targetOutcome targetAssetIndex
        claimedTargetStateHash) s' ∧
      s'.channels sourceChannelId ≠ s.channels sourceChannelId := by
  sorry

/-!
## E. Behavior-brief statements, on top of the three questions

This model also states four rules on top of the three questions: the
only fee is the shield-in fee, so a payout takes no fee; `conclude`
finalizes without moving value; the bulk paths `transferAllAssets` and
`concludeAndTransferAllAssets` revert; and value in the pool exists
only as notes.
-/

/-- A payout takes no fee: `transfer` mints exactly as much as it debits —
    the paid allocations' total plus the remainder equals the pre-call
    `heldValue`, with no amount withheld anywhere. Nitro-2019-219.pdf
    §5.1: `T(A, B, x)` "Reduces the funds held in channel A by x" —
    the channel is reduced by EXACTLY what it pays, with no third
    quantity withheld. The only fee ANYWHERE in the Armada
    design is the shield-in fee, charged by the pool's `ShieldModule`
    on a DIFFERENT entry point this adjudicator never calls
    (`ArmadaLean.Fee`, the root pool model's `fee_conservation` theorem,
    which this model does not restate — it belongs to the pool, not the
    adjudicator). -/
theorem payout_takes_no_fee
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s') :
    ∀ h : assetIndex < outcome.length,
      let (_, _, totalPayouts) := transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices
      totalPayouts + (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid - totalPayouts)
        = heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid := by
  intro h
  show (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 +
      (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2)
      = heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid
  have hle := transferEffects_totalPayouts_le (outcome.get ⟨assetIndex, h⟩).allocations
    (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices
  omega

/-- `conclude` finalizes without moving value: `conclude`'s `Step` case
    touches only `s'.channels`; `s'.pool` and `s'.holdings` are provably
    unchanged (`Operations.lean`'s `.conclude` doc comment states and
    explains this Armada-specific rule directly). -/
theorem conclude_moves_no_value
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (hstep : Step sig appRel actor s (.conclude fp candidate) s') :
    s'.pool = s.pool ∧ s'.holdings = s.holdings :=
  ⟨hstep.2.2.2.2.1, hstep.2.2.2.2.2.1⟩

/-- The bulk paths revert: `transferAllAssets` and
    `concludeAndTransferAllAssets` have no successful `Step`, for any
    arguments, any application rule and any actor (`Operations.lean`'s
    `.bulkTransferAllAssets`/`.bulkConcludeAndTransferAllAssets` doc
    comment states and explains this Armada-specific rule directly).
    DEPARTURE (`departures-found.md` item 5): the current code has no
    such override and both calls succeed, which is the bug this
    statement rules out of the model. -/
theorem bulk_paths_never_succeed
    (sig : SignatureAssumptions)
    (cid : Nat) (outcome : Outcome) (claimedStateHash : Nat)
    (fp : FixedPart) (candidate : VariablePart) :
    (∀ (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
        (actor : Actor) (s s' : AdjudicatorState),
      ¬ Step sig appRel actor s (.bulkTransferAllAssets cid outcome claimedStateHash) s') ∧
    (∀ (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
        (actor : Actor) (s s' : AdjudicatorState),
      ¬ Step sig appRel actor s (.bulkConcludeAndTransferAllAssets fp candidate) s') :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- Value in the pool exists only as notes, at the adjudicator's own
    interface: `AdjudicatorState` has no raw-balance field anywhere, and
    `heldValue` (`State.lean`) is always a read of a live note's preimage,
    never a stored integer — the armada-nitro rule (`State.lean`).
    This statement packages `holdings_point_to_live_notes` (C) and
    `notedValue_conserved_reachable` (C) as the single "value is notes"
    claim, on top of plain conservation. -/
theorem value_exists_only_as_notes
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (asset cid : Nat)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (held : Nat) (hheld : heldValue s asset cid = held) (hpos : 0 < held) :
    ∃ c, s.holdings asset cid = some c ∧ s.pool.isLive c ∧
      (s.pool.preimageOf c).map NotePreimage.value = some held := by
  unfold heldValue at hheld
  rcases hc : s.holdings asset cid with _ | c
  · rw [hc] at hheld; simp at hheld; omega
  · rw [hc] at hheld
    simp only at hheld
    rcases hp : s.pool.preimageOf c with _ | pre
    · rw [hp] at hheld; simp at hheld; omega
    · rw [hp] at hheld
      simp only [Option.map_some, Option.getD_some] at hheld
      refine ⟨c, rfl, ?_, ?_⟩
      · unfold PoolState.preimageOf at hp
        obtain ⟨q, hq, hqpre⟩ := Option.map_eq_some_iff.mp hp
        have hmem : q ∈ s.pool.liveNotes := List.mem_of_find?_eq_some hq
        have hq1 : q.1 = c := by
          have hb := List.find?_some hq
          simpa using hb
        exact ⟨q.2, by rw [← hq1]; exact hmem⟩
      · rw [hp]; simp [hheld]

/-!
## F. R1 mutation-test misses

`armada-nitro@5519526c:docs/tasks/
R1-adjudicator-rewrite.md` decided: "arn-7c4 (N3) found these
mutation-test misses against `src/ArmadaNitroAdjudicator.sol` on
`integrated`... Each rewrite chunk whose new code covers the old
mutated behavior closes the matching miss with a strengthened test or
names another test that already kills it." No other source records
these five old-code mutant offsets (2549, 2921, 11666, 11738, 11843,
12171, 12743); this deleted brief is the only source for this
empirical fact, cited by its git path (`Adjudicator.lean`'s module
comment names the exception this falls under). These are the Lean
statements of the same five closed gaps.

Statements 19, 21 and 22 formalize the SAME Armada encoding rule
(`State.lean`'s `heldValue` doc comment, stated once there): a balance
is held as one note, and a zero balance is held as no note — itself
Armada's specialization of Nitro-2019-219.pdf §3.1's "If an address
does not appear in the table we take the balance to be zero," and (for
21 and 22) §5.1's payout rule: "the allocation is in priority order...
if A can afford x for B, then `T(A, B, x)`: 1. Reduces the funds held
in channel A by x. 2. Increases the funds held by B by x." The "zero
balance is held as no note" half is the ADJUDICATOR's OWN invariant
over REACHABLE states, not a pool guarantee (`holdings_never_zero_
valued` below states and grounds it: `TransactOwned.circom:117-120`
only range-checks an output value, so a `0`-valued note is a VALID
pool commitment — the adjudicator's own `Step` cases are what keep one
from ever being recorded as a holding). Statement 20 stays an
adjudicator statement; it does not touch the owned-note circuit or the
balance encoding. Statements 21 and 22 are also adjudicator statements
in a second sense: both are about `.transfer`'s own OUTPUT
CONSTRUCTION (`Operations.lean`'s `payoutOutputs`/`holdings` update),
upstream of anything `ArmadaLean.PoolOwned` checks, so neither follows
from a POOL theorem. 23 DOES follow from one, now that
`PoolOwnedSpendStep` (`Notes.lean`) threads `usedNullifiers` through
`ArmadaLean.markSpent` — see its own doc comment.
-/

/-- The adjudicator's own invariant: it never records a `0`-value note
    as a channel's holding — it records NO holding instead.
    `TransactOwned.circom:117-120` only range-checks each output value
    to 120 bits (`Num2Bits(120)`), with no further constraint, so a
    `0`-valued output commitment is a VALID owned-spend output
    (`ArmadaLean.OwnedConstrained`, `TransactOwned.lean`, permits it)
    — this invariant CANNOT come from the pool or the circuit. It is
    the adjudicator's own rule, kept by every `Step` case that writes
    `holdings`: `.deposit` requires `0 < amount` (`Operations.lean`);
    `.transfer` writes `none`, not a `0`-valued commitment, exactly
    when the remainder is `0` (`full_payout_leaves_no_remainder`
    below); `.reclaim` never touches `holdings` at all
    (`s'.holdings = s.holdings`, `Operations.lean`'s `.reclaim` case). -/
theorem holdings_never_zero_valued
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (asset cid c : Nat) (pre : NotePreimage)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hholds : s.holdings asset cid = some c)
    (hpre : s.pool.preimageOf c = some pre) :
    pre.value ≠ 0 := by
  sorry

/-- Closes the `heldValue`'s `commitment == 0` miss (old offset 2549): an
    empty commitment reads as `0`, and — the mutant's blind spot — this
    cannot be confused with a REAL note the pool happens to value at `0`.
    Formalizes the Armada encoding rule's "zero balance is held as no
    note" half (`State.lean`'s `heldValue` doc comment, which also
    states the rule's other half, "a balance is held as one note").
    Needs `Reachable`, unlike a bare fact about `AdjudicatorState`: for
    an ARBITRARY (possibly unreachable) state, a `some c` holding whose
    preimage happens to read back `value = 0` would make `heldValue = 0`
    true while BOTH disjuncts below are false — `holdings_never_zero_
    valued` is exactly what rules that third case out, and it only
    holds over the reachable set. -/
theorem heldValue_zero_iff_no_collateral
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (asset cid : Nat)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) :
    heldValue s asset cid = 0 ↔
      s.holdings asset cid = none ∨
      ∃ c, s.holdings asset cid = some c ∧ s.pool.preimageOf c = none := by
  sorry

/-- Closes the constructor's `configuredAssets[...] = true` miss
    (`armada-nitro@5519526c:docs/tasks/
    R1-adjudicator-rewrite.md`, old offset 2921; no other source records
    this mutant): the configured-asset set never changes after
    deployment — every `Step` case leaves `s'.configuredAssets =
    s.configuredAssets` (`Operations.lean`), so it is exactly the
    deploy-time list for every reachable state. -/
theorem configuredAssets_invariant
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) :
    s.configuredAssets = assets :=
  reachable_preserves (P := fun s => s.configuredAssets = assets) rfl
    (fun actor call s s' hP hstep => (step_configuredAssets sig appRel actor s s' call hstep).trans hP)
    hreach

/-- Closes two of the five `_mintTransferPayout` misses (old offsets
    11666, 11738): an allocation paid exactly `0` mints no note at all —
    `transferEffects`'s `exitAllocations` (`Outcome.lean`) carries a
    position's allocation through `afford` regardless of selection, but
    `.transfer`'s output list (`Operations.lean`, `payoutOutputs`) is built
    by `filterMap`, which drops a `0`-amount entry outright, not a `≤ 0`/
    `< 1` check a mutant could weaken unnoticed. Formalizes the Armada
    encoding rule's "zero balance is held as no note" half for a PAYOUT
    destination (`State.lean`'s `heldValue` doc comment): Nitro-2019-
    219.pdf §3.1 ("an address [with] balance... zero" is simply absent
    from the table) is why a `0`-amount position — a normal outcome of
    §5.1's priority-order `afford` when the channel cannot pay it — must
    mint no note, not a `0`-value one. Adjudicator-level: the filtering
    happens in `Operations.lean`, before `outputPreimages` ever reaches
    `ArmadaLean.PoolOwnedSpendStep`, so this statement does not follow
    from a POOL theorem — it is consistent with, but independent of,
    `ArmadaLean.PoolOwned`'s own `isZeroPreimage`/`recordStep` zero-skip
    convention for the SEPARATE `PreimageRegistry` representation that
    file uses. -/
theorem zero_payout_mints_nothing
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) (dest : Allocation)
    (hdest : dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations) (hzero : dest.amount = 0) :
    ¬ ∃ pre : NotePreimage, pre.npk = dest.destination ∧ pre.value = 0 ∧
        (commitment pre.npk pre.token pre.value, pre) ∈ s'.pool.liveNotes ∧
        (commitment pre.npk pre.token pre.value, pre) ∉ s.pool.liveNotes := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨hpoolstep, _hholdseq, _hchanseq⟩ := hrest
  obtain ⟨_, _, _, hliveeq, _⟩ := hpoolstep
  rintro ⟨pre, _hnpk, hval, hin', hnin⟩
  rw [hliveeq] at hin'
  rcases List.mem_append.mp hin' with hc1 | hc2
  · exact hnin (List.mem_filter.mp hc1).1
  · obtain ⟨opre, hopre_mem, hopre_eq⟩ := List.mem_map.mp hc2
    have hpre_eq : opre = pre := (Prod.mk.injEq _ _ _ _ ▸ hopre_eq : _ ∧ opre = pre).2
    rw [hpre_eq] at hopre_mem
    rcases List.mem_append.mp hopre_mem with hc2a | hc2b
    · obtain ⟨a, _ha_mem, hfm⟩ := List.mem_filterMap.mp hc2a
      by_cases hamt : a.amount = 0
      · rw [if_pos hamt] at hfm; exact absurd hfm (by simp)
      · rw [if_neg hamt] at hfm
        have hveq : pre.value = a.amount := by
          have := Option.some.inj hfm
          rw [← this]
        rw [hveq] at hval
        exact hamt hval
    · split at hc2b
      · exact absurd hc2b List.not_mem_nil
      · rename_i hne
        rw [List.mem_singleton] at hc2b
        rw [hc2b] at hval
        simp only at hval
        exact hne hval

/-- Closes two more `_mintTransferPayout` misses (old offsets 11843,
    12171): a remainder note is minted only when the remainder is
    strictly positive — a full payout (every index selected, or
    `indices = []`, and `totalPayouts = heldValue`) leaves `holdings[
    asset][cid] = none`, never a dangling `0`-value commitment.
    Formalizes the Armada encoding rule's "zero balance is held as no
    note" half for the ADJUDICATOR's OWN remainder (`State.lean`'s
    `heldValue` doc comment): Nitro-2019-219.pdf §5.1's `T(A, B, x)`,
    "Reduces the funds held in channel A by x" — a FULL payout (`x =
    heldValue`) reduces A's held funds to exactly zero, which §3.1's "an
    address [with] balance... zero" is absent from the table" and the
    Armada encoding rule together require to be `none`, not a `0`-value
    commitment. Adjudicator-level, like `zero_payout_mints_nothing`: the
    `if remainder = 0 then none else ...` branch is `Operations.lean`'s
    own `holdings` update, not a fact `ArmadaLean.PoolOwned` states. -/
theorem full_payout_leaves_no_remainder
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length)
    (hfull :
      (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 =
      heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) :
    s'.holdings (outcome.get ⟨assetIndex, h⟩).asset cid = none := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨_hpoolstep, hholdseq, _hchanseq⟩ := hrest
  have hidx_eq : (⟨assetIndex, hidx⟩ : Fin outcome.length) = ⟨assetIndex, h⟩ := rfl
  rw [hidx_eq] at hholdseq
  change s'.holdings = update s.holdings (outcome.get ⟨assetIndex, h⟩).asset
      (update (s.holdings (outcome.get ⟨assetIndex, h⟩).asset) cid
        (if heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
            (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 = 0
         then none
         else some (commitment s.self (outcome.get ⟨assetIndex, h⟩).asset
           (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
             (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2)))) at hholdseq
  simp only [hfull, Nat.sub_self, if_true] at hholdseq
  rw [hholdseq]
  show (update s.holdings (outcome.get ⟨assetIndex, h⟩).asset
      (update (s.holdings (outcome.get ⟨assetIndex, h⟩).asset) cid none))
      (outcome.get ⟨assetIndex, h⟩).asset cid = none
  unfold update
  simp

/-- Closes the fifth `_mintTransferPayout` miss (old offset 12743): the
    old collateral commitment is nullified if and only if one existed —
    an unfunded channel's `transfer` call nullifies nothing. A
    CONSEQUENCE of a pool theorem:
    `PoolOwnedSpendStep` (`Notes.lean`) threads `usedNullifiers` through
    `ArmadaLean.markSpent` (`PoolOwned.lean`), with `N = (if
    nullifiedCommitment.isSome then 1 else 0)` nullifiers submitted.
    `N = 0` makes `List.ofFn pub.nullifiers = []`, and `markSpent spent []
    = some spent` by definition — `usedNullifiers` is UNCHANGED exactly
    when there was no prior holding. `N = 1` makes `markSpent` succeed
    only by `ArmadaLean.owned_no_double_spend`'s converse,
    `ArmadaLean.markSpent_succeeds`, appending exactly one FRESH nullifier
    — `usedNullifiers` CHANGES exactly when there was a prior holding. -/
theorem nullify_iff_commitment_was_some
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex cid claimedStateHash : Nat)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    (s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid = none) ↔
      s'.pool.usedNullifiers = s.pool.usedNullifiers := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨hpoolstep, _hholdseq, _hchanseq⟩ := hrest
  obtain ⟨_htoken, _hiscase, hex3, _hliveeq, _hsignedeq⟩ := hpoolstep
  obtain ⟨N, pub, _hself2, _hverify, _hcommits, hNeq, _hwitness, hmarkspent⟩ := hex3
  have hidx_eq : (⟨assetIndex, hidx⟩ : Fin outcome.length) = ⟨assetIndex, h⟩ := rfl
  rw [hidx_eq] at hNeq
  constructor
  · intro hnone
    rw [hnone] at hNeq
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hNeq
    subst hNeq
    rw [List.ofFn_zero] at hmarkspent
    unfold markSpent at hmarkspent
    exact (Option.some.inj hmarkspent).symm
  · intro hpost
    rcases hcase : s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid with _ | c
    · rfl
    · exfalso
      rw [hcase] at hNeq
      simp only [Option.isSome_some, if_true] at hNeq
      subst hNeq
      rw [List.ofFn_succ, List.ofFn_zero] at hmarkspent
      rw [markSpent_single] at hmarkspent
      split at hmarkspent
      · exact absurd hmarkspent (by simp)
      · have heq := Option.some.inj hmarkspent
        rw [← heq] at hpost
        have hlen : (pub.nullifiers 0 :: s.pool.usedNullifiers).length = s.pool.usedNullifiers.length := by
          rw [hpost]
        simp at hlen

end ArmadaLean.Adjudicator
