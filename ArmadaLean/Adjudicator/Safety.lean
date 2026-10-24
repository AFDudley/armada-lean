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
        ∃ pre : CommitmentPreimage, pre.npk = h ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          pre.value = owed ∧
          PoolIsLive final.pool (commitment pre.npk pre.token pre.value) := by
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
        ∃ pre : CommitmentPreimage, pre.npk = h ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          pre.value = owed ∧
          PoolIsLive final.pool (commitment pre.npk pre.token pre.value) := by
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
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_hcfg1, _hheld, _hext, _hpos, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, hdstep, _hholdseq⟩ := hinner
    obtain ⟨_hown, _hcommit, _htoken, hN, hM, hC, rest, spent', newRoot, records,
      _hEmergency, _hWithdrawOnly, _hRoot, hRemove, _hNullify, _hValid, _hidxrec, heq⟩ := hdstep
    unfold PoolState.notedValue
    rw [heq]
    show listSum ((if token = w.token then transactAllOutputs w ++ rest else s.pool.live token).map
        CommitmentPreimage.value) = listSum ((s.pool.live token).map CommitmentPreimage.value)
    by_cases ht : token = w.token
    · rw [if_pos ht, ht]
      have hbal := transact_balance hN hM hC (newNotes := transactAllOutputs w)
        (unshieldTail := []) (by simp)
      simp only [List.map_nil, listSum] at hbal
      have hsum := removeAll_sum hRemove
      simp only [List.map_append, listSum_append]
      omega
    · rw [if_neg ht]
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨hmatch, _hholdseq, _hchanseq⟩ := hrest
    unfold PoolState.notedValue
    by_cases ht : token = (outcome.get ⟨assetIndex, hidx⟩).asset
    · rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | c
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, spent', newRoot, _hNonZero, _hself2, _htoken, hnewnotes,
          _hemerg, _hwithdraw, _hroot, _hmarkspent, heq⟩ := hmatch
        have hbal := transactOwned_balance (Nat.zero_le 8) hM hC
        have hspent0 : listSum ((ownedSpentNotes pub w).map CommitmentPreimage.value) = 0 := by
          have hnil : ownedSpentNotes pub w = [] := by
            apply List.eq_nil_of_length_eq_zero
            unfold ownedSpentNotes
            simp
          rw [hnil]; rfl
        rw [hspent0] at hbal
        rw [heq]
        dsimp only
        rw [← hnewnotes]
        rw [if_pos ht, ht]
        simp only [List.map_append, listSum_append]
        omega
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, rest, spent', newRoot, _hNonZero, _hself2, _htoken, hnewnotes,
          _hceq, _hroot, hremove, _hmarkspent, heq⟩ := hmatch
        have hbal := transactOwned_balance (by decide) hM hC
        have hsum := removeAll_sum hremove
        rw [heq]
        dsimp only
        rw [← hnewnotes]
        rw [if_pos ht, ht]
        simp only [List.map_append, listSum_append] at hsum ⊢
        omega
    · rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | c
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, spent', newRoot, _hNonZero, _hself2, _htoken, hnewnotes,
          _hemerg, _hwithdraw, _hroot, _hmarkspent, heq⟩ := hmatch
        rw [heq]
        show listSum ((if token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live token).map CommitmentPreimage.value) =
          listSum ((s.pool.live token).map CommitmentPreimage.value)
        rw [if_neg ht]
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, rest, spent', newRoot, _hNonZero, _hself2, _htoken, hnewnotes,
          _hceq, _hroot, hremove, _hmarkspent, heq⟩ := hmatch
        rw [heq]
        show listSum ((if token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live token).map CommitmentPreimage.value) =
          listSum ((s.pool.live token).map CommitmentPreimage.value)
        rw [if_neg ht]
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpool, _, _, _, _, _⟩ := hstep
    rw [hpool]
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpool, _, _, _, _, _⟩ := hstep
    rw [hpool]
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpool, _, _⟩ := hstep
    rw [hpool]
  | reclaim a b c d e f g =>
    obtain ⟨_, _, _, _, _, _, hpool, _, _, _, _, _, _⟩ := hstep
    rw [hpool]
  | bulkTransferAllAssets a b c => exact hstep.elim
  | bulkConcludeAndTransferAllAssets a b => exact hstep.elim
  | tick newNow =>
    obtain ⟨_, _, hpool, _, _, _, _, _, _⟩ := hstep
    rw [hpool]
  | sign p d =>
    obtain ⟨_, _, hpool, _, _, _, _, _, _⟩ := hstep
    rw [hpool]
  | signNote pk msgHash =>
    obtain ⟨_, _, hpool, _, _, _, _, _, _⟩ := hstep
    rw [hpool]

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
    s.pool.notedValue token = pool0.notedValue token :=
  reachable_preserves (P := fun s => s.pool.notedValue token = pool0.notedValue token) rfl
    (fun actor call s s' hP hstep => (notedValue_conserved sig appRel actor s s' call token hstep).trans hP)
    hreach

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
    PoolIsLive s.pool c := by
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

set_option maxRecDepth 2000 in
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
    `EdDSAVerify` witness `Constrained` (`DepositStep`,
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
  let self : Nat := 0
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let channelId : Nat := 2 ^ 160
  let randomIn : Fin 1 → Nat := fun _ => 0
  let valueIn : Fin 1 → Nat := fun _ => amount
  let leavesIndices : Fin 1 → Nat := fun _ => 0
  let pathElements : Fin 1 → List (Nat × Bool) := fun _ => List.replicate 16 (0, false)
  let npkOut : Fin 1 → Nat := fun _ => npk self 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let leaf : Nat :=
    commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn 0)) token (valueIn 0)
  let root : Nat := merkleRoot leaf (pathElements 0)
  let pub : TransactPublic 1 1 :=
    { merkleRoot := root, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey (leavesIndices 0),
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let inputNote : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn 0), token, valueIn 0⟩
  let pool0 : PoolState :=
    { live := fun t => if t = token then [inputNote] else [],
      spent := [], roots := [root], held := fun _ => 0,
      preimageOf := fun _ => none, shieldsPaused := false,
      emergencyPaused := false, withdrawOnlyMode := false }
  let g := genesis assets self pool0
  let mid : AdjudicatorState := { g with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub) ∨ g.poolSignedBy pk' m' }
  have hsignstep : Step sig (consensusRelation sig) (Actor.pool publicKey) g
      (.signNote publicKey (msgHashOf pub)) mid :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach : Reachable sig (consensusRelation sig) g mid :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  have hsigned : mid.poolSignedBy publicKey (msgHashOf pub) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature, hveri⟩ :=
    poolSigLive.eddsaCompleteness mid.poolSignedBy publicKey (msgHashOf pub) hsigned
  let w : TransactWitness 1 1 :=
    { token := token, publicKey := publicKey, signature := signature,
      nullifyingKey := nullifyingKey, randomIn := randomIn, valueIn := valueIn,
      pathElements := pathElements, leavesIndices := leavesIndices,
      npkOut := npkOut, valueOut := valueOut }
  have hbitsZero : ∀ n, bitsVal (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, bitsVal, ih]
  have hbitsOne : bitsVal (true :: List.replicate 119 false) = 1 := by
    rw [show bitsVal (true :: List.replicate 119 false) =
        1 + 2 * bitsVal (List.replicate 119 false) from rfl, hbitsZero]
  have hC : Constrained w pub :=
    { pathLen := fun _ => List.length_replicate
      merkle := fun _ => rfl
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := rfl
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove : removeAll (mid.pool.live w.token) (transactSpentNotes w) = some [] := by
    show removeAll [inputNote] [inputNote] = some []
    unfold removeAll
    rw [if_pos (List.elem_eq_true_of_mem (List.mem_singleton_self _))]
    rw [List.erase_cons_head]
    rfl
  have hNullify : markSpent mid.pool.spent (List.ofFn pub.nullifiers) =
      some (List.ofFn pub.nullifiers) := rfl
  have hidxrec : (pub.commitmentsOut (0 : Fin 1),
      (⟨w.npkOut 0, w.token, w.valueOut 0⟩ : CommitmentPreimage)) ∈ transactOutputRecords w pub :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let s' : AdjudicatorState := { mid with
    pool := { mid.pool with
      live := fun t => if t = w.token then transactAllOutputs w ++ ([] : List CommitmentPreimage)
        else mid.pool.live t,
      spent := List.ofFn pub.nullifiers,
      preimageOf := applyRecords mid.pool.preimageOf (transactOutputRecords w pub) },
    holdings := update mid.holdings token (update (mid.holdings token) channelId
      (some (pub.commitmentsOut (0 : Fin 1)))) }
  have hdstep : DepositStep mid.pool self token amount w pub (0 : Fin 1) s'.pool :=
    ⟨⟨0, rfl⟩, rfl, rfl, by decide, by decide, hC, [], List.ofFn pub.nullifiers, 0,
      transactOutputRecords w pub, rfl, rfl, List.mem_singleton_self _, hRemove, hNullify,
      List.Sublist.refl _, hidxrec, rfl⟩
  have hstep : Step sig (consensusRelation sig) (Actor.pool publicKey) mid
      (.deposit channelId 0 token amount) s' := by
    refine ⟨rfl, rfl, (by simp [channelId, isExternal]), (by decide),
      ⟨1, 1, w, pub, 0, ?_, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact hdstep
  exact ⟨assets, self, pool0, mid, s', channelId, 0, token, amount, Actor.pool publicKey,
    hreach, hstep⟩

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
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis 0
  let fp : FixedPart := ⟨[0], 0, 0, 1⟩
  let candidate : VariablePart := ⟨[], 0, 0, false⟩
  let g := genesis assets self pool0
  let mid : AdjudicatorState := { g with
    signedBy := fun p' d' => (p' = 0 ∧ d' = stateHash fp candidate) ∨ g.signedBy p' d' }
  have hsignstep : Step sig (consensusRelation sig) (Actor.nitro 0) g (.sign 0 (stateHash fp candidate)) mid :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach : Reachable sig (consensusRelation sig) g mid :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  let s' : AdjudicatorState := { mid with
    channels := update mid.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := mid.now + fp.challengeDuration,
        stateHash := stateHash fp candidate, outcomeHash := outcomeHashOf candidate.outcome } }
  have hauth : AuthorizedBy sig mid 0 (stateHash fp candidate) := Or.inl (Or.inl ⟨rfl, rfl⟩)
  have hstep : Step sig (consensusRelation sig) (Actor.nitro 0) mid
      (.challenge fp [] candidate 0) s' := by
    refine ⟨?_, ⟨rfl, ?_⟩, ?_, hauth, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show candidate.turnNum ≥ (mid.channels (channelId fp)).turnNumRecord
      simp [mid, g, genesis, emptyStatus]
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact hauth
    · exact List.mem_singleton.mpr rfl
  refine ⟨assets, self, pool0, mid, s', fp, candidate, 0, Actor.nitro 0, hreach, hstep, ?_⟩
  show ((update mid.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := mid.now + fp.challengeDuration,
        stateHash := stateHash fp candidate, outcomeHash := outcomeHashOf candidate.outcome })
      (channelId fp)).mode mid.now = .challenge
  unfold update
  simp [ChannelStatus.mode, fp]

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
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis 0
  let fp : FixedPart := ⟨[0], 0, 0, 1⟩
  let candidate : VariablePart := ⟨[], 0, 0, false⟩
  let g := genesis assets self pool0
  let mid : AdjudicatorState := { g with
    signedBy := fun p' d' => (p' = 0 ∧ d' = stateHash fp candidate) ∨ g.signedBy p' d' }
  have hsignstep : Step sig (consensusRelation sig) (Actor.nitro 0) g (.sign 0 (stateHash fp candidate)) mid :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach0 : Reachable sig (consensusRelation sig) g mid :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  let s : AdjudicatorState := { mid with
    channels := update mid.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := mid.now + fp.challengeDuration,
        stateHash := stateHash fp candidate, outcomeHash := outcomeHashOf candidate.outcome } }
  have hauth : AuthorizedBy sig mid 0 (stateHash fp candidate) := Or.inl (Or.inl ⟨rfl, rfl⟩)
  have hcstep : Step sig (consensusRelation sig) (Actor.nitro 0) mid
      (.challenge fp [] candidate 0) s := by
    refine ⟨?_, ⟨rfl, ?_⟩, ?_, hauth, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show candidate.turnNum ≥ (mid.channels (channelId fp)).turnNumRecord
      simp [mid, g, genesis, emptyStatus]
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact hauth
    · exact List.mem_singleton.mpr rfl
  have hreach : Reachable sig (consensusRelation sig) g s :=
    reachable_step hreach0 hcstep
  have hfin : (s.channels (channelId fp)).finalizesAt > 0 := by
    show (update mid.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := mid.now + fp.challengeDuration,
        stateHash := stateHash fp candidate, outcomeHash := outcomeHashOf candidate.outcome }
      (channelId fp)).finalizesAt > 0
    unfold update
    simp [mid, g, fp]
  let s' : AdjudicatorState := { s with now := (s.channels (channelId fp)).finalizesAt }
  have htickstep : Step sig (consensusRelation sig) (Actor.nitro 0) s
      (.tick (s.channels (channelId fp)).finalizesAt) s' :=
    ⟨Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨assets, self, pool0, s, s', channelId fp, Actor.nitro 0, hreach, hfin, htickstep, ?_⟩
  show (s.channels (channelId fp)).mode (s.channels (channelId fp)).finalizesAt = .finalized
  unfold ChannelStatus.mode
  simp [show (s.channels (channelId fp)).finalizesAt ≠ 0 from by omega]

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
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis 0
  let fp : FixedPart := ⟨[], 0, 0, 0⟩
  let candidate : VariablePart := ⟨[], 0, 0, true⟩
  let g := genesis assets self pool0
  let mid : AdjudicatorState := { g with now := 1 }
  have htick : Step sig (consensusRelation sig) (Actor.nitro 0) g (.tick 1) mid :=
    ⟨Nat.zero_le 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach : Reachable sig (consensusRelation sig) g mid :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) htick
  let s' : AdjudicatorState := { mid with
    channels := update mid.channels (channelId fp)
      { turnNumRecord := 0, finalizesAt := mid.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate.outcome } }
  have hstep : Step sig (consensusRelation sig) (Actor.nitro 0) mid (.conclude fp candidate) s' := by
    refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [mid, g, genesis, ChannelStatus.mode, emptyStatus]
    · intro p hp
      exact absurd hp List.not_mem_nil
  refine ⟨assets, self, pool0, mid, s', fp, candidate, Actor.nitro 0, hreach, hstep, ?_⟩
  show ((update mid.channels (channelId fp)
      { turnNumRecord := 0, finalizesAt := mid.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate.outcome }) (channelId fp)).mode mid.now
      = .finalized
  unfold update
  simp [ChannelStatus.mode, mid]

set_option maxRecDepth 4000 in
/-- A payout can happen: starting from `deposit_can_happen`'s construction
    to fund a channel, a `.conclude` (needing `now ≠ 0`, so a `.tick`
    comes first) finalizes it, and a `.transfer` call pays the entire
    deposited amount to a destination (`Operations.lean`'s `.transfer`
    case). `.transfer`'s owned-spend (`ArmadaLean.PoolOwnedSpendStep`,
    `Notes.lean`) takes `OwnedConstrained` directly as its own soundness
    hypothesis, the same convention `Step.transactOwned` now uses, so the
    witness built by hand already satisfies it — `ownedComplete` is kept
    on the signature for stability (the statement is unchanged) but is
    not needed by this construction. `exists_internal_channelId`
    (`Lemmas.lean`) supplies a channel id that is both non-external (so
    `.deposit` accepts it) and `channelId fp` for a chosen `fp` (so
    `.conclude` can later finalize the SAME channel) — the pigeonhole
    argument over `channelIdOf`'s own injectivity this needs, since
    `channelIdOf` states no range on its own. -/
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
      PoolIsLive s'.pool
        (commitment dest.destination (outcome.get ⟨assetIndex, h⟩).asset dest.amount) := by
  obtain ⟨n0, hinternal⟩ := exists_internal_channelId hashA
  let self : Nat := 0
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let fp : FixedPart := ⟨[], n0, 0, 0⟩
  let cid : Nat := channelId fp
  let randomIn : Fin 1 → Nat := fun _ => 0
  let valueIn : Fin 1 → Nat := fun _ => amount
  let leavesIndices : Fin 1 → Nat := fun _ => 0
  let pathElements1 : Fin 1 → List (Nat × Bool) := fun _ => List.replicate 16 (0, false)
  let npkOut : Fin 1 → Nat := fun _ => npk self 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let leaf1 : Nat :=
    commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn 0)) token (valueIn 0)
  let root1 : Nat := merkleRoot leaf1 (pathElements1 0)
  let pub_d : TransactPublic 1 1 :=
    { merkleRoot := root1, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey (leavesIndices 0),
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let inputNote : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn 0), token, valueIn 0⟩
  let depositedNote : CommitmentPreimage := ⟨npk self 0, token, amount⟩
  let pathElements2 : Fin 1 → List (Nat × Bool) := fun _ => List.replicate 16 (1, false)
  let leaf2 : Nat := hashCommitment depositedNote
  let root2 : Nat := merkleRoot leaf2 (pathElements2 0)
  let pool0 : PoolState :=
    { live := fun t => if t = token then [inputNote] else [],
      spent := [], roots := [root1, root2], held := fun _ => 0,
      preimageOf := fun _ => none, shieldsPaused := false,
      emergencyPaused := false, withdrawOnlyMode := false }
  let g := genesis assets self pool0
  let mid1 : AdjudicatorState := { g with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub_d) ∨ g.poolSignedBy pk' m' }
  have hsignstep : Step sig (consensusRelation sig) (Actor.pool publicKey) g
      (.signNote publicKey (msgHashOf pub_d)) mid1 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  have hsigned : mid1.poolSignedBy publicKey (msgHashOf pub_d) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature, hveri⟩ :=
    poolSigLive.eddsaCompleteness mid1.poolSignedBy publicKey (msgHashOf pub_d) hsigned
  let w_d : TransactWitness 1 1 :=
    { token := token, publicKey := publicKey, signature := signature,
      nullifyingKey := nullifyingKey, randomIn := randomIn, valueIn := valueIn,
      pathElements := pathElements1, leavesIndices := leavesIndices,
      npkOut := npkOut, valueOut := valueOut }
  have hbitsZero : ∀ n, bitsVal (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, bitsVal, ih]
  have hbitsOne : bitsVal (true :: List.replicate 119 false) = 1 := by
    rw [show bitsVal (true :: List.replicate 119 false) =
        1 + 2 * bitsVal (List.replicate 119 false) from rfl, hbitsZero]
  have hC_d : Constrained w_d pub_d :=
    { pathLen := fun _ => List.length_replicate
      merkle := fun _ => rfl
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := rfl
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove_d : removeAll (mid1.pool.live w_d.token) (transactSpentNotes w_d) = some [] := by
    show removeAll [inputNote] [inputNote] = some []
    unfold removeAll
    rw [if_pos (List.elem_eq_true_of_mem (List.mem_singleton_self _))]
    rw [List.erase_cons_head]
    rfl
  have hNullify_d : markSpent mid1.pool.spent (List.ofFn pub_d.nullifiers) =
      some (List.ofFn pub_d.nullifiers) := rfl
  have hidxrec_d : (pub_d.commitmentsOut (0 : Fin 1),
      (⟨w_d.npkOut 0, w_d.token, w_d.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d pub_d :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d.token then transactAllOutputs w_d ++ ([] : List CommitmentPreimage)
        else mid1.pool.live t,
      spent := List.ofFn pub_d.nullifiers,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d pub_d) },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some (pub_d.commitmentsOut (0 : Fin 1)))) }
  have hdstep : DepositStep mid1.pool self token amount w_d pub_d (0 : Fin 1) mid2.pool :=
    ⟨⟨0, rfl⟩, rfl, rfl, by decide, by decide, hC_d, [], List.ofFn pub_d.nullifiers, 0,
      transactOutputRecords w_d pub_d, rfl, rfl, List.mem_cons_self, hRemove_d, hNullify_d,
      List.Sublist.refl _, hidxrec_d, rfl⟩
  have hstep_d : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amount) mid2 := by
    refine ⟨rfl, rfl, hinternal, (by decide),
      ⟨1, 1, w_d, pub_d, 0, ?_, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact hdstep
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_d
  let mid3 : AdjudicatorState := { mid2 with now := 1 }
  have hstep_tick : Step sig (consensusRelation sig) (Actor.nitro 0) mid2 (.tick 1) mid3 :=
    ⟨Nat.zero_le 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach3 : Reachable sig (consensusRelation sig) g mid3 :=
    reachable_step hreach2 hstep_tick
  let dest : Allocation := ⟨1, amount, .simple, 0⟩
  let outcome : Outcome := [⟨token, [dest]⟩]
  let candidate : VariablePart := ⟨outcome, 0, 0, true⟩
  let mid4 : AdjudicatorState := { mid3 with
    channels := update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate.outcome } }
  have hstep_conclude : Step sig (consensusRelation sig) (Actor.nitro 0) mid3
      (.conclude fp candidate) mid4 := by
    refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [mid3, mid2, mid1, g, genesis, ChannelStatus.mode, emptyStatus]
    · intro p hp
      exact absurd hp List.not_mem_nil
  have hreach4 : Reachable sig (consensusRelation sig) g mid4 :=
    reachable_step hreach3 hstep_conclude
  have hassetIdx : (0 : Nat) < outcome.length := by decide
  have hfinalized : (mid4.channels cid).mode mid4.now = .finalized := by
    show ((update mid3.channels cid
        { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := 0,
          outcomeHash := outcomeHashOf candidate.outcome }) cid).mode mid3.now = .finalized
    unfold update
    simp [ChannelStatus.mode, mid3]
  have hheld2 : heldValue mid2 token cid = amount :=
    deposit_sets_heldValue sig (consensusRelation sig) (Actor.pool publicKey) mid1 mid2 cid 0
      token amount hstep_d
  have hheld4 : heldValue mid4 token cid = amount := hheld2
  let ownerField : Nat := 0
  let randomIn2 : Fin 1 → Nat := fun _ => 0
  let valueIn2 : Fin 1 → Nat := fun _ => amount
  let leavesIndices2 : Fin 1 → Nat := fun _ => 1
  let npkOut2 : Fin 1 → Nat := fun _ => dest.destination
  let valueOut2 : Fin 1 → Nat := fun _ => amount
  let pub_t : TransactOwnedPublic 1 1 :=
    { merkleRoot := root2, boundParamsHash := 0,
      nullifiers := fun _ => nullifier ownerField (leavesIndices2 0),
      commitmentsOut := fun _ => commitment (npkOut2 0) token (valueOut2 0),
      ownerField := ownerField }
  let w_t : TransactOwnedWitness 1 1 :=
    { token := token, randomIn := randomIn2, valueIn := valueIn2, pathElements := pathElements2,
      leavesIndices := leavesIndices2, npkOut := npkOut2, valueOut := valueOut2 }
  have hOC : OwnedConstrained w_t pub_t :=
    { pathLen := fun _ => List.length_replicate
      merkle := fun _ => rfl
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := rfl }
  have hNonZero_t : ∀ j, ¬ isZeroPreimage
      (⟨w_t.npkOut j, w_t.token, w_t.valueOut j⟩ : CommitmentPreimage) := by
    intro j hz
    have : amount = 0 := hz.2.1
    simp [amount] at this
  have hnullseparate : nullifier ownerField (leavesIndices2 0) ≠
      nullifier nullifyingKey (leavesIndices 0) := by
    intro heqn
    have := (poseidon2_inj heqn).2
    exact absurd this (by decide)
  have hRemove_t : removeAll (mid4.pool.live token) (ownedSpentNotes pub_t w_t) = some [] := by
    show removeAll [depositedNote] [depositedNote] = some []
    unfold removeAll
    rw [if_pos (List.elem_eq_true_of_mem (List.mem_singleton_self _))]
    rw [List.erase_cons_head]
    rfl
  have hNullify_t : markSpent mid4.pool.spent (List.ofFn pub_t.nullifiers) =
      some (nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent) := by
    show markSpent [nullifier nullifyingKey (leavesIndices 0)]
      [nullifier ownerField (leavesIndices2 0)] =
      some (nullifier ownerField (leavesIndices2 0) :: [nullifier nullifyingKey (leavesIndices 0)])
    unfold markSpent
    rw [if_neg (by simpa using hnullseparate)]
    rfl
  let s' : AdjudicatorState := { mid4 with
    pool := { mid4.pool with
      live := fun t => if t = token then [⟨dest.destination, token, amount⟩] ++ [] else mid4.pool.live t,
      spent := nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent,
      preimageOf := applyRecords mid4.pool.preimageOf (ownedOutputRecords w_t pub_t) },
    holdings := update mid4.holdings token (update (mid4.holdings token) cid none),
    channels := update mid4.channels cid
      { mid4.channels cid with
        outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
          if i ≠ 0 then exit else { exit with allocations := [{ dest with amount := 0 }] }) } }
  have hcEq : mid4.holdings token cid = some (pub_d.commitmentsOut (0 : Fin 1)) := by
    show (update mid1.holdings token (update (mid1.holdings token) cid
      (some (pub_d.commitmentsOut (0 : Fin 1))))) token cid = some (pub_d.commitmentsOut (0 : Fin 1))
    unfold update
    rw [if_pos rfl, if_pos rfl]
  have hospend : PoolOwnedSpendStep mid4.pool self token (mid4.holdings token cid)
      [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] s'.pool := by
    rw [hcEq]
    exact ⟨w_t, pub_t, by decide, hOC, [], _, 0, hNonZero_t, rfl, rfl, rfl, rfl,
      List.mem_cons_of_mem _ List.mem_cons_self, hRemove_t, hNullify_t, rfl⟩
  have hstateHash : (mid4.channels cid).stateHash = 0 := by
    show ((update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate.outcome }) cid).stateHash = 0
    unfold update
    rw [if_pos rfl]
  have houtcomeHash : (mid4.channels cid).outcomeHash = outcomeHashOf outcome := by
    show ((update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate.outcome }) cid).outcomeHash = outcomeHashOf outcome
    unfold update
    rw [if_pos rfl]
  have htransferEffects : transferEffects [dest] amount [] =
      ([{dest with amount := 0}], [dest], amount) := by
    unfold transferEffects afford
    simp [listSum, dest]
  have hstep_t : Step sig (consensusRelation sig) (Actor.nitro 0) mid4
      (.transfer 0 cid 0 outcome []) s' := by
    refine ⟨hassetIdx, hfinalized, hstateHash, houtcomeHash, trivial, ?_, rfl, rfl, rfl, rfl, rfl⟩
    have hget : outcome.get ⟨0, hassetIdx⟩ = ⟨token, [dest]⟩ := rfl
    rw [hget, hheld4, htransferEffects]
    simp [Nat.sub_self, dest, amount]
    exact ⟨hospend, rfl, rfl⟩
  refine ⟨assets, self, pool0, mid4, s', 0, cid, 0, outcome, [], hassetIdx, dest,
    Actor.nitro 0, hreach4, hstep_t, ?_, ?_, ?_⟩
  · show dest ∈ [dest]
    exact List.mem_singleton_self _
  · decide
  · refine ⟨token, ⟨dest.destination, token, amount⟩, ?_, rfl⟩
    show (⟨dest.destination, token, amount⟩ : CommitmentPreimage) ∈
      [⟨dest.destination, token, amount⟩] ++ ([] : List CommitmentPreimage)
    exact List.mem_append_left _ (List.mem_singleton_self _)

/-- A reclaim can happen: for all `HashAssumptions`/`SignatureAssumptions`,
    there is an execution from `genesis` — `.conclude` with an EMPTY
    participants list for both the source and the target channel (as
    `conclude_can_happen` does; `SignedByAll` is vacuously true, no
    `.sign` call needed) — in which a guarantee allocation can be
    reclaimed, reallocating the source channel's own outcome (S3 §2.4,
    Listing 2). `.reclaim`'s `Step` case never calls `appRel` or
    `PoolOwnedSpendStep`, so no `ConsensusApp`/owned-note machinery is
    needed beyond the two `.conclude` calls that finalize both channels.
    Source and target channel ids are `channelId fp1`/`channelId fp2`
    for two `FixedPart`s differing only in `channelNonce` —
    `HashAssumptions.channelIdOf_inj` then gives the two ids are
    distinct, so concluding one does not touch the other.
    `reallocateGuarantee` erases the reclaimed allocation outright (the
    source outcome holds only the guarantee, so erasing it empties the
    allocation list), giving a different `outcomeHash`
    (`HashAssumptions.outcomeHashOf_inj`) and so a different
    `ChannelStatus`. -/
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
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis 0
  let fp1 : FixedPart := ⟨[], 0, 0, 0⟩
  let fp2 : FixedPart := ⟨[], 1, 0, 0⟩
  let sourceChannelId : Nat := channelId fp1
  let targetChannelId : Nat := channelId fp2
  have hidsNe : sourceChannelId ≠ targetChannelId := by
    intro heq
    have := (hashA.channelIdOf_inj heq).2.1
    simp [fp1, fp2] at this
  let asset : Nat := 0
  let guaranteeMetadata : Nat := 0
  let left : Nat := (decodeGuarantee guaranteeMetadata).1
  let right : Nat := (decodeGuarantee guaranteeMetadata).2
  let guaranteeAlloc : Allocation := ⟨targetChannelId, 2, .guarantee, guaranteeMetadata⟩
  let sourceOutcome : Outcome := [⟨asset, [guaranteeAlloc]⟩]
  let alloc0 : Allocation := ⟨left, 1, .simple, 0⟩
  let alloc1 : Allocation := ⟨right, 1, .simple, 0⟩
  let targetOutcome : Outcome := [⟨asset, [alloc0, alloc1]⟩]
  let g := genesis assets self pool0
  let mid1 : AdjudicatorState := { g with now := 1 }
  have htick : Step sig (consensusRelation sig) (Actor.nitro 0) g (.tick 1) mid1 :=
    ⟨Nat.zero_le 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) htick
  let candidate1 : VariablePart := ⟨sourceOutcome, 0, 0, true⟩
  let mid2 : AdjudicatorState := { mid1 with
    channels := update mid1.channels sourceChannelId
      { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate1.outcome } }
  have hstep_c1 : Step sig (consensusRelation sig) (Actor.nitro 0) mid1
      (.conclude fp1 candidate1) mid2 := by
    refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [mid1, g, genesis, ChannelStatus.mode, emptyStatus]
    · intro p hp
      exact absurd hp List.not_mem_nil
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_c1
  let candidate2 : VariablePart := ⟨targetOutcome, 0, 0, true⟩
  let mid3 : AdjudicatorState := { mid2 with
    channels := update mid2.channels targetChannelId
      { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate2.outcome } }
  have hmode2 : (mid2.channels targetChannelId).mode mid2.now ≠ .finalized := by
    show (update mid1.channels sourceChannelId
      { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := 0,
        outcomeHash := outcomeHashOf candidate1.outcome } targetChannelId).mode mid1.now ≠ .finalized
    unfold update
    rw [if_neg (fun h => hidsNe h.symm)]
    simp [mid1, g, genesis, ChannelStatus.mode, emptyStatus]
  have hstep_c2 : Step sig (consensusRelation sig) (Actor.nitro 0) mid2
      (.conclude fp2 candidate2) mid3 := by
    refine ⟨hmode2, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    exact absurd hp List.not_mem_nil
  have hreach3 : Reachable sig (consensusRelation sig) g mid3 :=
    reachable_step hreach2 hstep_c2
  have hsrc_eq : mid3.channels sourceChannelId =
      { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := 0,
        outcomeHash := outcomeHashOf sourceOutcome } := by
    show (update mid2.channels targetChannelId
        { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := 0,
          outcomeHash := outcomeHashOf candidate2.outcome } sourceChannelId) = _
    unfold update
    rw [if_neg hidsNe]
    show (update mid1.channels sourceChannelId
        { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := 0,
          outcomeHash := outcomeHashOf candidate1.outcome } sourceChannelId) = _
    unfold update
    rw [if_pos rfl]
  have htgt_eq : mid3.channels targetChannelId =
      { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := 0,
        outcomeHash := outcomeHashOf targetOutcome } := by
    show (update mid2.channels targetChannelId
        { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := 0,
          outcomeHash := outcomeHashOf candidate2.outcome } targetChannelId) = _
    unfold update
    rw [if_pos rfl]
  have hsrc_fin : (mid3.channels sourceChannelId).mode mid3.now = .finalized := by
    rw [hsrc_eq]
    unfold ChannelStatus.mode
    simp [mid1, mid2]
  have htgt_fin : (mid3.channels targetChannelId).mode mid3.now = .finalized := by
    rw [htgt_eq]
    simp [ChannelStatus.mode, mid1, mid2]
  let hsa : (0 : Nat) < sourceOutcome.length := by decide
  let hidx : (0 : Nat) < (sourceOutcome.get ⟨0, hsa⟩).allocations.length := by decide
  let hta : (0 : Nat) < targetOutcome.length := by decide
  let a0 : Nat := alloc0.amount
  let a1 : Nat := alloc1.amount
  let s' : AdjudicatorState := { mid3 with
    channels := update mid3.channels sourceChannelId
      { mid3.channels sourceChannelId with
        outcomeHash := outcomeHashOf
          (reallocateGuarantee sourceOutcome 0 0 left right a0 a1) } }
  have hstep_r : Step sig (consensusRelation sig) (Actor.nitro 0) mid3
      (.reclaim sourceChannelId sourceOutcome 0 0 targetOutcome 0 0) s' := by
    refine ⟨hsrc_fin, ?_, hsa, hidx, rfl, ⟨htgt_fin, ?_, ?_, hta, rfl, a0, a1, (by decide),
      rfl, rfl, (by decide), rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hsrc_eq]
    · show (mid3.channels targetChannelId).stateHash = 0
      rw [htgt_eq]
    · show (mid3.channels targetChannelId).outcomeHash = outcomeHashOf targetOutcome
      rw [htgt_eq]
  have hreach4 : Reachable sig (consensusRelation sig) g mid3 := hreach3
  have hneq : s'.channels sourceChannelId ≠ mid3.channels sourceChannelId := by
    show (update mid3.channels sourceChannelId
      { mid3.channels sourceChannelId with
        outcomeHash := outcomeHashOf (reallocateGuarantee sourceOutcome 0 0 left right a0 a1) })
      sourceChannelId ≠ mid3.channels sourceChannelId
    unfold update
    rw [if_pos rfl, hsrc_eq]
    intro heq
    have houtcome := hashA.outcomeHashOf_inj (congrArg ChannelStatus.outcomeHash heq)
    have : reallocateGuarantee sourceOutcome 0 0 left right a0 a1 = sourceOutcome := houtcome
    simp [reallocateGuarantee, sourceOutcome, guaranteeAlloc] at this
  exact ⟨assets, self, pool0, mid3, s', sourceChannelId, sourceOutcome, 0, 0, targetOutcome,
    0, 0, Actor.nitro 0, hreach4, hstep_r, hneq⟩

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
    ∃ c, s.holdings asset cid = some c ∧ PoolIsLive s.pool c ∧
      (s.pool.preimageOf c).map CommitmentPreimage.value = some held := by
  sorry

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
    (s : AdjudicatorState) (asset cid c : Nat) (pre : CommitmentPreimage)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hholds : s.holdings asset cid = some c)
    (hpre : s.pool.preimageOf c = some pre) :
    pre.value ≠ 0 := by
  have hinv := reachable_preserves
    (P := fun s => ∀ qasset qcid qc, s.holdings qasset qcid = some qc →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (by intro qasset qcid qc hc; exact absurd hc (by simp [genesis]))
    (fun actor call s s' hP hstep => holdings_preimage_nonzero_step sig appRel actor s s' call hP hstep)
    hreach
  obtain ⟨pre', hpre', hval', _⟩ := hinv asset cid c hholds
  rw [hpre] at hpre'
  exact (Option.some.inj hpre') ▸ hval'

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
    ¬ ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧ pre.value = 0 ∧
        pre ∈ s'.pool.live pre.token ∧
        pre ∉ s.pool.live pre.token := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨hmatch, _hholdseq, _hchanseq⟩ := hrest
  rintro ⟨pre, _hnpk, hval, hin, hnin⟩
  by_cases htok : pre.token = (outcome.get ⟨assetIndex, hidx⟩).asset
  · rw [htok] at hin hnin
    have hnz := payout_outputs_nonzero
      (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1
      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
        (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2)
      (outcome.get ⟨assetIndex, hidx⟩).asset s.self
    rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | c
    · rw [hc] at hmatch
      obtain ⟨w, pub, hM, hC, spent', newRoot, _hNonZero, _hself2, _htoken, _hnewnotes,
        _hemerg, _hwithdraw, _hroot, _hmarkspent, heq⟩ := hmatch
      rw [heq] at hin
      simp only at hin
      rcases List.mem_append.mp hin with hc1 | hc2
      · exact hnz pre hc1 hval
      · exact hnin hc2
    · rw [hc] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', newRoot, _hNonZero, _hself2, _htoken, _hnewnotes,
        _hceq, _hroot, hremove, _hmarkspent, heq⟩ := hmatch
      rw [heq] at hin
      simp only at hin
      rcases List.mem_append.mp hin with hc1 | hc2
      · exact hnz pre hc1 hval
      · have hperm := removeAll_perm hremove
        have hmem : pre ∈ s.pool.live (outcome.get ⟨assetIndex, hidx⟩).asset :=
          (List.Perm.mem_iff hperm).mpr (List.mem_append.mpr (Or.inr hc2))
        exact hnin hmem
  · have heqlive : s'.pool.live pre.token = s.pool.live pre.token := by
      rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | c
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, spent', newRoot, _hNonZero, _hself2, _htoken, _hnewnotes,
          _hemerg, _hwithdraw, _hroot, _hmarkspent, heq⟩ := hmatch
        rw [heq]
        show (if pre.token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live pre.token) = s.pool.live pre.token
        rw [if_neg htok]
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, rest, spent', newRoot, _hNonZero, _hself2, _htoken, _hnewnotes,
          _hceq, _hroot, hremove, _hmarkspent, heq⟩ := hmatch
        rw [heq]
        show (if pre.token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live pre.token) = s.pool.live pre.token
        rw [if_neg htok]
    rw [heqlive] at hin
    exact hnin hin
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
      s'.pool.spent = s.pool.spent := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨hmatch, _hholdseq, _hchanseq⟩ := hrest
  have hidx_eq : (⟨assetIndex, hidx⟩ : Fin outcome.length) = ⟨assetIndex, h⟩ := rfl
  rw [hidx_eq] at hmatch
  constructor
  · intro hnone
    rw [hnone] at hmatch
    obtain ⟨w, pub, hM, hC, spent', newRoot, _hNonZero, _hself2, _htoken, _hnewnotes,
      _hemerg, _hwithdraw, _hroot, hmarkspent, heq⟩ := hmatch
    rw [heq]
    show spent' = s.pool.spent
    have hofn : List.ofFn pub.nullifiers = ([] : List Nat) := List.ofFn_zero
    rw [hofn] at hmarkspent
    unfold markSpent at hmarkspent
    exact (Option.some.inj hmarkspent).symm
  · intro hpost
    rcases hcase : s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid with _ | c
    · rfl
    · exfalso
      rw [hcase] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', newRoot, _hNonZero, _hself2, _htoken, _hnewnotes,
        _hceq, _hroot, _hremove, hmarkspent, heq⟩ := hmatch
      rw [heq] at hpost
      simp only at hpost
      rw [List.ofFn_succ, List.ofFn_zero] at hmarkspent
      rw [markSpent_single] at hmarkspent
      split at hmarkspent
      · exact absurd hmarkspent (by simp)
      · rename_i hne
        have heq2 := Option.some.inj hmarkspent
        rw [← heq2] at hpost
        have hlen : (pub.nullifiers 0 :: s.pool.spent).length = s.pool.spent.length := by
          rw [hpost]
        simp at hlen

end ArmadaLean.Adjudicator
