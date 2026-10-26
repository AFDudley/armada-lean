/-
  ArmadaLean.Adjudicator.Safety — the theorem STATEMENTS stage A asks for.
  Every theorem below is proved; none carries `sorry`.

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

-- Several theorem signatures below carry a hypothesis kept only for
-- interface stability (so a later construction change never touches the
-- public signature) and not read by the current proof body. Each such
-- case is a deliberate, named choice, documented at its own theorem; the
-- linter cannot tell "kept for stability" from "forgotten", so this file
-- turns the warning off once, rather than once per theorem.
set_option linter.unusedVariables false

/-- A channel is finalized, right now, with exactly this `stateHash`/
    `outcomeHash` pair (S4 `0040-lifecycle-of-a-channel.md`, "Channel
    Modes"). A convenience predicate so the theorems below read as
    statements about the protocol's own storage fields, not about
    `ChannelStatus`'s internal shape. -/
def ChannelFinalizedWith (s : AdjudicatorState) (cid stateH outcomeH : Term) : Prop :=
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
    given `(stateHash, outcomeHash)` pair. RESTATED from the original
    text (which this file's own history found FALSE): `.transfer` and
    `.reclaim` (`Operations.lean`) both go on rewriting a finalized
    channel's own `outcomeHash` afterward, holding `stateHash` fixed, so
    a finalized channel's CURRENT `outcomeHash` need not be the
    signed/challenged outcome's hash directly — only `OutcomeDerivedFrom`
    (`Outcome.lean`) it, a chain of `.transfer`/`.reclaim` rewrites away;
    `OutcomeDerivedFrom`'s `.refl` case recovers the original claim as
    the special case where no `.transfer`/`.reclaim` ever touched the
    channel afterward. The "won a challenge" disjunct is ALSO restated:
    it now names the historical `.challenge` STEP itself (an existential
    over the state `s0` it fired from, and the state `s1` it produced),
    rather than re-asking whether `appRel`/`AuthorizedBy` hold at the
    theorem's OWN (possibly much later) `s` — `appRel` is a UNIVERSALLY
    quantified parameter with no stated relationship between its value
    at two different states, so the original text's `appRel s fp proof
    candidate` can be false at a LATER `s` even though the challenge
    that finalized `cid` genuinely fired at an earlier one.
    `SignedByAll`, by contrast, stays evaluated at the theorem's own `s`
    for `.conclude`: `signedBy` only ever grows (`step_signedBy_mono`,
    `Lemmas.lean`), so a `SignedByAll` fact once established survives,
    unchanged in truth value, to every later state — `.conclude` itself
    also clears `stateHash` to `Term.val 0` (`Operations.lean`'s
    `.conclude` case doc comment, citing `ForceMove.sol:160-167`), which
    is why this disjunct, like the original, states nothing about
    `stateH` at all. -/
theorem finalized_outcome_was_concluded_or_challenged
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (cid stateH outcomeH : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hfin : ChannelFinalizedWith s cid stateH outcomeH) :
    (∃ fp candidate, channelId fp = cid ∧ candidate.isFinal = true ∧
      SignedByAll sig s fp candidate ∧
      ∃ o, OutcomeDerivedFrom candidate.outcome o ∧ outcomeHashOf o = outcomeH) ∨
    (∃ fp proof candidate challenger actor0 s0 s1,
      channelId fp = cid ∧
      Reachable sig appRel (genesis assets selfInputs pool0) s0 ∧
      Step sig appRel actor0 s0 (.challenge fp proof candidate challenger) s1 ∧
      stateHash fp candidate = stateH ∧
      ∃ o, OutcomeDerivedFrom candidate.outcome o ∧ outcomeHashOf o = outcomeH) := by
  have hinv := reachable_preserves
    (P := fun s' => Reachable sig appRel (genesis assets selfInputs pool0) s' ∧
      ∀ cid', (s'.channels cid').finalizesAt ≠ 0 →
      (∃ fp candidate, channelId fp = cid' ∧ candidate.isFinal = true ∧
        SignedByAll sig s' fp candidate ∧
        ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
          outcomeHashOf o = (s'.channels cid').outcomeHash) ∨
      (∃ fp proof candidate challenger actor0 s0 s1,
        channelId fp = cid' ∧
        Reachable sig appRel (genesis assets selfInputs pool0) s0 ∧
        Step sig appRel actor0 s0 (.challenge fp proof candidate challenger) s1 ∧
        stateHash fp candidate = (s'.channels cid').stateHash ∧
        ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
          outcomeHashOf o = (s'.channels cid').outcomeHash))
    ⟨reachable_refl sig appRel (genesis assets selfInputs pool0),
      by intro cid' h; simp [genesis, emptyStatus] at h⟩
    (by
      intro actor call s1 s2 hP hstep
      refine ⟨reachable_step hP.1 hstep, ?_⟩
      have hlift : ∀ cid'',
          ((∃ fp candidate, channelId fp = cid'' ∧ candidate.isFinal = true ∧
              SignedByAll sig s1 fp candidate ∧
              ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
                outcomeHashOf o = (s1.channels cid'').outcomeHash) ∨
            (∃ fp proof candidate challenger actor0 s0 s1', channelId fp = cid'' ∧
              Reachable sig appRel (genesis assets selfInputs pool0) s0 ∧
              Step sig appRel actor0 s0 (.challenge fp proof candidate challenger) s1' ∧
              stateHash fp candidate = (s1.channels cid'').stateHash ∧
              ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
                outcomeHashOf o = (s1.channels cid'').outcomeHash)) →
          ((∃ fp candidate, channelId fp = cid'' ∧ candidate.isFinal = true ∧
              SignedByAll sig s2 fp candidate ∧
              ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
                outcomeHashOf o = (s1.channels cid'').outcomeHash) ∨
            (∃ fp proof candidate challenger actor0 s0 s1', channelId fp = cid'' ∧
              Reachable sig appRel (genesis assets selfInputs pool0) s0 ∧
              Step sig appRel actor0 s0 (.challenge fp proof candidate challenger) s1' ∧
              stateHash fp candidate = (s1.channels cid'').stateHash ∧
              ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
                outcomeHashOf o = (s1.channels cid'').outcomeHash)) := by
        intro cid'' h
        rcases h with ⟨fp, candidate, hc, hfi, hsb, o, hod, hoh⟩ | hright
        · exact Or.inl ⟨fp, candidate, hc, hfi,
            SignedByAll_mono sig appRel actor s1 s2 call hstep fp candidate hsb, o, hod, hoh⟩
        · exact Or.inr hright
      intro cid'
      cases call with
      | deposit channelId0 expectedHeld asset amount =>
        obtain ⟨_, _, _, _, _, hchan, _, _, _, _, _⟩ := hstep
        rw [hchan]
        intro hne
        exact hlift cid' (hP.2 cid' hne)
      | challenge fp proof candidate challenger =>
        have hstep2 := hstep
        obtain ⟨hmodeC, _, _, _, hchan, _, _, _, _, _, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid'
        · subst hcc
          rw [hchan]
          unfold update
          rw [if_pos rfl]
          intro _
          exact Or.inr ⟨fp, proof, candidate, challenger, actor, s1, s2, rfl, hP.1,
            hstep2, rfl, candidate.outcome, OutcomeDerivedFrom.refl _, rfl⟩
        · rw [hchan]
          unfold update
          rw [if_neg (fun h => hcc h.symm)]
          intro hne
          exact hlift cid' (hP.2 cid' hne)
      | checkpoint fp proof candidate =>
        obtain ⟨_, _, _, hchan, _, _, _, _, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid'
        · subst hcc
          rw [hchan]
          unfold update
          rw [if_pos rfl]
          intro hz; exact absurd rfl hz
        · rw [hchan]
          unfold update
          rw [if_neg (fun h => hcc h.symm)]
          intro hne
          exact hlift cid' (hP.2 cid' hne)
      | conclude fp candidate =>
        have hstep2 := hstep
        obtain ⟨_, hfi, hsb, hchan, _, _, _, _, _, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid'
        · subst hcc
          rw [hchan]
          unfold update
          rw [if_pos rfl]
          intro _
          exact Or.inl ⟨fp, candidate, rfl, hfi,
            SignedByAll_mono sig appRel actor s1 s2 _ hstep2 fp candidate hsb,
            candidate.outcome, OutcomeDerivedFrom.refl _, rfl⟩
        · rw [hchan]
          unfold update
          rw [if_neg (fun h => hcc h.symm)]
          intro hne
          exact hlift cid' (hP.2 cid' hne)
      | transfer assetIndex cid0 claimedStateHash outcome indices =>
        have hstep2 := hstep
        obtain ⟨hidx, hmodeT, hshT, hohT, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
        obtain ⟨_hguarantee, hrest⟩ := hinner
        obtain ⟨_r, _hmatch, _hholdseq, hchan⟩ := hrest
        by_cases hcc : cid0 = cid'
        · subst hcc
          rw [hchan]
          unfold update
          rw [if_pos rfl]
          intro _
          have hzne : (s1.channels cid0).finalizesAt ≠ 0 := fun hz => by
            simp [ChannelStatus.mode, hz] at hmodeT
          rcases hP.2 cid0 hzne with
              ⟨fp, candidate, hc, hfi, hsb, o, hod, hoh⟩ | ⟨fp, proof, candidate, challenger, actor0,
                s0, s1', hc, hreach0, hstep0, hsh, o, hod, hoh⟩
          · have hoeq : o = outcome := outcomeHashOf_inj (hoh.trans hohT)
            rw [hoeq] at hod
            exact Or.inl ⟨fp, candidate, hc, hfi,
              SignedByAll_mono sig appRel actor s1 s2 _ hstep2 fp candidate hsb, _,
              OutcomeDerivedFrom.transferStep assetIndex hidx
                (heldValue s1 (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices hod, rfl⟩
          · have hoeq : o = outcome := outcomeHashOf_inj (hoh.trans hohT)
            rw [hoeq] at hod
            exact Or.inr ⟨fp, proof, candidate, challenger, actor0, s0, s1', hc, hreach0, hstep0,
              hsh, _, OutcomeDerivedFrom.transferStep assetIndex hidx
                (heldValue s1 (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices hod, rfl⟩
        · rw [hchan]
          unfold update
          rw [if_neg (fun h => hcc h.symm)]
          intro hne
          exact hlift cid' (hP.2 cid' hne)
      | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
          targetAssetIndex claimedTargetStateHash =>
        have hstep2 := hstep
        obtain ⟨hmodeSrc, hohSrc, hsa, hidx1, hguarantee, hrest, _, _, _, _, _, _, _⟩ := hstep
        obtain ⟨_htgtMode, _htgtSh, _htgtOh, hta, _hassetEq, hfoundLeft, hfoundRight, a0, a1,
          _hlen2, _ha0, _ha1, hsum, hchan⟩ := hrest
        by_cases hcc : sourceChannelId = cid'
        · subst hcc
          rw [hchan]
          unfold update
          rw [if_pos rfl]
          intro _
          have hzne : (s1.channels sourceChannelId).finalizesAt ≠ 0 := fun hz => by
            simp [ChannelStatus.mode, hz] at hmodeSrc
          rcases hP.2 sourceChannelId hzne with
              ⟨fp, candidate, hc, hfi, hsb, o, hod, hoh⟩ | ⟨fp, proof, candidate, challenger, actor0,
                s0, s1', hc, hreach0, hstep0, hsh, o, hod, hoh⟩
          · have hoeq : o = sourceOutcome := outcomeHashOf_inj (hoh.trans hohSrc)
            rw [hoeq] at hod
            exact Or.inl ⟨fp, candidate, hc, hfi,
              SignedByAll_mono sig appRel actor s1 s2 _ hstep2 fp candidate hsb, _,
              OutcomeDerivedFrom.reclaimStep sourceAssetIndex indexOfTargetInSource hsa hidx1
                hguarantee a0 a1 hsum hfoundLeft hfoundRight hod, rfl⟩
          · have hoeq : o = sourceOutcome := outcomeHashOf_inj (hoh.trans hohSrc)
            rw [hoeq] at hod
            exact Or.inr ⟨fp, proof, candidate, challenger, actor0, s0, s1', hc, hreach0, hstep0, hsh,
              _, OutcomeDerivedFrom.reclaimStep sourceAssetIndex indexOfTargetInSource hsa hidx1
                hguarantee a0 a1 hsum hfoundLeft hfoundRight hod, rfl⟩
        · rw [hchan]
          unfold update
          rw [if_neg (fun h => hcc h.symm)]
          intro hne
          exact hlift cid' (hP.2 cid' hne)
      | bulkTransferAllAssets channelId0 outcome claimedStateHash =>
        have hstep2 := hstep
        obtain ⟨hmodeB, _hsh, hohB, newOutcome, hfold, hchan, _, _, _, _, _⟩ := hstep
        by_cases hcc : channelId0 = cid'
        · subst hcc
          rw [hchan]
          unfold update
          rw [if_pos rfl]
          intro _
          have hzne : (s1.channels channelId0).finalizesAt ≠ 0 := fun hz => by
            simp [ChannelStatus.mode, hz] at hmodeB
          have hderived := bulkTransferFold_outcomeDerivedFrom s1.self channelId0 outcome newOutcome
            s1.pool s2.pool s1.holdings s2.holdings hfold
          rcases hP.2 channelId0 hzne with
              ⟨fp, candidate, hc, hfi, hsb, o, hod, hoh⟩ | ⟨fp, proof, candidate, challenger, actor0,
                s0, s1', hc, hreach0, hstep0, hsh, o, hod, hoh⟩
          · have hoeq : o = outcome := outcomeHashOf_inj (hoh.trans hohB)
            rw [hoeq] at hod
            exact Or.inl ⟨fp, candidate, hc, hfi,
              SignedByAll_mono sig appRel actor s1 s2 _ hstep2 fp candidate hsb, newOutcome,
              hod.trans hderived, rfl⟩
          · have hoeq : o = outcome := outcomeHashOf_inj (hoh.trans hohB)
            rw [hoeq] at hod
            exact Or.inr ⟨fp, proof, candidate, challenger, actor0, s0, s1', hc, hreach0, hstep0, hsh,
              newOutcome, hod.trans hderived, rfl⟩
        · rw [hchan]
          unfold update
          rw [if_neg (fun h => hcc h.symm)]
          intro hne
          exact hlift cid' (hP.2 cid' hne)
      | bulkConcludeAndTransferAllAssets fp candidate =>
        have hstep2 := hstep
        obtain ⟨_hnotfinal, hfi, hsb, newOutcome, hfold, hchan, _, _, _, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid'
        · subst hcc
          rw [hchan]
          unfold update
          rw [if_pos rfl]
          intro _
          have hderived := bulkTransferFold_outcomeDerivedFrom s1.self (channelId fp) candidate.outcome
            newOutcome s1.pool s2.pool s1.holdings s2.holdings hfold
          exact Or.inl ⟨fp, candidate, rfl, hfi,
            SignedByAll_mono sig appRel actor s1 s2 _ hstep2 fp candidate hsb, newOutcome, hderived,
            rfl⟩
        · rw [hchan]
          unfold update
          rw [if_neg (fun h => hcc h.symm)]
          intro hne
          exact hlift cid' (hP.2 cid' hne)
      | tick newNow =>
        obtain ⟨_, _, _, _, hchan, _, _, _, _⟩ := hstep
        rw [hchan]
        intro hne
        exact hlift cid' (hP.2 cid' hne)
      | sign p d =>
        obtain ⟨_, _, _, hchan, _, _, _, _, _⟩ := hstep
        rw [hchan]
        intro hne
        exact hlift cid' (hP.2 cid' hne)
      | signNote pk msgHash =>
        obtain ⟨_, _, _, hchan, _, _, _, _, _⟩ := hstep
        rw [hchan]
        intro hne
        exact hlift cid' (hP.2 cid' hne))
    hreach
  have hfz : (s.channels cid).finalizesAt ≠ 0 := fun hz => by
    unfold ChannelFinalizedWith at hfin
    simp [ChannelStatus.mode, hz] at hfin
  rcases hinv.2 cid hfz with
      ⟨fp, candidate, hc, hfi, hsb, o, hod, hoh⟩ | ⟨fp, proof, candidate, challenger, actor0, s0, s1,
        hc, hreach0, hstep0, hsh, o, hod, hoh⟩
  · exact Or.inl ⟨fp, candidate, hc, hfi, hsb, o, hod, hfin.2.2 ▸ hoh⟩
  · exact Or.inr ⟨fp, proof, candidate, challenger, actor0, s0, s1, hc, hreach0, hstep0,
      hfin.2.1 ▸ hsh, o, hod, hfin.2.2 ▸ hoh⟩

/-- Which harm this rules out: a caller cannot name an `outcome`/`indices`
    to `transfer` that pays a destination the finalized outcome did not
    name, or a different amount than priority-order affordability gives
    it. This is `Step`'s `transfer` case made explicit as a theorem: the
    `outcome`/`claimedStateHash` a `transfer` call supplies must already
    equal the channel's stored `(stateHash, outcomeHash)`
    (`Operations.lean`'s `.transfer` case, mirroring
    `MultiAssetHolder._requireMatchingFingerprint`,
    `MultiAssetHolder.sol:506-516`), and every SELECTED allocation is
    reduced by EXACTLY its own `afford`-computed amount, an UNSELECTED
    allocation keeps its full recorded amount, and the total paid never
    exceeds the channel's held value — A-01, `statement-candidates.md`.
    STRENGTHENED from `paid ≤ amount`: `N19:747-751` "The allocation is
    in priority order, so that if the channel does not hold enough funds
    to pay all the coins that are due, then the addresses at the
    beginning of the allocation will receive funds first. We say that
    'A can afford x for B', if B would receive at least x coins, were
    the coins currently held by A to be paid out in priority order."
    `N19:765-770` T(A,B,x) "Reduces the funds held in channel A by x.
    Increases the funds held by B by x. Reduces the amount owed to B in
    the outcome of A by x." `FM:1845-1849` `pending := sum(r[i] - w[i];
    i < k)`; `amount := min(owed - w[k], Adjudicator.balance - pending)`.
    `DOC/0060:54` "If a channel were to finalize and be liquidated when
    underfunded ... the funds would be paid out in priority order."
    `SATP:377-379` (fn 9) "the order may also dictate which destinations
    receive priority in case the channel is insufficiently funded."
    Contract: `MAH.sol:157-190` (`affordsForDestination = min(amount,
    surplus)` at :167, `surplus -= affordsForDestination` at :189, run
    for EVERY index whether selected or not — `transferEffects`'s own
    `afford` call, `Outcome.lean`). -/
theorem transfer_pays_only_the_finalized_outcome
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    ChannelFinalizedWith s cid claimedStateHash (outcomeHashOf outcome) ∧
    (let allocs := (outcome.get ⟨assetIndex, h⟩).allocations
     let held := heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid
     let selected (i : Nat) : Bool := indices.isEmpty || i ∈ indices
     let paidAt := afford allocs held
     let newAllocs := (transferEffects allocs held indices).1
     ∀ i, i < allocs.length →
       (selected i → (newAllocs.getD i Allocation.default).amount =
         (allocs.getD i Allocation.default).amount - paidAt.getD i 0) ∧
       (¬ selected i → (newAllocs.getD i Allocation.default).amount =
         (allocs.getD i Allocation.default).amount)) ∧
    (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 ≤
      heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid := by
  obtain ⟨hidx, hmode, hsh, hoh, _hstrict, _hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  refine ⟨⟨hmode, hsh, hoh⟩, ?_, transferEffects_totalPayouts_le _ _ _⟩
  intro allocs held selected paidAt newAllocs i hi
  have := transferEffects_newAllocations_getD (outcome.get ⟨assetIndex, h⟩).allocations
    (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices i hi
  constructor
  · intro hsel
    rw [this, if_pos hsel]
  · intro hsel
    rw [this, if_neg hsel]

/-- A-02 — order does not change a simple-allocation payout: paying two
    DIFFERENT entries of the same finalized asset outcome, in either
    order (two `.transfer` calls, same channel, same asset, no
    `.deposit`/`.reclaim` on it in between — each possible order
    reaching its own final state), pays entry `i` the SAME amount
    either way, pays entry `j` the SAME amount either way, and leaves
    the SAME held value behind overall. Two-call instance of the
    general claim: "calling transfers out of order does not affect the
    ultimate result."
    Quotes: `N19:842-843` "It is also easy to see that calling
    transfers out of order does not affect the ultimate result."
    `FM:1814-1816` "The resolution at this point would attempt to give
    aResolution to Alice and bResolution to Bob, paying out Alice
    first, allowing her to recover her funds even if Bob does not
    deposit." Contract: `MAH.sol:161-190` (surplus is consumed for
    every index, selected or not). -/
theorem transfer_order_independent_for_simple_allocations
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor1 actor2 actor1' actor2' : Actor)
    (s mid1 fin1 mid1' fin1' : AdjudicatorState)
    (assetIndex : Nat) (cid claimedStateHash claimedStateHash' claimedStateHash'' : Term)
    (outcome outcome1 outcome2 : Outcome) (i j : Nat) (hij : i ≠ j)
    (h : assetIndex < outcome.length) (h1 : assetIndex < outcome1.length)
    (h2 : assetIndex < outcome2.length)
    (hnog : ∀ a ∈ (outcome.get ⟨assetIndex, h⟩).allocations, a.allocationType ≠ .guarantee)
    (hstep1 : Step sig appRel actor1 s (.transfer assetIndex cid claimedStateHash outcome [i]) mid1)
    (hstep2 : Step sig appRel actor2 mid1 (.transfer assetIndex cid claimedStateHash' outcome1 [j]) fin1)
    (hstep1' : Step sig appRel actor1' s (.transfer assetIndex cid claimedStateHash outcome [j]) mid1')
    (hstep2' : Step sig appRel actor2' mid1' (.transfer assetIndex cid claimedStateHash'' outcome2 [i]) fin1') :
    -- entry i is paid the same amount whether it goes first (`hstep1`) or second (`hstep2'`)
    (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).2.2 =
      (transferEffects (outcome2.get ⟨assetIndex, h2⟩).allocations
        (heldValue mid1' (outcome2.get ⟨assetIndex, h2⟩).asset cid) [i]).2.2 ∧
    -- entry j is paid the same amount whether it goes second (`hstep2`) or first (`hstep1'`)
    (transferEffects (outcome1.get ⟨assetIndex, h1⟩).allocations
        (heldValue mid1 (outcome1.get ⟨assetIndex, h1⟩).asset cid) [j]).2.2 =
      (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).2.2 ∧
    heldValue fin1 (outcome.get ⟨assetIndex, h⟩).asset cid =
      heldValue fin1' (outcome.get ⟨assetIndex, h⟩).asset cid := by
  have houtcome1 : outcome1 = outcome.mapIdx (fun idx exit =>
      if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).1 }) := by
    apply outcomeHashOf_inj
    obtain ⟨_, _, _, _, _, hinner1, _, _, _, _⟩ := hstep1
    obtain ⟨_, hrest1⟩ := hinner1
    obtain ⟨_, _, _, hchan1⟩ := hrest1
    obtain ⟨_, _, _, hoh2, _, _, _, _, _, _⟩ := hstep2
    rw [← hoh2, hchan1]
    unfold update
    rw [if_pos rfl]
    rfl
  subst houtcome1
  have houtcome2 : outcome2 = outcome.mapIdx (fun idx exit =>
      if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).1 }) := by
    apply outcomeHashOf_inj
    obtain ⟨_, _, _, _, _, hinner1', _, _, _, _⟩ := hstep1'
    obtain ⟨_, hrest1'⟩ := hinner1'
    obtain ⟨_, _, _, hchan1'⟩ := hrest1'
    obtain ⟨_, _, _, hoh2', _, _, _, _, _, _⟩ := hstep2'
    rw [← hoh2', hchan1']
    unfold update
    rw [if_pos rfl]
    rfl
  subst houtcome2
  have hget1 := mapIdx_get outcome (fun idx exit => if idx ≠ assetIndex then exit
    else { exit with allocations :=
      (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).1 }) assetIndex h h1
  have hget2 := mapIdx_get outcome (fun idx exit => if idx ≠ assetIndex then exit
    else { exit with allocations :=
      (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).1 }) assetIndex h h2
  simp only [ne_eq, not_true_eq_false, if_false] at hget1 hget2
  have hasset1 : ((outcome.mapIdx (fun idx exit => if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).1 })).get ⟨assetIndex, h1⟩).asset
      = (outcome.get ⟨assetIndex, h⟩).asset := by rw [hget1]
  have hasset2 : ((outcome.mapIdx (fun idx exit => if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).1 })).get ⟨assetIndex, h2⟩).asset
      = (outcome.get ⟨assetIndex, h⟩).asset := by rw [hget2]
  have hallocs1 : ((outcome.mapIdx (fun idx exit => if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).1 })).get ⟨assetIndex, h1⟩).allocations
      = (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).1 := by rw [hget1]
  have hallocs2 : ((outcome.mapIdx (fun idx exit => if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).1 })).get ⟨assetIndex, h2⟩).allocations
      = (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).1 := by rw [hget2]
  rw [hasset1, hallocs1, hasset2, hallocs2]
  have hheld1 := transfer_sets_heldValue sig appRel actor1 s mid1 assetIndex cid claimedStateHash
    outcome [i] hstep1 h
  have hheld1' := transfer_sets_heldValue sig appRel actor1' s mid1' assetIndex cid claimedStateHash
    outcome [j] hstep1' h
  have htp_i := transferEffects_totalPayouts_single (outcome.get ⟨assetIndex, h⟩).allocations
    (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) i
  have htp_j := transferEffects_totalPayouts_single (outcome.get ⟨assetIndex, h⟩).allocations
    (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) j
  rw [htp_i] at hheld1
  rw [htp_j] at hheld1'
  have htp_j' := transferEffects_totalPayouts_single
    (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
      (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).1
    (heldValue mid1 (outcome.get ⟨assetIndex, h⟩).asset cid) j
  have htp_i' := transferEffects_totalPayouts_single
    (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
      (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).1
    (heldValue mid1' (outcome.get ⟨assetIndex, h⟩).asset cid) i
  rw [hheld1] at htp_j'
  rw [hheld1'] at htp_i'
  have hexch_j := afford_exchange (outcome.get ⟨assetIndex, h⟩).allocations
    (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) i j hij
  have hexch_i := afford_exchange (outcome.get ⟨assetIndex, h⟩).allocations
    (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) j i (Ne.symm hij)
  have hpay_j := htp_j'.trans hexch_j
  have hpay_i := htp_i'.trans hexch_i
  have hheld2 := transfer_sets_heldValue sig appRel actor2 mid1 fin1 assetIndex cid claimedStateHash'
    (outcome.mapIdx (fun idx exit => if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [i]).1 })) [j] hstep2 h1
  have hheld2' := transfer_sets_heldValue sig appRel actor2' mid1' fin1' assetIndex cid claimedStateHash''
    (outcome.mapIdx (fun idx exit => if idx ≠ assetIndex then exit
      else { exit with allocations :=
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) [j]).1 })) [i] hstep2' h2
  rw [hasset1] at hheld2
  rw [hasset2] at hheld2'
  rw [hallocs1] at hheld2
  rw [hallocs2] at hheld2'
  rw [hheld1, hpay_j] at hheld2
  rw [hheld1', hpay_i] at hheld2'
  refine ⟨?_, ?_, ?_⟩
  · rw [htp_i, hheld1', hpay_i]
  · rw [hheld1, hpay_j, htp_j]
  · rw [hheld2, hheld2']
    omega

/-- A-03 — the turn-number record never decreases on a live channel: a
    `challenge`/`checkpoint`/`conclude` step either raises `fp`'s own
    `turnNumRecord`, leaves it the same, or (only `conclude`) drops it
    to `0` while finalizing the channel in the same step; no other call
    touches it at all. Needs `0 < s.now`: `conclude` writes `finalizesAt
    := s.now` (`Operations.lean`'s `.conclude` case), and the model
    allows `s.now = 0` (`tick` need never be called), at which
    `finalizesAt = 0` reads as `Open`, not `Finalized` — the deployed
    contract instead writes `block.timestamp`, always a positive Unix
    time on a real chain (`ForceMove.sol:160-167`,
    `ChannelData(0, uint48(block.timestamp), bytes32(0),
    NitroUtils.hashOutcome(...))`).
    Quotes: `DOC/0020:11` "Each state has a version number, with
    greater version numbers superceding lesser ones." `DOC/0020:19-21`
    "The only things enforced by the core protocol are: the rule that
    higher turn numbers take precedence over lower ones." `DOC/0010:138`
    "The turn number is the mechanism by which newer states take
    precedence over older ones." `DOC/0040:150-151` "turnNumRecord is
    the highest turn number that is known to the chain to be supported
    by a full set of signatures. The exception to this rule is that it
    is set to 0 when the channel is concluded via a conclude call."
    `DOC/0070:66` checkpoint establishes "a new and higher
    turnNumRecord." `SATP:308` `require(supportedStateVars.version >=
    adjudicatorStatus.version)`. `FM:1377-1381` "each of these
    responses lead to an increase in the turnNum ... this prevents the
    game from stalling indefinitely." `FM:1543-1545` "store the turnNum
    of the response state in the adjudicator. Only allow new
    force-moves if their response will increase this stored turnNum."
    Contract: `FM.sol:48-55`, `FM.sol:100`, `FM.sol:277-294`,
    `FM.sol:160-167`. -/
theorem turn_number_record_monotone
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hnowpos : 0 < s.now)
    (hstep : Step sig appRel actor s call s') :
    ((s'.channels cid).turnNumRecord > (s.channels cid).turnNumRecord ∨
      (s'.channels cid).turnNumRecord = (s.channels cid).turnNumRecord ∨
      ((s'.channels cid).turnNumRecord = 0 ∧ (s'.channels cid).mode s'.now = .finalized)) ∧
    (∀ fp proof candidate, call = .checkpoint fp proof candidate → channelId fp = cid →
      (s'.channels cid).turnNumRecord > (s.channels cid).turnNumRecord) ∧
    (∀ fp proof candidate challenger, call = .challenge fp proof candidate challenger →
      channelId fp = cid → (s.channels cid).mode s.now = .challenge →
      (s'.channels cid).turnNumRecord > (s.channels cid).turnNumRecord) := by
  cases call with
  | deposit channelId0 expectedHeld asset amount =>
    obtain ⟨_, _, _, _, _, hchan, _, _, _, _, _⟩ := hstep
    refine ⟨Or.inr (Or.inl ?_), ?_, ?_⟩
    · rw [hchan]
    · intro fp proof candidate heq; exact absurd heq (by simp)
    · intro fp proof candidate challenger heq; exact absurd heq (by simp)
  | challenge fp proof candidate challenger =>
    obtain ⟨hprecond, _, _, _, hchan, _, _, _, _, hnow, _, _⟩ := hstep
    refine ⟨?_, ?_, ?_⟩
    · by_cases hcc : channelId fp = cid
      · subst hcc
        rw [hchan]; unfold update; rw [if_pos rfl]
        rcases hmode : (s.channels (channelId fp)).mode s.now with _ | _ | _
        · rw [hmode] at hprecond; dsimp only; omega
        · rw [hmode] at hprecond; dsimp only; omega
        · rw [hmode] at hprecond; exact absurd hprecond id
      · rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]; right; left; rfl
    · intro fp' proof' candidate' heq; exact absurd heq (by simp)
    · intro fp' proof' candidate' challenger' heq hcc hmode
      injection heq with hfp hproof hcand hchallenger
      subst hfp; subst hcand
      rw [hcc] at hprecond
      rw [hmode] at hprecond
      rw [hchan]; unfold update; rw [if_pos hcc.symm]
      omega
  | checkpoint fp proof candidate =>
    obtain ⟨_, hprecond, _, hchan, _, _, _, _, _, _⟩ := hstep
    refine ⟨?_, ?_, ?_⟩
    · by_cases hcc : channelId fp = cid
      · subst hcc; rw [hchan]; unfold update; rw [if_pos rfl]; left; omega
      · rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]; right; left; rfl
    · intro fp' proof' candidate' heq hcc
      injection heq with hfp hproof hcand
      subst hfp; subst hcand
      rw [hcc] at hprecond
      rw [hchan]; unfold update; rw [if_pos hcc.symm]
      omega
    · intro fp' proof' candidate' challenger' heq; exact absurd heq (by simp)
  | conclude fp candidate =>
    obtain ⟨_, _, _, hchan, _, _, _, _, hnow, _⟩ := hstep
    refine ⟨?_, ?_, ?_⟩
    · by_cases hcc : channelId fp = cid
      · subst hcc
        right; right
        rw [hchan]; unfold update; rw [if_pos rfl]
        refine ⟨rfl, ?_⟩
        unfold ChannelStatus.mode
        rw [hnow]
        dsimp only
        rw [if_neg (by omega), if_pos (by omega)]
      · rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]; right; left; rfl
    · intro fp' proof' candidate' heq; exact absurd heq (by simp)
    · intro fp' proof' candidate' challenger' heq; exact absurd heq (by simp)
  | transfer assetIndex cid0 claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨_r, _hmatch, _hholdseq, hchan⟩ := hrest
    refine ⟨Or.inr (Or.inl ?_), ?_, ?_⟩
    · rw [hchan]; unfold update; by_cases hcc : cid = cid0 <;> simp [hcc]
    · intro fp proof candidate heq; exact absurd heq (by simp)
    · intro fp proof candidate challenger heq; exact absurd heq (by simp)
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, hrest, _, _, _, _, _, _, _⟩ := hstep
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hchan⟩ := hrest
    refine ⟨Or.inr (Or.inl ?_), ?_, ?_⟩
    · rw [hchan]; unfold update; by_cases hcc : cid = sourceChannelId <;> simp [hcc]
    · intro fp proof candidate heq; exact absurd heq (by simp)
    · intro fp proof candidate challenger heq; exact absurd heq (by simp)
  | bulkTransferAllAssets channelId0 outcome claimedStateHash =>
    obtain ⟨_, _, _, newOutcome, hfold, hchan, _, _, _, _, _⟩ := hstep
    refine ⟨Or.inr (Or.inl ?_), ?_, ?_⟩
    · rw [hchan]; unfold update; by_cases hcc : cid = channelId0 <;> simp [hcc]
    · intro fp proof candidate heq; exact absurd heq (by simp)
    · intro fp proof candidate challenger heq; exact absurd heq (by simp)
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, newOutcome, hfold, hchan, _, _, hnow, _, _⟩ := hstep
    refine ⟨?_, ?_, ?_⟩
    · by_cases hcc : channelId fp = cid
      · subst hcc
        right; right
        rw [hchan]; unfold update; rw [if_pos rfl]
        refine ⟨rfl, ?_⟩
        unfold ChannelStatus.mode
        rw [hnow]
        dsimp only
        rw [if_neg (by omega), if_pos (by omega)]
      · rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]; right; left; rfl
    · intro fp' proof' candidate' heq; exact absurd heq (by simp)
    · intro fp' proof' candidate' challenger' heq; exact absurd heq (by simp)
  | tick newNow =>
    obtain ⟨_, _, _, _, hchan, _, _, _, _⟩ := hstep
    refine ⟨Or.inr (Or.inl ?_), ?_, ?_⟩
    · rw [hchan]
    · intro fp proof candidate heq; exact absurd heq (by simp)
    · intro fp proof candidate challenger heq; exact absurd heq (by simp)
  | sign p d =>
    obtain ⟨_, _, _, hchan, _, _, _, _, _⟩ := hstep
    refine ⟨Or.inr (Or.inl ?_), ?_, ?_⟩
    · rw [congrFun hchan cid]
    · intro fp proof candidate heq; exact absurd heq (by simp)
    · intro fp proof candidate challenger heq; exact absurd heq (by simp)
  | signNote pk msgHash =>
    obtain ⟨_, _, _, hchan, _, _, _, _, _⟩ := hstep
    refine ⟨Or.inr (Or.inl ?_), ?_, ?_⟩
    · rw [congrFun hchan cid]
    · intro fp proof candidate heq; exact absurd heq (by simp)
    · intro fp proof candidate challenger heq; exact absurd heq (by simp)

/-- A-04 — finalization is permanent and fixes the state: once `cid` is
    finalized at `s`, it stays finalized at every state `AppliesAll`
    reaches from `s`, with the SAME `stateHash`/`finalizesAt`; only its
    `outcomeHash` can still change, and only by an `OutcomeDerivedFrom`
    rewrite (`.transfer`/`.reclaim`).
    Quotes: `N19:301-302` "it is crucial that the rules of operation
    only allow one outcome to be finalized for each channel."
    `N19:612-614` "The definition of finalizability excludes the case
    where two different finalizable outcomes are held by different
    participants." `FM:1262-1265` "the game transitions into the
    Terminated mode. In this mode, no further play is possible."
    `SATP:294-303` `isOpen` and `require(isOpen(adjudicatorStatus))` in
    `challenge`. `DOC/0040:104-110` the mode diagram has no edge out of
    `Finalized`. Contract: `FM.sol:54`, `FM.sol:99`, `FM.sol:147`,
    `FM.sol:301-303`; `MAH.sol:205,409-413` (fingerprint rewrite
    only). -/
theorem finalization_permanent
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (s s' : AdjudicatorState) (cid : Term) (o : Outcome)
    (hfin : (s.channels cid).mode s.now = .finalized)
    (hoh : (s.channels cid).outcomeHash = outcomeHashOf o)
    (calls : List (Actor × Call))
    (happ : AppliesAll sig appRel s calls s') :
    (s'.channels cid).mode s'.now = .finalized ∧
    (s'.channels cid).stateHash = (s.channels cid).stateHash ∧
    (s'.channels cid).finalizesAt = (s.channels cid).finalizesAt ∧
    ∃ o', OutcomeDerivedFrom o o' ∧ (s'.channels cid).outcomeHash = outcomeHashOf o' := by
  have hinv := appliesAll_preserves
    (P := fun s'' => (s''.channels cid).mode s''.now = .finalized ∧
      (s''.channels cid).stateHash = (s.channels cid).stateHash ∧
      (s''.channels cid).finalizesAt = (s.channels cid).finalizesAt ∧
      ∃ o', OutcomeDerivedFrom o o' ∧ (s''.channels cid).outcomeHash = outcomeHashOf o')
    (by
      intro actor call s1 s2 hP hstep
      obtain ⟨hmode1, hsh1, hfa1, o1, hod1, hoh1⟩ := hP
      have htrivial : s2.channels cid = s1.channels cid → s2.now = s1.now →
          (s2.channels cid).mode s2.now = .finalized ∧
          (s2.channels cid).stateHash = (s.channels cid).stateHash ∧
          (s2.channels cid).finalizesAt = (s.channels cid).finalizesAt ∧
          ∃ o', OutcomeDerivedFrom o o' ∧ (s2.channels cid).outcomeHash = outcomeHashOf o' := by
        intro hc hn
        rw [hc, hn]
        exact ⟨hmode1, hsh1, hfa1, o1, hod1, hoh1⟩
      cases call with
      | deposit channelId0 expectedHeld asset amount =>
        obtain ⟨_, _, _, _, _, hchan, _, _, hnow, _, _⟩ := hstep
        exact htrivial (congrFun hchan cid) hnow
      | challenge fp proof candidate challenger =>
        obtain ⟨hprecond, _, _, _, hchan, _, _, _, _, hnow, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid
        · subst hcc
          rw [hmode1] at hprecond
          exact absurd hprecond (by simp)
        · exact htrivial (by rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]) hnow
      | checkpoint fp proof candidate =>
        obtain ⟨hprecond, _, _, hchan, _, _, _, _, hnow, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid
        · subst hcc; rw [hmode1] at hprecond; exact absurd rfl hprecond
        · exact htrivial (by rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]) hnow
      | conclude fp candidate =>
        obtain ⟨hprecond, _, _, hchan, _, _, _, _, hnow, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid
        · subst hcc; rw [hmode1] at hprecond; exact absurd rfl hprecond
        · exact htrivial (by rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]) hnow
      | transfer assetIndex cid0 claimedStateHash outcome indices =>
        obtain ⟨hidx, hmodeT, hshT, hohT, _hstrict, hinner, _hcfg, _hself, hnow, _hsigned⟩ := hstep
        obtain ⟨_hguarantee, hrest⟩ := hinner
        obtain ⟨_r, _hmatch, _hholdseq, hchan⟩ := hrest
        by_cases hcc : cid0 = cid
        · subst hcc
          rw [hchan]; unfold update; rw [if_pos rfl, hnow]
          refine ⟨?_, ?_, ?_, ?_⟩
          · show (s1.channels cid0).mode s1.now = .finalized
            rw [← hmode1]
          · show (s1.channels cid0).stateHash = (s.channels cid0).stateHash
            exact hsh1
          · show (s1.channels cid0).finalizesAt = (s.channels cid0).finalizesAt
            have : (s2.channels cid0).finalizesAt = (s1.channels cid0).finalizesAt := by
              rw [hchan]; unfold update; rw [if_pos rfl]
            rw [← this] at hfa1 ⊢
            exact hfa1
          · have hoeq : o1 = outcome := outcomeHashOf_inj (hoh1.symm.trans hohT)
            rw [hoeq] at hod1
            exact ⟨_, OutcomeDerivedFrom.transferStep assetIndex hidx
              (heldValue s1 (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices hod1, rfl⟩
        · exact htrivial (by rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]) hnow
      | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
          targetAssetIndex claimedTargetStateHash =>
        obtain ⟨hmodeSrc, hohSrc, hsa, hidx1, hguarantee, hrest, _, _, _, _, hnow, _, _⟩ := hstep
        obtain ⟨_htgtMode, _htgtSh, _htgtOh, hta, _hassetEq, hfoundLeft, hfoundRight, a0, a1,
          _hlen2, _ha0, _ha1, hsum, hchan⟩ := hrest
        by_cases hcc : sourceChannelId = cid
        · subst hcc
          have hshEq : (s2.channels sourceChannelId).stateHash = (s1.channels sourceChannelId).stateHash := by
            rw [hchan]; unfold update; rw [if_pos rfl]
          have hfaEq : (s2.channels sourceChannelId).finalizesAt = (s1.channels sourceChannelId).finalizesAt := by
            rw [hchan]; unfold update; rw [if_pos rfl]
          refine ⟨?_, ?_, ?_, ?_⟩
          · show (s2.channels sourceChannelId).mode s2.now = .finalized
            unfold ChannelStatus.mode
            rw [hfaEq, hnow]
            unfold ChannelStatus.mode at hmode1
            exact hmode1
          · rw [hshEq]; exact hsh1
          · rw [hfaEq]; exact hfa1
          · have hoeq : o1 = sourceOutcome := outcomeHashOf_inj (hoh1.symm.trans hohSrc)
            rw [hoeq] at hod1
            exact ⟨_, OutcomeDerivedFrom.reclaimStep sourceAssetIndex indexOfTargetInSource hsa hidx1
              hguarantee a0 a1 hsum hfoundLeft hfoundRight hod1, by rw [hchan]; unfold update; rw [if_pos rfl]⟩
        · exact htrivial (by rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]) hnow
      | bulkTransferAllAssets channelId0 outcome claimedStateHash =>
        obtain ⟨hmodeB, _hsh, hohB, newOutcome, hfold, hchan, _, _, hnow, _, _⟩ := hstep
        by_cases hcc : channelId0 = cid
        · subst hcc
          have hderived := bulkTransferFold_outcomeDerivedFrom s1.self channelId0 outcome newOutcome
            s1.pool s2.pool s1.holdings s2.holdings hfold
          have hoeq : o1 = outcome := outcomeHashOf_inj (hoh1.symm.trans hohB)
          rw [hoeq] at hod1
          refine ⟨?_, ?_, ?_, ⟨newOutcome, hod1.trans hderived, by
            rw [hchan]; unfold update; rw [if_pos rfl]⟩⟩
          · rw [hchan]; unfold update; rw [if_pos rfl, hnow]; exact hmode1
          · rw [hchan]; unfold update; rw [if_pos rfl]; exact hsh1
          · rw [hchan]; unfold update; rw [if_pos rfl]; exact hfa1
        · exact htrivial (by rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]) hnow
      | bulkConcludeAndTransferAllAssets fp candidate =>
        obtain ⟨hprecond, _, _, _, _, hchan, _, _, hnow, _, _⟩ := hstep
        by_cases hcc : channelId fp = cid
        · subst hcc; rw [hmode1] at hprecond; exact absurd rfl hprecond
        · exact htrivial (by rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]) hnow
      | tick newNow =>
        obtain ⟨hge, hnow, _, _, hchan, _, _, _, _⟩ := hstep
        refine ⟨?_, by rw [hchan]; exact hsh1, by rw [hchan]; exact hfa1, o1, hod1,
          by rw [hchan]; exact hoh1⟩
        rw [hchan, hnow]
        have hfz : (s1.channels cid).finalizesAt ≠ 0 := by
          intro hz; unfold ChannelStatus.mode at hmode1; simp [hz] at hmode1
        have hfle : (s1.channels cid).finalizesAt ≤ s1.now := by
          unfold ChannelStatus.mode at hmode1
          rw [if_neg hfz] at hmode1
          split at hmode1
          · assumption
          · exact absurd hmode1 (by simp)
        unfold ChannelStatus.mode
        rw [if_neg hfz, if_pos (by omega)]
      | sign p d =>
        obtain ⟨_, _, _, hchan, _, _, _, hnow, _⟩ := hstep
        exact htrivial (congrFun hchan cid) hnow
      | signNote pk msgHash =>
        obtain ⟨_, _, _, hchan, _, _, _, hnow, _⟩ := hstep
        exact htrivial (congrFun hchan cid) hnow)
    ⟨hfin, rfl, rfl, o, OutcomeDerivedFrom.refl o, hoh⟩ happ
  exact hinv

/-- A-05 — only an authorized challenger can register a challenge: a
    successful `.challenge` call's `challenger` is always one of `fp`'s
    own participants, and always authorized `candidate`'s own
    `stateHash` — restates `.challenge`'s own `Step` precondition
    (`Operations.lean`) as a theorem.
    Quotes: `DOC/0070:52-56` "The challenger needs to sign this data:
    keccak256(abi.encode(challengeStateHash, 'forceMove')) ... This
    mechanism allows the challenge to be authorized only by a channel
    participant." `FM:1546-1548` "Add a certificate argument to the
    force-move operation, to identify the challenger ... Require that
    the challenger is one of the participants." Contract: `FM.sol:63`,
    `FM.sol:184-197`. -/
theorem challenge_requires_authorized_challenger
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (fp : FixedPart) (proof : List VariablePart)
    (candidate : VariablePart) (challenger : Nat)
    (hstep : Step sig appRel actor s (.challenge fp proof candidate challenger) s') :
    challenger ∈ fp.participants ∧ AuthorizedBy sig s challenger (stateHash fp candidate) := by
  obtain ⟨_, _, hchall, hauth, _, _, _, _, _, _, _, _⟩ := hstep
  exact ⟨hchall, hauth⟩

/-- A-06 — a deposit to an external destination fails: `.deposit` has no
    successful `Step` when its own `channelId` argument is an external
    address.
    Quotes: `DOC/0060:16` "Firstly, destination must NOT be an external
    destination." `DOC/0060:18` "The first rule prevents funds being
    escrowed against something other than a channelId." Contract:
    `ANA.sol:96`. Model: `Ops:142`. -/
theorem deposit_external_destination_fails
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (cid : Term) (expectedHeld asset amount : Nat)
    (hext : isExternal cid) :
    ¬ Step sig appRel actor s (.deposit cid expectedHeld asset amount) s' := by
  intro hstep
  obtain ⟨_, _, hnotext, _, _, _, _, _, _, _, _⟩ := hstep
  exact hnotext hext

/-- A-07 — a deposit with a wrong `expectedHeld` fails: `.deposit` has
    no successful `Step` when its own `expectedHeld` argument disagrees
    with the channel's CURRENT held value — this is what keeps a
    front-run depositor from losing funds.
    Quotes: `DOC/0060:16` "Secondly, the on-chain holdings for
    destination must be equal to expectedHeld." `DOC/0060:18` "The
    second rule prevents loss of funds: since holdings are paid out in
    preferential order, depositing before a counterparty has deposited
    implies that they can withdraw your funds." Contract:
    `ANA.sol:102,112`. Model: `Ops:141`. -/
theorem deposit_wrong_expected_held_fails
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (cid : Term) (expectedHeld asset amount : Nat)
    (hwrong : heldValue s asset cid ≠ expectedHeld) :
    ¬ Step sig appRel actor s (.deposit cid expectedHeld asset amount) s' := by
  intro hstep
  obtain ⟨_, hheld, _, _, _, _, _, _, _, _, _⟩ := hstep
  exact hwrong hheld

/-- A-08 — a deposit adds exactly its amount to one channel, and touches
    nothing else: promotes `deposit_sets_heldValue`/
    `deposit_merge_sets_heldValue` (`Lemmas.lean`) to a full statement,
    adding the frame condition those two theorems do not state — every
    OTHER `(asset, channel)` held value is unchanged, and no channel
    status changes. Needs `Reachable`: the MERGE branch reads the OLD
    held value off `s.pool.preimageOf`, which only reads back the
    actual value once `holdings_preimage_nonzero_step`'s own invariant
    (`Lemmas.lean`) guarantees the holding's commitment has a disclosed
    preimage at all — a bare `Step` hypothesis does not rule out an
    adversarial `s` where `s.holdings asset cid` already names a
    commitment nobody has disclosed yet.
    Quotes: `N19:165-168` "The deposit operation, DA(x), is an on-chain
    operation used to increase A's balance by x coins. There are no
    restrictions on who can deposit coins for an address, but the
    transaction must always include a transfer of x coins into the
    adjudicator." `N19:785-787` "a deposit into the system cannot
    reduce the value of any address and cannot increase the value of
    any address by more than the value of the deposit." Contract:
    `ANA.sol:86,111-112`. -/
theorem deposit_effect
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (cid : Term) (expectedHeld asset amount : Nat)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hstep : Step sig appRel actor s (.deposit cid expectedHeld asset amount) s') :
    heldValue s' asset cid = heldValue s asset cid + amount ∧
    (∀ asset' cid', (asset', cid') ≠ (asset, cid) →
      heldValue s' asset' cid' = heldValue s asset' cid') ∧
    s'.channels = s.channels := by
  have hwf := holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach
  have hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro qasset qcid qpos qc hc
    obtain ⟨⟨pre, hpre, hcons, hval, _⟩, _⟩ := hwf qasset qcid qpos qc hc
    exact ⟨pre, hpre, hval, hcons⟩
  have hchan : s'.channels = s.channels := by
    obtain ⟨_, _, _, _, _, h, _, _, _, _, _⟩ := hstep
    exact h
  refine ⟨?_, fun asset' cid' hne => deposit_frame sig appRel actor s s' cid expectedHeld asset
    amount hstep hinv asset' cid' hne, hchan⟩
  rcases hh : s.holdings asset cid with _ | ⟨oldPos, oldHolding⟩
  · rw [deposit_sets_heldValue sig appRel actor s s' cid expectedHeld asset amount hstep hh]
    unfold heldValue
    rw [hh]
    dsimp only
    omega
  · exact deposit_merge_sets_heldValue sig appRel actor s s' cid expectedHeld asset amount hstep
      hinv oldPos oldHolding hh

/-- A-10 — `transfer` never pays a guarantee allocation: restates
    `.transfer`'s own `Step` precondition (`Operations.lean`, `Ops:314`)
    as a theorem.
    Quotes: `DOC/0030:41` "When allocationType is set to guarantee,
    funds cannot be transferred in the usual way. Instead, they may be
    moved to another channel on chain using the reclaim method."
    Contract: `MAH.sol:169-170` `revert('cannot transfer a
    guarantee')`. -/
theorem transfer_never_pays_guarantee
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    ∀ a ∈ (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.1,
      a.allocationType ≠ .guarantee := by
  obtain ⟨_, _, _, _, _, hinner, _, _, _, _⟩ := hstep
  exact hinner.1

/-- A-11 — `reclaim` only reallocates a finalized guarantee, value-
    neutral: both the source and target channel are finalized, the
    named entry is a `.guarantee`, the target's own asset matches the
    source's, the two credited amounts sum to EXACTLY the guarantee's
    own amount, the source channel's NEW outcome is `reallocateGuarantee`
    of the OLD one with the guarantee's own decoded destinations, that
    asset's OWN total is unchanged by the reallocation, and
    `s'.pool`/`s'.holdings` are UNCHANGED — `reclaim` moves value
    between OUTCOME entries only, never into or out of the pool (the
    model does NOT follow the deployed `_settleReclaimExit`, which
    mints a brand-new commitment; departure item 2, `Ops:351-355`).
    Quotes: `SATP:344-364` Listing 2: `require(0 < ledgerStatus.
    finalizesAt <= now)`, `require(0 < targetStatus.finalizesAt <=
    now)`, `require(isGuarantee(guarantee))`, `o_ledger[left] +=
    o_target[0]`, `o_ledger[right] += o_target[1]`, `delete
    o_ledger[targetChannelId]`. `N19:1072-1074` "The funds held in a
    guarantee channel can only be paid out once the outcome of the
    target channel is finalized." `DOC/0080:143` "the parent and child
    channels must both be finalized on chain. If the child channel is
    funded with a guarantee, funds may be transferred from the child
    channel to the parent channel using reclaim." Contract:
    `MAH.sol:307,317-322,329-330,384-387`. -/
theorem reclaim_value_neutral
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState)
    (sourceChannelId : Term) (sourceOutcome : Outcome)
    (sourceAssetIndex indexOfTargetInSource : Nat) (targetOutcome : Outcome)
    (targetAssetIndex : Nat) (claimedTargetStateHash : Term)
    (hstep : Step sig appRel actor s (.reclaim sourceChannelId sourceOutcome
      sourceAssetIndex indexOfTargetInSource targetOutcome targetAssetIndex
      claimedTargetStateHash) s') :
    (s.channels sourceChannelId).mode s.now = .finalized ∧
    s'.pool = s.pool ∧
    s'.holdings = s.holdings ∧
    (∃ hsa : sourceAssetIndex < sourceOutcome.length,
      ∃ hidx : indexOfTargetInSource < (sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.length,
        let guarantee := (sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
          ⟨indexOfTargetInSource, hidx⟩
        guarantee.allocationType = .guarantee ∧
        (let (left, right) := decodeGuarantee guarantee.metadata
         (s.channels guarantee.destination).mode s.now = .finalized ∧
         ∃ hta : targetAssetIndex < targetOutcome.length,
         (targetOutcome.get ⟨targetAssetIndex, hta⟩).asset =
           (sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).asset ∧
         ∃ a0 a1 : Nat,
           a0 = ((targetOutcome.get ⟨targetAssetIndex, hta⟩).allocations.getD 0 Allocation.default).amount ∧
           a1 = ((targetOutcome.get ⟨targetAssetIndex, hta⟩).allocations.getD 1 Allocation.default).amount ∧
           a0 + a1 = guarantee.amount ∧
           (s'.channels sourceChannelId).outcomeHash = outcomeHashOf
             (reallocateGuarantee sourceOutcome sourceAssetIndex indexOfTargetInSource left right a0 a1) ∧
           listSum (((reallocateGuarantee sourceOutcome sourceAssetIndex indexOfTargetInSource
               left right a0 a1).getD sourceAssetIndex ⟨0, []⟩).allocations.map Allocation.amount) =
             listSum ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.map Allocation.amount))) := by
  obtain ⟨hmodeSrc, _hohSrc, hsa, hidx1, hguarantee, hrest, hpool, hholdings, _, _, _, _, _⟩ := hstep
  obtain ⟨htgtMode, _htgtSh, _htgtOh, hta, hassetEq, hfoundLeft, hfoundRight, a0, a1, _hlen2, ha0,
    ha1, hsum, hchan⟩ := hrest
  refine ⟨hmodeSrc, hpool, hholdings, hsa, hidx1, hguarantee, htgtMode, hta, hassetEq, a0, a1, ha0,
    ha1, hsum, ?_, ?_⟩
  · have hceq := congrFun hchan sourceChannelId
    rw [hceq]; unfold update; rw [if_pos rfl]
  · rw [reallocateGuarantee_getD sourceOutcome sourceAssetIndex indexOfTargetInSource hsa _ _ a0 a1
      ⟨0, []⟩]
    simp only
    have hleftSum := creditFirst_sum
      ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.eraseIdx indexOfTargetInSource)
      (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
        ⟨indexOfTargetInSource, hidx1⟩).metadata).1 a0 hfoundLeft
    have hrightFound := creditFirst_mono
      ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.eraseIdx indexOfTargetInSource)
      (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
        ⟨indexOfTargetInSource, hidx1⟩).metadata).1 a0 _ hfoundRight
    have hrightSum := creditFirst_sum
      (creditFirst ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.eraseIdx
        indexOfTargetInSource)
        (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
          ⟨indexOfTargetInSource, hidx1⟩).metadata).1 a0) _ a1 hrightFound
    have herase := listSum_eraseIdx_add (sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations
      indexOfTargetInSource hidx1
    rw [hrightSum, hleftSum]
    omega

/-- A-13 — channel value leaves only through a `.transfer`/bulk payout of
    a finalized channel: whenever a `Step` lowers a channel's own held
    value, that step is `.transfer`, `.bulkTransferAllAssets` or
    `.bulkConcludeAndTransferAllAssets` on that SAME channel, and the
    channel was already finalized when it ran (for the two bulk calls,
    "already finalized" covers `.bulkConcludeAndTransferAllAssets`'s own
    `.conclude` sub-step too, since that sub-step runs first, inside the
    SAME `Step`). No other call can ever lower a channel's collateral.
    REVISED from the audit's own A-13 text to name the bulk calls too:
    B4 restores them as real payout paths (`DOC/0080:77`), so excluding
    them here, as the audit's own candidate text does (it still assumed
    the pre-B4 model, where both bulk calls never succeed), would be
    false against the restored model.
    Quotes: `N19:227-229` "funds can only be withdrawn from participant
    addresses - and only by a party who knows the private key."
    `DOC/0080:5` "Defunding can only happen after a channel finalizes."
    `SATP:284-286` "assets deposited into an adjudicator contract are
    released only when given explicit consent on the final outcome by
    the channel's participants." `FM:1718-1726` "Once the game has
    ended ... a game's adjudicator should release funds";
    `Require(Adjudicator.isTerminated(channelId))`. Contract: holdings
    change only at `MAH.sol:228`, `ANA.sol:168`, `ANA.sol:199`
    (reclaim, departure) and `NA.sol:95` (bulk path — no longer a
    departure, B4). -/
theorem value_leaves_only_via_transfer_of_finalized_channel
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call) (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hstep : Step sig appRel actor s call s')
    (hdec : heldValue s' asset cid < heldValue s asset cid) :
    ((∃ assetIndex claimedStateHash outcome indices,
        call = .transfer assetIndex cid claimedStateHash outcome indices) ∧
      (s.channels cid).mode s.now = .finalized) ∨
    (∃ outcome claimedStateHash, call = .bulkTransferAllAssets cid outcome claimedStateHash ∧
      (s.channels cid).mode s.now = .finalized) ∨
    (∃ fp candidate, channelId fp = cid ∧ call = .bulkConcludeAndTransferAllAssets fp candidate) := by
  have hwf := holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach
  have hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro qasset qcid qpos qc hc
    obtain ⟨⟨pre, hpre, hcons, hval, _⟩, _⟩ := hwf qasset qcid qpos qc hc
    exact ⟨pre, hpre, hval, hcons⟩
  cases call with
  | deposit channelId0 expectedHeld asset0 amount =>
    exfalso
    by_cases hp : (asset0, channelId0) = (asset, cid)
    · have ha : asset0 = asset := congrArg Prod.fst hp
      have hc : channelId0 = cid := congrArg Prod.snd hp
      subst ha; subst hc
      have hinc := (deposit_effect sig appRel assets selfInputs pool0 actor s s' channelId0
        expectedHeld asset0 amount hreach hstep).1
      omega
    · have heq := deposit_frame sig appRel actor s s' channelId0 expectedHeld asset0 amount hstep
        hinv asset cid (Ne.symm hp)
      omega
  | challenge fp proof candidate challenger =>
    exfalso
    obtain ⟨_, _, _, _, _, hpool, hhold, _, _, _, _, _⟩ := hstep
    have heq : heldValue s' asset cid = heldValue s asset cid := by
      unfold heldValue; rw [hhold, hpool]
    omega
  | checkpoint fp proof candidate =>
    exfalso
    obtain ⟨_, _, _, _, hpool, hhold, _, _, _, _, _⟩ := hstep
    have heq : heldValue s' asset cid = heldValue s asset cid := by
      unfold heldValue; rw [hhold, hpool]
    omega
  | conclude fp candidate =>
    exfalso
    obtain ⟨_, _, _, _, hpool, hhold, _, _, _, _, _⟩ := hstep
    have heq : heldValue s' asset cid = heldValue s asset cid := by
      unfold heldValue; rw [hhold, hpool]
    omega
  | transfer assetIndex cid0 claimedStateHash outcome indices =>
    by_cases hcc : cid0 = cid
    · subst hcc
      obtain ⟨h, hmode, _, _, _, _, _, _, _, _⟩ := hstep
      exact Or.inl ⟨⟨assetIndex, claimedStateHash, outcome, indices, rfl⟩, hmode⟩
    · exfalso
      obtain ⟨h, _hmode, _, _, _, hinner, _, _, _, _⟩ := hstep
      obtain ⟨_hexit, hrest⟩ := hinner
      obtain ⟨r, hmatch, hholdseq, _hchan⟩ := hrest
      have hframe := PoolOwnedSpendStep_frame s.pool s'.pool s.self
        (outcome.get ⟨assetIndex, h⟩).asset cid0 _ r _ s.holdings
        (fun pre hpre => by
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
        hmatch hinv asset cid (fun hh => hcc (congrArg Prod.snd hh).symm)
      have heq : heldValue s' asset cid = heldValue s asset cid := by
        unfold heldValue; rw [hholdseq]; exact hframe
      omega
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    exfalso
    obtain ⟨_, _, _, _, _, _, hpool, hhold, _, _, _, _, _⟩ := hstep
    have heq : heldValue s' asset cid = heldValue s asset cid := by
      unfold heldValue; rw [hhold, hpool]
    omega
  | bulkTransferAllAssets cid0 outcome claimedStateHash =>
    by_cases hcc : cid0 = cid
    · subst hcc
      obtain ⟨hmode, _, _, newOutcome, _, _, _, _, _, _⟩ := hstep
      exact Or.inr (Or.inl ⟨outcome, claimedStateHash, rfl, hmode⟩)
    · exfalso
      obtain ⟨_hmode, _, _, newOutcome, hfold, _, _, _, _, _⟩ := hstep
      have hframe := bulkTransferFold_frame s.self cid0 outcome newOutcome s.pool s'.pool
        s.holdings s'.holdings hfold hinv asset cid (Ne.symm hcc)
      have heq : heldValue s' asset cid = heldValue s asset cid := by
        unfold heldValue; exact hframe
      omega
  | bulkConcludeAndTransferAllAssets fp candidate =>
    by_cases hcc : channelId fp = cid
    · exact Or.inr (Or.inr ⟨fp, candidate, hcc, rfl⟩)
    · exfalso
      obtain ⟨_hnotfin, _, _, newOutcome, hfold, _, _, _, _, _⟩ := hstep
      have hframe := bulkTransferFold_frame s.self (channelId fp) candidate.outcome newOutcome
        s.pool s'.pool s.holdings s'.holdings hfold hinv asset cid (Ne.symm hcc)
      have heq : heldValue s' asset cid = heldValue s asset cid := by
        unfold heldValue; exact hframe
      omega
  | tick newNow =>
    exfalso
    obtain ⟨_, _, hpool, hhold, _, _, _, _, _⟩ := hstep
    have heq : heldValue s' asset cid = heldValue s asset cid := by
      unfold heldValue; rw [hhold, hpool]
    omega
  | sign p d =>
    exfalso
    obtain ⟨_, _, hpool, _, hhold, _, _, _, _⟩ := hstep
    have heq : heldValue s' asset cid = heldValue s asset cid := by
      unfold heldValue; rw [hhold, hpool]
    omega
  | signNote pk msgHash =>
    exfalso
    obtain ⟨_, _, hpool, _, hhold, _, _, _, _⟩ := hstep
    have heq : heldValue s' asset cid = heldValue s asset cid := by
      unfold heldValue; rw [hhold, hpool]
    omega

/-- Like `OutcomeDerivedFrom`, but excluding `.reclaimStep`: reached
    from `o` by `.transfer` rewrites only, no `.reclaim` in between —
    what A-14 needs ("no `reclaim` on `c`"), since `.reclaimStep` is the
    one rewrite that can INCREASE an entry's own amount (crediting a
    guarantee's two destinations), breaking monotone decrease.
    Carries a THIRD index, `paid`: `paid i k` is the TOTAL amount asset
    `i`'s allocation `k` has been paid across the whole chain so far —
    at each `.transferStep`, the amount `.transfer` ACTUALLY pays entry
    `k` is the `afford`-computed amount at `k` when `k` is selected
    (the same value `A-01` uses), zero when `k` is not selected or the
    step touches a different asset. This is independent of
    `transferEffects`'s own old-minus-new arithmetic, so the theorem
    below is a real claim about what `.transfer` computes, not a
    restatement of subtraction. -/
inductive TransferOnlyDerivedFrom : Outcome → Outcome → (Nat → Nat → Nat) → Prop where
  | refl (o : Outcome) : TransferOnlyDerivedFrom o o (fun _ _ => 0)
  | transferStep {o mid : Outcome} {paid : Nat → Nat → Nat} (assetIndex : Nat)
      (h : assetIndex < mid.length) (heldBefore : Nat) (indices : List Nat)
      (hmid : TransferOnlyDerivedFrom o mid paid) :
      TransferOnlyDerivedFrom o
        (mid.mapIdx fun i exit => if i ≠ assetIndex then exit else
          { exit with allocations :=
              (transferEffects (mid.get ⟨assetIndex, h⟩).allocations heldBefore indices).1 })
        (fun i k => paid i k + (if i = assetIndex ∧ (indices = [] ∨ k ∈ indices) then
            (afford (mid.get ⟨assetIndex, h⟩).allocations heldBefore).getD k 0
          else 0))

/-- A-14 — cumulative payout to an entry never exceeds its allocation:
    across any `.transfer`-only call sequence from a finalized outcome
    `o` (no `.reclaim` in between — `TransferOnlyDerivedFrom`, above),
    entry `k`'s CURRENT remaining amount plus the TOTAL `paid i k` it
    has been paid across the whole sequence equals its ORIGINAL amount
    in `o` — so the total paid is at most what `o` allocated it.
    Quotes: `N19:836-837` "it is impossible to find a strategy that
    gives any node a value higher than allocated by this algorithm."
    `N19:770` T "Reduces the amount owed to B in the outcome of A by
    x." `FM:1843,1850` `w := Adjudicator.withdrawnAmounts`;
    `Adjudicator.withdrawnAmounts[k] += amount`. Contract:
    `MAH.sol:173,205` (amount reduced, fingerprint rewritten). -/
theorem cumulative_payout_never_exceeds_allocation
    (o o' : Outcome) (paid : Nat → Nat → Nat) (hder : TransferOnlyDerivedFrom o o' paid)
    (i k : Nat) :
    ((o'.getD i ⟨0, []⟩).allocations.getD k Allocation.default).amount + paid i k =
      ((o.getD i ⟨0, []⟩).allocations.getD k Allocation.default).amount ∧
    paid i k ≤ ((o.getD i ⟨0, []⟩).allocations.getD k Allocation.default).amount := by
  induction hder with
  | refl => simp
  | @transferStep mid paid0 assetIndex h heldBefore indices hmid ih =>
    obtain ⟨iheq, ihle⟩ := ih
    have hgetD : ((mid.mapIdx fun j exit => if j ≠ assetIndex then exit else
        { exit with allocations :=
            (transferEffects (mid.get ⟨assetIndex, h⟩).allocations heldBefore indices).1 }).getD i
        ⟨0, []⟩) =
        (if i ≠ assetIndex then mid.getD i ⟨0, []⟩ else
          { mid.get ⟨assetIndex, h⟩ with allocations :=
              (transferEffects (mid.get ⟨assetIndex, h⟩).allocations heldBefore indices).1 }) := by
      by_cases hi : i < mid.length
      · rw [mapIdx_getD mid _ i hi ⟨0, []⟩]
        by_cases hia : i = assetIndex
        · subst hia; simp
        · rw [if_pos hia, if_pos hia]
          congr 1
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          rfl
      · have h1 : (mid.mapIdx fun j exit => if j ≠ assetIndex then exit else
            { exit with allocations :=
                (transferEffects (mid.get ⟨assetIndex, h⟩).allocations heldBefore indices).1 }).getD i
            ⟨0, []⟩ = ⟨0, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]
          rfl
        have h2 : mid.getD i ⟨0, []⟩ = ⟨0, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
        have hia : i ≠ assetIndex := fun he => hi (he ▸ h)
        rw [h1, h2, if_pos hia]
    by_cases hia : i = assetIndex
    · subst hia
      rw [hgetD, if_neg (fun hne => hne rfl)]
      dsimp only
      have hlink : mid.getD i (⟨0, []⟩ : SingleAssetExit) = mid.get ⟨i, h⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
      rw [hlink] at iheq
      have hle := afford_le_getD (mid.get ⟨i, h⟩).allocations heldBefore k
      by_cases hsel : indices = [] ∨ k ∈ indices
      · have hval : ((transferEffects (mid.get ⟨i, h⟩).allocations heldBefore indices).1.getD k
            Allocation.default).amount =
            ((mid.get ⟨i, h⟩).allocations.getD k Allocation.default).amount -
              (afford (mid.get ⟨i, h⟩).allocations heldBefore).getD k 0 := by
          by_cases hik : k < (mid.get ⟨i, h⟩).allocations.length
          · have hget := transferEffects_newAllocations_getD (mid.get ⟨i, h⟩).allocations heldBefore
              indices k hik
            have hselb : (indices.isEmpty || k ∈ indices) = true := by
              rcases hsel with h0 | h0 <;> simp [h0]
            rw [hselb, if_pos rfl] at hget
            exact hget
          · have h1 : (mid.get ⟨i, h⟩).allocations.getD k Allocation.default = Allocation.default := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            have hlen := transferEffects_newAllocations_length (mid.get ⟨i, h⟩).allocations
              heldBefore indices
            have h2 : (transferEffects (mid.get ⟨i, h⟩).allocations heldBefore indices).1.getD k
                Allocation.default = Allocation.default := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            have hafford0' : (afford (mid.get ⟨i, h⟩).allocations heldBefore).getD k 0 = 0 := by
              have hlen2 := afford_length (mid.get ⟨i, h⟩).allocations heldBefore
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            rw [h1, h2, hafford0']
            omega
        rw [hval]
        split
        · omega
        · rename_i hc
          exact absurd ⟨rfl, hsel⟩ hc
      · have hval : ((transferEffects (mid.get ⟨i, h⟩).allocations heldBefore indices).1.getD k
            Allocation.default).amount = ((mid.get ⟨i, h⟩).allocations.getD k Allocation.default).amount := by
          by_cases hik : k < (mid.get ⟨i, h⟩).allocations.length
          · have hget := transferEffects_newAllocations_getD (mid.get ⟨i, h⟩).allocations heldBefore
              indices k hik
            have hselb : (indices.isEmpty || k ∈ indices) = false := by
              rw [not_or] at hsel
              simp [hsel.1, hsel.2]
            rw [hselb, if_neg (by simp)] at hget
            exact hget
          · have h1 : (mid.get ⟨i, h⟩).allocations.getD k Allocation.default = Allocation.default := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            have hlen := transferEffects_newAllocations_length (mid.get ⟨i, h⟩).allocations
              heldBefore indices
            have h2 : (transferEffects (mid.get ⟨i, h⟩).allocations heldBefore indices).1.getD k
                Allocation.default = Allocation.default := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            rw [h1, h2]
        rw [hval]
        split
        · rename_i hc
          exact absurd hc.2 hsel
        · omega
    · rw [hgetD, if_pos hia]
      dsimp only
      rw [if_neg (fun hc => hia hc.1)]
      omega

/-- A `.transfer` does not change the `heldValue` of any `(asset, channel)`
    key other than the paid key `((outcome.get ⟨assetIndex, _⟩).asset, cid)`.
    `PoolOwnedSpendStep_frame` keeps every other holding. -/
theorem transfer_heldValue_frame
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState)
    (assetIndex : Nat) (cid claimedStateHash : Term) (outcome : Outcome) (indices : List Nat)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hstep : Step sig appRel actor s (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (qasset : Nat) (c : Term) (hne : ∀ hidx : assetIndex < outcome.length,
      (qasset, c) ≠ ((outcome.get ⟨assetIndex, hidx⟩).asset, cid)) :
    heldValue s' qasset c = heldValue s qasset c := by
  obtain ⟨hidx, _, _, _, _, ⟨_, r, hospend, hholdseq, _⟩, _⟩ := hstep
  have htokPayout : ∀ pre ∈ (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1
      |>.filterMap (fun a => if a.amount = 0 then none else
        some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ :
          CommitmentPreimage)),
      pre.token = (outcome.get ⟨assetIndex, hidx⟩).asset := by
    intro pre hpre
    obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
    by_cases hamt : a.amount = 0
    · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
    · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl
  unfold heldValue
  rw [hholdseq]
  exact PoolOwnedSpendStep_frame s.pool s'.pool s.self (outcome.get ⟨assetIndex, hidx⟩).asset cid _
    r _ s.holdings htokPayout hospend (fun qa qc qpos qcm hq => by
      obtain ⟨⟨pre, hpre, hconsist, hval, _⟩, _⟩ :=
        holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach qa qc qpos qcm hq
      exact ⟨pre, hpre, hval, hconsist⟩)
    qasset c (hne hidx)

/-- The finalized part of `UnbeatablePaysInv`, for a channel `cid` and a
    reference outcome `o`. Disjunct A1: `cid` is finalized with a TRACKED
    current outcome `curOutcome`. `curOutcome` has the asset list of `o`.
    Its entry at `assetIndex` has no guarantee allocation. Its `destIdx`
    allocation is STILL `dest` (never selected yet) and still affords `x`.
    `afford_exchange_sel` carries this through a payout of any OTHER
    index. A1 keeps a full `curOutcome`, because `.reclaim` can rewrite
    the guarantee allocation of an OTHER asset index. Disjunct A2:
    `dest.destination` holds a live note worth at least `x`. A `.transfer`
    or `.bulkTransferAllAssets` mints this note the one time it pays
    `destIdx`. `appliesAll_note_survives` keeps the note live after that.
    `finalizedPaysInv_step` needs only an actor other than `Actor.pool pk`.
    Ticks are allowed, because finalization is permanent
    (`finalization_permanent`). -/
def FinalizedPaysInv (cid : Term) (o : Outcome) (assetIndex destIdx : Nat)
    (hAI : assetIndex < o.length) (x : Nat) (dest : Allocation) (mid : AdjudicatorState) : Prop :=
  (∃ (curOutcome : Outcome) (hci : assetIndex < curOutcome.length),
    (mid.channels cid).mode mid.now = .finalized ∧
    (mid.channels cid).outcomeHash = outcomeHashOf curOutcome ∧
    curOutcome.map SingleAssetExit.asset = o.map SingleAssetExit.asset ∧
    (∀ a ∈ (curOutcome.get ⟨assetIndex, hci⟩).allocations, a.allocationType ≠ .guarantee) ∧
    (curOutcome.get ⟨assetIndex, hci⟩).asset = (o.get ⟨assetIndex, hAI⟩).asset ∧
    (curOutcome.get ⟨assetIndex, hci⟩).allocations.getD destIdx Allocation.default = dest ∧
    x ≤ (afford (curOutcome.get ⟨assetIndex, hci⟩).allocations
      (heldValue mid (o.get ⟨assetIndex, hAI⟩).asset cid)).getD destIdx 0) ∨
  (∃ pre : CommitmentPreimage,
    pre.npk = dest.destination ∧
    pre.token = (o.get ⟨assetIndex, hAI⟩).asset ∧ x ≤ pre.value ∧
    PoolIsLive mid.pool (commitment pre.npk pre.token pre.value))

/-- `FinalizedPaysInv`'s one-step preservation. The actor is not
    `Actor.pool pk`, and the `poolSignedBy pk` row is still its `s0`
    value. A2 survives every call (`note_survives_step`). A1 survives
    every call. A `.challenge`, `.checkpoint`, `.conclude` or
    `.bulkConcludeAndTransferAllAssets` on `cid` cannot run, because `cid`
    is finalized. A `.tick` keeps `cid` finalized. A `.transfer` that
    selects `destIdx`, or a `.bulkTransferAllAssets` on `cid`, changes A1
    into A2. Any other `.transfer` or `.reclaim` on `cid` keeps A1 with a
    new `curOutcome`. A deposit can only increase `heldValue`. -/
theorem finalizedPaysInv_step
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (cid : Term) (o : Outcome) (assetIndex destIdx : Nat) (hAI : assetIndex < o.length) (x : Nat)
    (hxpos : 0 < x)
    (dest : Allocation) (pk : Nat × Nat) (nk r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (s0 : AdjudicatorState)
    (hassetunique : ∀ i (hi : i < o.length), i ≠ assetIndex →
      (o.get ⟨i, hi⟩).asset ≠ (o.get ⟨assetIndex, hAI⟩).asset)
    (hhonestPool : ∀ m, s0.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hstep : Step sig appRel actor s call s')
    (hactorPool : actor ≠ Actor.pool pk)
    (hprow : s.poolSignedBy pk = s0.poolSignedBy pk)
    (hinv : FinalizedPaysInv cid o assetIndex destIdx hAI x dest s) :
    FinalizedPaysInv cid o assetIndex destIdx hAI x dest s' := by
  unfold FinalizedPaysInv at hinv ⊢
  rcases hinv with hA1 | ⟨pre, hnpkA2, htokenA2, hxleA2, t, tn, pos, pre', hmem, hhash⟩
  rotate_left
  · have hpreeq : pre' = pre := hashCommitment_inj hhash
    have hmem' : ((tn, pos), pre) ∈ s'.pool.live t :=
      note_survives_step sig appRel pk nk r s0
        (fun m hm {N M} w pub hmh hc hpk i => hh_dest ▸ hhonestPool m hm w pub hmh hc hpk i)
        actor s s' call hstep hactorPool hprow
        t (tn, pos) pre (hnpkA2.trans hh_dest) (hpreeq ▸ hmem)
    exact Or.inr ⟨pre, hnpkA2, htokenA2, hxleA2, t, tn, pos, pre, hmem', rfl⟩
  obtain ⟨curOutcome, hci, hfin, hohA1, hassetprojA1, hnogA1, hasset, hallocD, haffA1⟩ := hA1
  have hframe : s'.channels cid = s.channels cid → (s.channels cid).mode s'.now = .finalized →
      heldValue s (o.get ⟨assetIndex, hAI⟩).asset cid ≤
        heldValue s' (o.get ⟨assetIndex, hAI⟩).asset cid →
      FinalizedPaysInv cid o assetIndex destIdx hAI x dest s' := fun hc hm hle =>
    Or.inl ⟨curOutcome, hci, by rw [hc]; exact hm, by rw [hc]; exact hohA1, hassetprojA1, hnogA1,
      hasset, hallocD, Nat.le_trans haffA1 (afford_mono _ hle destIdx)⟩
  have hheldOf : s'.holdings = s.holdings → s'.pool = s.pool →
      heldValue s (o.get ⟨assetIndex, hAI⟩).asset cid ≤
        heldValue s' (o.get ⟨assetIndex, hAI⟩).asset cid :=
    fun hh hp => Nat.le_of_eq (by unfold heldValue; rw [hh, hp])
  have hholdinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro qasset qcid qpos qc hc
    obtain ⟨⟨pre, hpre, hconsist, hval, _⟩, _⟩ :=
      holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach qasset qcid qpos qc hc
    exact ⟨pre, hpre, hval, hconsist⟩
  cases call with
  | tick newNow =>
    obtain ⟨hge, hnow, hpool, hhold, hchan, _⟩ := hstep
    refine hframe (by rw [hchan]) ?_ (hheldOf hhold hpool)
    have hfz : (s.channels cid).finalizesAt ≠ 0 := by
      intro hz; unfold ChannelStatus.mode at hfin; simp [hz] at hfin
    have hfle : (s.channels cid).finalizesAt ≤ s.now := by
      unfold ChannelStatus.mode at hfin
      rw [if_neg hfz] at hfin
      split at hfin
      · assumption
      · exact absurd hfin (by simp)
    rw [hnow]
    unfold ChannelStatus.mode
    rw [if_neg hfz, if_pos (by omega)]
  | sign p d =>
    obtain ⟨_, _, hpool, hchan, hholdeq, _, _, hnow, _⟩ := hstep
    exact hframe (by rw [hchan]) (hnow ▸ hfin) (hheldOf hholdeq hpool)
  | signNote pk' msgHash =>
    obtain ⟨_, _, hpool, hchan, hholdeq, _, _, hnow, _⟩ := hstep
    exact hframe (by rw [hchan]) (hnow ▸ hfin) (hheldOf hholdeq hpool)
  | deposit cid' expectedHeld asset amount =>
    obtain ⟨hdeffect, hdframe, hchan⟩ :=
      deposit_effect sig appRel assets selfInputs pool0 actor s s' cid' expectedHeld asset amount
        hreach hstep
    obtain ⟨_, _, _, _, _, _, _, _, hnow, _⟩ := hstep
    refine hframe (by rw [hchan]) (hnow ▸ hfin) ?_
    by_cases hac : ((o.get ⟨assetIndex, hAI⟩).asset, cid) = (asset, cid')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hac
      rw [hdeffect]; exact Nat.le_add_right _ _
    · exact Nat.le_of_eq (hdframe _ _ hac).symm
  | challenge fp' proof candidate' challenger =>
    obtain ⟨hprecond, _, _, _, hchan, hspool, hsholdeq, _, _, hnow, _⟩ := hstep
    by_cases hcc : channelId fp' = cid
    · exfalso
      rw [← hcc] at hfin
      rw [hfin] at hprecond
      exact hprecond
    · exact hframe (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)])
        (hnow ▸ hfin) (hheldOf hsholdeq hspool)
  | checkpoint fp' proof candidate' =>
    obtain ⟨hprecond, _, _, hchan, hspool, hsholdeq, _, _, hnow, _⟩ := hstep
    by_cases hcc : channelId fp' = cid
    · rw [← hcc] at hfin
      exact absurd hfin hprecond
    · exact hframe (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)])
        (hnow ▸ hfin) (hheldOf hsholdeq hspool)
  | conclude fp' candidate' =>
    obtain ⟨hprecond, _, _, hchan, hspool, hsholdeq, _, _, hnow, _⟩ := hstep
    by_cases hcc : channelId fp' = cid
    · rw [← hcc] at hfin
      exact absurd hfin hprecond
    · exact hframe (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)])
        (hnow ▸ hfin) (hheldOf hsholdeq hspool)
  | transfer assetIndex' cid' claimedStateHash outcome indices =>
    by_cases hcc : cid' = cid
    rotate_left
    · have hheld := transfer_heldValue_frame sig appRel assets selfInputs pool0 actor s s'
        assetIndex' cid' claimedStateHash outcome indices hreach hstep
        (o.get ⟨assetIndex, hAI⟩).asset cid (fun _ heq => hcc (congrArg Prod.snd heq).symm)
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, hchan⟩, _, _, hnow, _⟩ := hstep
      exact hframe (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)])
        (hnow ▸ hfin) (Nat.le_of_eq hheld.symm)
    subst cid'
    have hframeT := transfer_heldValue_frame sig appRel assets selfInputs pool0 actor s s'
      assetIndex' cid claimedStateHash outcome indices hreach hstep (o.get ⟨assetIndex, hAI⟩).asset cid
    obtain ⟨hidx, _, _, hohT, _, ⟨_, r, hospend, hholdseq, hchan⟩, _, _, hnow, _⟩ := hstep
    have houtcome_eq : curOutcome = outcome := outcomeHashOf_inj (hohA1.symm.trans hohT)
    subst curOutcome
    by_cases hai : assetIndex' = assetIndex
    · subst hai
      have hallocDEq : (outcome.get ⟨assetIndex', hidx⟩).allocations.getD destIdx
          Allocation.default = dest := hallocD
      have hdestNeDefault : dest ≠ Allocation.default := by
        intro hcon
        have heq2 : dest.destination = Term.val 0 := by rw [hcon]; rfl
        rw [hh_dest] at heq2
        unfold npk at heq2
        exact Term.val_ne_hash 0 .poseidon _ heq2.symm
      let allocs := (outcome.get ⟨assetIndex', hidx⟩).allocations
      let surplus := heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid
      let sel : Nat → Bool := fun i => indices.isEmpty || i ∈ indices
      have hdestIdxRange : destIdx < allocs.length := by
        by_cases hcon : destIdx < allocs.length
        · exact hcon
        · exfalso
          have hge : allocs.length ≤ destIdx := Nat.le_of_not_lt hcon
          have hnone : allocs[destIdx]? = none := List.getElem?_eq_none_iff.mpr hge
          rw [List.getD_eq_getElem?_getD, hnone] at hallocDEq
          exact hdestNeDefault hallocDEq.symm
      have hteq : (transferEffects allocs surplus indices) =
          transferEffectsSel allocs surplus sel := transferEffects_eq_sel allocs surplus indices
      have haffA1' : x ≤ (afford allocs surplus).getD destIdx 0 := by
        show x ≤ (afford allocs (heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid)).getD
          destIdx 0
        rw [hasset]; exact haffA1
      by_cases hsel : sel destIdx = true
      · right
        have hpaidNe : (afford allocs surplus).getD destIdx 0 ≠ 0 := by omega
        have hexitmem : { allocs.getD destIdx Allocation.default with
            amount := (afford allocs surplus).getD destIdx 0 } ∈
            (transferEffectsSel allocs surplus sel).2.1 :=
          transferEffectsSel_exit_mem allocs surplus sel destIdx hdestIdxRange hsel
        rw [← hteq] at hexitmem
        rw [hallocDEq] at hexitmem
        have hexitmem' : { dest with amount := (afford allocs surplus).getD destIdx 0 } ∈
            (transferEffects allocs surplus indices).2.1 := hexitmem
        have hpayoutmem : (⟨dest.destination, (outcome.get ⟨assetIndex', hidx⟩).asset,
            (afford allocs surplus).getD destIdx 0⟩ : CommitmentPreimage) ∈
            (transferEffects allocs surplus indices).2.1.filterMap (fun a =>
              if a.amount = 0 then none else
                some (⟨a.destination, (outcome.get ⟨assetIndex', hidx⟩).asset, a.amount⟩ :
                  CommitmentPreimage)) := by
          apply List.mem_filterMap.mpr
          refine ⟨{ dest with amount := (afford allocs surplus).getD destIdx 0 }, hexitmem', ?_⟩
          rw [if_neg hpaidNe]
        have houtmem : (⟨dest.destination, (outcome.get ⟨assetIndex', hidx⟩).asset,
            (afford allocs surplus).getD destIdx 0⟩ : CommitmentPreimage) ∈
            (transferEffects allocs surplus indices).2.1.filterMap (fun a =>
              if a.amount = 0 then none else
                some (⟨a.destination, (outcome.get ⟨assetIndex', hidx⟩).asset, a.amount⟩ :
                  CommitmentPreimage)) ++
            (if heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                (transferEffects allocs surplus indices).2.2 = 0 then []
             else [(⟨npk s.self r, (outcome.get ⟨assetIndex', hidx⟩).asset,
               heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                 (transferEffects allocs surplus indices).2.2⟩ : CommitmentPreimage)]) :=
          List.mem_append_left _ hpayoutmem
        obtain ⟨pos, hposmem⟩ := withTreePositionsFrom_mem_fwd
          (treeNumber := insertTreeNumber s.pool.closedTrees s.pool.leaves
            (((transferEffects allocs surplus indices).2.1.filterMap (fun a =>
                if a.amount = 0 then none else
                  some (⟨a.destination, (outcome.get ⟨assetIndex', hidx⟩).asset, a.amount⟩ :
                    CommitmentPreimage))).length +
              (if heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                  (transferEffects allocs surplus indices).2.2 = 0 then []
               else [(⟨npk s.self r, (outcome.get ⟨assetIndex', hidx⟩).asset,
                 heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                   (transferEffects allocs surplus indices).2.2⟩ : CommitmentPreimage)]).length))
          (start := insertStartPos s.pool.leaves
            (((transferEffects allocs surplus indices).2.1.filterMap (fun a =>
                if a.amount = 0 then none else
                  some (⟨a.destination, (outcome.get ⟨assetIndex', hidx⟩).asset, a.amount⟩ :
                    CommitmentPreimage))).length +
              (if heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                  (transferEffects allocs surplus indices).2.2 = 0 then []
               else [(⟨npk s.self r, (outcome.get ⟨assetIndex', hidx⟩).asset,
                 heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                   (transferEffects allocs surplus indices).2.2⟩ : CommitmentPreimage)]).length))
          houtmem
        have hlivemem : ((insertTreeNumber s.pool.closedTrees s.pool.leaves
            (((transferEffects allocs surplus indices).2.1.filterMap (fun a =>
                if a.amount = 0 then none else
                  some (⟨a.destination, (outcome.get ⟨assetIndex', hidx⟩).asset, a.amount⟩ :
                    CommitmentPreimage))).length +
              (if heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                  (transferEffects allocs surplus indices).2.2 = 0 then []
               else [(⟨npk s.self r, (outcome.get ⟨assetIndex', hidx⟩).asset,
                 heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid -
                   (transferEffects allocs surplus indices).2.2⟩ : CommitmentPreimage)]).length),
            pos), (⟨dest.destination, (outcome.get ⟨assetIndex', hidx⟩).asset,
            (afford allocs surplus).getD destIdx 0⟩ : CommitmentPreimage)) ∈
            s'.pool.live (outcome.get ⟨assetIndex', hidx⟩).asset := by
          rcases hh : s.holdings (outcome.get ⟨assetIndex', hidx⟩).asset cid with
            _ | ⟨pos0, c0⟩
          · rw [hh] at hospend
            obtain ⟨w, pub, hM, hC, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes,
              hroot, hmark, hRandomOut, heq⟩ := hospend
            rw [heq]; dsimp only
            rw [if_pos rfl]
            exact List.mem_append_left _ hposmem
          · rw [hh] at hospend
            obtain ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero, hself, htoken,
              hnewnotes, hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hospend
            rw [heq]; dsimp only
            rw [if_pos rfl]
            exact List.mem_append_left _ hposmem
        refine ⟨⟨dest.destination, (outcome.get ⟨assetIndex', hidx⟩).asset,
          (afford allocs surplus).getD destIdx 0⟩, rfl, ?_, haffA1', ?_⟩
        · exact hasset
        · exact ⟨(outcome.get ⟨assetIndex', hidx⟩).asset, _, pos, _, hlivemem, rfl⟩
      · left
        have hselfalse : sel destIdx = false := by
          rcases hbsel : sel destIdx with _ | _
          · rfl
          · exact absurd hbsel hsel
        have hnewAllocsDestD : (transferEffectsSel allocs surplus sel).1.getD destIdx
            Allocation.default = dest := by
          rw [transferEffectsSel_getD_full allocs surplus sel destIdx hdestIdxRange, hselfalse]
          exact hallocDEq
        have hnewAffordDest : (afford (transferEffectsSel allocs surplus sel).1
            (surplus - (transferEffectsSel allocs surplus sel).2.2)).getD destIdx 0 =
            (afford allocs surplus).getD destIdx 0 :=
          afford_exchange_sel allocs surplus sel destIdx hselfalse
        have htokPayout : ∀ pre ∈ (transferEffects allocs surplus indices).2.1
            |>.filterMap (fun a => if a.amount = 0 then none else
              some (⟨a.destination, (outcome.get ⟨assetIndex', hidx⟩).asset, a.amount⟩ :
                CommitmentPreimage)),
            pre.token = (outcome.get ⟨assetIndex', hidx⟩).asset := by
          intro pre hpre
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl
        have hheldEq' : heldValue s' (outcome.get ⟨assetIndex', hidx⟩).asset cid =
            surplus - (transferEffectsSel allocs surplus sel).2.2 := by
          have ht : heldValue s' (outcome.get ⟨assetIndex', hidx⟩).asset cid =
              surplus - (transferEffects allocs surplus indices).2.2 := by
            unfold heldValue
            rw [hholdseq]
            exact PoolOwnedSpendStep_sets_heldValue s.pool s'.pool s.self
              (outcome.get ⟨assetIndex', hidx⟩).asset cid _ r _ s.holdings
              htokPayout hospend
          rw [ht, hteq]
        let g : Nat → SingleAssetExit → SingleAssetExit := fun i exit =>
          if i ≠ assetIndex' then exit else
            { exit with allocations := (transferEffectsSel allocs surplus sel).1 }
        have hci' : assetIndex' < (outcome.mapIdx g).length := by
          rw [List.length_mapIdx]; exact hidx
        have hentryEq : (outcome.mapIdx g).get ⟨assetIndex', hci'⟩ =
            { outcome.get ⟨assetIndex', hidx⟩ with
              allocations := (transferEffectsSel allocs surplus sel).1 } := by
          rw [mapIdx_get outcome g assetIndex' hidx hci']
          show (if assetIndex' ≠ assetIndex' then outcome.get ⟨assetIndex', hidx⟩ else _) = _
          rw [if_neg (fun h => h rfl)]
        refine ⟨outcome.mapIdx g, hci', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hchan, hnow]; unfold update; rw [if_pos rfl]; dsimp only; exact hfin
        · rw [hchan]; unfold update; rw [if_pos rfl]; rfl
        · exact (mapIdx_asset_preserved outcome g (by
            intro i exit
            show (if i ≠ assetIndex' then exit else _).asset = exit.asset
            split <;> rfl)).trans hassetprojA1
        · rw [hentryEq]; dsimp only
          intro a ha
          have hlenNew : (transferEffectsSel allocs surplus sel).1.length = allocs.length := by
            unfold transferEffectsSel; simp [afford_length]
          obtain ⟨i, hilt, hieq⟩ := List.mem_iff_getElem.mp ha
          have hilt' : i < allocs.length := hlenNew ▸ hilt
          have hfull := transferEffectsSel_getD_full allocs surplus sel i hilt'
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt] at hfull
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt'] at hfull
          simp only [Option.getD_some] at hfull
          have : a.allocationType = (allocs[i]'hilt').allocationType := by
            rw [← hieq, hfull]
          rw [this]
          exact hnogA1 _ (List.getElem_mem hilt')
        · rw [hentryEq]; dsimp only; exact hasset
        · rw [hentryEq]; dsimp only; exact hnewAllocsDestD
        · rw [hentryEq]; dsimp only
          rw [← hasset, hheldEq', hnewAffordDest]
          exact haffA1'
    · left
      have hidxOcand : assetIndex' < o.length := by
        have := congrArg List.length hassetprojA1; simp at this; omega
      have hassetdiff : (outcome.get ⟨assetIndex', hidx⟩).asset ≠
          (o.get ⟨assetIndex, hAI⟩).asset := by
        have hmap : (outcome.map SingleAssetExit.asset)[assetIndex']? =
            (o.map SingleAssetExit.asset)[assetIndex']? := by rw [hassetprojA1]
        rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hidx,
          List.getElem?_eq_getElem hidxOcand] at hmap
        have heq : (outcome.get ⟨assetIndex', hidx⟩).asset =
            (o.get ⟨assetIndex', hidxOcand⟩).asset := by
          simpa [List.get_eq_getElem] using Option.some.inj hmap
        rw [heq]; exact hassetunique assetIndex' hidxOcand hai
      let f : Nat → SingleAssetExit → SingleAssetExit := fun i exit =>
        if i ≠ assetIndex' then exit else
          { exit with allocations :=
              (transferEffects (outcome.get ⟨assetIndex', hidx⟩).allocations
                (heldValue s (outcome.get ⟨assetIndex', hidx⟩).asset cid)
                indices).1 }
      have hci' : assetIndex < (outcome.mapIdx f).length := by
        rw [List.length_mapIdx]; exact hci
      have hentryEq : (outcome.mapIdx f).get ⟨assetIndex, hci'⟩ = outcome.get ⟨assetIndex, hci⟩ := by
        rw [mapIdx_get outcome f assetIndex hci hci']
        show (if assetIndex ≠ assetIndex' then outcome.get ⟨assetIndex, hci⟩ else _) =
          outcome.get ⟨assetIndex, hci⟩
        rw [if_pos (Ne.symm hai)]
      have hheldEq := hframeT (fun _ heq => hassetdiff (congrArg Prod.fst heq).symm)
      refine ⟨outcome.mapIdx f, hci', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchan, hnow]; unfold update; rw [if_pos rfl]; dsimp only; exact hfin
      · rw [hchan]; unfold update; rw [if_pos rfl]; rfl
      · exact (mapIdx_asset_preserved outcome f (by
          intro i exit
          show (if i ≠ assetIndex' then exit else _).asset = exit.asset
          split <;> rfl)).trans hassetprojA1
      · rw [hentryEq]; exact hnogA1
      · rw [hentryEq]; exact hasset
      · rw [hentryEq]; exact hallocD
      · rw [hentryEq, hheldEq]; exact haffA1
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, hohSrc, hsa, hidx1, hguarantee, hrest, hspool, hsholdeq, _, _, hnow, _⟩ := hstep
    obtain ⟨_, _, _, _, _, _, _, a0, a1, _, _, _, _, hchan⟩ := hrest
    by_cases hcc : sourceChannelId = cid
    rotate_left
    · exact hframe (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)])
        (hnow ▸ hfin) (hheldOf hsholdeq hspool)
    subst sourceChannelId
    have houtcome_eq : curOutcome = sourceOutcome := outcomeHashOf_inj (hohA1.symm.trans hohSrc)
    subst curOutcome
    by_cases hai : sourceAssetIndex = assetIndex
    · subst hai
      exact absurd hguarantee (hnogA1 _ (List.get_mem ..))
    · left
      have hci' : assetIndex < (reallocateGuarantee sourceOutcome sourceAssetIndex
          indexOfTargetInSource
          (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
            ⟨indexOfTargetInSource, hidx1⟩).metadata).1
          (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
            ⟨indexOfTargetInSource, hidx1⟩).metadata).2 a0 a1).length := by
        unfold reallocateGuarantee; rw [List.length_mapIdx]; exact hci
      have hentryEq : (reallocateGuarantee sourceOutcome sourceAssetIndex indexOfTargetInSource
          (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
            ⟨indexOfTargetInSource, hidx1⟩).metadata).1
          (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
            ⟨indexOfTargetInSource, hidx1⟩).metadata).2 a0 a1).get ⟨assetIndex, hci'⟩ =
          sourceOutcome.get ⟨assetIndex, hci⟩ := by
        unfold reallocateGuarantee
        rw [mapIdx_get sourceOutcome _ assetIndex hci hci']
        show (if assetIndex ≠ sourceAssetIndex then sourceOutcome.get ⟨assetIndex, hci⟩
          else _) = _
        rw [if_pos (Ne.symm hai)]
      refine ⟨reallocateGuarantee sourceOutcome sourceAssetIndex indexOfTargetInSource
        (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
          ⟨indexOfTargetInSource, hidx1⟩).metadata).1
        (decodeGuarantee ((sourceOutcome.get ⟨sourceAssetIndex, hsa⟩).allocations.get
          ⟨indexOfTargetInSource, hidx1⟩).metadata).2 a0 a1, hci', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchan, hnow]; unfold update; rw [if_pos rfl]; dsimp only; exact hfin
      · rw [hchan]; unfold update; rw [if_pos rfl]
      · unfold reallocateGuarantee
        exact (mapIdx_asset_preserved sourceOutcome _ (by
          intro i exit
          show (if i ≠ sourceAssetIndex then exit else _).asset = exit.asset
          split <;> rfl)).trans hassetprojA1
      · rw [hentryEq]; exact hnogA1
      · rw [hentryEq]; exact hasset
      · rw [hentryEq]; exact hallocD
      · rw [hentryEq]
        exact Nat.le_trans haffA1 (afford_mono _ (hheldOf hsholdeq hspool) destIdx)
  | bulkTransferAllAssets cid' outcome claimedStateHash =>
    obtain ⟨_, _, hohBulk, newOutcome, hfold, hchan, _, _, hnow, _⟩ := hstep
    by_cases hcc : cid' = cid
    rotate_left
    · have hheld : heldValue s' (o.get ⟨assetIndex, hAI⟩).asset cid =
          heldValue s (o.get ⟨assetIndex, hAI⟩).asset cid := by
        unfold heldValue
        exact bulkTransferFold_heldValue_frame_cid s.self cid' outcome newOutcome s.pool s'.pool
          s.holdings s'.holdings hfold hholdinv _ cid (fun heq => hcc heq.symm)
      exact hframe (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)])
        (hnow ▸ hfin) (Nat.le_of_eq hheld.symm)
    subst cid'
    have houtcome_eq : curOutcome = outcome := outcomeHashOf_inj (hohA1.symm.trans hohBulk)
    subst curOutcome
    right
    have hidxN : assetIndex < newOutcome.length := by
      rw [bulkTransferFold_length s.self cid outcome newOutcome s.pool s'.pool
        s.holdings s'.holdings hfold]
      exact hci
    have hassetuniqueFold : ∀ j (hj : j < outcome.length), j ≠ assetIndex →
        (outcome.get ⟨j, hj⟩).asset ≠ (outcome.get ⟨assetIndex, hci⟩).asset := by
      intro j hj hjne
      have hjCand : j < o.length := by
        have := congrArg List.length hassetprojA1; simp at this; omega
      have hmap : (outcome.map SingleAssetExit.asset)[j]? = (o.map SingleAssetExit.asset)[j]? := by
        rw [hassetprojA1]
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hjCand] at hmap
      have heq : (outcome.get ⟨j, hj⟩).asset = (o.get ⟨j, hjCand⟩).asset := by
        simpa [List.get_eq_getElem] using Option.some.inj hmap
      rw [heq, hasset]
      exact hassetunique j hjCand hjne
    obtain ⟨_, hpayoutExists⟩ :=
      bulkTransferFold_index_payout s.self cid outcome newOutcome s.pool s'.pool
        s.holdings s'.holdings hfold hholdinv assetIndex hci hassetuniqueFold hidxN
    have haffAtDest : x ≤ (afford (outcome.get ⟨assetIndex, hci⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, hci⟩).asset cid)).getD destIdx 0 := by
      rw [hasset]; exact haffA1
    have hpayoutNe : (afford (outcome.get ⟨assetIndex, hci⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, hci⟩).asset cid)).getD destIdx 0 ≠ 0 := by omega
    obtain ⟨pos, hlivemem⟩ := hpayoutExists destIdx hpayoutNe
    refine ⟨⟨(outcome.get ⟨assetIndex, hci⟩).allocations.getD destIdx
      Allocation.default |>.destination, (outcome.get ⟨assetIndex, hci⟩).asset,
      (afford (outcome.get ⟨assetIndex, hci⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, hci⟩).asset cid)).getD destIdx 0⟩,
      ?_, hasset, haffAtDest, ?_⟩
    · rw [hallocD]
    · exact ⟨(outcome.get ⟨assetIndex, hci⟩).asset, pos.1, pos.2, _, hlivemem, rfl⟩
  | bulkConcludeAndTransferAllAssets fp' candidate' =>
    obtain ⟨hprecond, _, _, newOutcome, hfold, hchan, _, _, hnow, _⟩ := hstep
    by_cases hcc : channelId fp' = cid
    · rw [← hcc] at hfin
      exact absurd hfin hprecond
    · have hheld : heldValue s' (o.get ⟨assetIndex, hAI⟩).asset cid =
          heldValue s (o.get ⟨assetIndex, hAI⟩).asset cid := by
        unfold heldValue
        exact bulkTransferFold_heldValue_frame_cid s.self (channelId fp') candidate'.outcome
          newOutcome s.pool s'.pool s.holdings s'.holdings hfold hholdinv _ cid
          (fun heq => hcc heq.symm)
      exact hframe (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)])
        (hnow ▸ hfin) (Nat.le_of_eq hheld.symm)

/-- `finalizedPaysInv_step` across a whole call sequence. No call in the
    sequence is by `Actor.pool pk`. Ticks are allowed. The result also
    keeps the `poolSignedBy pk` row at its `s0` value. -/
theorem finalizedPaysInv_appliesAll
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (cid : Term) (o : Outcome) (assetIndex destIdx : Nat) (hAI : assetIndex < o.length) (x : Nat)
    (hxpos : 0 < x)
    (dest : Allocation) (pk : Nat × Nat) (nk r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (s0 : AdjudicatorState)
    (hassetunique : ∀ i (hi : i < o.length), i ≠ assetIndex →
      (o.get ⟨i, hi⟩).asset ≠ (o.get ⟨assetIndex, hAI⟩).asset)
    (hhonestPool : ∀ m, s0.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) :
    ∀ {calls : List (Actor × Call)} {s s' : AdjudicatorState},
      Reachable sig appRel (genesis assets selfInputs pool0) s →
      AppliesAll sig appRel s calls s' →
      (∀ actor call, (actor, call) ∈ calls → actor ≠ Actor.pool pk) →
      s.poolSignedBy pk = s0.poolSignedBy pk →
      FinalizedPaysInv cid o assetIndex destIdx hAI x dest s →
      FinalizedPaysInv cid o assetIndex destIdx hAI x dest s'
  | [], s, s', _, happ, _, _, hinv => by
    rw [show s' = s from happ]; exact hinv
  | (actor, call) :: rest, s, _, hreach, happ, hexcl, hprow, hinv => by
    obtain ⟨mid, hstep, hrest⟩ := happ
    have hactorPool : actor ≠ Actor.pool pk := hexcl actor call (List.mem_cons_self ..)
    exact finalizedPaysInv_appliesAll sig appRel cid o assetIndex destIdx hAI x hxpos dest pk nk r
      hh_dest s0 hassetunique hhonestPool assets selfInputs pool0 (reachable_step hreach hstep)
      hrest (fun actor' call' hc => hexcl actor' call' (List.mem_cons_of_mem _ hc))
      ((poolSignedBy_frame sig appRel actor s mid call hstep pk hactorPool).trans hprow)
      (finalizedPaysInv_step sig appRel cid o assetIndex destIdx hAI x hxpos dest pk nk r hh_dest
        s0 hassetunique hhonestPool assets selfInputs pool0 actor s mid call hreach hstep
        hactorPool hprow hinv)

/-- `unbeatable_pays`/`unbeatable_pays_after_timeout`'s own interleaving
    invariant, carried one `Step` at a time. EITHER (B) `fp`'s own channel
    is not yet finalized, `candidate` still has every participant's own
    signature, and `destIdx` still affords `x`, OR the finalized part
    `FinalizedPaysInv` holds for `channelId fp` and `candidate.outcome`
    (A1: finalized with a tracked current outcome that still affords `x`
    at `destIdx`; A2: `dest` already holds a live note worth `x`). -/
def UnbeatablePaysInv (sig : SignatureAssumptions) (fp : FixedPart) (candidate : VariablePart)
    (assetIndex destIdx : Nat) (hAssetIdx : assetIndex < candidate.outcome.length) (x : Nat)
    (dest : Allocation) (mid : AdjudicatorState) : Prop :=
  ((mid.channels (channelId fp)).mode mid.now ≠ .finalized ∧ SignedByAll sig mid fp candidate ∧
    x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
      (heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
        (channelId fp))).getD destIdx 0) ∨
  FinalizedPaysInv (channelId fp) candidate.outcome assetIndex destIdx hAssetIdx x dest mid

/-- `UnbeatablePaysInv`'s own one-step preservation: given an actor OTHER
    than `h`/`h`'s own pool key, and `h`'s `signedBy`/`poolSignedBy` rows
    still exactly their `s0` (anchor) values, the invariant survives. The
    finalized disjuncts use `finalizedPaysInv_step`. B either stays B, or
    becomes A1 by a `.conclude` of `candidate`, or becomes A2 by a
    `.bulkConcludeAndTransferAllAssets` of `candidate` (`hhonest`). -/
theorem unbeatablePaysInv_step
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (h : Nat) (fp : FixedPart) (candidate : VariablePart) (hp : h ∈ fp.participants)
    (hduration : 0 < fp.challengeDuration)
    (assetIndex destIdx : Nat) (hAssetIdx : assetIndex < candidate.outcome.length) (x : Nat)
    (hxpos : 0 < x)
    (dest : Allocation) (pk : Nat × Nat) (nk r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (s0 : AdjudicatorState)
    (hdest : (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations[destIdx]? = some dest)
    (hassetunique : ∀ i (hi : i < candidate.outcome.length), i ≠ assetIndex →
      (candidate.outcome.get ⟨i, hi⟩).asset ≠ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset)
    (hnoguarantee : ∀ a ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations,
      a.allocationType ≠ .guarantee)
    (hhonest : ∀ candidate', candidate'.isFinal = true →
      AuthorizedBy sig s0 h (stateHash fp candidate') →
      stateHash fp candidate' = stateHash fp candidate)
    (hhonestPool : ∀ m, s0.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hstep : Step sig appRel actor s call s')
    (hactor : actor ≠ Actor.nitro h) (hactorPool : actor ≠ Actor.pool pk)
    (hnotick : ∀ newNow, call ≠ Call.tick newNow)
    (hsrow : s.signedBy h = s0.signedBy h) (hprow : s.poolSignedBy pk = s0.poolSignedBy pk)
    (hinv : UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest s) :
    UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest s' := by
  unfold UnbeatablePaysInv at hinv ⊢
  rcases hinv with ⟨hmode, hsigned, haff⟩ | hF
  rotate_left
  · exact Or.inr (finalizedPaysInv_step sig appRel (channelId fp) candidate.outcome assetIndex
      destIdx hAssetIdx x hxpos dest pk nk r hh_dest s0 hassetunique hhonestPool assets selfInputs
      pool0 actor s s' call hreach hstep hactorPool hprow hF)
  have hSBAiff : ∀ (sA sB : AdjudicatorState), sA.signedBy = sB.signedBy →
      (SignedByAll sig sA fp candidate ↔ SignedByAll sig sB fp candidate) := by
    intro sA sB heq
    unfold SignedByAll AuthorizedBy
    rw [heq]
  have hBmode : (s'.channels (channelId fp)).mode s'.now ≠ .finalized → s'.signedBy = s.signedBy →
      heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) ≤
        heldValue s' (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) →
      UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest s' :=
    fun hm hsb hle => Or.inl ⟨hm, (hSBAiff s s' hsb.symm).mp hsigned,
      Nat.le_trans haff (afford_mono _ hle destIdx)⟩
  have hB : s'.channels (channelId fp) = s.channels (channelId fp) → s'.now = s.now →
      s'.signedBy = s.signedBy →
      heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) ≤
        heldValue s' (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) →
      UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest s' :=
    fun hc hn => hBmode (by rw [hc, hn]; exact hmode)
  have hheldOf : s'.holdings = s.holdings → s'.pool = s.pool →
      heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) ≤
        heldValue s' (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) :=
    fun hh hpl => Nat.le_of_eq (by unfold heldValue; rw [hh, hpl])
  have hholdinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro qasset qcid qpos qc hc
    obtain ⟨⟨pre, hpre, hconsist, hval, _⟩, _⟩ :=
      holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach qasset qcid qpos qc hc
    exact ⟨pre, hpre, hval, hconsist⟩
  cases call with
  | tick newNow => exact absurd rfl (hnotick newNow)
  | sign p d =>
    obtain ⟨_, hsbeq, hpool, hchan, hholdeq, _, _, hnow, _⟩ := hstep
    refine Or.inl ⟨by rw [hchan, hnow]; exact hmode, ?_,
      Nat.le_trans haff (afford_mono _ (hheldOf hholdeq hpool) destIdx)⟩
    intro q hq
    rcases hsigned q hq with hsbq | hcaq
    · left; rw [hsbeq]; exact Or.inr hsbq
    · right; exact hcaq
  | signNote pk' msgHash =>
    obtain ⟨_, _, hpool, hchan, hholdeq, _, _, hnow, hsb⟩ := hstep
    exact hB (by rw [hchan]) hnow hsb (hheldOf hholdeq hpool)
  | deposit cid expectedHeld asset amount =>
    obtain ⟨hdeffect, hdframe, hchan⟩ :=
      deposit_effect sig appRel assets selfInputs pool0 actor s s' cid expectedHeld asset amount
        hreach hstep
    obtain ⟨_, _, _, _, _, _, _, _, hnow, hsbeq, _⟩ := hstep
    refine hB (by rw [hchan]) hnow hsbeq ?_
    by_cases hac : ((candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset, channelId fp) =
        (asset, cid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hac
      rw [hdeffect]; exact Nat.le_add_right _ _
    · exact Nat.le_of_eq (hdframe _ _ hac).symm
  | challenge fp' proof candidate' challenger =>
    obtain ⟨_, _, _, _, hchan, hspool, hsholdeq, _, _, hnow, hsbpair⟩ := hstep
    by_cases hcc : channelId fp' = channelId fp
    · obtain ⟨_, _, _, hdur⟩ := channelIdOf_inj hcc
      have hchanEq : s'.channels (channelId fp) =
          { turnNumRecord := candidate'.turnNum, finalizesAt := s.now + fp'.challengeDuration,
            stateHash := stateHash fp' candidate', outcomeHash := outcomeHashOf candidate'.outcome } := by
        rw [hchan]; unfold update; rw [if_pos hcc.symm]
      refine hBmode ?_ hsbpair.1 (hheldOf hsholdeq hspool)
      rw [hchanEq, hnow]
      unfold ChannelStatus.mode
      dsimp only
      rw [hdur, if_neg (by omega), if_neg (by omega)]
      exact fun h => nomatch h
    · exact hB (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)]) hnow
        hsbpair.1 (hheldOf hsholdeq hspool)
  | checkpoint fp' proof candidate' =>
    obtain ⟨_, _, _, hchan, hspool, hsholdeq, _, _, hnow, hsbpair⟩ := hstep
    by_cases hcc : channelId fp' = channelId fp
    · have hchanEq : s'.channels (channelId fp) =
          { turnNumRecord := candidate'.turnNum, finalizesAt := 0, stateHash := Term.val 0,
            outcomeHash := Term.val 0 } := by
        rw [hchan]; unfold update; rw [if_pos hcc.symm]
      refine hBmode ?_ hsbpair.1 (hheldOf hsholdeq hspool)
      rw [hchanEq]
      unfold ChannelStatus.mode
      dsimp only
      rw [if_pos rfl]
      exact fun h => nomatch h
    · exact hB (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)]) hnow
        hsbpair.1 (hheldOf hsholdeq hspool)
  | conclude fp' candidate' =>
    obtain ⟨_, hisfinal, hcsigned, hchan, hspool, hsholdeq, _, _, hnow, hsbpair⟩ := hstep
    by_cases hcc : channelId fp' = channelId fp
    rotate_left
    · exact hB (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)]) hnow
        hsbpair.1 (hheldOf hsholdeq hspool)
    have hfpeq : fp' = fp := channelId_inj hcc
    rw [hfpeq] at hchan hcsigned
    have hchanEq : s'.channels (channelId fp) =
        { turnNumRecord := 0, finalizesAt := s.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate'.outcome } := by
      rw [hchan]; unfold update; rw [if_pos rfl]
    by_cases hnow0 : s.now = 0
    · refine hBmode ?_ hsbpair.1 (hheldOf hsholdeq hspool)
      rw [hchanEq, hnow, hnow0]
      unfold ChannelStatus.mode
      dsimp only
      rw [if_pos rfl]
      exact fun h => nomatch h
    have hcsigned0 : AuthorizedBy sig s0 h (stateHash fp candidate') := by
      have hc := hcsigned h hp
      unfold AuthorizedBy at hc ⊢
      rwa [hsrow] at hc
    have hsheq := hhonest candidate' hisfinal hcsigned0
    have houtcome_eq := (stateHashOf_inj hsheq).2.2.1
    have hfin' : (s'.channels (channelId fp)).mode s'.now = .finalized := by
      rw [hchanEq, hnow]
      unfold ChannelStatus.mode
      dsimp only
      rw [if_neg hnow0, if_pos (Nat.le_refl _)]
    have hoh' : (s'.channels (channelId fp)).outcomeHash = outcomeHashOf candidate.outcome := by
      rw [hchanEq]
      show outcomeHashOf candidate'.outcome = outcomeHashOf candidate.outcome
      rw [houtcome_eq]
    refine Or.inr (Or.inl ⟨candidate.outcome, hAssetIdx, hfin', hoh', rfl, hnoguarantee, rfl, ?_,
      Nat.le_trans haff (afford_mono _ (hheldOf hsholdeq hspool) destIdx)⟩)
    rw [List.getD_eq_getElem?_getD, hdest]; rfl
  | transfer assetIndex' cid claimedStateHash outcome indices =>
    have hheld := transfer_heldValue_frame sig appRel assets selfInputs pool0 actor s s' assetIndex'
      cid claimedStateHash outcome indices hreach hstep
      (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp)
    obtain ⟨_, hmodeT, _, _, _, ⟨_, _, _, _, hchan⟩, _, _, hnow, hsb⟩ := hstep
    by_cases hcc : cid = channelId fp
    · rw [hcc] at hmodeT; exact absurd hmodeT hmode
    · exact hB (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)]) hnow hsb.1
        (Nat.le_of_eq (hheld (fun _ heq => hcc (congrArg Prod.snd heq).symm)).symm)
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨hmodeSrc, _, _, _, _, hrest, hspool, hsholdeq, _, _, hnow, hsb⟩ := hstep
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hchan⟩ := hrest
    by_cases hcc : sourceChannelId = channelId fp
    · rw [hcc] at hmodeSrc; exact absurd hmodeSrc hmode
    · exact hB (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)]) hnow hsb.1
        (hheldOf hsholdeq hspool)
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨hmodeBulk, _, _, newOutcome, hfold, hchan, _, _, hnow, hsb⟩ := hstep
    by_cases hcc : cid = channelId fp
    · rw [hcc] at hmodeBulk; exact absurd hmodeBulk hmode
    · refine hB (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)]) hnow hsb.1
        (Nat.le_of_eq ?_)
      unfold heldValue
      exact (bulkTransferFold_heldValue_frame_cid s.self cid outcome newOutcome s.pool s'.pool
        s.holdings s'.holdings hfold hholdinv _ (channelId fp) (fun heq => hcc heq.symm)).symm
  | bulkConcludeAndTransferAllAssets fp' candidate' =>
    obtain ⟨_, hisfinal, hcsigned, newOutcome, hfold, hchan, _, _, hnow, hsb⟩ := hstep
    by_cases hcc : channelId fp' = channelId fp
    rotate_left
    · refine hB (by rw [hchan]; unfold update; rw [if_neg (fun heq => hcc heq.symm)]) hnow hsb.1
        (Nat.le_of_eq ?_)
      unfold heldValue
      exact (bulkTransferFold_heldValue_frame_cid s.self (channelId fp') candidate'.outcome
        newOutcome s.pool s'.pool s.holdings s'.holdings hfold hholdinv _ (channelId fp)
        (fun heq => hcc heq.symm)).symm
    have hfpeq : fp' = fp := channelId_inj hcc
    rw [hfpeq] at hcsigned hfold
    have hcsigned0 : AuthorizedBy sig s0 h (stateHash fp candidate') := by
      have hc := hcsigned h hp
      unfold AuthorizedBy at hc ⊢
      rwa [hsrow] at hc
    have hsheq := hhonest candidate' hisfinal hcsigned0
    have houtcome_eq : candidate'.outcome = candidate.outcome := (stateHashOf_inj hsheq).2.2.1
    rw [houtcome_eq] at hfold
    have hidxN : assetIndex < newOutcome.length := by
      rw [bulkTransferFold_length s.self (channelId fp) candidate.outcome newOutcome s.pool
        s'.pool s.holdings s'.holdings hfold]
      exact hAssetIdx
    obtain ⟨_heqNewOutcome, hpayoutExists⟩ :=
      bulkTransferFold_index_payout s.self (channelId fp) candidate.outcome newOutcome s.pool
        s'.pool s.holdings s'.holdings hfold hholdinv assetIndex hAssetIdx hassetunique hidxN
    have hpayoutNe : (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
        (heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
          (channelId fp))).getD destIdx 0 ≠ 0 := by omega
    obtain ⟨pos, hlivemem⟩ := hpayoutExists destIdx hpayoutNe
    refine Or.inr (Or.inr ⟨⟨(candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations.getD destIdx
      Allocation.default |>.destination, (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset,
      (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
        (heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
          (channelId fp))).getD destIdx 0⟩, ?_, rfl, haff, ?_⟩)
    · rw [List.getD_eq_getElem?_getD, hdest]; rfl
    · exact ⟨(candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset, pos.1, pos.2, _, hlivemem, rfl⟩

/-- `unbeatablePaysInv_step` across a whole `interleaved` sequence. -/
theorem unbeatablePaysInv_appliesAll
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (h : Nat) (fp : FixedPart) (candidate : VariablePart) (hp : h ∈ fp.participants)
    (hduration : 0 < fp.challengeDuration)
    (assetIndex destIdx : Nat) (hAssetIdx : assetIndex < candidate.outcome.length) (x : Nat)
    (hxpos : 0 < x)
    (dest : Allocation) (pk : Nat × Nat) (nk r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (s0 : AdjudicatorState)
    (hdest : (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations[destIdx]? = some dest)
    (hassetunique : ∀ i (hi : i < candidate.outcome.length), i ≠ assetIndex →
      (candidate.outcome.get ⟨i, hi⟩).asset ≠ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset)
    (hnoguarantee : ∀ a ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations,
      a.allocationType ≠ .guarantee)
    (hhonest : ∀ candidate', candidate'.isFinal = true →
      AuthorizedBy sig s0 h (stateHash fp candidate') →
      stateHash fp candidate' = stateHash fp candidate)
    (hhonestPool : ∀ m, s0.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) :
    ∀ {calls : List (Actor × Call)} {s s' : AdjudicatorState},
      Reachable sig appRel (genesis assets selfInputs pool0) s →
      AppliesAll sig appRel s calls s' →
      (∀ actor call, (actor, call) ∈ calls → actor ≠ Actor.nitro h ∧ actor ≠ Actor.pool pk) →
      (∀ actor newNow, (actor, Call.tick newNow) ∉ calls) →
      s.signedBy h = s0.signedBy h → s.poolSignedBy pk = s0.poolSignedBy pk →
      UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest s →
      UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest s' ∧
        s'.signedBy h = s0.signedBy h ∧ s'.poolSignedBy pk = s0.poolSignedBy pk
  | [], s, s', _, happ, _, _, hsrow, hprow, hinv => by
    rw [show s' = s from happ]; exact ⟨hinv, hsrow, hprow⟩
  | (actor, call) :: rest, s, s', hreach, happ, hexcl, hexclTick, hsrow, hprow, hinv => by
    obtain ⟨mid, hstep, hrest⟩ := happ
    have hactor : actor ≠ Actor.nitro h := (hexcl actor call (List.mem_cons_self ..)).1
    have hactorPool : actor ≠ Actor.pool pk := (hexcl actor call (List.mem_cons_self ..)).2
    have hnotick : ∀ newNow, call ≠ Call.tick newNow := fun newNow heq =>
      hexclTick actor newNow (heq ▸ List.mem_cons_self ..)
    have hinv_mid := unbeatablePaysInv_step sig appRel h fp candidate hp hduration assetIndex
      destIdx hAssetIdx x hxpos dest pk nk r hh_dest s0 hdest hassetunique hnoguarantee hhonest
      hhonestPool assets selfInputs pool0 actor s mid call hreach hstep hactor hactorPool hnotick
      hsrow hprow hinv
    have hsrow_mid : mid.signedBy h = s0.signedBy h :=
      (step_signedBy_frame sig appRel actor s mid call hstep h hactor).trans hsrow
    have hprow_mid : mid.poolSignedBy pk = s0.poolSignedBy pk :=
      (poolSignedBy_frame sig appRel actor s mid call hstep pk hactorPool).trans hprow
    have hreach_mid : Reachable sig appRel (genesis assets selfInputs pool0) mid :=
      reachable_step hreach hstep
    exact unbeatablePaysInv_appliesAll sig appRel h fp candidate hp hduration assetIndex destIdx
      hAssetIdx x hxpos dest pk nk r hh_dest s0 hdest hassetunique hnoguarantee hhonest hhonestPool
      assets selfInputs
      pool0 hreach_mid hrest (fun actor' call' hc => hexcl actor' call' (List.mem_cons_of_mem _ hc))
      (fun actor' newNow' hc => hexclTick actor' newNow' (List.mem_cons_of_mem _ hc))
      hsrow_mid hprow_mid hinv_mid

/-- Given a `.transfer` step that ALREADY exists (its own `PoolOwnedSpendStep`
    witness supplied elsewhere — this theorem never inspects it), with
    `indices = [destIdx]` naming a single selected allocation, the minted
    payout note pays at least `x`: `destIdx`'s own allocation
    (`hdest`) is `exitAllocations`'s own one member for a singleton
    selection (`transferEffectsSel_exit_forall`, with `sel i = (i =
    destIdx)` since `i ∈ [destIdx] ↔ i = destIdx`), so the minted
    `payoutOutputs` is `[⟨dest.destination, asset, paidAmt⟩]` with
    `paidAmt = (afford ...).getD destIdx 0 ≥ x` (`haffordable`), and
    `PoolOwnedSpendStep`'s own `live` update lands it at the pool's
    then-current leaf count — a live note `unbeatable_pays`/
    `unbeatable_pays_after_timeout` can cite directly. Self/ownerField-
    representation-independent: every fact here is `transferEffects`/
    `afford`/`PoolOwnedSpendStep`'s own `live` update, none of
    `PoolOwnedSpendStep`'s own owned-spend witness. -/
theorem transfer_step_pays_selected
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (mid final : AdjudicatorState) (assetIndex : Nat)
    (cid claimedStateHash : Term) (curOutcome : Outcome) (destIdx : Nat)
    (hstep : Step sig appRel actor mid
      (.transfer assetIndex cid claimedStateHash curOutcome [destIdx]) final)
    (hci : assetIndex < curOutcome.length) (dest : Allocation)
    (hdest : (curOutcome.get ⟨assetIndex, hci⟩).allocations[destIdx]? = some dest)
    (hnoguarantee : ∀ a ∈ (curOutcome.get ⟨assetIndex, hci⟩).allocations,
      a.allocationType ≠ .guarantee)
    (x : Nat) (hxpos : 0 < x)
    (haffordable : x ≤ (afford (curOutcome.get ⟨assetIndex, hci⟩).allocations
      (heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid)).getD destIdx 0) :
    ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧
      pre.token = (curOutcome.get ⟨assetIndex, hci⟩).asset ∧ x ≤ pre.value ∧
      PoolIsLive final.pool (commitment pre.npk pre.token pre.value) := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hselfInputs, _hnow, _hsigned,
    _hpoolSigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨r, hmatch, _hholdseq, _hchanseq⟩ := hrest
  have hAO : curOutcome.get ⟨assetIndex, hidx⟩ = curOutcome.get ⟨assetIndex, hci⟩ := rfl
  change PoolOwnedSpendStep mid.pool mid.self (curOutcome.get ⟨assetIndex, hci⟩).asset
    (mid.holdings (curOutcome.get ⟨assetIndex, hci⟩).asset cid)
    ((transferEffects (curOutcome.get ⟨assetIndex, hci⟩).allocations
        (heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid) [destIdx]).2.1.filterMap (fun a =>
      if a.amount = 0 then none
      else some (⟨a.destination, (curOutcome.get ⟨assetIndex, hci⟩).asset, a.amount⟩ : CommitmentPreimage)))
    (if heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid -
        (transferEffects (curOutcome.get ⟨assetIndex, hci⟩).allocations
          (heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid) [destIdx]).2.2 = 0
     then []
     else [(⟨npk mid.self r, (curOutcome.get ⟨assetIndex, hci⟩).asset,
       heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid -
         (transferEffects (curOutcome.get ⟨assetIndex, hci⟩).allocations
           (heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid) [destIdx]).2.2⟩ : CommitmentPreimage)])
    final.pool at hmatch
  generalize hallocsDef : (curOutcome.get ⟨assetIndex, hci⟩).allocations = allocs
    at hdest hnoguarantee haffordable hmatch
  generalize hassetDef : (curOutcome.get ⟨assetIndex, hci⟩).asset = asset at haffordable hmatch
  generalize hsurplusDef : heldValue mid asset cid = surplus at haffordable hmatch
  have hdestlt : destIdx < allocs.length := (List.getElem?_eq_some_iff.mp hdest).1
  have hexitmem := transferEffectsSel_exit_mem allocs surplus
    (fun i => [destIdx].isEmpty || i ∈ [destIdx]) destIdx hdestlt (by simp)
  rw [← transferEffects_eq_sel] at hexitmem
  have hallocsD : allocs.getD destIdx Allocation.default = dest := by
    rw [List.getD_eq_getElem?_getD, hdest]; rfl
  rw [hallocsD] at hexitmem
  generalize hpaidDef : (afford allocs surplus).getD destIdx 0 = paidAmt at haffordable hexitmem
  generalize hPayoutDef : (transferEffects allocs surplus [destIdx]).2.1.filterMap (fun a =>
      if a.amount = 0 then none else some (⟨a.destination, asset, a.amount⟩ : CommitmentPreimage)) =
    payoutOutputs at hmatch
  generalize hRemDef : surplus -
    (transferEffects allocs surplus [destIdx]).2.2 = remainder at hmatch
  have hpayoutmem : (⟨dest.destination, asset, paidAmt⟩ : CommitmentPreimage) ∈ payoutOutputs := by
    rw [← hPayoutDef]
    refine List.mem_filterMap.mpr ⟨{ dest with amount := paidAmt }, hexitmem, ?_⟩
    rw [if_neg (show paidAmt ≠ 0 by omega)]
  unfold PoolOwnedSpendStep at hmatch
  rcases hc0 : mid.holdings asset cid with _ | c0
  · rw [hc0] at hmatch
    obtain ⟨w, pub, hM, hC, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes, hroot, hmark,
      hRandomOut, heq⟩ := hmatch
    refine ⟨⟨dest.destination, asset, paidAmt⟩, rfl, rfl, haffordable, ?_⟩
    have houtmem : (⟨dest.destination, asset, paidAmt⟩ : CommitmentPreimage) ∈
        payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]) :=
      List.mem_append_left _ hpayoutmem
    obtain ⟨pos, hposmem⟩ := withTreePositionsFrom_mem_fwd
      (treeNumber := insertTreeNumber mid.pool.closedTrees mid.pool.leaves
        (payoutOutputs.length + (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]).length))
      (start := insertStartPos mid.pool.leaves
        (payoutOutputs.length + (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]).length))
      houtmem
    refine ⟨asset, insertTreeNumber mid.pool.closedTrees mid.pool.leaves
        (payoutOutputs.length + (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]).length),
      pos, ⟨dest.destination, asset, paidAmt⟩, ?_, rfl⟩
    rw [heq]; dsimp only
    rw [if_pos rfl]
    exact List.mem_append.mpr (Or.inl hposmem)
  · rw [hc0] at hmatch
    obtain ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes,
      hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
    refine ⟨⟨dest.destination, asset, paidAmt⟩, rfl, rfl, haffordable, ?_⟩
    have houtmem : (⟨dest.destination, asset, paidAmt⟩ : CommitmentPreimage) ∈
        payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]) :=
      List.mem_append_left _ hpayoutmem
    obtain ⟨pos, hposmem⟩ := withTreePositionsFrom_mem_fwd
      (treeNumber := insertTreeNumber mid.pool.closedTrees mid.pool.leaves
        (payoutOutputs.length + (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]).length))
      (start := insertStartPos mid.pool.leaves
        (payoutOutputs.length + (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]).length))
      houtmem
    refine ⟨asset, insertTreeNumber mid.pool.closedTrees mid.pool.leaves
        (payoutOutputs.length + (if remainder = 0 then [] else
          [(⟨npk mid.self r, asset, remainder⟩ : CommitmentPreimage)]).length),
      pos, ⟨dest.destination, asset, paidAmt⟩, ?_, rfl⟩
    rw [heq]; dsimp only
    rw [if_pos rfl]
    exact List.mem_append.mpr (Or.inl hposmem)

/-- Not-yet-finalized plus `SignedByAll` always lets `h` (or anyone)
    reach a finalized state naming `candidate`: one `.conclude`
    (`ChannelStatus.mode` reads `.open` when `finalizesAt = 0`, so
    `.conclude` right at `mid.now = 0` would set `finalizesAt := 0`
    again, NOT actually finalizing — the caller supplies `hnowpos` to
    rule this out; ticking first is NOT a safe general fix, since a
    channel already in `.challenge` mode with `finalizesAt` exactly
    one tick away would then finalize via the CHALLENGE timeout
    instead, with the challenge's own `outcomeHash`, not
    `candidate`'s). Self/ownerField-representation-independent:
    `.conclude` touches no `pool`/`holdings`/`self` field at all
    (`Operations.lean`'s own `.conclude` case, every pool/holdings
    field an equation to the PRIOR state). What `unbeatable_pays`'s
    own B case needs before handing off to
    `transfer_step_pays_selected`. -/
theorem conclude_step_finalizes
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (mid : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (hnotfinal : (mid.channels (channelId fp)).mode mid.now ≠ .finalized)
    (hnowpos : 0 < mid.now)
    (hfinal : candidate.isFinal = true)
    (hsigned : SignedByAll sig mid fp candidate) :
    ∃ (payCalls : List (Actor × Call)) (mid1 : AdjudicatorState),
      AppliesAll sig appRel mid payCalls mid1 ∧
      (mid1.channels (channelId fp)).mode mid1.now = .finalized ∧
      (mid1.channels (channelId fp)).outcomeHash = outcomeHashOf candidate.outcome ∧
      mid1.pool = mid.pool ∧ mid1.holdings = mid.holdings ∧ mid1.self = mid.self ∧
      mid1.signedBy = mid.signedBy ∧ mid1.poolSignedBy = mid.poolSignedBy := by
  let newStatus : ChannelStatus :=
    ⟨0, mid.now, Term.val 0, outcomeHashOf candidate.outcome⟩
  have hconcludestep : Step sig appRel actor mid (.conclude fp candidate)
      { mid with channels := update mid.channels (channelId fp) newStatus } :=
    ⟨hnotfinal, hfinal, hsigned, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨[(actor, .conclude fp candidate)], _, ⟨_, hconcludestep, rfl⟩, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · show (update mid.channels (channelId fp) newStatus (channelId fp)).mode mid.now = .finalized
    unfold update; rw [if_pos rfl]; unfold ChannelStatus.mode
    rw [if_neg (show mid.now ≠ 0 by omega)]
    rw [if_pos (Nat.le_refl _)]
  · show (update mid.channels (channelId fp) newStatus (channelId fp)).outcomeHash =
      outcomeHashOf candidate.outcome
    unfold update; rw [if_pos rfl]

/-- A channel's own `heldValue`, at ANY reachable state, is below `2 ^
    120` — true because every note ever minted passed the owning
    circuit's own `Num2Bits(120)` range check (`Constrained`/
    `OwnedConstrained`'s own `rangeIn`/`rangeOut` fields) at mint time,
    so every LIVE note's own value is in range (`live_values_lt_2pow120`,
    `PoolSafety.lean`, lifted through `adjudicator_pool_reachable`), and
    `heldValue` only ever reads a live note's own value (`State.lean`,
    via `holdingWellFormed_reachable`). -/
theorem heldValue_range_placeholder (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0) (mid : AdjudicatorState)
    (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid) :
    RangeChecked120 (heldValue mid asset cid) := by
  rcases hh : mid.holdings asset cid with _ | ⟨pos, c⟩
  · unfold heldValue; rw [hh]; exact rangeCheck120_complete 0 (Nat.two_pow_pos 120)
  · obtain ⟨⟨pre, hpre, _hconsist, _hval, _htok, hlive, _⟩, _⟩ :=
      holdingWellFormed_reachable sig appRel assets selfInputs pool0 mid hreach asset cid pos c hh
    have hReachMidPool : _root_.Reachable mid.pool :=
      adjudicator_pool_reachable sig appRel assets selfInputs pool0 hReachPool mid hreach
    have hlt : pre.value < 2 ^ 120 := live_values_lt_2pow120 hReachMidPool asset (pos, pre) hlive
    unfold heldValue
    rw [hh]
    simp only [hpre, Option.map_some, Option.getD_some]
    exact rangeCheck120_complete pre.value hlt

/-- A channel's own recorded holding position names the EXACT pool leaf
    its own commitment lives at, at ANY reachable state:
    `holdingWellFormed_reachable` gives the holding's own live membership,
    `live_leaf_matches` (`PoolSafety.lean`) reads that membership's own
    leaf content back. -/
theorem holdings_position_leaf_value_placeholder (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0) (mid : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid) :
    ∀ asset cid (pos : Nat × Nat) c, mid.holdings asset cid = some (pos, c) →
      (mid.pool.leavesAt' pos.1).getD pos.2 (Term.val 0) = c := by
  intro asset cid pos c hc
  obtain ⟨⟨pre, _hpre, hconsist, _hval, _htok, hlive, _⟩, _⟩ :=
    holdingWellFormed_reachable sig appRel assets selfInputs pool0 mid hreach asset cid pos c hc
  have hReachMidPool : _root_.Reachable mid.pool :=
    adjudicator_pool_reachable sig appRel assets selfInputs pool0 hReachPool mid hreach
  rw [← hconsist]
  exact live_leaf_matches hReachMidPool asset pos.1 pos.2 pre hlive

/-- A live, owned note's own nullifier is never already spent — true
    because a note leaves `live` the SAME step its nullifier enters
    `spent` (`PoolOwnedSpendStep`'s own `removeAll`/`markSpent` pairing,
    `Notes.lean`), so a note that stays live was never spent
    (`live_note_unspent`, `PoolSafety.lean`, lifted through
    `adjudicator_pool_reachable`). -/
theorem live_note_nullifier_unspent_placeholder (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0) (mid : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid)
    (asset : Nat) (cid : Term) (pos : Nat × Nat) (c ownerField : Term) (r : Nat)
    (hholds : mid.holdings asset cid = some (pos, c))
    (hown : mid.pool.ownedRandomOf c = some ⟨ownerField, r⟩) :
    nullifier ownerField pos.2 ∉ mid.pool.spent pos.1 := by
  obtain ⟨⟨pre, _hpre, _hconsist, _hval, _htok, hlive, _⟩, _⟩ :=
    holdingWellFormed_reachable sig appRel assets selfInputs pool0 mid hreach asset cid pos c hholds
  have hReachMidPool : _root_.Reachable mid.pool :=
    adjudicator_pool_reachable sig appRel assets selfInputs pool0 hReachPool mid hreach
  exact live_note_unspent hReachMidPool asset pos.1 pos.2 pre hlive ownerField

/-- Removing a single already-live element from a pool always succeeds,
    leaving it erased. Generic over `removeAll`'s own `[DecidableEq α]`
    parameter so the `BEq` instance it derives internally stays pinned
    to the SAME one this lemma's own statement uses — what
    `transfer_step_exists` needs for `PoolOwnedSpendStep`'s own
    `removeAll` obligation on a singleton `ownedSpentPositions`. -/
theorem removeAll_singleton_of_mem {α : Type} [DecidableEq α] {l : List α} {x : α}
    (h : x ∈ l) : removeAll l [x] = some (l.erase x) := by
  unfold removeAll
  rw [if_pos (List.elem_iff.mpr h)]
  rfl

/-- The full per-step holdings-position invariant (`Lemmas.lean`)
    preserves, lifted to any reachable state: a holding's own position is
    live with the holding's own commitment (naming the EXACT `(position,
    preimage)` pair, not just that SOME live note matches the
    commitment), within the pool's own leaf range, and distinct from
    every unrelated holding's own position. `holdings_point_to_live_notes`
    weakens this to `PoolIsLive`; `transfer_step_exists` needs the exact
    pair, to name `removeAll`'s own witness. -/
theorem holdings_position_live_reachable
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ s.pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, s.self = ownerField ∧ pre.npk = npk ownerField r) ∨
          ∃ r, pre.npk = npk s.self r)) ∧
      qpos.2 < (s.pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', s.holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  intro qasset qcid qpos qc hc
  obtain ⟨⟨pre, _hpre, hconsist, _hval, _htok, hlive, r, hnpk, _hown⟩, hbound, huniq⟩ :=
    holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach qasset qcid qpos qc hc
  exact ⟨⟨pre, hlive, hconsist, Or.inl ⟨s.self, r, rfl, hnpk⟩⟩, hbound, huniq⟩

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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (asset : Nat) (cid : Term) (pos : Nat × Nat) (c : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hholds : s.holdings asset cid = some (pos, c)) :
    PoolIsLive s.pool c := by
  obtain ⟨⟨pre, _hpre, hconsist, _hval, _htok, hlive, _r, _hnpk, _hown⟩, _, _⟩ :=
    holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach asset cid pos c hholds
  exact ⟨asset, pos.1, pos.2, pre, hlive, hconsist⟩

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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (held : Nat) (hheld : heldValue s asset cid = held) (hpos : 0 < held) :
    ∃ pos c, s.holdings asset cid = some (pos, c) ∧ PoolIsLive s.pool c ∧
      (s.pool.preimageOf c).map CommitmentPreimage.value = some held := by
  rcases hh : s.holdings asset cid with _ | ⟨pos, c⟩
  · exfalso
    simp only [heldValue, hh] at hheld
    omega
  · obtain ⟨⟨pre, hpre, hconsist, _hval, _htok, hlive, _r, _hnpk, _hown⟩, _, _⟩ :=
      holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach asset cid pos c hh
    refine ⟨pos, c, rfl, ⟨asset, pos.1, pos.2, pre, hlive, hconsist⟩, ?_⟩
    simp only [heldValue, hh, hpre, Option.map_some, Option.getD_some] at hheld
    simp only [hpre, Option.map_some, hheld]

/-- Given a finalized channel at `mid` naming `curOutcome` at
    `assetIndex`, with `destIdx` still affording `x` (`haffordable`), a
    `.transfer` step naming exactly `destIdx` exists from `mid` — the
    owned-spend witness `owned_spend_witness_exists` builds, applied to
    the channel's own held note at an ARBITRARY reachable state. What
    `unbeatable_pays`'s own B/A1 cases need before handing off to
    `transfer_step_pays_selected` for the payout itself. -/
theorem transfer_step_exists
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0)
    (actor : Actor) (mid : AdjudicatorState) (assetIndex : Nat) (cid : Term)
    (curOutcome : Outcome) (destIdx : Nat)
    (hci : assetIndex < curOutcome.length)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid)
    (hmode : (mid.channels cid).mode mid.now = .finalized)
    (hoh : (mid.channels cid).outcomeHash = outcomeHashOf curOutcome)
    (dest : Allocation)
    (hdest : (curOutcome.get ⟨assetIndex, hci⟩).allocations[destIdx]? = some dest)
    (hnoguarantee : ∀ a ∈ (curOutcome.get ⟨assetIndex, hci⟩).allocations,
      a.allocationType ≠ .guarantee)
    (x : Nat) (hxpos : 0 < x)
    (haffordable : x ≤ (afford (curOutcome.get ⟨assetIndex, hci⟩).allocations
      (heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid)).getD destIdx 0) :
    ∃ final, Step sig appRel actor mid
      (.transfer assetIndex cid (mid.channels cid).stateHash curOutcome [destIdx]) final := by
  have hheldpos : 0 < heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid := by
    rcases Nat.eq_zero_or_pos (heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid) with
      hz | hpos
    · rw [hz, afford_zero_surplus] at haffordable; omega
    · exact hpos
  generalize hassetDef : (curOutcome.get ⟨assetIndex, hci⟩).asset = asset at hdest hnoguarantee haffordable hheldpos
  generalize hheldDef : heldValue mid asset cid = held at haffordable hheldpos
  obtain ⟨pos, c, hholds, hlive0, hvalmap⟩ :=
    value_exists_only_as_notes sig appRel assets selfInputs pool0 mid asset cid hreach held
      hheldDef hheldpos
  obtain ⟨pre, ownerField, r, hpreOf, hhash, htok, hself, hrand, hnpk⟩ :=
    held_note_owned_disclosure_reachable sig appRel assets selfInputs pool0 mid hreach
      asset cid pos c hholds
  have hpreval : pre.value = held := by
    rw [hpreOf] at hvalmap; simpa using hvalmap
  obtain ⟨⟨pre', hlivemem, hhash', _⟩, hposlt, hdistinct⟩ :=
    holdings_position_live_reachable sig appRel assets selfInputs pool0 mid hreach
      asset cid pos c hholds
  have hpreeq : pre' = pre := hashCommitment_inj (hhash'.trans hhash.symm)
  rw [hpreeq] at hlivemem
  have hrandeq : mid.pool.ownedRandomOf (hashCommitment pre) = some ⟨ownerField, r⟩ := by
    rw [hhash]; exact hrand
  have hReachPoolMid : _root_.Reachable mid.pool :=
    adjudicator_pool_reachable sig appRel assets selfInputs pool0 hReachPool mid hreach
  have hposlt2 : pos.2 < 2 ^ TreeDepth := by
    have hcap := reachable_leavesAt_capacity hReachPoolMid pos.1
    omega
  have hleafval := holdings_position_leaf_value_placeholder sig appRel assets selfInputs pool0
    hReachPool mid hreach asset cid pos c hholds
  have hrangeheld := heldValue_range_placeholder sig appRel assets selfInputs pool0 hReachPool mid
    asset cid hreach
  rw [hheldDef] at hrangeheld
  have hnullunspent := live_note_nullifier_unspent_placeholder sig appRel assets selfInputs pool0
    hReachPool mid hreach asset cid pos c ownerField r hholds hrand
  generalize hallocsDef : (curOutcome.get ⟨assetIndex, hci⟩).allocations = allocs at hdest hnoguarantee haffordable
  have hdestlt : destIdx < allocs.length := (List.getElem?_eq_some_iff.mp hdest).1
  have hexitmem := transferEffectsSel_exit_mem allocs held
    (fun i => [destIdx].isEmpty || i ∈ [destIdx]) destIdx hdestlt (by simp)
  rw [← transferEffects_eq_sel] at hexitmem
  have hallocsD : allocs.getD destIdx Allocation.default = dest := by
    rw [List.getD_eq_getElem?_getD, hdest]; rfl
  rw [hallocsD] at hexitmem
  generalize hpaidDef : (afford allocs held).getD destIdx 0 = paidAmt at haffordable hexitmem
  have hpaidleheld : paidAmt ≤ held := hpaidDef ▸ afford_getD_le_surplus allocs held destIdx
  generalize hPayoutDef : (transferEffects allocs held [destIdx]).2.1.filterMap (fun a =>
      if a.amount = 0 then none else some (⟨a.destination, asset, a.amount⟩ : CommitmentPreimage)) =
    payoutOutputs
  have hTotalPayoutsDef : (transferEffects allocs held [destIdx]).2.2 = paidAmt := by
    rw [← hpaidDef]; exact transferEffects_totalPayouts_single allocs held destIdx
  generalize hRemDef : held - (transferEffects allocs held [destIdx]).2.2 = remainder
  rw [hTotalPayoutsDef] at hRemDef
  have hremleheld : remainder ≤ held := by omega
  have hpayoutmem : (⟨dest.destination, asset, paidAmt⟩ : CommitmentPreimage) ∈ payoutOutputs := by
    rw [← hPayoutDef]
    refine List.mem_filterMap.mpr ⟨{ dest with amount := paidAmt }, hexitmem, ?_⟩
    rw [if_neg (show paidAmt ≠ 0 by omega)]
  have hpayouttok : ∀ a ∈ payoutOutputs, a.token = asset := by
    rw [← hPayoutDef]
    intro a ha
    obtain ⟨b, _, hb⟩ := List.mem_filterMap.mp ha
    split at hb
    · cases hb
    · injection hb with hb; rw [← hb]
  have hexitall : ∀ x ∈ (transferEffects allocs held [destIdx]).2.1,
      x = { dest with amount := paidAmt } := by
    intro x hx
    rw [transferEffects_eq_sel allocs held [destIdx]] at hx
    obtain ⟨i, _, hseli, hxeq⟩ := transferEffectsSel_exit_forall allocs held
      (fun i => [destIdx].isEmpty || i ∈ [destIdx]) x hx
    simp only [List.isEmpty_cons, Bool.false_or, List.mem_singleton,
      decide_eq_true_eq] at hseli
    subst hseli
    rw [hallocsD, hpaidDef] at hxeq
    exact hxeq
  have hpayoutval : ∀ b ∈ payoutOutputs, b.value = paidAmt := by
    rw [← hPayoutDef]
    intro b hb
    obtain ⟨a, ha, hab⟩ := List.mem_filterMap.mp hb
    rw [hexitall a ha] at hab
    split at hab
    · cases hab
    · injection hab with hab; rw [← hab]
  classical
  let remainderOutputs : List CommitmentPreimage :=
    if remainder = 0 then [] else [⟨npk mid.self 0, asset, remainder⟩]
  have hgetval : ∀ (k : Nat) (hk : k < remainderOutputs.length),
      remainderOutputs.get ⟨k, hk⟩ = (⟨npk mid.self 0, asset, remainder⟩ : CommitmentPreimage) := by
    intro k hk
    have hremne : remainder ≠ 0 := by
      intro hr0
      have hlen0 : remainderOutputs.length = 0 := by
        show (if remainder = 0 then ([] : List CommitmentPreimage)
          else [⟨npk mid.self 0, asset, remainder⟩]).length = 0
        simp [if_pos hr0]
      omega
    have hk1 : k < 1 := by
      have hlen1 : remainderOutputs.length = 1 := by
        show (if remainder = 0 then ([] : List CommitmentPreimage)
          else [⟨npk mid.self 0, asset, remainder⟩]).length = 1
        simp [if_neg hremne]
      omega
    show remainderOutputs[k]'hk = _
    have heq : remainderOutputs = [⟨npk mid.self 0, asset, remainder⟩] := by
      show (if remainder = 0 then ([] : List CommitmentPreimage)
        else [⟨npk mid.self 0, asset, remainder⟩]) = _
      rw [if_neg hremne]
    simp only [heq]
    exact List.getElem_singleton hk1
  have hgetvalE : ∀ (k : Nat) (hk : k < remainderOutputs.length),
      remainderOutputs[k]'hk = (⟨npk mid.self 0, asset, remainder⟩ : CommitmentPreimage) :=
    hgetval
  have hpaidpos : 0 < paidAmt := by omega
  have hpayoutlen1 : payoutOutputs.length ≤ 1 := by
    rw [← hPayoutDef, transferEffects_exit_single allocs held destIdx hdestlt]
    simp only [List.filterMap_cons, List.filterMap_nil]
    split <;> simp
  have hremlen1 : remainderOutputs.length ≤ 1 := by
    show (if remainder = 0 then ([] : List CommitmentPreimage)
      else [⟨npk mid.self 0, asset, remainder⟩]).length ≤ 1
    split <;> simp
  let M : Nat := payoutOutputs.length + remainderOutputs.length
  have hM : M ≤ 4 := by show payoutOutputs.length + remainderOutputs.length ≤ 4; omega
  let npkOut : Fin M → Term := fun j =>
    if h : j.val < payoutOutputs.length then (payoutOutputs.get ⟨j.val, h⟩).npk
    else (remainderOutputs.get ⟨j.val - payoutOutputs.length, by omega⟩).npk
  let valueOut : Fin M → Nat := fun j =>
    if h : j.val < payoutOutputs.length then (payoutOutputs.get ⟨j.val, h⟩).value
    else (remainderOutputs.get ⟨j.val - payoutOutputs.length, by omega⟩).value
  have hvalueOutLow : ∀ j (h : j.val < payoutOutputs.length),
      valueOut j = (payoutOutputs.get ⟨j.val, h⟩).value := by
    intro j h; show (if h' : j.val < payoutOutputs.length then _ else _) = _; rw [dif_pos h]
  have hvalueOutHigh : ∀ j (h : ¬ j.val < payoutOutputs.length),
      valueOut j = (remainderOutputs.get ⟨j.val - payoutOutputs.length, by omega⟩).value := by
    intro j h; show (if h' : j.val < payoutOutputs.length then _ else _) = _; rw [dif_neg h]
  have hRangeOut : ∀ j, RangeChecked120 (valueOut j) := by
    intro j
    by_cases h : j.val < payoutOutputs.length
    · rw [hvalueOutLow j h, hpayoutval _ (List.get_mem payoutOutputs ⟨j.val, h⟩)]
      exact rangeCheck120_mono hpaidleheld hrangeheld
    · rw [hvalueOutHigh j h]
      have hmem : (remainderOutputs.get ⟨j.val - payoutOutputs.length, by omega⟩) ∈
          remainderOutputs := List.get_mem remainderOutputs _
      change remainderOutputs.get _ ∈
        (if remainder = 0 then ([] : List CommitmentPreimage)
          else [⟨npk mid.self 0, asset, remainder⟩]) at hmem
      split at hmem
      · exact absurd hmem (List.not_mem_nil)
      · rcases List.mem_singleton.mp hmem with hmem
        rw [hmem]; exact rangeCheck120_mono hremleheld hrangeheld
  have hRangeIn : ∀ i : Fin 1, RangeChecked120 ((fun _ : Fin 1 => pre) i).value := by
    intro i; rw [hpreval]; exact hrangeheld
  have hToken : ∀ i : Fin 1, ((fun _ : Fin 1 => pre) i).token = asset := fun _ => htok
  have hOwned : ∀ i : Fin 1, ∃ r', mid.pool.ownedRandomOf
      (hashCommitment ((fun _ : Fin 1 => pre) i)) = some ⟨ownerField, r'⟩ ∧
      npk ownerField r' = ((fun _ : Fin 1 => pre) i).npk := fun _ => ⟨r, hrandeq, hnpk⟩
  have hLeafIndex : ∀ i : Fin 1, (fun _ : Fin 1 => pos.2) i < 2 ^ TreeDepth := fun _ => hposlt2
  have hLeafValue : ∀ i : Fin 1, (mid.pool.leavesAt' pos.1).getD ((fun _ : Fin 1 => pos.2) i)
      (Term.val 0) = hashCommitment ((fun _ : Fin 1 => pre) i) := fun _ => hleafval.trans hhash.symm
  have hBalance : listSum (List.ofFn fun i : Fin 1 => ((fun _ : Fin 1 => pre) i).value) =
      listSum (List.ofFn valueOut) := by
    have hfiltersum : ∀ (l : List Allocation) (tok : Nat),
        listSum ((l.filterMap (fun a => if a.amount = 0 then none
          else some (⟨a.destination, tok, a.amount⟩ : CommitmentPreimage))).map
          CommitmentPreimage.value) = listSum (l.map Allocation.amount) := by
      intro l tok
      induction l with
      | nil => simp [listSum]
      | cons a as ih =>
        by_cases hz : a.amount = 0
        · simp only [List.filterMap_cons, hz, if_pos, List.map_cons, listSum]
          rw [ih]; omega
        · simp only [List.filterMap_cons, if_neg hz, List.map_cons, listSum]
          rw [ih]
    have hofffn : List.ofFn valueOut =
        payoutOutputs.map CommitmentPreimage.value ++ remainderOutputs.map CommitmentPreimage.value := by
      apply List.ext_getElem
      · rw [List.length_ofFn, List.length_append, List.length_map, List.length_map]
      · intro n h1 h2
        rw [List.getElem_ofFn h1]
        have h1' : n < payoutOutputs.length + remainderOutputs.length := by
          have := List.length_ofFn (f := valueOut)
          omega
        by_cases h : n < payoutOutputs.length
        · rw [hvalueOutLow ⟨n, h1'⟩ h]
          rw [List.getElem_append_left (by simpa using h)]
          simp
        · rw [hvalueOutHigh ⟨n, h1'⟩ h]
          rw [List.getElem_append_right (by simpa using h)]
          simp
    rw [hofffn]
    show pre.value = listSum (payoutOutputs.map CommitmentPreimage.value ++
      remainderOutputs.map CommitmentPreimage.value)
    rw [hpreval]
    have hsplit : listSum (payoutOutputs.map CommitmentPreimage.value) +
        listSum (remainderOutputs.map CommitmentPreimage.value) =
        listSum (payoutOutputs.map CommitmentPreimage.value ++
          remainderOutputs.map CommitmentPreimage.value) := by
      generalize payoutOutputs.map CommitmentPreimage.value = l1
      generalize remainderOutputs.map CommitmentPreimage.value = l2
      induction l1 with
      | nil => simp [listSum]
      | cons x xs ih => simp only [List.cons_append, listSum]; rw [← ih]; omega
    rw [← hsplit]
    have hpayoutsum : listSum (payoutOutputs.map CommitmentPreimage.value) = paidAmt := by
      rw [← hPayoutDef, hfiltersum]
      exact hTotalPayoutsDef
    have hremsum : listSum (remainderOutputs.map CommitmentPreimage.value) = remainder := by
      show listSum ((if remainder = 0 then [] else
        [⟨npk mid.self 0, asset, remainder⟩]).map CommitmentPreimage.value) = remainder
      split
      · next hz => simp [listSum, hz]
      · simp [listSum]
    rw [hpayoutsum, hremsum]
    omega
  let w : TransactOwnedWitness 1 M :=
    { token := asset, randomIn := fun _ => r, valueIn := fun _ => pre.value,
      pathElements := fun _ => treePath TreeDepth (mid.pool.leavesAt' pos.1) pos.2,
      leavesIndices := fun _ => pos.2, npkOut := npkOut, valueOut := valueOut }
  let pub : TransactOwnedPublic 1 M :=
    { merkleRoot := treeRoot TreeDepth (mid.pool.leavesAt' pos.1), boundParamsHash := 0,
      nullifiers := fun _ => nullifier ownerField pos.2,
      commitmentsOut := fun j => commitment (npkOut j) asset (valueOut j),
      ownerField := ownerField }
  have hcommit0 : hashCommitment pre = commitment (npk ownerField r) asset pre.value := by
    unfold hashCommitment; rw [hnpk, htok]
  have hmerkle0 : merkleRoot (commitment (npk ownerField r) asset pre.value)
      (treePath TreeDepth (mid.pool.leavesAt' pos.1) pos.2) =
      treeRoot TreeDepth (mid.pool.leavesAt' pos.1) := by
    rw [← hcommit0, hhash, ← hleafval]
    exact treePath_correct TreeDepth (mid.pool.leavesAt' pos.1) pos.2 hposlt2
  have hC : OwnedConstrained w pub :=
    { pathLen := fun _ => treePath_length TreeDepth (mid.pool.leavesAt' pos.1) pos.2,
      merkle := fun _ => hmerkle0, nullifiers := fun _ => rfl, outputs := fun _ => rfl,
      rangeIn := hRangeIn, rangeOut := hRangeOut, balance := congrArg (· % p) hBalance }
  have hprematch : (⟨npk ownerField r, asset, pre.value⟩ : CommitmentPreimage) = pre := by
    rw [hnpk, ← htok]
  have hospos : ownedSpentPositions pos.1 pub w = [(pos, pre)] := by
    show List.ofFn (fun _ : Fin 1 =>
      ((pos.1, pos.2), (⟨npk ownerField r, asset, pre.value⟩ : CommitmentPreimage))) = [(pos, pre)]
    simp only [List.ofFn_succ, List.ofFn_zero, hprematch]
  obtain ⟨rest, hremove⟩ : ∃ rest, removeAll (mid.pool.live asset) (ownedSpentPositions pos.1 pub w) =
      some rest := ⟨_, by rw [hospos]; exact removeAll_singleton_of_mem hlivemem⟩
  have hmarkfresh : nullifier ownerField pos.2 ∉ mid.pool.spent pos.1 := hnullunspent
  obtain ⟨spent', hmark⟩ := markSpent_succeeds
    (spent := mid.pool.spent pos.1) (ns := List.ofFn pub.nullifiers)
    (by
      show (List.ofFn pub.nullifiers).Pairwise (· ≠ ·)
      simp only [List.ofFn_succ, List.ofFn_zero]
      simp)
    (by
      intro n hn
      change n ∈ [nullifier ownerField pos.2] at hn
      simp only [List.mem_singleton] at hn
      rw [hn]; exact hmarkfresh)
  let ownedRandom : Fin remainderOutputs.length → Nat := fun _ => 0
  have hNonZero : ∀ j, ¬ isZeroPreimage
      (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage) := by
    intro j hz
    unfold isZeroPreimage at hz
    change npkOut j = Term.val 0 ∧ valueOut j = 0 ∧ asset = 0 at hz
    by_cases h : j.val < payoutOutputs.length
    · rw [hvalueOutLow j h, hpayoutval _ (List.get_mem payoutOutputs ⟨j.val, h⟩)] at hz
      exact (by omega : paidAmt ≠ 0) hz.2.1
    · rw [hvalueOutHigh j h] at hz
      have hmem : (remainderOutputs.get ⟨j.val - payoutOutputs.length, by omega⟩) ∈
          remainderOutputs := List.get_mem remainderOutputs _
      change remainderOutputs.get _ ∈
        (if remainder = 0 then ([] : List CommitmentPreimage)
          else [⟨npk mid.self 0, asset, remainder⟩]) at hmem
      split at hmem
      · exact absurd hmem (List.not_mem_nil)
      · next hrpos =>
          rcases List.mem_singleton.mp hmem with hmem
          rw [hmem] at hz; exact hrpos hz.2.1
  have hRandomOut : ∀ j : Fin remainderOutputs.length, w.npkOut (Fin.natAdd payoutOutputs.length j) =
      npk mid.self (ownedRandom j) := by
    intro j
    show npkOut (Fin.natAdd payoutOutputs.length j) = npk mid.self 0
    have hnotlow : ¬ (Fin.natAdd payoutOutputs.length j).val < payoutOutputs.length := by
      show ¬ payoutOutputs.length + j.val < payoutOutputs.length; omega
    show (if h : (Fin.natAdd payoutOutputs.length j).val < payoutOutputs.length then _ else
        (remainderOutputs.get ⟨(Fin.natAdd payoutOutputs.length j).val - payoutOutputs.length,
          by omega⟩).npk) = npk mid.self 0
    rw [dif_neg hnotlow]
    rw [hgetval _ (by omega)]
  have htoken : w.token = asset := rfl
  have hleavesIdx : w.leavesIndices 0 = pos.2 := rfl
  have hcommitFinal : commitment (npk pub.ownerField (w.randomIn 0)) w.token (w.valueIn 0) = c := by
    show commitment (npk ownerField r) asset pre.value = c
    rw [← hcommit0, hhash]
  have hroot : pub.merkleRoot ∈ mid.pool.rootsAt' pos.1 := by
    show treeRoot TreeDepth (mid.pool.leavesAt' pos.1) ∈ mid.pool.rootsAt' pos.1
    rcases reachable_rootAt_matches_leavesAt hReachPoolMid pos.1 with hnil | hmem
    · exact absurd hposlt (by simp [hnil])
    · exact hmem
  have hnewnotes : ownedNewNotes w = payoutOutputs ++ remainderOutputs := by
    show List.ofFn (fun j : Fin M => (⟨npkOut j, asset, valueOut j⟩ : CommitmentPreimage)) =
      payoutOutputs ++ remainderOutputs
    apply List.ext_getElem
    · rw [List.length_ofFn, List.length_append]
    · intro n h1 h2
      rw [List.getElem_ofFn h1]
      have h1' : n < payoutOutputs.length + remainderOutputs.length := by
        have := List.length_ofFn (f := fun j : Fin M => (⟨npkOut j, asset, valueOut j⟩ :
          CommitmentPreimage))
        omega
      by_cases h : n < payoutOutputs.length
      · show (⟨npkOut ⟨n, h1'⟩, asset, valueOut ⟨n, h1'⟩⟩ : CommitmentPreimage) = _
        have hnpkLow : npkOut ⟨n, h1'⟩ = (payoutOutputs.get ⟨n, h⟩).npk := by
          show (if h' : n < payoutOutputs.length then _ else _) = _; rw [dif_pos h]
        rw [hnpkLow, hvalueOutLow ⟨n, h1'⟩ h, ← hpayouttok _ (List.get_mem payoutOutputs ⟨n, h⟩)]
        rw [List.getElem_append_left (by simpa using h)]
        rfl
      · show (⟨npkOut ⟨n, h1'⟩, asset, valueOut ⟨n, h1'⟩⟩ : CommitmentPreimage) = _
        have hnpkHigh : npkOut ⟨n, h1'⟩ =
            (remainderOutputs.get ⟨n - payoutOutputs.length, by omega⟩).npk := by
          show (if h' : n < payoutOutputs.length then _ else _) = _; rw [dif_neg h]
        rw [hnpkHigh, hvalueOutHigh ⟨n, h1'⟩ h]
        have hremeq := hgetval (n - payoutOutputs.length) (by omega)
        rw [hremeq]
        rw [List.getElem_append_right (by simpa using h)]
        rw [hgetvalE (n - payoutOutputs.length) (by omega)]
  have hnoguarantee' : ∀ a ∈ (transferEffects allocs held [destIdx]).2.1,
      a.allocationType ≠ .guarantee := by
    intro a ha
    rw [hexitall a ha]
    exact hnoguarantee dest (List.mem_of_getElem? hdest)
  let res := insertResult mid.pool.closedTrees mid.pool.leaves mid.pool.roots
    ((payoutOutputs ++ remainderOutputs).map hashCommitment)
  let finalPool : PoolState :=
    { mid.pool with
      live := fun t => if t = asset
        then withTreePositionsFrom (insertTreeNumber mid.pool.closedTrees mid.pool.leaves M)
          (insertStartPos mid.pool.leaves M) (payoutOutputs ++ remainderOutputs) ++
          rest
        else mid.pool.live t,
      spent := fun n => if n = pos.1 then spent' else mid.pool.spent n,
      closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
      preimageOf := applyRecords mid.pool.preimageOf (ownedOutputRecords w pub),
      ownedRandomOf := applyOwnedRecords mid.pool.ownedRandomOf
        ((List.finRange remainderOutputs.length).map fun j =>
          (pub.commitmentsOut (Fin.natAdd payoutOutputs.length j),
            (⟨mid.self, ownedRandom j⟩ : OwnedDisclosure))) }
  have hospendstep : PoolOwnedSpendStep mid.pool mid.self asset (mid.holdings asset cid)
      payoutOutputs remainderOutputs finalPool := by
    show PoolOwnedSpendStep mid.pool mid.self asset (mid.holdings asset cid)
      payoutOutputs remainderOutputs finalPool
    rw [hholds]
    exact ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero,
      hself, htoken, hnewnotes, hleavesIdx, hcommitFinal, hroot, hremove, hmark, hRandomOut, rfl⟩
  let outputsLen : Nat := (payoutOutputs ++ remainderOutputs).length
  let finalHoldings : Nat → Term → Option ((Nat × Nat) × Term) :=
    update mid.holdings asset (update (mid.holdings asset) cid
      (if remainder = 0 then none
       else some ((insertTreeNumber mid.pool.closedTrees mid.pool.leaves outputsLen,
           insertStartPos mid.pool.leaves outputsLen + outputsLen - 1),
         commitment (npk mid.self 0) asset remainder)))
  let finalChannels := update mid.channels cid
    { mid.channels cid with
      outcomeHash := outcomeHashOf (curOutcome.mapIdx fun i exit =>
        if i ≠ assetIndex then exit else
          { exit with allocations := (transferEffects allocs held [destIdx]).1 }) }
  let final : AdjudicatorState :=
    { mid with pool := finalPool, holdings := finalHoldings, channels := finalChannels }
  refine ⟨final, hci, hmode, rfl, hoh, True.intro, ?_, rfl, rfl, rfl, rfl, rfl⟩
  dsimp only
  rw [hassetDef, hallocsDef, hheldDef, hTotalPayoutsDef, hRemDef, hPayoutDef]
  exact ⟨hnoguarantee', 0, hospendstep, rfl, rfl⟩

/-- The payout step of `FinalizedPaysInv`. At a reachable state where the
    invariant holds, `actor` makes at most one call. After it,
    `dest.destination` holds a live note worth at least `x`. Under A2 the
    note exists already, and no call is necessary. Under A1,
    `transfer_step_exists` gives a `.transfer` that selects only
    `destIdx`, and `transfer_step_pays_selected` shows that this call
    mints the note. -/
theorem finalizedPaysInv_pays
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0) (actor : Actor)
    (cid : Term) (o : Outcome) (assetIndex destIdx : Nat) (hAI : assetIndex < o.length) (x : Nat)
    (hxpos : 0 < x) (dest : Allocation) (mid : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid)
    (hinv : FinalizedPaysInv cid o assetIndex destIdx hAI x dest mid) :
    ∃ (payCalls : List (Actor × Call)) (final : AdjudicatorState),
      AppliesAll sig appRel mid payCalls final ∧
      ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧
        pre.token = (o.get ⟨assetIndex, hAI⟩).asset ∧
        x ≤ pre.value ∧
        PoolIsLive final.pool (commitment pre.npk pre.token pre.value) := by
  rcases hinv with ⟨curOutcome, hci, hfinA1, hohA1, _, hnogA1, hassetA1, hgetDA1, haffA1⟩ | hA2
  · have hdestlt_cur : destIdx < (curOutcome.get ⟨assetIndex, hci⟩).allocations.length := by
      rcases Nat.lt_or_ge destIdx (curOutcome.get ⟨assetIndex, hci⟩).allocations.length with
        hlt | hge
      · exact hlt
      · exfalso
        have hafford0 : (afford (curOutcome.get ⟨assetIndex, hci⟩).allocations
            (heldValue mid (o.get ⟨assetIndex, hAI⟩).asset cid)).getD destIdx 0 = 0 := by
          have hlen := afford_length (curOutcome.get ⟨assetIndex, hci⟩).allocations
            (heldValue mid (o.get ⟨assetIndex, hAI⟩).asset cid)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
        omega
    have hdest_cur : (curOutcome.get ⟨assetIndex, hci⟩).allocations[destIdx]? = some dest := by
      have h1 : (curOutcome.get ⟨assetIndex, hci⟩).allocations[destIdx]? =
          some ((curOutcome.get ⟨assetIndex, hci⟩).allocations.getD destIdx Allocation.default) := by
        rw [List.getD_eq_getElem?_getD]
        cases hdd : (curOutcome.get ⟨assetIndex, hci⟩).allocations[destIdx]? with
        | none => rw [List.getElem?_eq_none_iff] at hdd; omega
        | some a => simp
      rw [h1, hgetDA1]
    have haffordable_cur : x ≤ (afford (curOutcome.get ⟨assetIndex, hci⟩).allocations
        (heldValue mid (curOutcome.get ⟨assetIndex, hci⟩).asset cid)).getD destIdx 0 := by
      rw [hassetA1]; exact haffA1
    obtain ⟨final0, hstepTransfer⟩ := transfer_step_exists sig appRel assets selfInputs pool0
      hReachPool actor mid assetIndex cid curOutcome destIdx hci
      hreach hfinA1 hohA1 dest hdest_cur hnogA1 x hxpos haffordable_cur
    obtain ⟨pre, hpreNpk, hpreTok, hxlepre, hlive⟩ := transfer_step_pays_selected sig appRel
      actor mid final0 assetIndex cid (mid.channels cid).stateHash
      curOutcome destIdx hstepTransfer hci dest hdest_cur hnogA1 x hxpos haffordable_cur
    refine ⟨[(actor, .transfer assetIndex cid (mid.channels cid).stateHash curOutcome [destIdx])],
      final0, ⟨final0, hstepTransfer, rfl⟩, pre, hpreNpk, ?_, hxlepre, hlive⟩
    rw [hpreTok, hassetA1]
  · exact ⟨[], mid, rfl, hA2⟩

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
    OWN actor identities (the Nitro identity `h`, and the pool key `pk`
    `dest.destination` names) from `interleaved`: without it,
    `interleaved` could contain a step only `h` themselves could take
    (`.sign h d` for an arbitrary `d` `h` never chose, `Operations.lean`'s
    actor check) and have it count as "the adversary's" doing, when it is
    really `h`'s own action. `h`'s own steps belong only
    in the witnessed `payCalls`, never in `interleaved`. `hnotick`
    excludes a `.tick` from `interleaved` too: a `.tick` is nobody's
    signed action, so `hnotActor` alone does not rule it out, but an
    adversary ticking the clock forward could otherwise time a stale
    challenge into `.finalized` mode with the WRONG outcome before `h`'s
    own strategy runs; `h`'s own strategy may still tick the clock, in
    `payCalls`, if its own `conclude` needs one. `hduration` and
    `hnotfinal` are what make the no-tick exclusion sufficient: a fresh
    `.challenge` registered during `interleaved` always sets `finalizesAt
    > now` (`0 < fp.challengeDuration`), so it cannot finalize the
    channel without a further tick, and the channel is not ALREADY
    finalized (with some stale outcome) at `s` to begin with. `hnowpos`
    is what lets `h`'s own `.conclude` actually finalize the channel: on
    a real chain `block.timestamp` is a positive Unix time, so `conclude`
    (`ForceMove.sol:160-167`, writes `uint48(block.timestamp)`) always
    finalizes; the model's own `finalizesAt := s.now` (`Operations.lean`'s
    `.conclude` case) treats `0` as the SAME sentinel `ChannelStatus.mode`
    reads as "no deadline set" (`.open`), so concluding at `s.now = 0`
    would not finalize. `hhonest`
    closes the one remaining way an adversary could still finalize the
    channel with the WRONG outcome during `interleaved`, via `.conclude`:
    `h` may, in an earlier round, have signed some OTHER final state for
    this same channel (a stale offer, since withdrawn) that still
    satisfies `AuthorizedBy` at `s`; `hhonest` says `h` never signed any
    final state for `fp` OTHER than `candidate` itself, so no adversary-
    assembled `SignedByAll` for a different final state can ever succeed.
    `hsigned` reads unanimous signing at `s`; since `.sign` only ever
    adds to `signedBy`, and only in the ACTING participant's own row,
    `interleaved` (now excluding `h`'s own actor) cannot UN-sign
    anything, so `SignedByAll` still holds at `mid`. The payout note's
    own key, `dest.destination`, is restated as a USER note key
    (`npk (masterPublicKey pk nk) r`) rather than a raw address:
    `pk`/`nk`/`r` are `h`'s own keys and the random `h` chose when the
    outcome was signed (the same convention `DepositStep`'s own witness
    uses, `Notes.lean`), so the note this theorem mints is one `h` can
    actually spend — a RAW address (`Term.val h`, the original text)
    names a note no `npk` derivation can ever equal (`Term`'s
    `val`/`hash` constructors are disjoint), so a payout to one would be
    unspendable by anyone. "Getting money owed" is a live note in the
    pool, matching this model's note-based payment (`Notes.lean`): `h`
    can later spend it with their own key, which is the Armada-layer
    meaning of "paid" — the armada-nitro rule (`State.lean`). `0 < x`:
    a zero payment carries no content, and no call mints a note for a
    zero payout (`zero_payout_mints_nothing`), so `x = 0` would need a
    DIFFERENT, pre-existing note at `dest.destination` no hypothesis
    here supplies. `actor ≠ Actor.pool pk`: another `.transfer` can
    legitimately pay `destIdx` itself before `h`'s own calls run (clause
    24 names no caller restriction); when it does, the minted note is
    THIS theorem's own witness directly. The ONE further gap a MODEL FIX
    closes (found proving this theorem): `.deposit`'s own witness, left
    unconstrained beyond the abstract `EdDSAVerify`, could otherwise
    nullify that note's position by merely CLAIMING its npk/value, since
    nothing tied the claim back to a real prior signing
    (`Operations.lean`'s `.deposit` case, "MODEL FIX" comment). The fix
    gates `.deposit` on `s.poolSignedBy w.publicKey (msgHashOf pub)`,
    grown only by `.signNote` taken AS `.pool pk` (the module comment on
    `.sign`/`.signNote`); excluding `actor ≠ Actor.pool pk` from
    `interleaved` then means NO step in it can newly authorize that
    key's spend (`poolSignedBy_frame`), and `deposit_spend_requires_
    signer` (`Lemmas.lean`) shows a `.deposit` under any OTHER key could
    not have named this note's position in the first place — together,
    once minted, the note survives the rest of `interleaved` untouched,
    PROVIDED `pk` had not ALREADY signed a spend of it before `s`, which
    neither lemma rules out on its own (`poolSignedBy_frame` only shows
    `pk`'s row cannot GROW during `interleaved`; it says nothing about
    what the row already held at `s`, and `s` is chosen before the note
    even exists). `hhonestPool` is the pool-layer half of the SAME
    honest-participant condition `hhonest` states for the Nitro layer:
    an honest `h` signs a pool spend only for a transaction it actually
    means to make, so at `s`, key `pk` has signed no transaction whose
    witness nullifies a note keyed to `dest.destination` — the one fact
    `deposit_spend_requires_signer`/`poolSignedBy_frame` need together
    with `hhonestPool` to rule out EVERY `.deposit` in `interleaved`
    spending this note, not just ones authorized DURING it. -/
theorem unbeatable_pays
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (h : Nat) (assetIndex : Nat)
    (hAssetIdx : assetIndex < candidate.outcome.length)
    (destIdx : Nat) (x : Nat) (dest : Allocation)
    (hReachPool : _root_.Reachable pool0)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) (hp : h ∈ fp.participants)
    (hfinal : candidate.isFinal = true)
    (hduration : 0 < fp.challengeDuration)
    (hnotfinal : (s.channels (channelId fp)).mode s.now ≠ .finalized) (hnowpos : 0 < s.now)
    (hsigned : SignedByAll sig s fp candidate)
    (hdest : (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations[destIdx]? = some dest)
    (hassetunique : ∀ i (hi : i < candidate.outcome.length), i ≠ assetIndex →
      (candidate.outcome.get ⟨i, hi⟩).asset ≠ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset)
    (hnoguarantee : ∀ a ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations,
      a.allocationType ≠ .guarantee)
    (pk : Nat × Nat) (nk : Nat) (r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (hxpos : 0 < x)
    (haffordable : x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
      (heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp))).getD destIdx 0)
    (hhonest : ∀ candidate', candidate'.isFinal = true →
      AuthorizedBy sig s h (stateHash fp candidate') →
      stateHash fp candidate' = stateHash fp candidate)
    (hhonestPool : ∀ m, s.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination) :
    ∀ (interleaved : List (Actor × Call)) (mid : AdjudicatorState),
      AppliesAll sig appRel s interleaved mid →
      (∀ actor call, (actor, call) ∈ interleaved →
        actor ≠ Actor.nitro h ∧ actor ≠ Actor.pool pk) →
      (∀ actor newNow, (actor, Call.tick newNow) ∉ interleaved) →
      ∃ (payCalls : List (Actor × Call)) (final : AdjudicatorState),
        AppliesAll sig appRel mid payCalls final ∧
        ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          x ≤ pre.value ∧
          PoolIsLive final.pool (commitment pre.npk pre.token pre.value) := by
  intro interleaved mid happ hexcl hexclTick
  have hinv_s : UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest s :=
    Or.inl ⟨hnotfinal, hsigned, haffordable⟩
  obtain ⟨hinv_mid, _, _⟩ := unbeatablePaysInv_appliesAll sig appRel h fp candidate hp hduration
    assetIndex destIdx hAssetIdx x hxpos dest pk nk r hh_dest s hdest hassetunique hnoguarantee
    hhonest hhonestPool assets selfInputs pool0 hreach happ hexcl hexclTick rfl rfl hinv_s
  have hreach_mid : Reachable sig appRel (genesis assets selfInputs pool0) mid := by
    obtain ⟨calls0, happ0⟩ := hreach
    exact ⟨calls0 ++ interleaved, appliesAll_append happ0 happ⟩
  rcases hinv_mid with hB | hF
  · obtain ⟨hnotfinal_mid, hsigned_mid, haffordable_mid⟩ := hB
    have hnow_mid : mid.now = s.now := appliesAll_now_frame sig appRel s mid interleaved happ hexclTick
    have hnowpos_mid : 0 < mid.now := hnow_mid ▸ hnowpos
    obtain ⟨payCalls1, mid1, happ1, hmode1, hoh1, hpool1, hhold1, _hself1, _hsigned1, _hpoolSigned1⟩ :=
      conclude_step_finalizes sig appRel (Actor.nitro h) mid fp candidate hnotfinal_mid hnowpos_mid
        hfinal hsigned_mid
    have hreach_mid1 : Reachable sig appRel (genesis assets selfInputs pool0) mid1 := by
      obtain ⟨calls0, happ0⟩ := hreach_mid
      exact ⟨calls0 ++ payCalls1, appliesAll_append happ0 happ1⟩
    have hheldeq : heldValue mid1 (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) =
        heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) := by
      unfold heldValue; rw [hhold1, hpool1]
    have haffordable_mid1 : x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
        (heldValue mid1 (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
          (channelId fp))).getD destIdx 0 := by
      rw [hheldeq]; exact haffordable_mid
    obtain ⟨final0, hstepTransfer⟩ := transfer_step_exists sig appRel assets selfInputs pool0
      hReachPool (Actor.nitro h) mid1 assetIndex (channelId fp) candidate.outcome destIdx hAssetIdx
      hreach_mid1 hmode1 hoh1 dest hdest hnoguarantee x hxpos haffordable_mid1
    obtain ⟨pre, hpreNpk, hpreTok, hxlepre, hlive⟩ := transfer_step_pays_selected sig appRel
      (Actor.nitro h) mid1 final0 assetIndex (channelId fp) (mid1.channels (channelId fp)).stateHash
      candidate.outcome destIdx hstepTransfer hAssetIdx dest hdest hnoguarantee x hxpos
      haffordable_mid1
    refine ⟨payCalls1 ++
      [(Actor.nitro h, .transfer assetIndex (channelId fp) (mid1.channels (channelId fp)).stateHash
        candidate.outcome [destIdx])], final0,
      appliesAll_append happ1 ⟨final0, hstepTransfer, rfl⟩, pre, hpreNpk, hpreTok, hxlepre, hlive⟩
  · exact finalizedPaysInv_pays sig appRel assets selfInputs pool0 hReachPool (Actor.nitro h)
      (channelId fp) candidate.outcome assetIndex destIdx hAssetIdx x hxpos dest mid hreach_mid hF

/-- `.challenge`'s own effect sets `turnNumRecord := candidate'.turnNum` together with
    `stateHash := stateHash fp' candidate'` (`Operations.lean`). `.checkpoint`/`.conclude`
    (and `.bulkConcludeAndTransferAllAssets`) instead clear `stateHash` to `Term.val 0`,
    never a genuine hash (`Term.val_ne_hash`); `.transfer`/`.reclaim`/
    `.bulkTransferAllAssets` only ever rewrite a channel's own `outcomeHash`, leaving
    `stateHash`/`turnNumRecord` as they found them. So whenever a reachable channel's
    own `stateHash` reads as SOME `stateHash fp candidate` (a genuine hash, never the
    cleared sentinel), the LAST write to it was a `.challenge` registering exactly
    `candidate` — `stateHashOf_inj` (the variable part's own hash includes `turnNum`)
    pins `turnNumRecord` to `candidate.turnNum`, whatever mode the channel is in now.
    What `unbeatable_pays_after_timeout` needs: a rival `.challenge`/`.checkpoint`
    cannot displace the registered challenge unless its own turn number exceeds
    `candidate.turnNum`, which `hnohigher` rules out. -/
theorem challenge_mode_status_matches
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hsh : (s.channels (channelId fp)).stateHash = stateHash fp candidate) :
    (s.channels (channelId fp)).turnNumRecord = candidate.turnNum := by
  have hinv : ∀ fp' candidate', (s.channels (channelId fp')).stateHash =
      stateHash fp' candidate' → (s.channels (channelId fp')).turnNumRecord = candidate'.turnNum :=
    reachable_preserves
      (P := fun st => ∀ fp' candidate', (st.channels (channelId fp')).stateHash =
        stateHash fp' candidate' → (st.channels (channelId fp')).turnNumRecord = candidate'.turnNum)
      (by
        intro fp' candidate' hsh0
        exfalso
        have hne : Term.val 0 ≠ stateHash fp' candidate' := by
          unfold stateHash stateHashOf Term.keccak
          exact Term.val_ne_hash 0 .keccak _
        exact hne hsh0)
      (by
        intro actor call st st' hP hstep
        intro fp' candidate' hsh'
        cases call with
        | deposit cid expectedHeld asset amount =>
          obtain ⟨_, _, _, _, _, hchan, _, _, _, _, _⟩ := hstep
          rw [hchan] at hsh' ⊢; exact hP fp' candidate' hsh'
        | sign p d =>
          obtain ⟨_, _, _, hchan, _, _, _, _, _⟩ := hstep
          rw [hchan] at hsh' ⊢; exact hP fp' candidate' hsh'
        | signNote pk' msgHash =>
          obtain ⟨_, _, _, hchan, _, _, _, _, _⟩ := hstep
          rw [hchan] at hsh' ⊢; exact hP fp' candidate' hsh'
        | tick newNow =>
          obtain ⟨_, _, _, _, hchan, _, _, _, _⟩ := hstep
          rw [hchan] at hsh' ⊢; exact hP fp' candidate' hsh'
        | challenge fp'' proof candidate'' challenger =>
          obtain ⟨_, _, _, _, hchan, _, _, _, _, _, _⟩ := hstep
          by_cases hcc : channelId fp'' = channelId fp'
          · have hchanEq : st'.channels (channelId fp') =
                { turnNumRecord := candidate''.turnNum,
                  finalizesAt := st.now + fp''.challengeDuration,
                  stateHash := stateHash fp'' candidate'',
                  outcomeHash := outcomeHashOf candidate''.outcome } := by
              rw [hchan]; unfold update; rw [if_pos hcc.symm]
            rw [hchanEq] at hsh' ⊢
            dsimp only at hsh' ⊢
            exact (stateHashOf_inj hsh').2.2.2.1
          · have hchanEq : st'.channels (channelId fp') = st.channels (channelId fp') := by
              rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
            rw [hchanEq] at hsh' ⊢
            exact hP fp' candidate' hsh'
        | checkpoint fp'' proof candidate'' =>
          obtain ⟨_, _, _, hchan, _, _, _, _, _, _, _⟩ := hstep
          by_cases hcc : channelId fp'' = channelId fp'
          · exfalso
            have hchanEq : st'.channels (channelId fp') =
                { turnNumRecord := candidate''.turnNum, finalizesAt := 0,
                  stateHash := Term.val 0, outcomeHash := Term.val 0 } := by
              rw [hchan]; unfold update; rw [if_pos hcc.symm]
            rw [hchanEq] at hsh'
            dsimp only at hsh'
            have hne : Term.val 0 ≠ stateHash fp' candidate' := by
              unfold stateHash stateHashOf Term.keccak
              exact Term.val_ne_hash 0 .keccak _
            exact hne hsh'
          · have hchanEq : st'.channels (channelId fp') = st.channels (channelId fp') := by
              rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
            rw [hchanEq] at hsh' ⊢
            exact hP fp' candidate' hsh'
        | conclude fp'' candidate'' =>
          obtain ⟨_, _, _, hchan, _, _, _, _, _, _⟩ := hstep
          by_cases hcc : channelId fp'' = channelId fp'
          · exfalso
            have hchanEq : st'.channels (channelId fp') =
                { turnNumRecord := 0, finalizesAt := st.now,
                  stateHash := Term.val 0, outcomeHash := outcomeHashOf candidate''.outcome } := by
              rw [hchan]; unfold update; rw [if_pos hcc.symm]
            rw [hchanEq] at hsh'
            dsimp only at hsh'
            have hne : Term.val 0 ≠ stateHash fp' candidate' := by
              unfold stateHash stateHashOf Term.keccak
              exact Term.val_ne_hash 0 .keccak _
            exact hne hsh'
          · have hchanEq : st'.channels (channelId fp') = st.channels (channelId fp') := by
              rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
            rw [hchanEq] at hsh' ⊢
            exact hP fp' candidate' hsh'
        | transfer assetIndex' cid claimedStateHash outcome indices =>
          obtain ⟨hidx, hmodeT, hshT, hohT, hstrict, hinner, _hcfg, _hself, hnow, hsb⟩ := hstep
          obtain ⟨_hguarantee, hrest⟩ := hinner
          obtain ⟨r, hospend, hholdseq, hchan⟩ := hrest
          have hstateEq : (st'.channels (channelId fp')).stateHash =
              (st.channels (channelId fp')).stateHash := by
            rw [hchan]; unfold update
            by_cases hcc : channelId fp' = cid
            · rw [if_pos hcc, hcc]
            · rw [if_neg hcc]
          have hturnEq : (st'.channels (channelId fp')).turnNumRecord =
              (st.channels (channelId fp')).turnNumRecord := by
            rw [hchan]; unfold update
            by_cases hcc : channelId fp' = cid
            · rw [if_pos hcc, hcc]
            · rw [if_neg hcc]
          rw [hstateEq] at hsh'
          rw [hturnEq]
          exact hP fp' candidate' hsh'
        | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource
            targetOutcome targetAssetIndex claimedTargetStateHash =>
          obtain ⟨_, _, _, _, _, hrest, _, _, _, _, _, _, _⟩ := hstep
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hchan⟩ := hrest
          have hstateEq : (st'.channels (channelId fp')).stateHash =
              (st.channels (channelId fp')).stateHash := by
            rw [hchan]; unfold update
            by_cases hcc : channelId fp' = sourceChannelId
            · rw [if_pos hcc, hcc]
            · rw [if_neg hcc]
          have hturnEq : (st'.channels (channelId fp')).turnNumRecord =
              (st.channels (channelId fp')).turnNumRecord := by
            rw [hchan]; unfold update
            by_cases hcc : channelId fp' = sourceChannelId
            · rw [if_pos hcc, hcc]
            · rw [if_neg hcc]
          rw [hstateEq] at hsh'
          rw [hturnEq]
          exact hP fp' candidate' hsh'
        | bulkTransferAllAssets cid outcome claimedStateHash =>
          obtain ⟨hmodeBulk, hshBulk, hohBulk, newOutcome, hfold, hchan, _hcfg, _hself, hnow, hsb⟩ :=
            hstep
          have hstateEq : (st'.channels (channelId fp')).stateHash =
              (st.channels (channelId fp')).stateHash := by
            rw [hchan]; unfold update
            by_cases hcc : channelId fp' = cid
            · rw [if_pos hcc, hcc]
            · rw [if_neg hcc]
          have hturnEq : (st'.channels (channelId fp')).turnNumRecord =
              (st.channels (channelId fp')).turnNumRecord := by
            rw [hchan]; unfold update
            by_cases hcc : channelId fp' = cid
            · rw [if_pos hcc, hcc]
            · rw [if_neg hcc]
          rw [hstateEq] at hsh'
          rw [hturnEq]
          exact hP fp' candidate' hsh'
        | bulkConcludeAndTransferAllAssets fp'' candidate'' =>
          obtain ⟨hprecond, hisfinal, hcsigned, newOutcome, hfold, hchan, _hcfg, _hself, hnow, hsb⟩ :=
            hstep
          by_cases hcc : channelId fp'' = channelId fp'
          · exfalso
            have hchanEq : st'.channels (channelId fp') =
                { turnNumRecord := 0, finalizesAt := st.now,
                  stateHash := Term.val 0, outcomeHash := outcomeHashOf newOutcome } := by
              rw [hchan]; unfold update; rw [if_pos hcc.symm]
            rw [hchanEq] at hsh'
            dsimp only at hsh'
            have hne : Term.val 0 ≠ stateHash fp' candidate' := by
              unfold stateHash stateHashOf Term.keccak
              exact Term.val_ne_hash 0 .keccak _
            exact hne hsh'
          · have hchanEq : st'.channels (channelId fp') = st.channels (channelId fp') := by
              rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
            rw [hchanEq] at hsh' ⊢
            exact hP fp' candidate' hsh')
      hreach
  exact hinv fp candidate hsh

/-- `unbeatable_pays_after_timeout`'s own carried fact: `fp`'s channel
    still reads exactly as registered at `s0` (so still `.challenge`,
    still naming `candidate`), and `destIdx` still affords `x`. Plays
    the same role `UnbeatablePaysInv`'s own B disjunct plays for
    `unbeatable_pays` — except it carries no `SignedByAll` fact, since
    a registered challenge does not need one. -/
def TimeoutChallengeInv (s0 : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (assetIndex destIdx : Nat) (hAssetIdx : assetIndex < candidate.outcome.length) (x : Nat)
    (st : AdjudicatorState) : Prop :=
  st.channels (channelId fp) = s0.channels (channelId fp) ∧ st.now = s0.now ∧
  x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
    (heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp))).getD
    destIdx 0

/-- `TimeoutChallengeInv`'s own one-interleaving carry: at every state an
    `interleaved`-style sequence (no `h`/`Actor.pool pk` actor, no
    `.tick`, every higher-turn `appRel` approval ruled out by
    `hnohigher`) reaches, EITHER the registered challenge still reads
    exactly as at `s0` (`TimeoutChallengeInv` survives: `.challenge`/
    `.checkpoint` against `fp`'s own channel need a turn exceeding
    `candidate.turnNum`, which `hnohigher` rules out since `fp`'s
    channel's own `turnNumRecord` is pinned to `candidate.turnNum`
    (`hturn`); `.transfer`/`.reclaim`/`.bulkTransferAllAssets` against
    it are impossible outright, needing a `.finalized` channel; every
    other call leaves `fp`'s channel untouched) OR a `.conclude`/
    `.bulkConcludeAndTransferAllAssets` against it succeeded — only
    possible with `candidate` itself (`hhonest`/`stateHashOf_inj`,
    exactly `unbeatablePaysInv_step`'s own `.conclude` argument), at
    which point `UnbeatablePaysInv` takes over and the rest of
    `interleaved` delegates to the already-proved
    `unbeatablePaysInv_appliesAll`. -/
theorem TimeoutInv_appliesAll
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (h : Nat) (fp : FixedPart) (candidate : VariablePart) (hp : h ∈ fp.participants)
    (hduration : 0 < fp.challengeDuration)
    (assetIndex destIdx : Nat) (hAssetIdx : assetIndex < candidate.outcome.length) (x : Nat)
    (hxpos : 0 < x)
    (dest : Allocation) (pk : Nat × Nat) (nk r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (s0 : AdjudicatorState)
    (hdest : (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations[destIdx]? = some dest)
    (hassetunique : ∀ i (hi : i < candidate.outcome.length), i ≠ assetIndex →
      (candidate.outcome.get ⟨i, hi⟩).asset ≠ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset)
    (hnoguarantee : ∀ a ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations,
      a.allocationType ≠ .guarantee) (hnowpos : 0 < s0.now)
    (hhonest : ∀ candidate', candidate'.isFinal = true →
      AuthorizedBy sig s0 h (stateHash fp candidate') →
      stateHash fp candidate' = stateHash fp candidate)
    (hhonestPool : ∀ m, s0.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hregMode : (s0.channels (channelId fp)).mode s0.now = .challenge)
    (hturn : (s0.channels (channelId fp)).turnNumRecord = candidate.turnNum) :
    ∀ {calls : List (Actor × Call)} {st st' : AdjudicatorState},
      Reachable sig appRel (genesis assets selfInputs pool0) st →
      AppliesAll sig appRel st calls st' →
      (∀ actor call, (actor, call) ∈ calls → actor ≠ Actor.nitro h ∧ actor ≠ Actor.pool pk) →
      (∀ actor newNow, (actor, Call.tick newNow) ∉ calls) →
      st.signedBy h = s0.signedBy h → st.poolSignedBy pk = s0.poolSignedBy pk →
      (∀ (pre post : List (Actor × Call)) (stm : AdjudicatorState),
        calls = pre ++ post → AppliesAll sig appRel st pre stm →
        ∀ proof' cand, cand.turnNum > candidate.turnNum → ¬ appRel stm fp proof' cand) →
      TimeoutChallengeInv s0 fp candidate assetIndex destIdx hAssetIdx x st →
      ((UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest st' ∧
        candidate.isFinal = true) ∨
        TimeoutChallengeInv s0 fp candidate assetIndex destIdx hAssetIdx x st') ∧
        st'.signedBy h = s0.signedBy h ∧ st'.poolSignedBy pk = s0.poolSignedBy pk
  | [], st, st', _, happ, _, _, hsrow, hprow, _, hT => by
    rw [show st' = st from happ]; exact ⟨Or.inr hT, hsrow, hprow⟩
  | (actor, call) :: rest, st, st', hreach, happ, hexcl, hexclTick, hsrow, hprow, hnohigher, hT => by
    obtain ⟨mid, hstep, hrest⟩ := happ
    obtain ⟨hTchan, hTnow, hTaff⟩ := hT
    have hactor : actor ≠ Actor.nitro h := (hexcl actor call (List.mem_cons_self ..)).1
    have hactorPool : actor ≠ Actor.pool pk := (hexcl actor call (List.mem_cons_self ..)).2
    have hnotick : ∀ newNow, call ≠ Call.tick newNow := fun newNow heq =>
      hexclTick actor newNow (heq ▸ List.mem_cons_self ..)
    have hreach_mid : Reachable sig appRel (genesis assets selfInputs pool0) mid :=
      reachable_step hreach hstep
    have hnow_mid : mid.now = st.now := step_now_frame sig appRel actor st mid call hnotick hstep
    have hT2_mid : mid.now = s0.now := hnow_mid.trans hTnow
    have hsrow_mid : mid.signedBy h = s0.signedBy h :=
      (step_signedBy_frame sig appRel actor st mid call hstep h hactor).trans hsrow
    have hprow_mid : mid.poolSignedBy pk = s0.poolSignedBy pk :=
      (poolSignedBy_frame sig appRel actor st mid call hstep pk hactorPool).trans hprow
    have hnohigher_head : ∀ proof' cand, cand.turnNum > candidate.turnNum →
        ¬ appRel st fp proof' cand :=
      hnohigher [] ((actor, call) :: rest) st rfl rfl
    have hmidnowpos : 0 < mid.now := hT2_mid ▸ hnowpos
    have hmid_cases : (UnbeatablePaysInv sig fp candidate assetIndex destIdx hAssetIdx x dest mid ∧
        candidate.isFinal = true) ∨
        TimeoutChallengeInv s0 fp candidate assetIndex destIdx hAssetIdx x mid := by
      cases call with
      | deposit cid expectedHeld asset amount =>
        obtain ⟨hdeffect, hdframe, hchan⟩ :=
          deposit_effect sig appRel assets selfInputs pool0 actor st mid cid expectedHeld asset
            amount hreach hstep
        have hheld : ∀ a c, heldValue mid a c = heldValue st a c ∨
            (a = asset ∧ c = cid) ∧ heldValue mid a c = heldValue st a c + amount := by
          intro a c
          by_cases hac : (a, c) = (asset, cid)
          · right
            have ha : a = asset := (Prod.ext_iff.mp hac).1
            have hc : c = cid := (Prod.ext_iff.mp hac).2
            subst ha; subst hc; exact ⟨⟨rfl, rfl⟩, hdeffect⟩
          · left; exact hdframe a c hac
        refine Or.inr ⟨by rw [hchan]; exact hTchan, hT2_mid, ?_⟩
        rcases hheld (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp) with
          heq | ⟨_, heq⟩
        · rw [heq]; exact hTaff
        · rw [heq]
          exact Nat.le_trans hTaff
            (afford_mono (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
              (Nat.le_add_right _ _) destIdx)
      | sign p d =>
        obtain ⟨_, _, hpool, hchan, hhold, _, _, _, _⟩ := hstep
        refine Or.inr ⟨by rw [hchan]; exact hTchan, hT2_mid, ?_⟩
        have hheldEq : heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
            (channelId fp) = heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
            (channelId fp) := by unfold heldValue; rw [hhold, hpool]
        rw [hheldEq]; exact hTaff
      | signNote pk' msgHash =>
        obtain ⟨_, _, hpool, hchan, hhold, _, _, _, _⟩ := hstep
        refine Or.inr ⟨by rw [hchan]; exact hTchan, hT2_mid, ?_⟩
        have hheldEq : heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
            (channelId fp) = heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
            (channelId fp) := by unfold heldValue; rw [hhold, hpool]
        rw [hheldEq]; exact hTaff
      | tick newNow => exact absurd rfl (hnotick newNow)
      | challenge fp'' proof' candidate'' challenger =>
        obtain ⟨hprecond, happrv, _, _, hchan, hspool, hshold, _, _, _, _, _⟩ := hstep
        by_cases hcc : channelId fp'' = channelId fp
        · exfalso
          have hfpeq : fp'' = fp := channelId_inj hcc
          rw [hfpeq] at hprecond happrv
          have hmode_mid : (st.channels (channelId fp)).mode st.now = .challenge := by
            rw [hTchan, hTnow]; exact hregMode
          rw [hmode_mid] at hprecond
          have hturnrec : (st.channels (channelId fp)).turnNumRecord = candidate.turnNum := by
            rw [hTchan]; exact hturn
          rw [hturnrec] at hprecond
          exact (hnohigher_head proof' candidate'' hprecond) happrv
        · have hchanEq : mid.channels (channelId fp) = st.channels (channelId fp) := by
            rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
          have hheldEq : heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) = heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) := by unfold heldValue; rw [hshold, hspool]
          refine Or.inr ⟨?_, hT2_mid, ?_⟩
          · rw [hchanEq]; exact hTchan
          · rw [hheldEq]; exact hTaff
      | checkpoint fp'' proof' candidate'' =>
        obtain ⟨_, hprecond, happrv, hchan, hspool, hshold, _, _, _, _, _⟩ := hstep
        by_cases hcc : channelId fp'' = channelId fp
        · exfalso
          have hfpeq : fp'' = fp := channelId_inj hcc
          rw [hfpeq] at hprecond happrv
          have hturnrec : (st.channels (channelId fp)).turnNumRecord = candidate.turnNum := by
            rw [hTchan]; exact hturn
          rw [hturnrec] at hprecond
          exact (hnohigher_head proof' candidate'' hprecond) happrv
        · have hchanEq : mid.channels (channelId fp) = st.channels (channelId fp) := by
            rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
          have hheldEq : heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) = heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) := by unfold heldValue; rw [hshold, hspool]
          refine Or.inr ⟨?_, hT2_mid, ?_⟩
          · rw [hchanEq]; exact hTchan
          · rw [hheldEq]; exact hTaff
      | conclude fp'' candidate'' =>
        obtain ⟨hprecond, hisfinal, hcsigned, hchan, hspool, hsholdeq, _, _, hnow, hsbpair⟩ := hstep
        have hsbeq := hsbpair.1
        have hheldEq : ∀ a c, heldValue mid a c = heldValue st a c := by
          intro a c; unfold heldValue; rw [hsholdeq, hspool]
        by_cases hcc : channelId fp'' = channelId fp
        · have hfpeq : fp'' = fp := channelId_inj hcc
          rw [hfpeq] at hchan hcsigned
          have hchanEq : mid.channels (channelId fp) =
              { turnNumRecord := 0, finalizesAt := st.now, stateHash := Term.val 0,
                outcomeHash := outcomeHashOf candidate''.outcome } := by
            rw [hchan]; unfold update; rw [if_pos rfl]
          have hcsigned0 : AuthorizedBy sig s0 h (stateHash fp candidate'') := by
            have hc := hcsigned h hp
            unfold AuthorizedBy at hc ⊢
            rwa [hsrow] at hc
          have hsheq := hhonest candidate'' hisfinal hcsigned0
          have houtcome_eq := (stateHashOf_inj hsheq).2.2.1
          have hcandfinal : candidate.isFinal = true := (stateHashOf_inj hsheq).2.2.2.2 ▸ hisfinal
          have hstpos : st.now ≠ 0 := by rw [hTnow]; omega
          refine Or.inl ⟨Or.inr (Or.inl ⟨candidate.outcome, hAssetIdx, ?_, ?_, rfl, hnoguarantee,
            rfl, ?_, ?_⟩), hcandfinal⟩
          · rw [hchanEq, hnow]
            unfold ChannelStatus.mode
            dsimp only
            rw [if_neg hstpos, if_pos (Nat.le_refl _)]
          · rw [hchanEq]
            show outcomeHashOf candidate''.outcome = outcomeHashOf candidate.outcome
            rw [houtcome_eq]
          · rw [List.getD_eq_getElem?_getD, hdest]; rfl
          · rw [hheldEq]; exact hTaff
        · have hchanEq : mid.channels (channelId fp) = st.channels (channelId fp) := by
            rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
          exact Or.inr ⟨by rw [hchanEq]; exact hTchan, hT2_mid, by rw [hheldEq]; exact hTaff⟩
      | transfer assetIndex' cid claimedStateHash outcome indices =>
        have hheldEq := transfer_heldValue_frame sig appRel assets selfInputs pool0 actor st mid
          assetIndex' cid claimedStateHash outcome indices hreach hstep
          (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp)
        obtain ⟨_, hmodeT, _, _, _, ⟨_, _, _, _, hchan⟩, _⟩ := hstep
        by_cases hcc : cid = channelId fp
        · exfalso
          have hm : (st.channels (channelId fp)).mode st.now = .challenge := by
            rw [hTchan, hTnow]; exact hregMode
          rw [hcc, hm] at hmodeT
          exact absurd hmodeT (by decide)
        · have hchanEq : mid.channels (channelId fp) = st.channels (channelId fp) := by
            rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
          exact Or.inr ⟨by rw [hchanEq]; exact hTchan, hT2_mid,
            by rw [hheldEq (fun _ heq => hcc (congrArg Prod.snd heq).symm)]; exact hTaff⟩
      | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
          targetAssetIndex claimedTargetStateHash =>
        obtain ⟨hmodeSrc, hohSrc, hsa, hidx1, hguarantee, hrest', hspool, hsholdeq, _hcfg, _hself,
          hnow, hsb⟩ := hstep
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hchan⟩ := hrest'
        by_cases hcc : sourceChannelId = channelId fp
        · exfalso
          have hm : (st.channels (channelId fp)).mode st.now = .challenge := by
            rw [hTchan, hTnow]; exact hregMode
          rw [hcc, hm] at hmodeSrc
          exact absurd hmodeSrc (by decide)
        · have hchanEq : mid.channels (channelId fp) = st.channels (channelId fp) := by
            rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
          have hheldEq : heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) = heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) := by unfold heldValue; rw [hsholdeq, hspool]
          exact Or.inr ⟨by rw [hchanEq]; exact hTchan, hT2_mid, by rw [hheldEq]; exact hTaff⟩
      | bulkTransferAllAssets cid outcome claimedStateHash =>
        obtain ⟨hmodeBulk, hshBulk, hohBulk, newOutcome, hfold, hchan, _hcfg, _hself, hnow, hsb⟩ :=
          hstep
        by_cases hcc : cid = channelId fp
        · exfalso
          have hm : (st.channels (channelId fp)).mode st.now = .challenge := by
            rw [hTchan, hTnow]; exact hregMode
          rw [hcc, hm] at hmodeBulk
          exact absurd hmodeBulk (by decide)
        · have hchanEq : mid.channels (channelId fp) = st.channels (channelId fp) := by
            rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
          have hpreimageInv : ∀ qasset qcid qpos qc, st.holdings qasset qcid = some (qpos, qc) →
              ∃ pre, st.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
            intro qasset qcid qpos qc hc
            obtain ⟨⟨pre, hpre, hconsist, hval, _⟩, _⟩ :=
              holdingWellFormed_reachable sig appRel assets selfInputs pool0 st hreach qasset qcid
                qpos qc hc
            exact ⟨pre, hpre, hval, hconsist⟩
          have hheldEqAny : heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) = heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) := by
            unfold heldValue
            exact bulkTransferFold_heldValue_frame_cid st.self cid outcome newOutcome st.pool
              mid.pool st.holdings mid.holdings hfold hpreimageInv
              (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp)
              (fun heq => hcc heq.symm)
          exact Or.inr ⟨by rw [hchanEq]; exact hTchan, hT2_mid, by rw [hheldEqAny]; exact hTaff⟩
      | bulkConcludeAndTransferAllAssets fp'' candidate'' =>
        obtain ⟨hprecond, hisfinal, hcsigned, newOutcome, hfold, hchan, _hcfg, _hself, hnow, hsb⟩ :=
          hstep
        have hpreimageInv : ∀ qasset qcid qpos qc, st.holdings qasset qcid = some (qpos, qc) →
            ∃ pre, st.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
          intro qasset qcid qpos qc hc
          obtain ⟨⟨pre, hpre, hconsist, hval, _⟩, _⟩ :=
            holdingWellFormed_reachable sig appRel assets selfInputs pool0 st hreach qasset qcid
              qpos qc hc
          exact ⟨pre, hpre, hval, hconsist⟩
        by_cases hcc : channelId fp'' = channelId fp
        · have hfpeq : fp'' = fp := channelId_inj hcc
          rw [hfpeq] at hchan hcsigned hprecond hfold
          have hcsigned0 : AuthorizedBy sig s0 h (stateHash fp candidate'') := by
            have hc := hcsigned h hp
            unfold AuthorizedBy at hc ⊢
            rwa [hsrow] at hc
          have hsheq := hhonest candidate'' hisfinal hcsigned0
          have houtcome_eq : candidate''.outcome = candidate.outcome := (stateHashOf_inj hsheq).2.2.1
          have hcandfinal : candidate.isFinal = true := (stateHashOf_inj hsheq).2.2.2.2 ▸ hisfinal
          rw [houtcome_eq] at hfold
          have hidxN : assetIndex < newOutcome.length := by
            rw [bulkTransferFold_length st.self (channelId fp) candidate.outcome newOutcome st.pool
              mid.pool st.holdings mid.holdings hfold]
            exact hAssetIdx
          obtain ⟨_heqNewOutcome, hpayoutExists⟩ :=
            bulkTransferFold_index_payout st.self (channelId fp) candidate.outcome newOutcome
              st.pool mid.pool st.holdings mid.holdings hfold hpreimageInv assetIndex hAssetIdx
              hassetunique hidxN
          have hpayoutNe : (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
              (heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
                (channelId fp))).getD destIdx 0 ≠ 0 := by omega
          obtain ⟨pos, hlivemem⟩ := hpayoutExists destIdx hpayoutNe
          refine Or.inl ⟨Or.inr (Or.inr ⟨⟨((candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations.getD destIdx Allocation.default).destination,
            (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset,
            (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
              (heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
                (channelId fp))).getD destIdx 0⟩, ?_, rfl, hTaff, ?_⟩), hcandfinal⟩
          · rw [List.getD_eq_getElem?_getD, hdest]; rfl
          · exact ⟨(candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset, pos.1, pos.2, _,
              hlivemem, rfl⟩
        · have hchanEq : mid.channels (channelId fp) = st.channels (channelId fp) := by
            rw [hchan]; unfold update; rw [if_neg (fun h => hcc h.symm)]
          have hheldEqAny : heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) = heldValue st (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
              (channelId fp) := by
            unfold heldValue
            exact bulkTransferFold_heldValue_frame_cid st.self (channelId fp'') candidate''.outcome
              newOutcome st.pool mid.pool st.holdings mid.holdings hfold hpreimageInv
              (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp)
              (fun heq => hcc heq.symm)
          exact Or.inr ⟨by rw [hchanEq]; exact hTchan, hT2_mid, by rw [hheldEqAny]; exact hTaff⟩
    rcases hmid_cases with ⟨hUBP_mid, hcandfinal_mid⟩ | hT_mid
    · obtain ⟨res, hsrow', hprow'⟩ := unbeatablePaysInv_appliesAll sig appRel h fp candidate hp
        hduration assetIndex destIdx hAssetIdx x hxpos dest pk nk r hh_dest s0 hdest hassetunique
        hnoguarantee hhonest hhonestPool assets selfInputs pool0 hreach_mid hrest
        (fun actor' call' hc => hexcl actor' call' (List.mem_cons_of_mem _ hc))
        (fun actor' newNow' hc => hexclTick actor' newNow' (List.mem_cons_of_mem _ hc))
        hsrow_mid hprow_mid hUBP_mid
      exact ⟨Or.inl ⟨res, hcandfinal_mid⟩, hsrow', hprow'⟩
    · have hnohigher_rest : ∀ (pre post : List (Actor × Call)) (stm : AdjudicatorState),
          rest = pre ++ post → AppliesAll sig appRel mid pre stm →
          ∀ proof' cand, cand.turnNum > candidate.turnNum → ¬ appRel stm fp proof' cand := by
        intro pre post stm heq happre proof' cand hcand
        exact hnohigher ((actor, call) :: pre) post stm (by rw [heq, List.cons_append])
          ⟨mid, hstep, happre⟩
          proof' cand hcand
      exact TimeoutInv_appliesAll sig appRel h fp candidate hp hduration assetIndex destIdx
        hAssetIdx x hxpos dest pk nk r hh_dest s0 hdest hassetunique hnoguarantee hnowpos hhonest
        hhonestPool assets selfInputs pool0 hregMode hturn hreach_mid hrest
        (fun actor' call' hc => hexcl actor' call' (List.mem_cons_of_mem _ hc))
        (fun actor' newNow' hc => hexclTick actor' newNow' (List.mem_cons_of_mem _ hc))
        hsrow_mid hprow_mid hnohigher_rest hT_mid

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
    `hregistered` replaces the weaker, pre-existing `hsupported`/
    `hchallenger`/`hauth`/`hfinalizing` quartet: it states directly that
    `fp`'s own channel is, right now, challenged with `candidate`'s own
    `stateHash`/`outcomeHash` — not merely that SOME challenge fired for
    SOME state, which left the registered candidate unconstrained
    against `candidate` itself. `hnotActor` excludes `h`'s own actor
    identities from `interleaved`, `hnotick` excludes a `.tick` from it
    too, and `hduration`/`hhonest` play the same role as in
    `unbeatable_pays`, for the same reason it needs them: ruling out an
    adversary finalizing the channel early, by `.conclude`, with a
    DIFFERENT final state `h` once signed. The payout note's own key is
    restated the same way `unbeatable_pays` restates it, for the same
    reason. `0 < x`, for the same reason `unbeatable_pays` needs it:
    no call mints a note for a zero payout
    (`zero_payout_mints_nothing`). `hnowpos`, for the same reason
    `unbeatable_pays` needs it: a `.conclude` at `now = 0`
    (`ForceMove.sol:160-167`'s `uint48(block.timestamp)`, always
    positive on a real chain) resets `finalizesAt` to `0` instead of
    finalizing, so even the timeout guarantee needs `s.now` positive
    to keep a stray `.conclude` from clearing the registered
    challenge instead of winning it. -/
theorem unbeatable_pays_after_timeout
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (proof : List VariablePart)
    (candidate : VariablePart) (challenger h : Nat)
    (assetIndex : Nat)
    (hAssetIdx : assetIndex < candidate.outcome.length)
    (destIdx : Nat) (x : Nat) (dest : Allocation)
    (hReachPool : _root_.Reachable pool0)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) (hp : h ∈ fp.participants)
    (hregistered : (s.channels (channelId fp)).mode s.now = .challenge ∧
      (s.channels (channelId fp)).stateHash = stateHash fp candidate ∧
      (s.channels (channelId fp)).outcomeHash = outcomeHashOf candidate.outcome)
    (hduration : 0 < fp.challengeDuration) (hnowpos : 0 < s.now)
    (hdest : (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations[destIdx]? = some dest)
    (hassetunique : ∀ i (hi : i < candidate.outcome.length), i ≠ assetIndex →
      (candidate.outcome.get ⟨i, hi⟩).asset ≠ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset)
    (hnoguarantee : ∀ a ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations,
      a.allocationType ≠ .guarantee)
    (pk : Nat × Nat) (nk : Nat) (r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (hxpos : 0 < x)
    (haffordable : x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
      (heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp))).getD destIdx 0)
    (hhonest : ∀ candidate', candidate'.isFinal = true →
      AuthorizedBy sig s h (stateHash fp candidate') →
      stateHash fp candidate' = stateHash fp candidate)
    (hhonestPool : ∀ m, s.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination) :
    ∀ (interleaved : List (Actor × Call)) (mid : AdjudicatorState),
      AppliesAll sig appRel s interleaved mid →
      (∀ actor call, (actor, call) ∈ interleaved →
        actor ≠ Actor.nitro h ∧ actor ≠ Actor.pool pk) →
      (∀ actor newNow, (actor, Call.tick newNow) ∉ interleaved) →
      (∀ (pre post : List (Actor × Call)) (st : AdjudicatorState),
        interleaved = pre ++ post → AppliesAll sig appRel s pre st →
        ∀ proof' cand, cand.turnNum > candidate.turnNum → ¬ appRel st fp proof' cand) →
      ∃ (payCalls : List (Actor × Call)) (final : AdjudicatorState),
        AppliesAll sig appRel mid payCalls final ∧
        ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧
          pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
          x ≤ pre.value ∧
          PoolIsLive final.pool (commitment pre.npk pre.token pre.value) := by
  intro interleaved mid happ hexcl hexclTick hnohigher
  have hturn : (s.channels (channelId fp)).turnNumRecord = candidate.turnNum :=
    challenge_mode_status_matches sig appRel assets selfInputs pool0 s fp candidate hreach
      hregistered.2.1
  have hT0 : TimeoutChallengeInv s fp candidate assetIndex destIdx hAssetIdx x s :=
    ⟨rfl, rfl, haffordable⟩
  obtain ⟨hinv_mid, _, _⟩ := TimeoutInv_appliesAll sig appRel h fp candidate hp hduration
    assetIndex destIdx hAssetIdx x hxpos dest pk nk r hh_dest s hdest hassetunique hnoguarantee
    hnowpos hhonest hhonestPool assets selfInputs pool0 hregistered.1 hturn hreach happ hexcl
    hexclTick rfl rfl hnohigher hT0
  have hreach_mid : Reachable sig appRel (genesis assets selfInputs pool0) mid := by
    obtain ⟨calls0, happ0⟩ := hreach
    exact ⟨calls0 ++ interleaved, appliesAll_append happ0 happ⟩
  rcases hinv_mid with ⟨hUBP, hcandfinal⟩ | hTmid
  · rcases hUBP with hB | hF
    · obtain ⟨hnotfinal_mid, hsigned_mid, haffordable_mid⟩ := hB
      have hnow_mid_eq : mid.now = s.now :=
        appliesAll_now_frame sig appRel s mid interleaved happ hexclTick
      have hnowpos_mid : 0 < mid.now := hnow_mid_eq ▸ hnowpos
      obtain ⟨payCalls1, mid1, happ1, hmode1, hoh1, hpool1, hhold1, _hself1, _hsigned1,
        _hpoolSigned1⟩ := conclude_step_finalizes sig appRel (Actor.nitro h) mid fp candidate
        hnotfinal_mid hnowpos_mid hcandfinal hsigned_mid
      have hreach_mid1 : Reachable sig appRel (genesis assets selfInputs pool0) mid1 := by
        obtain ⟨calls0, happ0⟩ := hreach_mid
        exact ⟨calls0 ++ payCalls1, appliesAll_append happ0 happ1⟩
      have hheldeq : heldValue mid1 (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
          (channelId fp) = heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
          (channelId fp) := by unfold heldValue; rw [hhold1, hpool1]
      have haffordable_mid1 : x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
          (heldValue mid1 (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
            (channelId fp))).getD destIdx 0 := by rw [hheldeq]; exact haffordable_mid
      obtain ⟨final0, hstepTransfer⟩ := transfer_step_exists sig appRel assets selfInputs pool0
        hReachPool (Actor.nitro h) mid1 assetIndex (channelId fp) candidate.outcome destIdx
        hAssetIdx hreach_mid1 hmode1 hoh1 dest hdest hnoguarantee x hxpos haffordable_mid1
      obtain ⟨pre, hpreNpk, hpreTok, hxlepre, hlive⟩ := transfer_step_pays_selected sig appRel
        (Actor.nitro h) mid1 final0 assetIndex (channelId fp) (mid1.channels (channelId fp)).stateHash
        candidate.outcome destIdx hstepTransfer hAssetIdx dest hdest hnoguarantee x hxpos
        haffordable_mid1
      refine ⟨payCalls1 ++
        [(Actor.nitro h, .transfer assetIndex (channelId fp) (mid1.channels (channelId fp)).stateHash
          candidate.outcome [destIdx])], final0,
        appliesAll_append happ1 ⟨final0, hstepTransfer, rfl⟩, pre, hpreNpk, hpreTok, hxlepre, hlive⟩
    · exact finalizedPaysInv_pays sig appRel assets selfInputs pool0 hReachPool (Actor.nitro h)
        (channelId fp) candidate.outcome assetIndex destIdx hAssetIdx x hxpos dest mid hreach_mid hF
  · obtain ⟨hTchanMid, hTnowMid, hTaffMid⟩ := hTmid
    have hmode_mid : (mid.channels (channelId fp)).mode mid.now = .challenge := by
      rw [hTchanMid, hTnowMid]; exact hregistered.1
    have hz : (mid.channels (channelId fp)).finalizesAt ≠ 0 := by
      intro hz0
      unfold ChannelStatus.mode at hmode_mid
      rw [hz0] at hmode_mid
      simp at hmode_mid
    have hfinAtGt : mid.now < (mid.channels (channelId fp)).finalizesAt := by
      rcases Nat.lt_or_ge mid.now (mid.channels (channelId fp)).finalizesAt with hlt | hge
      · exact hlt
      · exfalso
        unfold ChannelStatus.mode at hmode_mid
        rw [if_neg hz, if_pos hge] at hmode_mid
        exact absurd hmode_mid (by decide)
    let midTicked : AdjudicatorState := { mid with now := (mid.channels (channelId fp)).finalizesAt }
    have hstepTick : Step sig appRel (Actor.nitro h) mid
        (.tick (mid.channels (channelId fp)).finalizesAt) midTicked :=
      ⟨Nat.le_of_lt hfinAtGt, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hreach_ticked : Reachable sig appRel (genesis assets selfInputs pool0) midTicked :=
      reachable_step hreach_mid hstepTick
    have hmode_ticked : (midTicked.channels (channelId fp)).mode midTicked.now = .finalized := by
      show (mid.channels (channelId fp)).mode (mid.channels (channelId fp)).finalizesAt = .finalized
      unfold ChannelStatus.mode
      rw [if_neg hz, if_pos (Nat.le_refl _)]
    have hoh_ticked : (midTicked.channels (channelId fp)).outcomeHash =
        outcomeHashOf candidate.outcome := by
      show (mid.channels (channelId fp)).outcomeHash = outcomeHashOf candidate.outcome
      rw [hTchanMid]; exact hregistered.2.2
    have haff_ticked : x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
        (heldValue midTicked (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
          (channelId fp))).getD destIdx 0 := by
      show x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
        (heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp))).getD
        destIdx 0
      exact hTaffMid
    obtain ⟨final0, hstepTransfer⟩ := transfer_step_exists sig appRel assets selfInputs pool0
      hReachPool (Actor.nitro h) midTicked assetIndex (channelId fp) candidate.outcome destIdx
      hAssetIdx hreach_ticked hmode_ticked hoh_ticked dest hdest hnoguarantee x hxpos haff_ticked
    obtain ⟨pre, hpreNpk, hpreTok, hxlepre, hlive⟩ := transfer_step_pays_selected sig appRel
      (Actor.nitro h) midTicked final0 assetIndex (channelId fp)
      (midTicked.channels (channelId fp)).stateHash candidate.outcome destIdx hstepTransfer
      hAssetIdx dest hdest hnoguarantee x hxpos haff_ticked
    refine ⟨[(Actor.nitro h, .tick (mid.channels (channelId fp)).finalizesAt),
      (Actor.nitro h, .transfer assetIndex (channelId fp)
        (midTicked.channels (channelId fp)).stateHash candidate.outcome [destIdx])], final0,
      ⟨midTicked, hstepTick, ⟨final0, hstepTransfer, rfl⟩⟩, pre, hpreNpk, hpreTok, hxlepre, hlive⟩

/-- Which harm this rules out: once a channel is finalized, no caller can
    stop an entry from collecting what the channel can still afford for
    it, whatever transfers, reclaims or deposits other callers make first.
    Nitro-2019-219.pdf §5.2, "Unbeatable Redistribution": "if you can find
    one strategy to move a certain amount into an address, then no-one else
    can prevent this from occurring." §5.1 gives the strategy: "If A can
    afford x for B, then T(A, B, x)" succeeds, where "'A can afford x for
    B', if B would receive at least x coins, were the coins currently held
    by A to be paid out in priority order" — `afford` over `heldValue` at
    the CURRENT state `s`, so earlier transfers on the same channel are
    already counted. `unbeatable_pays` covers a channel that is not yet
    finalized; this statement covers a channel that is finalized at `s`,
    paid in part or not at all. The strategy is one `.transfer` naming
    `destIdx`. `interleaved` may contain any call by any actor except `h`'s
    own pool key `pk`, ticks included: finalization is permanent
    (`finalization_permanent`). `hhonestPool` is the same pool-layer honesty
    condition `unbeatable_pays` states. "Collecting" is a live note worth at
    least `x` keyed to `dest.destination`, the Armada meaning of "paid"
    (`State.lean`). -/
theorem finalized_affordable_pays
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0)
    (s : AdjudicatorState) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (o : Outcome) (assetIndex : Nat) (hci : assetIndex < o.length)
    (hmode : (s.channels cid).mode s.now = .finalized)
    (hoh : (s.channels cid).outcomeHash = outcomeHashOf o)
    (destIdx : Nat) (x : Nat) (dest : Allocation)
    (hdest : (o.get ⟨assetIndex, hci⟩).allocations[destIdx]? = some dest)
    (hassetunique : ∀ i (hi : i < o.length), i ≠ assetIndex →
      (o.get ⟨i, hi⟩).asset ≠ (o.get ⟨assetIndex, hci⟩).asset)
    (hnoguarantee : ∀ a ∈ (o.get ⟨assetIndex, hci⟩).allocations,
      a.allocationType ≠ .guarantee)
    (pk : Nat × Nat) (nk : Nat) (r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (hxpos : 0 < x)
    (haffordable : x ≤ (afford (o.get ⟨assetIndex, hci⟩).allocations
      (heldValue s (o.get ⟨assetIndex, hci⟩).asset cid)).getD destIdx 0)
    (hhonestPool : ∀ m, s.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ dest.destination) :
    ∀ (interleaved : List (Actor × Call)) (mid : AdjudicatorState),
      AppliesAll sig appRel s interleaved mid →
      (∀ actor call, (actor, call) ∈ interleaved → actor ≠ Actor.pool pk) →
      ∃ (payCalls : List (Actor × Call)) (final : AdjudicatorState),
        AppliesAll sig appRel mid payCalls final ∧
        ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧
          pre.token = (o.get ⟨assetIndex, hci⟩).asset ∧
          x ≤ pre.value ∧
          PoolIsLive final.pool (commitment pre.npk pre.token pre.value) := by
  intro interleaved mid happ hexcl
  have hinv_s : FinalizedPaysInv cid o assetIndex destIdx hci x dest s :=
    Or.inl ⟨o, hci, hmode, hoh, rfl, hnoguarantee, rfl,
      by rw [List.getD_eq_getElem?_getD, hdest]; rfl, haffordable⟩
  have hreach_mid : Reachable sig appRel (genesis assets selfInputs pool0) mid := by
    obtain ⟨calls0, happ0⟩ := hreach
    exact ⟨calls0 ++ interleaved, appliesAll_append happ0 happ⟩
  exact finalizedPaysInv_pays sig appRel assets selfInputs pool0 hReachPool (Actor.pool pk) cid o
    assetIndex destIdx hci x hxpos dest mid hreach_mid
    (finalizedPaysInv_appliesAll sig appRel cid o assetIndex destIdx hci x hxpos dest pk nk r
      hh_dest s hassetunique hhonestPool assets selfInputs pool0 hreach happ hexcl rfl hinv_s)

/-- `DepositStep`'s effect on `PoolState.notedValue`: the fresh notes minted
    from one deposit's own spent inputs always sum to the inputs' own
    total value (`transact_balance`'s own conservation, upgraded past
    `removeAll`), so the pool's own per-token noted total is unchanged —
    `notedValue_conserved`'s own `.deposit` FIRST-TIME case. -/
theorem DepositStep_notedValue_conserved {N M : Nat}
    (pool pool' : PoolState) (self : Term) (token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (spendTreeNumber treeNumber position : Nat)
    (hstep : DepositStep pool self token amount w pub idx spendTreeNumber treeNumber position pool') :
    ∀ t, pool'.notedValue t = pool.notedValue t := by
  intro t
  unfold DepositStep at hstep
  obtain ⟨r, hnpkOut, hcommOut, htoken, htreeNumber, hposition, hN, hM, hC, rest, spent', records,
    hroot, hremove, hmark, hsub, hmem, heq⟩ := hstep
  unfold PoolState.notedValue
  rw [heq]
  dsimp only
  by_cases ht : t = w.token
  · rw [ht, if_pos rfl]
    have hbal := transact_balance spendTreeNumber hN hM hC
      (newNotes := transactAllOutputs w) (unshieldTail := []) (by simp)
    simp only [List.map_nil, listSum] at hbal
    have hsum := removeAll_sum (fun p => p.2.value) hremove
    have hpos := withTreePositionsFrom_map CommitmentPreimage.value treeNumber
      (insertStartPos pool.leaves M) (transactAllOutputs w)
    rw [List.map_append, listSum_append, hpos]
    omega
  · rw [if_neg ht]

/-- `DepositMergeStep`'s effect on `PoolState.notedValue`: a top-up merge
    nullifies the old holding and the fresh deposit note, and mints their
    sum as one merged note — `transactOwned_balance`'s own conservation
    upgraded past `removeAll`, `notedValue_conserved`'s own `.deposit`
    TOP-UP case. -/
theorem DepositMergeStep_notedValue_conserved
    (pool pool' : PoolState) (self : Term) (token : Nat)
    (oldTreeNumber oldPos : Nat) (oldHolding : Term) (newTreeNumber newPos : Nat)
    (newNote merged : Term) (spendTreeNumber mergedTreeNumber mergedPos : Nat)
    (hstep : DepositMergeStep pool self token oldTreeNumber oldPos oldHolding newTreeNumber newPos
      newNote merged spendTreeNumber mergedTreeNumber mergedPos pool') :
    ∀ t, pool'.notedValue t = pool.notedValue t := by
  intro t
  unfold DepositMergeStep at hstep
  obtain ⟨hmergedTree, hmergedPos, w, pub, hC, rest, spent', r, randomOut, hNonZero, hself, htoken,
    hnpkOut0, hmergedEq, hleaf0, hleaf1, hcommitOld, hcommitNew, holdTree, hnewTree, hroot,
    hremove, hmark, hnpkRandomOut, heq⟩ := hstep
  unfold PoolState.notedValue
  rw [heq]
  dsimp only
  by_cases ht : t = token
  · rw [ht, if_pos rfl]
    have hbal := transactOwned_balance spendTreeNumber (by decide) (by decide) hC
    have hsum := removeAll_sum (fun p => p.2.value) hremove
    have hpos := withTreePositionsFrom_map CommitmentPreimage.value mergedTreeNumber mergedPos
      (ownedNewNotes w)
    rw [List.map_append, listSum_append, hpos]
    omega
  · rw [if_neg ht]

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
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_, _, _, _, hinner, _⟩ := hstep
    obtain ⟨N, M, w, pub, idx, spendTreeNumber, treeNumber, position, midPool, hdstep,
      _hpoolsigned, hmatch⟩ := hinner
    have hmidConserved := DepositStep_notedValue_conserved s.pool midPool s.self asset amount w pub
      idx spendTreeNumber treeNumber position hdstep token
    rcases hh : s.holdings asset channelId with _ | ⟨⟨oldTreeNumber, oldPos⟩, oldHoldingVal⟩
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, _⟩ := hmatch
      rw [hpoolEq]
      exact hmidConserved
    · rw [hh] at hmatch
      obtain ⟨merged, mergeSpendTreeNumber, mergedTreeNumber, mergedPos, hmerge, _⟩ := hmatch
      have hmergeConserved := DepositMergeStep_notedValue_conserved midPool s'.pool s.self asset
        oldTreeNumber oldPos oldHoldingVal treeNumber position (pub.commitmentsOut idx) merged
        mergeSpendTreeNumber mergedTreeNumber mergedPos hmerge token
      rw [hmergeConserved]
      exact hmidConserved
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, hinner, _⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨r, hmatch, hholdseq, hchanseq⟩ := hrest
    exact PoolOwnedSpendStep_notedValue_conserved _ _ _ _ _ _ _ hmatch token
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpool, _⟩ := hstep
    rw [hpool]
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpool, _⟩ := hstep
    rw [hpool]
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpool, _⟩ := hstep
    rw [hpool]
  | reclaim a b c d e f g =>
    obtain ⟨_, _, _, _, _, _, hpool, _⟩ := hstep
    rw [hpool]
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨hmode, hsh, hoh, newOutcome, hfold, hchanseq, _⟩ := hstep
    exact bulkTransferFold_notedValue_conserved s.self channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold token
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨hnotfinal, hfinal, hsigned, newOutcome, hfold, hchanseq, _⟩ := hstep
    exact bulkTransferFold_notedValue_conserved s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold token
  | tick newNow =>
    obtain ⟨_, _, hpool, _⟩ := hstep
    rw [hpool]
  | sign p d =>
    obtain ⟨_, _, hpool, _⟩ := hstep
    rw [hpool]
  | signNote pk msgHash =>
    obtain ⟨_, _, hpool, _⟩ := hstep
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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (token : Nat)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    s.pool.notedValue token = pool0.notedValue token :=
  reachable_preserves (P := fun s => s.pool.notedValue token = pool0.notedValue token) rfl
    (fun actor call s s' hP hstep =>
      (notedValue_conserved sig appRel actor s s' call token hstep).trans hP)
    hreach

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

/-- A `.sign` call by `p` on `d` always succeeds from any state `st`:
    `.sign`'s own `Step` case (`Operations.lean`) checks only `actor =
    .nitro p` and touches only `signedBy`. Shared by every can-happen
    proof below that builds a `.sign` call. -/
theorem sign_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (st : AdjudicatorState) (p : Nat) (d : Term) :
    Step sig appRel (Actor.nitro p) st (.sign p d)
      { st with signedBy := fun p' d' => (p' = p ∧ d' = d) ∨ st.signedBy p' d' } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A `.signNote` call by `pk` on `msgHash` always succeeds from any
    state `st`: `.signNote`'s own `Step` case (`Operations.lean`) checks
    only `actor = .pool pk` and touches only `poolSignedBy`. Shared by
    every can-happen proof below that builds a `.signNote` call. -/
theorem signNote_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (st : AdjudicatorState) (pk : Nat × Nat) (msgHash : Term) :
    Step sig appRel (Actor.pool pk) st (.signNote pk msgHash)
      { st with poolSignedBy := fun pk' m' => (pk' = pk ∧ m' = msgHash) ∨ st.poolSignedBy pk' m' } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- One `_root_.Step.shield` at zero fee, computed the same way
    `_root_.Step.shield`'s own conclusion is (`Pool.lean`) — a `def`,
    not a hand-written record, so `(shieldPool pool token amount
    npkV).leaves`/`.roots`/`.live` reduce exactly the way the shield
    step's own target state does. Shared by every can-happen proof
    below that starts from one shielded note. -/
def shieldPool (pool : PoolState) (token amount : Nat) (npkV : Term) : PoolState :=
  let note : CommitmentPreimage := ⟨npkV, token, shieldBase 0 amount⟩
  let tn := insertTreeNumber pool.closedTrees pool.leaves 1
  let pos := insertStartPos pool.leaves 1
  let res := insertResult pool.closedTrees pool.leaves pool.roots [hashCommitment note]
  { pool with
      live := fun t => if t = token then ((tn, pos), note) :: pool.live t else pool.live t,
      held := fun t => if t = token then pool.held t + note.value else pool.held t,
      closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
      preimageOf := recordStep pool.preimageOf (hashCommitment note) note }

/-- `shieldPool`'s own `_root_.Step`. -/
theorem shieldPool_step (pool : PoolState) (token amount : Nat) (npkV : Term)
    (hNotPaused : pool.shieldsPaused = false) (hValue : 0 < amount)
    (hRange : RangeChecked120 (shieldBase 0 amount)) :
    _root_.Step pool (shieldPool pool token amount npkV) :=
  _root_.Step.shield token amount 0 npkV hNotPaused hValue (by decide) hRange

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

/-- A-09 — a checkpoint can happen, and clears a challenge back to Open:
    there is a reachable challenged channel and a `.checkpoint` call
    that moves it to `.open` mode, with `turnNumRecord` raised to the
    checkpoint's own turn and `finalizesAt` cleared to `0`. The only
    lifecycle edge with no prior can-happen theorem.
    Quotes: `DOC/0070:66` "The checkpoint method allows anyone with a
    supported off-chain state to establish a new and higher
    turnNumRecord on chain, and leave the resulting channel in the
    'Open' mode. It can be used to clear a challenge." `DOC/0040:105,108`
    `Open --> Open: checkpoint`; `Challenge--> Open: checkpoint`.
    `DOC/0070:35` "This delay allows the challenge to be cleared by a
    timely and well-formed respond or checkpoint transaction."
    `FM:1266-1269` "If a valid response is received, the game returns
    to the Collaborative mode." Contract: `FM.sol:90-119`. Model:
    `Ops:227-237`. -/
theorem checkpoint_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      (s.channels (channelId fp)).mode s.now = .challenge ∧
      Step sig (consensusRelation sig) actor s (.checkpoint fp [] candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .open ∧
      (s'.channels (channelId fp)).turnNumRecord = candidate.turnNum ∧
      (s'.channels (channelId fp)).finalizesAt = 0 := by
  let assets : Nat → Prop := fun _ => False
  let selfInputs : List Term := []
  let pool0 : PoolState := _root_.genesis
  let fp : FixedPart := ⟨[0], 0, 0, 1⟩
  let candidate0 : VariablePart := ⟨[], 0, 0, false⟩
  let candidate : VariablePart := ⟨[], 0, 1, false⟩
  let g := genesis assets selfInputs pool0
  let mid1 : AdjudicatorState := { g with
    signedBy := fun p' d' => (p' = 0 ∧ d' = stateHash fp candidate0) ∨ g.signedBy p' d' }
  have hsignstep1 := sign_step sig (consensusRelation sig) g 0 (stateHash fp candidate0)
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep1
  let mid1b : AdjudicatorState := { mid1 with
    signedBy := fun p' d' => (p' = 0 ∧ d' = stateHash fp candidate) ∨ mid1.signedBy p' d' }
  have hsignstep1b := sign_step sig (consensusRelation sig) mid1 0 (stateHash fp candidate)
  have hreach1b : Reachable sig (consensusRelation sig) g mid1b :=
    reachable_step hreach1 hsignstep1b
  let s : AdjudicatorState := { mid1b with
    channels := update mid1b.channels (channelId fp)
      { turnNumRecord := candidate0.turnNum, finalizesAt := mid1b.now + fp.challengeDuration,
        stateHash := stateHash fp candidate0, outcomeHash := outcomeHashOf candidate0.outcome } }
  have hauth0 : AuthorizedBy sig mid1b 0 (stateHash fp candidate0) :=
    Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hcstep : Step sig (consensusRelation sig) (Actor.nitro 0) mid1b
      (.challenge fp [] candidate0 0) s := by
    refine ⟨?_, ⟨rfl, ?_⟩, ?_, hauth0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show candidate0.turnNum ≥ (mid1b.channels (channelId fp)).turnNumRecord
      simp [mid1b, mid1, g, genesis, emptyStatus]
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact hauth0
    · exact List.mem_singleton.mpr rfl
  have hreach2 : Reachable sig (consensusRelation sig) g s :=
    reachable_step hreach1b hcstep
  have hmodeChallenge : (s.channels (channelId fp)).mode s.now = .challenge := by
    show ((update mid1b.channels (channelId fp)
      { turnNumRecord := candidate0.turnNum, finalizesAt := mid1b.now + fp.challengeDuration,
        stateHash := stateHash fp candidate0, outcomeHash := outcomeHashOf candidate0.outcome })
      (channelId fp)).mode mid1b.now = .challenge
    unfold update
    simp [ChannelStatus.mode, fp]
  have hauth1 : AuthorizedBy sig s 0 (stateHash fp candidate) := Or.inl (Or.inl ⟨rfl, rfl⟩)
  have hturnGt : candidate.turnNum > (s.channels (channelId fp)).turnNumRecord := by
    show (1 : Nat) > ((update mid1b.channels (channelId fp)
      { turnNumRecord := candidate0.turnNum, finalizesAt := mid1b.now + fp.challengeDuration,
        stateHash := stateHash fp candidate0, outcomeHash := outcomeHashOf candidate0.outcome })
      (channelId fp)).turnNumRecord
    unfold update
    rw [if_pos rfl]
    decide
  have hmodeNeFin : (s.channels (channelId fp)).mode s.now ≠ .finalized := by
    rw [hmodeChallenge]; decide
  let s' : AdjudicatorState := { s with
    channels := update s.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := 0, stateHash := Term.val 0,
        outcomeHash := Term.val 0 } }
  have hckstep : Step sig (consensusRelation sig) (Actor.nitro 0) s
      (.checkpoint fp [] candidate) s' := by
    refine ⟨hmodeNeFin, hturnGt, ⟨rfl, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hauth1
  refine ⟨assets, selfInputs, pool0, s, s', fp, candidate, Actor.nitro 0,
    _root_.Reachable.genesis, hreach2, hmodeChallenge, hckstep, ?_, ?_, ?_⟩
  · show ((update s.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := 0, stateHash := Term.val 0,
        outcomeHash := Term.val 0 }) (channelId fp)).mode s.now = .open
    unfold update
    rw [if_pos rfl]
    simp [ChannelStatus.mode]
  · show ((update s.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := 0, stateHash := Term.val 0,
        outcomeHash := Term.val 0 }) (channelId fp)).turnNumRecord = candidate.turnNum
    unfold update
    rw [if_pos rfl]
  · show ((update s.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := 0, stateHash := Term.val 0,
        outcomeHash := Term.val 0 }) (channelId fp)).finalizesAt = 0
    unfold update
    rw [if_pos rfl]

/-- The real construction behind `deposit_can_happen`, below, carrying
    three extra facts its own build already has on hand — the pre-deposit
    state's `channels`/`holdings` equal `genesis`'s own, and its own
    `channelId` is `channelId fp1` for the specific `fp1` this
    construction picks. A-12 (`guarantee_reallocation_order_dependent`)
    needs those to build `.conclude` calls on top without re-deriving the
    deposit circuit; `deposit_can_happen` itself is NOT restated here —
    it stays the audit-approved text, proved below by dropping these three
    down to the plain existence claim.

    A deposit can happen: for all `HashAssumptions`, `SignatureAssumptions`,
    `PoolSignatureLiveness`, there is an execution from
    `genesis` — with a pool state `pool0` that already holds the
    deposit succeeds (Nitro-2019-219.pdf §3.1: "There are no
    restrictions on who can deposit coins for an address"; the
    armada-nitro rule, `State.lean`, specializes the deposited coins to
    a note). `PoolSignatureLiveness.
    eddsaCompleteness` turns the recorded signing fact into the
    `EdDSAVerify` witness `Constrained` (`DepositStep`,
    `Notes.lean`) needs. Unrelated to owned notes: `.deposit` uses the
    BASE `Transact` circuit (EdDSA), not `ArmadaLean.OwnedConstrained`,
    so no `OwnedProofCompleteness` argument is needed here. -/
theorem deposit_can_happen_witness
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (channelId : Term) (expectedHeld asset amount : Nat) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      s.channels = (genesis assets selfInputs pool0).channels ∧
      s.holdings = (genesis assets selfInputs pool0).holdings ∧
      channelId = ArmadaLean.Adjudicator.channelId ⟨[], 0, 0, 0⟩ ∧
      Step sig (consensusRelation sig) actor s
        (.deposit channelId expectedHeld asset amount) s' := by
  let selfInputs : List Term := []
  let selfTerm : Term := Term.keccak selfInputs
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let fp1 : FixedPart := ⟨[], 0, 0, 0⟩
  let channelId : Term := channelId fp1
  let note : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amount⟩
  let pool0 : PoolState := shieldPool _root_.genesis token amount note.npk
  have hNotPaused0 : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue0 : 0 < amount := by decide
  have hRange0 : RangeChecked120 (shieldBase 0 amount) := rangeCheck120_complete _ (by decide)
  have hshield : _root_.Step (_root_.genesis : PoolState) pool0 :=
    shieldPool_step _root_.genesis token amount note.npk hNotPaused0 hValue0 hRange0
  have hReachPool : _root_.Reachable pool0 :=
    _root_.Reachable.step _root_.Reachable.genesis hshield
  have hleavesAt : pool0.leavesAt' 0 = pool0.leaves := rfl
  have hi : 0 < (pool0.leavesAt' 0).length := by rw [hleavesAt]; show (0:Nat) < 1; decide
  have hmerkle := leaf_has_merkle_witness hReachPool 0 hi
  have hgetD : (pool0.leavesAt' 0).getD 0 (Term.val 0) = hashCommitment note := by
    rw [hleavesAt]; rfl
  let root : Term := treeRoot TreeDepth (pool0.leavesAt' 0)
  let pathElements : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth (pool0.leavesAt' 0) 0
  let npkOut : Fin 1 → Term := fun _ => npk selfTerm 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let pub : TransactPublic 1 1 :=
    { merkleRoot := root, boundParamsHash := 0,
      nullifiers := fun _ => nullifier (Term.val nullifyingKey) 0,
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let g := genesis assets selfInputs pool0
  let mid : AdjudicatorState := { g with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub) ∨ g.poolSignedBy pk' m' }
  have hsignstep := signNote_step sig (consensusRelation sig) g publicKey (msgHashOf pub)
  have hreach : Reachable sig (consensusRelation sig) g mid :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  have hsigned : mid.poolSignedBy publicKey (msgHashOf pub) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature, hveri⟩ :=
    poolSigLive.eddsaCompleteness mid.poolSignedBy publicKey (msgHashOf pub) hsigned
  let w : TransactWitness 1 1 :=
    { token := token, publicKey := publicKey, signature := signature,
      nullifyingKey := nullifyingKey, randomIn := fun _ => 0, valueIn := fun _ => note.value,
      pathElements := pathElements, leavesIndices := fun _ => 0,
      npkOut := npkOut, valueOut := valueOut }
  have hC : Constrained w pub :=
    { pathLen := fun _ => treePath_length TreeDepth (pool0.leavesAt' 0) 0
      merkle := fun _ => by
        show merkleRoot (commitment (npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn 0))
          w.token (w.valueIn 0)) (pathElements 0) = root
        rw [show commitment (npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn 0))
          w.token (w.valueIn 0) = hashCommitment note from rfl, ← hgetD]
        exact hmerkle.1
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => rangeCheck120_complete note.value (by decide)
      rangeOut := fun _ => rangeCheck120_complete amount (by decide)
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amount)))
        show fieldEq note.value amount
        show fieldEq (shieldBase 0 amount) amount
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove : removeAll (mid.pool.live w.token) (transactSpentPositions 0 w) = some [] := by
    show removeAll [((0, 0), note)] [((0, 0), note)] = some []
    decide
  have hNullify : markSpent (mid.pool.spent 0) (List.ofFn pub.nullifiers) =
      some (List.ofFn pub.nullifiers) := rfl
  have hidxrec : (pub.commitmentsOut (0 : Fin 1),
      (⟨w.npkOut 0, w.token, w.valueOut 0⟩ : CommitmentPreimage)) ∈ transactOutputRecords w pub :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let s' : AdjudicatorState := { mid with
    pool := { mid.pool with
      live := fun t => if t = w.token
        then withTreePositionsFrom 0 (insertStartPos mid.pool.leaves 1) (transactAllOutputs w) ++ []
        else mid.pool.live t,
      spent := fun n => if n = 0 then List.ofFn pub.nullifiers else mid.pool.spent n,
      leaves := mid.pool.leaves ++ (transactAllOutputs w).map hashCommitment,
      roots := treeRoot TreeDepth (mid.pool.leaves ++ (transactAllOutputs w).map hashCommitment) ::
        mid.pool.roots,
      preimageOf := applyRecords mid.pool.preimageOf (transactOutputRecords w pub),
      ownedRandomOf := applyOwnedRecords mid.pool.ownedRandomOf
        [(pub.commitmentsOut (0 : Fin 1), (⟨selfTerm, 0⟩ : OwnedDisclosure))] },
    holdings := update mid.holdings token (update (mid.holdings token) channelId
      (some ((0, 1), pub.commitmentsOut (0 : Fin 1))))}
  have hdstep : DepositStep mid.pool selfTerm token amount w pub (0 : Fin 1) 0 0 1 s'.pool :=
    ⟨0, rfl, rfl, rfl, rfl, rfl, (by decide), (by decide), hC, [], List.ofFn pub.nullifiers,
      transactOutputRecords w pub, hmerkle.2, hRemove, hNullify,
      List.Sublist.refl _, hidxrec, rfl⟩
  have hstep : Step sig (consensusRelation sig) (Actor.pool publicKey) mid
      (.deposit channelId 0 token amount) s' := by
    refine ⟨rfl, rfl, channelId_not_external fp1, (by decide),
      ⟨1, 1, w, pub, 0, 0, 0, 1, s'.pool, ?_, hsigned, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep
    · exact ⟨rfl, rfl⟩
  exact ⟨assets, selfInputs, pool0, mid, s', channelId, 0, token, amount, Actor.pool publicKey,
    hReachPool, hreach, rfl, rfl, rfl, hstep⟩

/-- A deposit can happen: for all `HashAssumptions`, `SignatureAssumptions`,
    `PoolSignatureLiveness`, there is an execution from
    `genesis` — with a pool state `pool0` that already holds the
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
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (channelId : Term) (expectedHeld asset amount : Nat) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.deposit channelId expectedHeld asset amount) s' := by
  obtain ⟨assets, selfInputs, pool0, s, s', channelId, expectedHeld, asset, amount, actor,
    hReachPool, hReach, _, _, _, hstep⟩ := deposit_can_happen_witness hashA sig poolSigLive
  exact ⟨assets, selfInputs, pool0, s, s', channelId, expectedHeld, asset, amount, actor,
    hReachPool, hReach, hstep⟩

/-- A-12 — guarantee reallocation can change a later transfer's payout:
    there is a reachable state `s` and a real `.reclaim` `Step` from `s`
    to `s1` on `cid`, after which `cid`'s own outcome hash is some
    `outcome'`, such that transferring to a destination `dIdx` pays a
    DIFFERENT amount computed from `outcome` at `heldValue s` than
    computed from `outcome'` at `heldValue s1` — `heldValue s1 =
    heldValue s` by `A-11` (`reclaim` is value-neutral on the pool), so
    this isolates the OUTCOME rewrite itself as the source of the
    difference, not a held-value change. This bounds A-02: order
    independence holds only for simple allocations, not once a
    guarantee is in play.
    Quotes: `N19:1148-1151` "it is possible to construct situations
    where the same outcome can lead to different values, depending on
    the order in which guarantees are claimed." `N19:1152-1154,1174-1177`
    lower bounds only ("participant I will receive their 5 coins, even
    though we cannot say anything about how the remaining 5 coins will
    be distributed"). [INFERENCE from `MAH.sol:359-387` and
    `:161-190`, not a source quote: the source states this for Nitro
    2019 `claim`; the same effect exists with `reclaim` — example:
    outcome `[A:0, B:0, d:5, G:5(left=A,right=B)]`, held 5, target
    outcome `[5,0]`. `transfer d` first pays `d` 5. `reclaim` first
    gives `[A:5, B:0, d:5]`, then `transfer d` pays 0.] -/
theorem guarantee_reallocation_order_dependent
    (hashA : HashAssumptions) (sig : SignatureAssumptions) (poolSigLive : PoolSignatureLiveness) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s1 : AdjudicatorState) (cid : Term) (asset : Nat)
      (outcome outcome' targetOutcome : Outcome)
      (assetIndex indexOfTargetInSource targetAssetIndex dIdx : Nat)
      (claimedTargetStateHash : Term) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      (outcome.getD assetIndex ⟨0, []⟩).asset = asset ∧
      Step sig (consensusRelation sig) actor s
        (.reclaim cid outcome assetIndex indexOfTargetInSource
          targetOutcome targetAssetIndex claimedTargetStateHash) s1 ∧
      (s1.channels cid).outcomeHash = outcomeHashOf outcome' ∧
      (transferEffects (outcome.getD assetIndex ⟨0, []⟩).allocations
          (heldValue s asset cid) [dIdx]).2.2 ≠
      (transferEffects (outcome'.getD assetIndex ⟨0, []⟩).allocations
          (heldValue s1 asset cid) [dIdx]).2.2 := by
  obtain ⟨assets, selfInputs, pool0, sPre, sPost, cid, expectedHeld, asset, amount, actor0,
    hReachPool, hReachPre, hChanPre, hHoldPre, hCidEq, hDepStep⟩ :=
    deposit_can_happen_witness hashA sig poolSigLive
  have hamtPos : 0 < amount := hDepStep.2.2.2.1
  have hde := deposit_effect sig (consensusRelation sig) assets selfInputs pool0 actor0 sPre sPost cid
    expectedHeld asset amount hReachPre hDepStep
  have hReachPost : Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) sPost :=
    reachable_step hReachPre hDepStep
  have hheldPre : heldValue sPre asset cid = 0 := by
    unfold heldValue
    rw [hHoldPre]; rfl
  have hheldPost : heldValue sPost asset cid = amount := by rw [hde.1, hheldPre]; omega
  have hchanPost : sPost.channels = sPre.channels := hde.2.2
  let sPostTick : AdjudicatorState := { sPost with now := sPost.now + 1 }
  have hstep_tick : Step sig (consensusRelation sig) (Actor.nitro 0) sPost (.tick (sPost.now + 1))
      sPostTick := by
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    omega
  have hreach_tick : Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) sPostTick :=
    reachable_step hReachPost hstep_tick
  have hchanTick : sPostTick.channels = sPost.channels := rfl
  have hheldTick : heldValue sPostTick asset cid = amount := hheldPost
  let fp1 : FixedPart := ⟨[], 0, 0, 0⟩
  let fp2 : FixedPart := ⟨[], 1, 0, 0⟩
  let targetChannelId : Term := channelId fp2
  have hidsNe : (channelId fp1 : Term) ≠ channelId fp2 := by
    intro heq
    have := (channelIdOf_inj heq).2.1
    simp [fp1, fp2] at this
  let guaranteeMetadata : Nat := 0
  let left : Term := (decodeGuarantee guaranteeMetadata).1
  let right : Term := (decodeGuarantee guaranteeMetadata).2
  let destD : Term := Term.val 102
  let allocA : Allocation := ⟨left, 0, .simple, 0⟩
  let allocB : Allocation := ⟨right, 0, .simple, 0⟩
  let allocD : Allocation := ⟨destD, amount, .simple, 0⟩
  let guaranteeAlloc : Allocation := ⟨targetChannelId, amount, .guarantee, guaranteeMetadata⟩
  let outcome : Outcome := [⟨asset, [allocA, allocB, allocD, guaranteeAlloc]⟩]
  let alloc0 : Allocation := ⟨left, amount, .simple, 0⟩
  let alloc1 : Allocation := ⟨right, 0, .simple, 0⟩
  let targetOutcome : Outcome := [⟨asset, [alloc0, alloc1]⟩]
  let candidate1 : VariablePart := ⟨outcome, 0, 0, true⟩
  let sC1 : AdjudicatorState := { sPostTick with
    channels := update sPostTick.channels (channelId fp1)
      { turnNumRecord := 0, finalizesAt := sPostTick.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate1.outcome } }
  have hmode1 : (sPostTick.channels (channelId fp1)).mode sPostTick.now ≠ .finalized := by
    rw [← hCidEq, hchanTick, hchanPost, hChanPre]
    simp [ChannelStatus.mode, genesis, emptyStatus]
  have hstep_c1 : Step sig (consensusRelation sig) (Actor.nitro 0) sPostTick
      (.conclude fp1 candidate1) sC1 := by
    refine ⟨hmode1, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    cases hp
  have hreach_c1 : Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) sC1 :=
    reachable_step hreach_tick hstep_c1
  let candidate2 : VariablePart := ⟨targetOutcome, 0, 0, true⟩
  let sC2 : AdjudicatorState := { sC1 with
    channels := update sC1.channels targetChannelId
      { turnNumRecord := 0, finalizesAt := sC1.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate2.outcome } }
  have hmode2 : (sC1.channels targetChannelId).mode sC1.now ≠ .finalized := by
    show ((update sPostTick.channels (channelId fp1)
        { turnNumRecord := 0, finalizesAt := sPostTick.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate1.outcome }) targetChannelId).mode sPostTick.now ≠
        .finalized
    unfold update
    rw [if_neg (Ne.symm hidsNe), hchanTick, hchanPost, hChanPre]
    simp [ChannelStatus.mode, genesis, emptyStatus]
  have hstep_c2 : Step sig (consensusRelation sig) (Actor.nitro 0) sC1
      (.conclude fp2 candidate2) sC2 := by
    refine ⟨hmode2, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    cases hp
  have hreach_c2 : Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) sC2 :=
    reachable_step hreach_c1 hstep_c2
  have hsrc_eq : sC2.channels (channelId fp1) =
      { turnNumRecord := 0, finalizesAt := sPostTick.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf outcome } := by
    show (update sC1.channels targetChannelId
        { turnNumRecord := 0, finalizesAt := sC1.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate2.outcome }) (channelId fp1) = _
    unfold update
    rw [if_neg hidsNe]
    show (update sPostTick.channels (channelId fp1)
        { turnNumRecord := 0, finalizesAt := sPostTick.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate1.outcome }) (channelId fp1) = _
    unfold update
    rw [if_pos rfl]
  have htgt_eq : sC2.channels targetChannelId =
      { turnNumRecord := 0, finalizesAt := sC1.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf targetOutcome } := by
    show (update sC1.channels targetChannelId
        { turnNumRecord := 0, finalizesAt := sC1.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate2.outcome }) targetChannelId = _
    unfold update
    rw [if_pos rfl]
  have hnz : sPostTick.now ≠ 0 := Nat.succ_ne_zero sPost.now
  have hle : sPostTick.now ≤ sPostTick.now := Nat.le_refl _
  have hsrc_fin : (sC2.channels (channelId fp1)).mode sC2.now = .finalized := by
    rw [hsrc_eq]
    unfold ChannelStatus.mode
    rw [if_neg hnz, if_pos hle]
  have htgt_fin : (sC2.channels targetChannelId).mode sC2.now = .finalized := by
    rw [htgt_eq]
    unfold ChannelStatus.mode
    rw [if_neg hnz, if_pos hle]
  let hsa : (0 : Nat) < outcome.length := by simp [outcome]
  let hidx : (3 : Nat) < (outcome.get ⟨0, hsa⟩).allocations.length := by simp [outcome]
  let hta : (0 : Nat) < targetOutcome.length := by simp [targetOutcome]
  let a0 : Nat := amount
  let a1 : Nat := 0
  let outcome' : Outcome := reallocateGuarantee outcome 0 3 left right a0 a1
  let s1 : AdjudicatorState := { sC2 with
    channels := update sC2.channels (channelId fp1)
      { sC2.channels (channelId fp1) with outcomeHash := outcomeHashOf outcome' } }
  have hstep_r : Step sig (consensusRelation sig) (Actor.nitro 0) sC2
      (.reclaim (channelId fp1) outcome 0 3 targetOutcome 0 (Term.val 0)) s1 := by
    refine ⟨hsrc_fin, ?_, hsa, hidx, rfl, ⟨htgt_fin, ?_, ?_, hta, rfl,
      ⟨allocA, List.mem_cons_self, rfl⟩,
      ⟨allocB, List.mem_cons_of_mem allocA List.mem_cons_self, rfl⟩,
      a0, a1, (by simp [targetOutcome, alloc0, alloc1]), rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩
    · rw [hsrc_eq]
    · show (sC2.channels targetChannelId).stateHash = Term.val 0
      rw [htgt_eq]
    · show (sC2.channels targetChannelId).outcomeHash = outcomeHashOf targetOutcome
      rw [htgt_eq]
  have hreach_s : Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) sC2 := hreach_c2
  have hheld_sC2 : heldValue sC2 asset (channelId fp1) = amount := by
    have heq : heldValue sC2 asset (channelId fp1) = heldValue sPost asset (channelId fp1) := rfl
    rw [heq, ← hCidEq]
    exact hheldPost
  have hheld_s1 : heldValue s1 asset (channelId fp1) = amount := hheld_sC2
  have hs1chan : (s1.channels (channelId fp1)).outcomeHash = outcomeHashOf outcome' := by
    show ((update sC2.channels (channelId fp1)
      { sC2.channels (channelId fp1) with outcomeHash := outcomeHashOf outcome' })
      (channelId fp1)).outcomeHash = outcomeHashOf outcome'
    unfold update
    rw [if_pos rfl]
  have hrange4 : List.range 4 = [0, 1, 2, 3] := by decide
  have hrange3 : List.range 3 = [0, 1, 2] := by decide
  have hbefore : (transferEffects (outcome.getD 0 ⟨0, []⟩).allocations amount [2]).2.2 = amount := by
    simp [outcome, allocA, allocB, allocD, guaranteeAlloc, transferEffects, afford, listSum,
      hrange4]
  have hafter : (transferEffects (outcome'.getD 0 ⟨0, []⟩).allocations amount [2]).2.2 = 0 := by
    simp [outcome', outcome, a0, a1, reallocateGuarantee, creditFirst, allocA, allocB, allocD,
      guaranteeAlloc, transferEffects, afford, listSum, hrange3]
  refine ⟨assets, selfInputs, pool0, sC2, s1, channelId fp1, asset, outcome, outcome', targetOutcome,
    0, 3, 0, 2, Term.val 0, Actor.nitro 0, hReachPool, hreach_s, rfl, hstep_r, hs1chan, ?_⟩
  rw [hheld_sC2, hheld_s1, hbefore, hafter]
  omega

/-- A top-up can happen: for all `HashAssumptions`/`SignatureAssumptions`,
    two deposits into the same channel, with the second deposit MERGING
    its fresh note with the first deposit's holding
    (`Notes.lean`'s `DepositMergeStep`) rather than replacing it —
    `heldValue` increases by exactly the second deposit's amount.
    `depositBinding` (`ArmadaNitroAdjudicator.sol:60-72`) binds the
    proof to `(channelId, expectedHeld)` so a deposit always adds to,
    never replaces, the prior holding; the merge is what makes this
    model keep that promise (see `deposit_sets_heldValue`'s own doc
    comment for the gap a plain, non-merging deposit would leave).
    The merge's two spent notes (the first deposit's holding, the
    second deposit's fresh note) share one Merkle root, by construction
    (a one-level tree with the two notes as its leaves, each reached by
    its own direction bit) — the pool's own two-nullifier `transactOwned`
    machinery needs no further assumption beyond that root existing. -/
theorem topup_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s mid s' : AdjudicatorState) (cid : Term) (a1 a2 asset amt1 amt2 : Nat) (actor1 actor2 : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor1 s (.deposit cid a1 asset amt1) mid ∧
      Step sig (consensusRelation sig) actor2 mid (.deposit cid a2 asset amt2) s' ∧
      heldValue s' asset cid = heldValue mid asset cid + amt2 := by
  let selfInputs : List Term := []
  let selfTerm : Term := Term.keccak selfInputs
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amt1 : Nat := 1
  let amt2 : Nat := 1
  let fp1 : FixedPart := ⟨[], 0, 0, 0⟩
  let cid : Term := channelId fp1
  let note1 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amt1⟩
  let pool_a : PoolState := shieldPool _root_.genesis token amt1 note1.npk
  have hNotPaused_a : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue_a : 0 < amt1 := by decide
  have hRange_a : RangeChecked120 (shieldBase 0 amt1) := rangeCheck120_complete _ (by decide)
  have hshield_a : _root_.Step (_root_.genesis : PoolState) pool_a :=
    shieldPool_step _root_.genesis token amt1 note1.npk hNotPaused_a hValue_a hRange_a
  have hReach_a : _root_.Reachable pool_a :=
    _root_.Reachable.step _root_.Reachable.genesis hshield_a
  let note2 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 1, token, shieldBase 0 amt2⟩
  let pool0 : PoolState := shieldPool pool_a token amt2 note2.npk
  have hNotPaused_b : pool_a.shieldsPaused = false := rfl
  have hValue_b : 0 < amt2 := by decide
  have hRange_b : RangeChecked120 (shieldBase 0 amt2) := rangeCheck120_complete _ (by decide)
  have hshield_b : _root_.Step pool_a pool0 :=
    shieldPool_step pool_a token amt2 note2.npk hNotPaused_b hValue_b hRange_b
  have hReachPool : _root_.Reachable pool0 := _root_.Reachable.step hReach_a hshield_b
  have hleaves0 : pool0.leaves = [hashCommitment note1, hashCommitment note2] := rfl
  let root0 : Term := treeRoot TreeDepth pool0.leaves
  let pathIn1 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut1 : Fin 1 → Term := fun _ => npk selfTerm 0
  let valueOut1 : Fin 1 → Nat := fun _ => amt1
  let pub_d1 : TransactPublic 1 1 :=
    { merkleRoot := root0, boundParamsHash := 0,
      nullifiers := fun _ => nullifier (Term.val nullifyingKey) 0,
      commitmentsOut := fun _ => commitment (npkOut1 0) token (valueOut1 0) }
  let firstNote : CommitmentPreimage := ⟨npk selfTerm 0, token, amt1⟩
  let pathIn2 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 1
  let npkOut2 : Fin 1 → Term := fun _ => npk selfTerm 1
  let valueOut2 : Fin 1 → Nat := fun _ => amt2
  let pub_d2 : TransactPublic 1 1 :=
    { merkleRoot := root0, boundParamsHash := 0,
      nullifiers := fun _ => nullifier (Term.val nullifyingKey) 1,
      commitmentsOut := fun _ => commitment (npkOut2 0) token (valueOut2 0) }
  let secondNote : CommitmentPreimage := ⟨npk selfTerm 1, token, amt2⟩
  let g := genesis assets selfInputs pool0
  let mid0 : AdjudicatorState := { g with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub_d1) ∨ g.poolSignedBy pk' m' }
  have hsignstep1 := signNote_step sig (consensusRelation sig) g publicKey (msgHashOf pub_d1)
  have hreach0 : Reachable sig (consensusRelation sig) g mid0 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep1
  have hsigned1 : mid0.poolSignedBy publicKey (msgHashOf pub_d1) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature1, hveri1⟩ :=
    poolSigLive.eddsaCompleteness mid0.poolSignedBy publicKey (msgHashOf pub_d1) hsigned1
  let mid1 : AdjudicatorState := { mid0 with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub_d2) ∨ mid0.poolSignedBy pk' m' }
  have hsignstep2 := signNote_step sig (consensusRelation sig) mid0 publicKey (msgHashOf pub_d2)
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step hreach0 hsignstep2
  have hsigned2 : mid1.poolSignedBy publicKey (msgHashOf pub_d2) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature2, hveri2⟩ :=
    poolSigLive.eddsaCompleteness mid1.poolSignedBy publicKey (msgHashOf pub_d2) hsigned2
  let w_d1 : TransactWitness 1 1 :=
    { token := token, publicKey := publicKey, signature := signature1,
      nullifyingKey := nullifyingKey, randomIn := fun _ => 0, valueIn := fun _ => note1.value,
      pathElements := pathIn1, leavesIndices := fun _ => 0,
      npkOut := npkOut1, valueOut := valueOut1 }
  let w_d2 : TransactWitness 1 1 :=
    { token := token, publicKey := publicKey, signature := signature2,
      nullifyingKey := nullifyingKey, randomIn := fun _ => 1, valueIn := fun _ => note2.value,
      pathElements := pathIn2, leavesIndices := fun _ => 1,
      npkOut := npkOut2, valueOut := valueOut2 }
  have hC_d1 : Constrained w_d1 pub_d1 :=
    { pathLen := fun _ => treePath_length TreeDepth pool0.leaves 0
      merkle := fun _ => by
        rw [show commitment (npk (masterPublicKey w_d1.publicKey w_d1.nullifyingKey) (w_d1.randomIn 0))
          w_d1.token (w_d1.valueIn 0) = hashCommitment note1 from rfl]
        exact treePath_correct TreeDepth pool0.leaves 0 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => rangeCheck120_complete note1.value (by decide)
      rangeOut := fun _ => rangeCheck120_complete amt1 (by decide)
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note1.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amt1)))
        show fieldEq note1.value amt1
        show fieldEq (shieldBase 0 amt1) amt1
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri1 }
  have hC_d2 : Constrained w_d2 pub_d2 :=
    { pathLen := fun _ => treePath_length TreeDepth pool0.leaves 1
      merkle := fun _ => by
        rw [show commitment (npk (masterPublicKey w_d2.publicKey w_d2.nullifyingKey) (w_d2.randomIn 0))
          w_d2.token (w_d2.valueIn 0) = hashCommitment note2 from rfl]
        exact treePath_correct TreeDepth pool0.leaves 1 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => rangeCheck120_complete note2.value (by decide)
      rangeOut := fun _ => rangeCheck120_complete amt2 (by decide)
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note2.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amt2)))
        show fieldEq note2.value amt2
        show fieldEq (shieldBase 0 amt2) amt2
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri2 }
  have hRemove_d1 : removeAll (mid1.pool.live w_d1.token) (transactSpentPositions 0 w_d1) =
      some [((0, 1), note2)] := by
    show removeAll [((0, 1), note2), ((0, 0), note1)] [((0, 0), note1)] = some [((0, 1), note2)]
    decide
  have hNullify_d1 : markSpent (mid1.pool.spent 0) (List.ofFn pub_d1.nullifiers) =
      some (List.ofFn pub_d1.nullifiers) := rfl
  have hidxrec_d1 : (pub_d1.commitmentsOut (0 : Fin 1),
      (⟨w_d1.npkOut 0, w_d1.token, w_d1.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d1 pub_d1 :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d1.token
        then withTreePositionsFrom 0 (insertStartPos mid1.pool.leaves 1) (transactAllOutputs w_d1) ++
          [((0, 1), note2)]
        else mid1.pool.live t,
      spent := fun n => if n = 0 then List.ofFn pub_d1.nullifiers else mid1.pool.spent n,
      leaves := mid1.pool.leaves ++ (transactAllOutputs w_d1).map hashCommitment,
      roots := treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d1).map hashCommitment) ::
        mid1.pool.roots,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d1 pub_d1),
      ownedRandomOf := applyOwnedRecords mid1.pool.ownedRandomOf
        [(pub_d1.commitmentsOut (0 : Fin 1), (⟨selfTerm, 0⟩ : OwnedDisclosure))] },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some ((0, 2), pub_d1.commitmentsOut (0 : Fin 1)))) }
  have hdstep1 : DepositStep mid1.pool selfTerm token amt1 w_d1 pub_d1 (0 : Fin 1) 0 0 2 mid2.pool :=
    ⟨0, rfl, rfl, rfl, rfl, rfl, (by decide), (by decide), hC_d1, [((0, 1), note2)],
      List.ofFn pub_d1.nullifiers, transactOutputRecords w_d1 pub_d1,
      (by show root0 ∈ mid1.pool.roots; show root0 ∈ pool0.roots; exact List.mem_cons_self),
      hRemove_d1, hNullify_d1, List.Sublist.refl _, hidxrec_d1, rfl⟩
  have hstep_d1 : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amt1) mid2 := by
    refine ⟨rfl, rfl, channelId_not_external fp1, (by decide),
      ⟨1, 1, w_d1, pub_d1, 0, 0, 0, 2, mid2.pool, ?_, Or.inr hsigned1, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep1
    · exact ⟨rfl, rfl⟩
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_d1
  have hheld2 : heldValue mid2 token cid = amt1 :=
    deposit_sets_heldValue sig (consensusRelation sig) (Actor.pool publicKey) mid1 mid2 cid 0
      token amt1 hstep_d1 rfl
  have hmid2holds : mid2.holdings token cid = some ((0, 2), pub_d1.commitmentsOut (0 : Fin 1)) := rfl
  have hRemove_d2 : removeAll (mid2.pool.live w_d2.token) (transactSpentPositions 0 w_d2) =
      some [((0, 2), firstNote)] := by
    show removeAll [((0, 2), firstNote), ((0, 1), note2)] [((0, 1), note2)] =
      some [((0, 2), firstNote)]
    decide
  have hNullify_d2 : markSpent (mid2.pool.spent 0) (List.ofFn pub_d2.nullifiers) =
      some (pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers) := by
    show markSpent (List.ofFn pub_d1.nullifiers) (List.ofFn pub_d2.nullifiers) = _
    have hnotmem : pub_d2.nullifiers (0 : Fin 1) ∉ List.ofFn pub_d1.nullifiers := by
      simp only [List.mem_ofFn]
      rintro ⟨i, hi⟩
      have h01 := Term.val.inj (Term.hash2_inj hi).2
      simp at h01
    show markSpent (List.ofFn pub_d1.nullifiers) [pub_d2.nullifiers 0] = _
    unfold markSpent
    rw [if_neg hnotmem]
    rfl
  have hidxrec_d2 : (pub_d2.commitmentsOut (0 : Fin 1),
      (⟨w_d2.npkOut 0, w_d2.token, w_d2.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d2 pub_d2 :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let midPool2 : PoolState := { mid2.pool with
    live := fun t => if t = w_d2.token
      then withTreePositionsFrom 0 (insertStartPos mid2.pool.leaves 1) (transactAllOutputs w_d2) ++
        [((0, 2), firstNote)]
      else mid2.pool.live t,
    spent := fun n => if n = 0 then pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers
      else mid2.pool.spent n,
    leaves := mid2.pool.leaves ++ (transactAllOutputs w_d2).map hashCommitment,
    roots := treeRoot TreeDepth (mid2.pool.leaves ++ (transactAllOutputs w_d2).map hashCommitment) ::
      mid2.pool.roots,
    preimageOf := applyRecords mid2.pool.preimageOf (transactOutputRecords w_d2 pub_d2),
    ownedRandomOf := applyOwnedRecords mid2.pool.ownedRandomOf
      [(pub_d2.commitmentsOut (0 : Fin 1), (⟨selfTerm, 1⟩ : OwnedDisclosure))] }
  have hdstep2 : DepositStep mid2.pool selfTerm token amt2 w_d2 pub_d2 (0 : Fin 1) 0 0 3 midPool2 :=
    ⟨1, rfl, rfl, rfl, rfl, rfl, (by decide), (by decide), hC_d2, [((0, 2), firstNote)],
      pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers, transactOutputRecords w_d2 pub_d2,
      (by
        show root0 ∈ mid2.pool.roots
        show root0 ∈ (treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d1).map
          hashCommitment) :: mid1.pool.roots)
        exact List.mem_cons_of_mem _ (show root0 ∈ pool0.roots from List.mem_cons_self)),
      hRemove_d2, hNullify_d2, List.Sublist.refl _, hidxrec_d2, rfl⟩
  let rootM : Term := treeRoot TreeDepth midPool2.leaves
  let pathM : Fin 2 → List (Term × Bool) :=
    fun i => if i = 0 then treePath TreeDepth midPool2.leaves 2 else treePath TreeDepth midPool2.leaves 3
  let randomInM : Fin 2 → Nat := fun i => if i = 0 then 0 else 1
  let valueInM : Fin 2 → Nat := fun i => if i = 0 then amt1 else amt2
  let leavesIndicesM : Fin 2 → Nat := fun i => if i = 0 then (2 : Nat) else 3
  let npkOutM : Fin 1 → Term := fun _ => npk selfTerm 2
  let valueOutM : Fin 1 → Nat := fun _ => amt1 + amt2
  let w_m : TransactOwnedWitness 2 1 :=
    { token := token, randomIn := randomInM, valueIn := valueInM, pathElements := pathM,
      leavesIndices := leavesIndicesM, npkOut := npkOutM, valueOut := valueOutM }
  let pub_m : TransactOwnedPublic 2 1 :=
    { merkleRoot := rootM, boundParamsHash := 0,
      nullifiers := fun i => nullifier selfTerm (leavesIndicesM i),
      commitmentsOut := fun _ => commitment (npkOutM 0) token (valueOutM 0),
      ownerField := selfTerm }
  have hmidPool2leaves : midPool2.leaves = pool0.leaves ++ [hashCommitment firstNote,
      hashCommitment secondNote] := rfl
  have hOC : OwnedConstrained w_m pub_m :=
    { pathLen := fun i => by
        match i with
        | 0 => exact treePath_length TreeDepth midPool2.leaves 2
        | 1 => exact treePath_length TreeDepth midPool2.leaves 3
      merkle := fun i => by
        match i with
        | 0 =>
          show merkleRoot (commitment (npk selfTerm 0) token amt1)
            (treePath TreeDepth midPool2.leaves 2) = rootM
          rw [show commitment (npk selfTerm 0) token amt1 = hashCommitment firstNote from rfl]
          exact treePath_correct TreeDepth midPool2.leaves 2 (by decide)
        | 1 =>
          show merkleRoot (commitment (npk selfTerm 1) token amt2)
            (treePath TreeDepth midPool2.leaves 3) = rootM
          rw [show commitment (npk selfTerm 1) token amt2 = hashCommitment secondNote from rfl]
          exact treePath_correct TreeDepth midPool2.leaves 3 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun i => by
        match i with
        | 0 => exact rangeCheck120_complete amt1 (by decide)
        | 1 => exact rangeCheck120_complete amt2 (by decide)
      rangeOut := fun _ => rangeCheck120_complete (amt1 + amt2) (by decide)
      balance := by
        show fieldEq (listSum (List.ofFn valueInM)) (listSum (List.ofFn valueOutM))
        unfold fieldEq
        decide }
  have hNonZero_m : ¬ isZeroPreimage (⟨w_m.npkOut 0, w_m.token, w_m.valueOut 0⟩ : CommitmentPreimage) := by
    unfold isZeroPreimage
    intro ⟨_, hv, _⟩
    exact absurd (show valueOutM 0 = 0 from hv) (by decide)
  have hremove_m : removeAll (midPool2.live token) (ownedSpentPositions 0 pub_m w_m) = some [] := by
    show removeAll [((0, 3), secondNote), ((0, 2), firstNote)]
      [((0, 2), firstNote), ((0, 3), secondNote)] = some []
    decide
  have hnullifier_ne : ∀ (a b : Term) (i j : Nat), i ≠ j → nullifier a i ≠ nullifier b j := by
    intro a b i j hij heq
    exact hij (Term.val.inj (Term.hash2_inj heq).2)
  have hnotmem_m0 : pub_m.nullifiers (0 : Fin 2) ∉ midPool2.spent 0 := by
    show nullifier selfTerm (leavesIndicesM 0) ∉
      (pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers)
    simp only [List.mem_cons, List.mem_ofFn, not_or]
    refine ⟨hnullifier_ne selfTerm (Term.val nullifyingKey) 2 1 (by decide), ?_⟩
    rintro ⟨i, hi⟩
    exact hnullifier_ne selfTerm (Term.val nullifyingKey) 2 0 (by decide) hi.symm
  have hnotmem_m1 : pub_m.nullifiers (1 : Fin 2) ∉ midPool2.spent 0 := by
    show nullifier selfTerm (leavesIndicesM 1) ∉
      (pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers)
    simp only [List.mem_cons, List.mem_ofFn, not_or]
    refine ⟨hnullifier_ne selfTerm (Term.val nullifyingKey) 3 1 (by decide), ?_⟩
    rintro ⟨i, hi⟩
    exact hnullifier_ne selfTerm (Term.val nullifyingKey) 3 0 (by decide) hi.symm
  have hne01 : pub_m.nullifiers (1 : Fin 2) ≠ pub_m.nullifiers (0 : Fin 2) :=
    hnullifier_ne selfTerm selfTerm 3 2 (by decide)
  have hmarkspent_m : markSpent (midPool2.spent 0) (List.ofFn pub_m.nullifiers) =
      some (pub_m.nullifiers (1 : Fin 2) :: pub_m.nullifiers (0 : Fin 2) :: midPool2.spent 0) := by
    show markSpent (midPool2.spent 0) [pub_m.nullifiers 0, pub_m.nullifiers 1] = _
    unfold markSpent
    rw [if_neg hnotmem_m0]
    unfold markSpent
    rw [if_neg (by
      simp only [List.mem_cons, not_or]
      exact ⟨hne01, hnotmem_m1⟩)]
    rfl
  let mergedCommitment : Term := commitment (npk selfTerm 2) token (amt1 + amt2)
  let s' : AdjudicatorState := { mid2 with
    pool := { midPool2 with
      live := fun t => if t = token
        then withTreePositionsFrom 0 (insertStartPos midPool2.leaves 1) (ownedNewNotes w_m) ++ []
        else midPool2.live t,
      spent := fun n => if n = 0
        then pub_m.nullifiers (1 : Fin 2) :: pub_m.nullifiers (0 : Fin 2) :: midPool2.spent 0
        else midPool2.spent n,
      leaves := midPool2.leaves ++ (ownedNewNotes w_m).map hashCommitment,
      roots := treeRoot TreeDepth (midPool2.leaves ++ (ownedNewNotes w_m).map hashCommitment) ::
        midPool2.roots,
      preimageOf := applyRecords midPool2.preimageOf (ownedOutputRecords w_m pub_m),
      ownedRandomOf := applyOwnedRecords midPool2.ownedRandomOf
        [(pub_m.commitmentsOut 0, (⟨selfTerm, 2⟩ : OwnedDisclosure))] },
    holdings := update mid2.holdings token (update (mid2.holdings token) cid
      (some ((0, 4), mergedCommitment))) }
  have hdstep_merge : DepositMergeStep midPool2 selfTerm token 0 2 (pub_d1.commitmentsOut (0 : Fin 1))
      0 3 (pub_d2.commitmentsOut (0 : Fin 1)) mergedCommitment 0 0 4 s'.pool :=
    ⟨rfl, rfl, w_m, pub_m, hOC, [], pub_m.nullifiers (1 : Fin 2) :: pub_m.nullifiers (0 : Fin 2) ::
      midPool2.spent 0, 2, 2, hNonZero_m, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      (by show rootM ∈ midPool2.roots; exact List.mem_cons_self),
      hremove_m, hmarkspent_m, rfl, rfl⟩
  have hstep_d2 : Step sig (consensusRelation sig) (Actor.pool publicKey) mid2
      (.deposit cid amt1 token amt2) s' := by
    refine ⟨rfl, hheld2, channelId_not_external fp1, (by decide),
      ⟨1, 1, w_d2, pub_d2, 0, 0, 0, 3, midPool2, ?_, hsigned2, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep2
    · rw [hmid2holds]
      exact ⟨mergedCommitment, 0, 0, 4, hdstep_merge, rfl⟩
  have hreach3 : Reachable sig (consensusRelation sig) g s' :=
    reachable_step hreach2 hstep_d2
  have hwf2 : HoldingWellFormed mid2 :=
    holdingWellFormed_reachable sig (consensusRelation sig) assets selfInputs pool0 mid2 hreach2
  have hinv2 : ∀ qasset qcid qpos qc, mid2.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, mid2.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc :=
    fun qasset qcid qpos qc h =>
      (hwf2 qasset qcid qpos qc h).1.imp (fun pre ⟨a, b, c, _, _, _⟩ => ⟨a, c, b⟩)
  have hfinal : heldValue s' token cid = heldValue mid2 token cid + amt2 :=
    deposit_merge_sets_heldValue sig (consensusRelation sig) (Actor.pool publicKey) mid2 s' cid
      amt1 token amt2 hstep_d2 hinv2 (0, 2) (pub_d1.commitmentsOut (0 : Fin 1)) hmid2holds
  exact ⟨assets, selfInputs, pool0, mid1, mid2, s', cid, 0, amt1, token, amt1, amt2,
    Actor.pool publicKey, Actor.pool publicKey, hReachPool, hreach1, hstep_d1, hstep_d2, hfinal⟩

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
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
      (challenger : Nat) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.challenge fp [] candidate challenger) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .challenge := by
  let assets : Nat → Prop := fun _ => False
  let selfInputs : List Term := []
  let pool0 : PoolState := _root_.genesis
  let fp : FixedPart := ⟨[0], 0, 0, 1⟩
  let candidate : VariablePart := ⟨[], 0, 0, false⟩
  let g := genesis assets selfInputs pool0
  let mid : AdjudicatorState := { g with
    signedBy := fun p' d' => (p' = 0 ∧ d' = stateHash fp candidate) ∨ g.signedBy p' d' }
  have hsignstep := sign_step sig (consensusRelation sig) g 0 (stateHash fp candidate)
  have hreach1 : Reachable sig (consensusRelation sig) g mid :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  have hauth : AuthorizedBy sig mid 0 (stateHash fp candidate) := Or.inl (Or.inl ⟨rfl, rfl⟩)
  let s' : AdjudicatorState := { mid with
    channels := update mid.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := mid.now + fp.challengeDuration,
        stateHash := stateHash fp candidate, outcomeHash := outcomeHashOf candidate.outcome } }
  have hcstep : Step sig (consensusRelation sig) (Actor.nitro 0) mid
      (.challenge fp [] candidate 0) s' := by
    refine ⟨?_, ⟨rfl, ?_⟩, ?_, hauth, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show candidate.turnNum ≥ (mid.channels (channelId fp)).turnNumRecord
      simp [mid, g, genesis, emptyStatus]
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact hauth
    · exact List.mem_singleton.mpr rfl
  have hreach2 : Reachable sig (consensusRelation sig) g s' :=
    reachable_step hreach1 hcstep
  refine ⟨assets, selfInputs, pool0, mid, s', fp, candidate, 0, Actor.nitro 0,
    _root_.Reachable.genesis, hreach1, hcstep, ?_⟩
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
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (cid : Term) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      (s.channels cid).finalizesAt > 0 ∧
      Step sig (consensusRelation sig) actor s (.tick (s.channels cid).finalizesAt) s' ∧
      (s'.channels cid).mode s'.now = .finalized := by
  obtain ⟨assets, selfInputs, pool0, mid, s, fp, candidate, challenger, actor0,
    hReachPool, hReach, hstep, hmode⟩ := challenge_can_happen hashA sig
  have hgt : (s.channels (channelId fp)).finalizesAt > s.now := by
    unfold ChannelStatus.mode at hmode
    by_cases h0 : (s.channels (channelId fp)).finalizesAt = 0
    · rw [if_pos h0] at hmode
      exact absurd hmode (by decide)
    · by_cases hle : (s.channels (channelId fp)).finalizesAt ≤ s.now
      · rw [if_neg h0, if_pos hle] at hmode
        exact absurd hmode (by decide)
      · omega
  have hfin : (s.channels (channelId fp)).finalizesAt > 0 := by omega
  have hReach' : Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s :=
    reachable_step hReach hstep
  let s' : AdjudicatorState := { s with now := (s.channels (channelId fp)).finalizesAt }
  have htickstep : Step sig (consensusRelation sig) (Actor.nitro 0) s
      (.tick (s.channels (channelId fp)).finalizesAt) s' := by
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    omega
  refine ⟨assets, selfInputs, pool0, s, s', channelId fp, Actor.nitro 0,
    hReachPool, hReach', hfin, htickstep, ?_⟩
  show (s.channels (channelId fp)).mode (s.channels (channelId fp)).finalizesAt = .finalized
  unfold ChannelStatus.mode
  rw [if_neg (by omega), if_pos (Nat.le_refl _)]

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
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s (.conclude fp candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .finalized := by
  let assets : Nat → Prop := fun _ => False
  let selfInputs : List Term := []
  let pool0 : PoolState := _root_.genesis
  let fp : FixedPart := ⟨[], 0, 0, 0⟩
  let candidate : VariablePart := ⟨[], 0, 0, true⟩
  let g := genesis assets selfInputs pool0
  let g1 : AdjudicatorState := { g with now := 1 }
  have htickstep : Step sig (consensusRelation sig) (Actor.nitro 0) g (.tick 1) g1 := by
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    decide
  have hreachg1 : Reachable sig (consensusRelation sig) g g1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) htickstep
  have hmodeNeFin : (g1.channels (channelId fp)).mode g1.now ≠ .finalized := by
    show (g.channels (channelId fp)).mode 1 ≠ .finalized
    simp [g, genesis, emptyStatus, ChannelStatus.mode]
  let s' : AdjudicatorState := { g1 with
    channels := update g1.channels (channelId fp)
      { turnNumRecord := 0, finalizesAt := g1.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate.outcome } }
  have hcstep : Step sig (consensusRelation sig) (Actor.nitro 0) g1
      (.conclude fp candidate) s' := by
    refine ⟨hmodeNeFin, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    cases hp
  refine ⟨assets, selfInputs, pool0, g1, s', fp, candidate, Actor.nitro 0,
    _root_.Reachable.genesis, hreachg1, hcstep, ?_⟩
  show ((update g1.channels (channelId fp)
    { turnNumRecord := 0, finalizesAt := g1.now, stateHash := Term.val 0,
      outcomeHash := outcomeHashOf candidate.outcome }) (channelId fp)).mode g1.now = .finalized
  unfold update
  rw [if_pos rfl]
  unfold ChannelStatus.mode
  show (if (g1.now : Nat) = 0 then ChannelMode.open
    else if g1.now ≤ g1.now then ChannelMode.finalized else ChannelMode.challenge) = .finalized
  simp [g1]

/-- A payout can happen: starting from `deposit_can_happen`'s construction
    to fund a channel, a `.conclude` (needing `now ≠ 0`, so a `.tick`
    comes first) finalizes it, and a `.transfer` call pays the entire
    deposited amount to a destination (`Operations.lean`'s `.transfer`
    case). `.transfer`'s owned-spend (`ArmadaLean.PoolOwnedSpendStep`,
    `Notes.lean`) takes `OwnedConstrained` directly as its own soundness
    hypothesis, the same convention `Step.transactOwned` now uses, so the
    witness built by hand already satisfies it — `ownedComplete` is kept
    on the signature for stability (the statement is unchanged) but is
    not needed by this construction. `channelId fp` is used directly for
    both `.deposit`'s target and `.conclude`'s own channel: now that
    channel ids are `Term`s (`pool-model`'s `af91ab2`), `channelId fp` is
    ALWAYS non-external (`channelId_not_external`, `Lemmas.lean` — a
    `Term.hash` term can never be a `Term.val` term, by construction), so
    the old pigeonhole argument over `channelIdOf`'s injectivity
    (`exists_internal_channelId`, needed when channel ids were `Nat`s
    with no stated range) is no longer needed. -/
theorem payout_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness)
    (ownedComplete : OwnedProofCompleteness) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
      (outcome : Outcome) (indices : List Nat) (h : assetIndex < outcome.length)
      (dest : Allocation) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.transfer assetIndex cid claimedStateHash outcome indices) s' ∧
      dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations ∧
      0 < dest.amount ∧
      PoolIsLive s'.pool
        (commitment dest.destination (outcome.get ⟨assetIndex, h⟩).asset dest.amount) := by
  let selfInputs : List Term := []
  let selfTerm : Term := Term.keccak selfInputs
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let fp : FixedPart := ⟨[], 0, 0, 0⟩
  let cid : Term := channelId fp
  let note1 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amount⟩
  let pool0 : PoolState := shieldPool _root_.genesis token amount note1.npk
  have hNotPaused0 : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue0 : 0 < amount := by decide
  have hRange0 : RangeChecked120 (shieldBase 0 amount) := rangeCheck120_complete _ (by decide)
  have hshield : _root_.Step (_root_.genesis : PoolState) pool0 :=
    shieldPool_step _root_.genesis token amount note1.npk hNotPaused0 hValue0 hRange0
  have hReachPool : _root_.Reachable pool0 :=
    _root_.Reachable.step _root_.Reachable.genesis hshield
  let root1 : Term := treeRoot TreeDepth pool0.leaves
  let pathElements1 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut : Fin 1 → Term := fun _ => npk selfTerm 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let pub_d : TransactPublic 1 1 :=
    { merkleRoot := root1, boundParamsHash := 0,
      nullifiers := fun _ => nullifier (Term.val nullifyingKey) 0,
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let depositedNote : CommitmentPreimage := ⟨npk selfTerm 0, token, amount⟩
  let g := genesis assets selfInputs pool0
  let mid1 : AdjudicatorState := { g with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub_d) ∨ g.poolSignedBy pk' m' }
  have hsignstep := signNote_step sig (consensusRelation sig) g publicKey (msgHashOf pub_d)
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  have hsigned : mid1.poolSignedBy publicKey (msgHashOf pub_d) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature, hveri⟩ :=
    poolSigLive.eddsaCompleteness mid1.poolSignedBy publicKey (msgHashOf pub_d) hsigned
  let w_d : TransactWitness 1 1 :=
    { token := token, publicKey := publicKey, signature := signature,
      nullifyingKey := nullifyingKey, randomIn := fun _ => 0, valueIn := fun _ => note1.value,
      pathElements := pathElements1, leavesIndices := fun _ => 0,
      npkOut := npkOut, valueOut := valueOut }
  have hC_d : Constrained w_d pub_d :=
    { pathLen := fun _ => treePath_length TreeDepth pool0.leaves 0
      merkle := fun _ => by
        rw [show commitment (npk (masterPublicKey w_d.publicKey w_d.nullifyingKey) (w_d.randomIn 0))
          w_d.token (w_d.valueIn 0) = hashCommitment note1 from rfl]
        exact treePath_correct TreeDepth pool0.leaves 0 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => rangeCheck120_complete note1.value (by decide)
      rangeOut := fun _ => rangeCheck120_complete amount (by decide)
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note1.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amount)))
        show fieldEq note1.value amount
        show fieldEq (shieldBase 0 amount) amount
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove_d : removeAll (mid1.pool.live w_d.token) (transactSpentPositions 0 w_d) = some [] := by
    show removeAll [((0, 0), note1)] [((0, 0), note1)] = some []
    decide
  have hNullify_d : markSpent (mid1.pool.spent 0) (List.ofFn pub_d.nullifiers) =
      some (List.ofFn pub_d.nullifiers) := rfl
  have hidxrec_d : (pub_d.commitmentsOut (0 : Fin 1),
      (⟨w_d.npkOut 0, w_d.token, w_d.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d pub_d :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d.token
        then withTreePositionsFrom 0 (insertStartPos mid1.pool.leaves 1) (transactAllOutputs w_d) ++ []
        else mid1.pool.live t,
      spent := fun n => if n = 0 then List.ofFn pub_d.nullifiers else mid1.pool.spent n,
      leaves := mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment,
      roots := treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment) ::
        mid1.pool.roots,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d pub_d),
      ownedRandomOf := applyOwnedRecords mid1.pool.ownedRandomOf
        [(pub_d.commitmentsOut (0 : Fin 1), (⟨selfTerm, 0⟩ : OwnedDisclosure))] },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some ((0, 1), pub_d.commitmentsOut (0 : Fin 1)))) }
  have hdstep : DepositStep mid1.pool selfTerm token amount w_d pub_d (0 : Fin 1) 0 0 1 mid2.pool :=
    ⟨0, rfl, rfl, rfl, rfl, rfl, (by decide), (by decide), hC_d, [], List.ofFn pub_d.nullifiers,
      transactOutputRecords w_d pub_d,
      (by show root1 ∈ mid1.pool.roots; show root1 ∈ pool0.roots; exact List.mem_cons_self),
      hRemove_d, hNullify_d, List.Sublist.refl _, hidxrec_d, rfl⟩
  have hstep_d : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amount) mid2 := by
    refine ⟨rfl, rfl, channelId_not_external fp, (by decide),
      ⟨1, 1, w_d, pub_d, 0, 0, 0, 1, mid2.pool, ?_, hsigned, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep
    · exact ⟨rfl, rfl⟩
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_d
  let mid3 : AdjudicatorState := { mid2 with now := 1 }
  have hstep_tick : Step sig (consensusRelation sig) (Actor.nitro 0) mid2 (.tick 1) mid3 :=
    ⟨Nat.zero_le 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach3 : Reachable sig (consensusRelation sig) g mid3 :=
    reachable_step hreach2 hstep_tick
  let recipientPK : Nat × Nat := (2, 2)
  let recipientNK : Nat := 2
  let dest : Allocation :=
    ⟨npk (masterPublicKey recipientPK recipientNK) 0, amount, .simple, 0⟩
  let outcome : Outcome := [⟨token, [dest]⟩]
  let candidate : VariablePart := ⟨outcome, 0, 0, true⟩
  let mid4 : AdjudicatorState := { mid3 with
    channels := update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate.outcome } }
  have hstep_conclude : Step sig (consensusRelation sig) (Actor.nitro 0) mid3
      (.conclude fp candidate) mid4 := by
    refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [mid3, mid2, mid1, g, genesis, ChannelStatus.mode, emptyStatus]
    · intro p hp
      cases hp
  have hreach4 : Reachable sig (consensusRelation sig) g mid4 :=
    reachable_step hreach3 hstep_conclude
  have hassetIdx : (0 : Nat) < outcome.length := by decide
  have hfinalized : (mid4.channels cid).mode mid4.now = .finalized := by
    show ((update mid3.channels cid
        { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate.outcome }) cid).mode mid3.now = .finalized
    unfold update
    simp [ChannelStatus.mode, mid3]
  have hheld2 : heldValue mid2 token cid = amount :=
    deposit_sets_heldValue sig (consensusRelation sig) (Actor.pool publicKey) mid1 mid2 cid 0
      token amount hstep_d rfl
  have hheld4 : heldValue mid4 token cid = amount := hheld2
  let rootT : Term := treeRoot TreeDepth mid4.pool.leaves
  let pathElements2 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth mid4.pool.leaves 1
  let randomIn2 : Fin 1 → Nat := fun _ => 0
  let valueIn2 : Fin 1 → Nat := fun _ => amount
  let leavesIndices2 : Fin 1 → Nat := fun _ => 1
  let npkOut2 : Fin 1 → Term := fun _ => dest.destination
  let valueOut2 : Fin 1 → Nat := fun _ => amount
  let pub_t : TransactOwnedPublic 1 1 :=
    { merkleRoot := rootT, boundParamsHash := 0,
      nullifiers := fun _ => nullifier selfTerm (leavesIndices2 0),
      commitmentsOut := fun _ => commitment (npkOut2 0) token (valueOut2 0),
      ownerField := selfTerm }
  let w_t : TransactOwnedWitness 1 1 :=
    { token := token, randomIn := randomIn2, valueIn := valueIn2, pathElements := pathElements2,
      leavesIndices := leavesIndices2, npkOut := npkOut2, valueOut := valueOut2 }
  have hOC : OwnedConstrained w_t pub_t :=
    { pathLen := fun _ => treePath_length TreeDepth mid4.pool.leaves 1
      merkle := fun _ => by
        rw [show commitment (npk pub_t.ownerField (w_t.randomIn 0)) w_t.token
          (w_t.valueIn 0) = hashCommitment depositedNote from rfl]
        exact treePath_correct TreeDepth mid4.pool.leaves 1 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => rangeCheck120_complete amount (by decide)
      rangeOut := fun _ => rangeCheck120_complete amount (by decide)
      balance := rfl }
  have hNonZero_t : ∀ j, ¬ isZeroPreimage
      (⟨w_t.npkOut j, w_t.token, w_t.valueOut j⟩ : CommitmentPreimage) := by
    intro j hz
    have : amount = 0 := hz.2.1
    simp [amount] at this
  have hRemove_t : removeAll (mid4.pool.live token) (ownedSpentPositions 0 pub_t w_t) = some [] := by
    show removeAll [((0, 1), depositedNote)] [((0, 1), depositedNote)] = some []
    decide
  have hNullify_t : markSpent (mid4.pool.spent 0) (List.ofFn pub_t.nullifiers) =
      some (nullifier selfTerm (leavesIndices2 0) :: mid4.pool.spent 0) := by
    show markSpent [nullifier (Term.val nullifyingKey) 0] [nullifier selfTerm (leavesIndices2 0)] =
      some (nullifier selfTerm (leavesIndices2 0) :: [nullifier (Term.val nullifyingKey) 0])
    have hnullseparate : nullifier selfTerm (leavesIndices2 0) ≠ nullifier (Term.val nullifyingKey) 0 := by
      intro heqn
      have h01 := Term.val.inj (Term.hash2_inj heqn).2
      exact absurd h01 (by decide)
    unfold markSpent
    rw [if_neg (by simpa using hnullseparate)]
    rfl
  let s' : AdjudicatorState := { mid4 with
    pool := { mid4.pool with
      live := fun t => if t = token
        then withTreePositionsFrom 0 (insertStartPos mid4.pool.leaves 1)
          [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] ++ []
        else mid4.pool.live t,
      spent := fun n => if n = 0 then nullifier selfTerm (leavesIndices2 0) :: mid4.pool.spent 0
        else mid4.pool.spent n,
      leaves := mid4.pool.leaves ++ [commitment dest.destination token amount],
      roots := treeRoot TreeDepth (mid4.pool.leaves ++ [commitment dest.destination token amount]) ::
        mid4.pool.roots,
      preimageOf := applyRecords mid4.pool.preimageOf (ownedOutputRecords w_t pub_t),
      ownedRandomOf := mid4.pool.ownedRandomOf },
    holdings := update mid4.holdings token (update (mid4.holdings token) cid none),
    channels := update mid4.channels cid
      { mid4.channels cid with
        outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
          if i ≠ 0 then exit else { exit with allocations := [{ dest with amount := 0 }] }) } }
  have hcEq : mid4.holdings token cid = some ((0, 1), pub_d.commitmentsOut (0 : Fin 1)) := by
    show (update mid1.holdings token (update (mid1.holdings token) cid
      (some ((0, 1), pub_d.commitmentsOut (0 : Fin 1))))) token cid =
      some ((0, 1), pub_d.commitmentsOut (0 : Fin 1))
    unfold update
    rw [if_pos rfl, if_pos rfl]
  have hospend : PoolOwnedSpendStep mid4.pool selfTerm token (mid4.holdings token cid)
      [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] [] s'.pool := by
    rw [hcEq]
    refine ⟨w_t, pub_t, (by decide), hOC, [], nullifier selfTerm (leavesIndices2 0) :: mid4.pool.spent 0,
      (fun j => j.elim0), hNonZero_t, rfl, rfl, rfl, rfl, rfl, ?_, hRemove_t, hNullify_t,
      (fun j => j.elim0), rfl⟩
    · show rootT ∈ mid4.pool.rootsAt' 0
      show rootT ∈ mid2.pool.rootsAt' 0
      show rootT ∈ mid2.pool.roots
      show rootT ∈ (treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d).map
        hashCommitment) :: mid1.pool.roots)
      exact List.mem_cons_self
  have hstateHash : (mid4.channels cid).stateHash = Term.val 0 := by
    show ((update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate.outcome }) cid).stateHash = Term.val 0
    unfold update
    rw [if_pos rfl]
  have houtcomeHash : (mid4.channels cid).outcomeHash = outcomeHashOf outcome := by
    show ((update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate.outcome }) cid).outcomeHash = outcomeHashOf outcome
    unfold update
    rw [if_pos rfl]
  have htransferEffects : transferEffects [dest] amount [] =
      ([{dest with amount := 0}], [dest], amount) := by
    unfold transferEffects afford
    simp [listSum, dest]
  have hstep_t : Step sig (consensusRelation sig) (Actor.nitro 0) mid4
      (.transfer 0 cid (Term.val 0) outcome []) s' := by
    refine ⟨hassetIdx, hfinalized, hstateHash, houtcomeHash, trivial, ?_, rfl, rfl, rfl, rfl, rfl⟩
    have hget : outcome.get ⟨0, hassetIdx⟩ = ⟨token, [dest]⟩ := rfl
    rw [hget, hheld4, htransferEffects]
    simp only [Nat.sub_self]
    refine ⟨?_, 0, ?_, rfl, rfl⟩
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      decide
    · exact hospend
  refine ⟨assets, selfInputs, pool0, mid4, s', 0, cid, Term.val 0, outcome, [], hassetIdx, dest,
    Actor.nitro 0, hReachPool, hreach4, hstep_t, ?_, ?_, ?_⟩
  · show dest ∈ [dest]
    exact List.mem_singleton_self _
  · decide
  · refine ⟨token, 0, 2, ⟨dest.destination, token, amount⟩, ?_, rfl⟩
    show ((0, 2), (⟨dest.destination, token, amount⟩ : CommitmentPreimage)) ∈
      withTreePositionsFrom 0 (insertStartPos mid4.pool.leaves 1) [(⟨dest.destination, token, amount⟩ :
        CommitmentPreimage)] ++ ([] : List ((Nat × Nat) × CommitmentPreimage))
    apply List.mem_append.mpr
    left
    have hlen : insertStartPos mid4.pool.leaves 1 = 2 := rfl
    rw [hlen]
    simp [withTreePositionsFrom, withPositionsFrom]

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
    `channelIdOf_inj` (`Assumptions.lean`, PROVED from `Term`'s own
    constructors, `pool-model`'s `af91ab2` — no longer a
    `HashAssumptions` field) then gives the two ids are distinct, so
    concluding one does not touch the other. `reallocateGuarantee`
    erases the reclaimed allocation outright (the source outcome holds
    only the guarantee, so erasing it empties the allocation list),
    giving a different `outcomeHash` (`outcomeHashOf_inj`, likewise now
    proved, not assumed) and so a different `ChannelStatus`. -/
theorem reclaim_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (sourceChannelId : Term) (sourceOutcome : Outcome)
      (sourceAssetIndex indexOfTargetInSource : Nat) (targetOutcome : Outcome)
      (targetAssetIndex : Nat) (claimedTargetStateHash : Term) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s (.reclaim sourceChannelId sourceOutcome
        sourceAssetIndex indexOfTargetInSource targetOutcome targetAssetIndex
        claimedTargetStateHash) s' ∧
      s'.channels sourceChannelId ≠ s.channels sourceChannelId := by
  let assets : Nat → Prop := fun _ => False
  let selfInputs : List Term := []
  let pool0 : PoolState := _root_.genesis
  let fp1 : FixedPart := ⟨[], 0, 0, 0⟩
  let fp2 : FixedPart := ⟨[], 1, 0, 0⟩
  let sourceChannelId : Term := channelId fp1
  let targetChannelId : Term := channelId fp2
  have hidsNe : sourceChannelId ≠ targetChannelId := by
    intro heq
    have := (channelIdOf_inj heq).2.1
    simp [fp1, fp2] at this
  let asset : Nat := 0
  let guaranteeMetadata : Nat := 0
  let left : Term := (decodeGuarantee guaranteeMetadata).1
  let right : Term := (decodeGuarantee guaranteeMetadata).2
  let guaranteeAlloc : Allocation := ⟨targetChannelId, 2, .guarantee, guaranteeMetadata⟩
  let allocLeft : Allocation := ⟨left, 0, .simple, 0⟩
  let allocRight : Allocation := ⟨right, 0, .simple, 0⟩
  let sourceOutcome : Outcome := [⟨asset, [guaranteeAlloc, allocLeft, allocRight]⟩]
  let alloc0 : Allocation := ⟨left, 1, .simple, 0⟩
  let alloc1 : Allocation := ⟨right, 1, .simple, 0⟩
  let targetOutcome : Outcome := [⟨asset, [alloc0, alloc1]⟩]
  let g := genesis assets selfInputs pool0
  let mid1 : AdjudicatorState := { g with now := 1 }
  have htick : Step sig (consensusRelation sig) (Actor.nitro 0) g (.tick 1) mid1 :=
    ⟨Nat.zero_le 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) htick
  let candidate1 : VariablePart := ⟨sourceOutcome, 0, 0, true⟩
  let mid2 : AdjudicatorState := { mid1 with
    channels := update mid1.channels sourceChannelId
      { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate1.outcome } }
  have hstep_c1 : Step sig (consensusRelation sig) (Actor.nitro 0) mid1
      (.conclude fp1 candidate1) mid2 := by
    refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [mid1, g, genesis, ChannelStatus.mode, emptyStatus]
    · intro p hp
      cases hp
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_c1
  let candidate2 : VariablePart := ⟨targetOutcome, 0, 0, true⟩
  let mid3 : AdjudicatorState := { mid2 with
    channels := update mid2.channels targetChannelId
      { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate2.outcome } }
  have hmode2 : (mid2.channels targetChannelId).mode mid2.now ≠ .finalized := by
    show (update mid1.channels sourceChannelId
      { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate1.outcome } targetChannelId).mode mid1.now ≠ .finalized
    unfold update
    rw [if_neg (fun h => hidsNe h.symm)]
    simp [mid1, g, genesis, ChannelStatus.mode, emptyStatus]
  have hstep_c2 : Step sig (consensusRelation sig) (Actor.nitro 0) mid2
      (.conclude fp2 candidate2) mid3 := by
    refine ⟨hmode2, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    cases hp
  have hreach3 : Reachable sig (consensusRelation sig) g mid3 :=
    reachable_step hreach2 hstep_c2
  have hsrc_eq : mid3.channels sourceChannelId =
      { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf sourceOutcome } := by
    show (update mid2.channels targetChannelId
        { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate2.outcome } sourceChannelId) = _
    unfold update
    rw [if_neg hidsNe]
    show (update mid1.channels sourceChannelId
        { turnNumRecord := 0, finalizesAt := mid1.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf candidate1.outcome } sourceChannelId) = _
    unfold update
    rw [if_pos rfl]
  have htgt_eq : mid3.channels targetChannelId =
      { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf targetOutcome } := by
    show (update mid2.channels targetChannelId
        { turnNumRecord := 0, finalizesAt := mid2.now, stateHash := Term.val 0,
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
      (.reclaim sourceChannelId sourceOutcome 0 0 targetOutcome 0 (Term.val 0)) s' := by
    refine ⟨hsrc_fin, ?_, hsa, hidx, rfl, ⟨htgt_fin, ?_, ?_, hta, rfl,
      ⟨allocLeft, List.mem_cons_self, rfl⟩,
      ⟨allocRight, List.mem_cons_of_mem allocLeft List.mem_cons_self, rfl⟩,
      a0, a1, (by decide), rfl, rfl, (by decide), rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hsrc_eq]
    · show (mid3.channels targetChannelId).stateHash = Term.val 0
      rw [htgt_eq]
    · show (mid3.channels targetChannelId).outcomeHash = outcomeHashOf targetOutcome
      rw [htgt_eq]
  have hneq : s'.channels sourceChannelId ≠ mid3.channels sourceChannelId := by
    show (update mid3.channels sourceChannelId
      { mid3.channels sourceChannelId with
        outcomeHash := outcomeHashOf (reallocateGuarantee sourceOutcome 0 0 left right a0 a1) })
      sourceChannelId ≠ mid3.channels sourceChannelId
    unfold update
    rw [if_pos rfl, hsrc_eq]
    intro heq
    have houtcome := outcomeHashOf_inj (congrArg ChannelStatus.outcomeHash heq)
    have : reallocateGuarantee sourceOutcome 0 0 left right a0 a1 = sourceOutcome := houtcome
    simp [reallocateGuarantee, sourceOutcome, guaranteeAlloc, creditFirst, allocLeft, allocRight] at this
    split at this <;> simp_all
  exact ⟨assets, selfInputs, pool0, mid3, s', sourceChannelId, sourceOutcome, 0, 0, targetOutcome,
    0, Term.val 0, Actor.nitro 0, _root_.Reachable.genesis, hreach3, hstep_r, hneq⟩
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
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
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

/-- B4 — `bulkTransferAllAssets` has EXACTLY `transferAllAssets`'s own
    documented effect (`DOC/0080:77`, `0080-defunding-a-channel.md`:
    "There is a convenience method concludeAndTransferAllAssets which
    combines concluding with transferring for every asset -- batching
    them to save gas."): transfer EVERY asset of the claimed outcome, in
    order, each paying every index in full — the SAME per-asset
    owned-spend `.transfer` itself uses, applied once per asset
    (`bulkTransferFold`, `Operations.lean`'s own `.bulkTransferAllAssets`
    case, restated here as a direct consequence). This REPLACES
    `bulk_paths_never_succeed`, which stated the Armada departure the
    model no longer follows (DOC presents the bulk path as valid; see
    `Operations.lean`'s module comment on this case). -/
theorem bulk_transfer_all_assets_effect
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (cid : Term) (outcome : Outcome)
    (claimedStateHash : Term)
    (hstep : Step sig appRel actor s (.bulkTransferAllAssets cid outcome claimedStateHash) s') :
    (s.channels cid).mode s.now = .finalized ∧
    (s.channels cid).stateHash = claimedStateHash ∧
    (s.channels cid).outcomeHash = outcomeHashOf outcome ∧
    ∃ newOutcome : Outcome,
      bulkTransferFold s.self cid outcome s.pool s.holdings newOutcome s'.pool s'.holdings ∧
      s'.channels = update s.channels cid { s.channels cid with outcomeHash := outcomeHashOf newOutcome } := by
  obtain ⟨hmode, hsh, hoh, newOutcome, hfold, hchan, _⟩ := hstep
  exact ⟨hmode, hsh, hoh, newOutcome, hfold, hchan⟩

/-- B4 — `bulkConcludeAndTransferAllAssets` has EXACTLY `concludeAndTransferAllAssets`'s
    own documented effect (`DOC/0080:77`, quoted above): `.conclude`'s own
    precondition and effect, immediately followed by transferring EVERY
    asset of the just-concluded outcome, in full
    (`bulkTransferFold`, `Operations.lean`'s own
    `.bulkConcludeAndTransferAllAssets` case, restated here). -/
theorem bulk_conclude_and_transfer_all_assets_effect
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (hstep : Step sig appRel actor s (.bulkConcludeAndTransferAllAssets fp candidate) s') :
    (s.channels (channelId fp)).mode s.now ≠ .finalized ∧
    candidate.isFinal = true ∧
    SignedByAll sig s fp candidate ∧
    ∃ newOutcome : Outcome,
      bulkTransferFold s.self (channelId fp) candidate.outcome s.pool s.holdings newOutcome
        s'.pool s'.holdings ∧
      s'.channels = update s.channels (channelId fp)
        { turnNumRecord := 0, finalizesAt := s.now, stateHash := Term.val 0,
          outcomeHash := outcomeHashOf newOutcome } := by
  obtain ⟨hmode, hisFinal, hsigned, newOutcome, hfold, hchan, _⟩ := hstep
  exact ⟨hmode, hisFinal, hsigned, newOutcome, hfold, hchan⟩

/-- B4 — a bulk conclude-and-transfer can happen: for all
    `HashAssumptions`/`SignatureAssumptions`, there is an execution from
    `genesis` — a `.sign` call for every one of `fp`'s participants on
    `stateHash fp candidate` — in which a single
    `.bulkConcludeAndTransferAllAssets` call finalizes a channel and pays
    out one of its allocations in the SAME step (`DOC/0080:77`). Built by
    real steps, from a real shield past the pool's own genesis, the same
    way `payout_can_happen` is. -/
theorem bulk_conclude_and_transfer_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness) (ownedComplete : OwnedProofCompleteness) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
      (assetIndex : Nat) (h : assetIndex < candidate.outcome.length)
      (dest : Allocation) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.bulkConcludeAndTransferAllAssets fp candidate) s' ∧
      dest ∈ (candidate.outcome.get ⟨assetIndex, h⟩).allocations ∧
      0 < dest.amount ∧
      PoolIsLive s'.pool
        (commitment dest.destination (candidate.outcome.get ⟨assetIndex, h⟩).asset dest.amount) := by
  let selfInputs : List Term := []
  let selfTerm : Term := Term.keccak selfInputs
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let fp : FixedPart := ⟨[], 0, 0, 0⟩
  let cid : Term := channelId fp
  let note1 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amount⟩
  let pool0 : PoolState := shieldPool _root_.genesis token amount note1.npk
  have hNotPaused0 : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue0 : 0 < amount := by decide
  have hRange0 : RangeChecked120 (shieldBase 0 amount) := rangeCheck120_complete _ (by decide)
  have hshield : _root_.Step (_root_.genesis : PoolState) pool0 :=
    shieldPool_step _root_.genesis token amount note1.npk hNotPaused0 hValue0 hRange0
  have hReachPool : _root_.Reachable pool0 :=
    _root_.Reachable.step _root_.Reachable.genesis hshield
  let root1 : Term := treeRoot TreeDepth pool0.leaves
  let pathElements1 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut : Fin 1 → Term := fun _ => npk selfTerm 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let pub_d : TransactPublic 1 1 :=
    { merkleRoot := root1, boundParamsHash := 0,
      nullifiers := fun _ => nullifier (Term.val nullifyingKey) 0,
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let depositedNote : CommitmentPreimage := ⟨npk selfTerm 0, token, amount⟩
  let g := genesis assets selfInputs pool0
  let mid1 : AdjudicatorState := { g with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub_d) ∨ g.poolSignedBy pk' m' }
  have hsignstep := signNote_step sig (consensusRelation sig) g publicKey (msgHashOf pub_d)
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep
  have hsigned : mid1.poolSignedBy publicKey (msgHashOf pub_d) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature, hveri⟩ :=
    poolSigLive.eddsaCompleteness mid1.poolSignedBy publicKey (msgHashOf pub_d) hsigned
  let w_d : TransactWitness 1 1 :=
    { token := token, publicKey := publicKey, signature := signature,
      nullifyingKey := nullifyingKey, randomIn := fun _ => 0, valueIn := fun _ => note1.value,
      pathElements := pathElements1, leavesIndices := fun _ => 0,
      npkOut := npkOut, valueOut := valueOut }
  have hC_d : Constrained w_d pub_d :=
    { pathLen := fun _ => treePath_length TreeDepth pool0.leaves 0
      merkle := fun _ => by
        rw [show commitment (npk (masterPublicKey w_d.publicKey w_d.nullifyingKey) (w_d.randomIn 0))
          w_d.token (w_d.valueIn 0) = hashCommitment note1 from rfl]
        exact treePath_correct TreeDepth pool0.leaves 0 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => rangeCheck120_complete note1.value (by decide)
      rangeOut := fun _ => rangeCheck120_complete amount (by decide)
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note1.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amount)))
        show fieldEq note1.value amount
        show fieldEq (shieldBase 0 amount) amount
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove_d : removeAll (mid1.pool.live w_d.token) (transactSpentPositions 0 w_d) = some [] := by
    show removeAll [((0, 0), note1)] [((0, 0), note1)] = some []
    decide
  have hNullify_d : markSpent (mid1.pool.spent 0) (List.ofFn pub_d.nullifiers) =
      some (List.ofFn pub_d.nullifiers) := rfl
  have hidxrec_d : (pub_d.commitmentsOut (0 : Fin 1),
      (⟨w_d.npkOut 0, w_d.token, w_d.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d pub_d :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d.token
        then withTreePositionsFrom 0 (insertStartPos mid1.pool.leaves 1) (transactAllOutputs w_d) ++ []
        else mid1.pool.live t,
      spent := fun n => if n = 0 then List.ofFn pub_d.nullifiers else mid1.pool.spent n,
      leaves := mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment,
      roots := treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment) ::
        mid1.pool.roots,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d pub_d),
      ownedRandomOf := applyOwnedRecords mid1.pool.ownedRandomOf
        [(pub_d.commitmentsOut (0 : Fin 1), (⟨selfTerm, 0⟩ : OwnedDisclosure))] },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some ((0, 1), pub_d.commitmentsOut (0 : Fin 1)))) }
  have hdstep : DepositStep mid1.pool selfTerm token amount w_d pub_d (0 : Fin 1) 0 0 1 mid2.pool :=
    ⟨0, rfl, rfl, rfl, rfl, rfl, (by decide), (by decide), hC_d, [], List.ofFn pub_d.nullifiers,
      transactOutputRecords w_d pub_d,
      (by show root1 ∈ mid1.pool.roots; show root1 ∈ pool0.roots; exact List.mem_cons_self),
      hRemove_d, hNullify_d, List.Sublist.refl _, hidxrec_d, rfl⟩
  have hstep_d : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amount) mid2 := by
    refine ⟨rfl, rfl, channelId_not_external fp, (by decide),
      ⟨1, 1, w_d, pub_d, 0, 0, 0, 1, mid2.pool, ?_, hsigned, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep
    · exact ⟨rfl, rfl⟩
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_d
  let mid3 : AdjudicatorState := { mid2 with now := 1 }
  have hstep_tick : Step sig (consensusRelation sig) (Actor.nitro 0) mid2 (.tick 1) mid3 :=
    ⟨Nat.zero_le 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach3 : Reachable sig (consensusRelation sig) g mid3 :=
    reachable_step hreach2 hstep_tick
  let recipientPK : Nat × Nat := (2, 2)
  let recipientNK : Nat := 2
  let dest : Allocation :=
    ⟨npk (masterPublicKey recipientPK recipientNK) 0, amount, .simple, 0⟩
  let outcome : Outcome := [⟨token, [dest]⟩]
  let candidate : VariablePart := ⟨outcome, 0, 0, true⟩
  have hassetIdx : (0 : Nat) < outcome.length := by decide
  have hnotfinalized : (mid3.channels cid).mode mid3.now ≠ .finalized := by
    simp [mid3, mid2, mid1, g, genesis, ChannelStatus.mode, emptyStatus]
  have hheld2 : heldValue mid2 token cid = amount :=
    deposit_sets_heldValue sig (consensusRelation sig) (Actor.pool publicKey) mid1 mid2 cid 0
      token amount hstep_d rfl
  have hheld3 : heldValue mid3 token cid = amount := hheld2
  let rootT : Term := treeRoot TreeDepth mid3.pool.leaves
  let pathElements2 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth mid3.pool.leaves 1
  let randomIn2 : Fin 1 → Nat := fun _ => 0
  let valueIn2 : Fin 1 → Nat := fun _ => amount
  let leavesIndices2 : Fin 1 → Nat := fun _ => 1
  let npkOut2 : Fin 1 → Term := fun _ => dest.destination
  let valueOut2 : Fin 1 → Nat := fun _ => amount
  let pub_t : TransactOwnedPublic 1 1 :=
    { merkleRoot := rootT, boundParamsHash := 0,
      nullifiers := fun _ => nullifier selfTerm (leavesIndices2 0),
      commitmentsOut := fun _ => commitment (npkOut2 0) token (valueOut2 0),
      ownerField := selfTerm }
  let w_t : TransactOwnedWitness 1 1 :=
    { token := token, randomIn := randomIn2, valueIn := valueIn2, pathElements := pathElements2,
      leavesIndices := leavesIndices2, npkOut := npkOut2, valueOut := valueOut2 }
  have hOC : OwnedConstrained w_t pub_t :=
    { pathLen := fun _ => treePath_length TreeDepth mid3.pool.leaves 1
      merkle := fun _ => by
        rw [show commitment (npk pub_t.ownerField (w_t.randomIn 0)) w_t.token
          (w_t.valueIn 0) = hashCommitment depositedNote from rfl]
        exact treePath_correct TreeDepth mid3.pool.leaves 1 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => rangeCheck120_complete amount (by decide)
      rangeOut := fun _ => rangeCheck120_complete amount (by decide)
      balance := rfl }
  have hNonZero_t : ∀ j, ¬ isZeroPreimage
      (⟨w_t.npkOut j, w_t.token, w_t.valueOut j⟩ : CommitmentPreimage) := by
    intro j hz
    have : amount = 0 := hz.2.1
    simp [amount] at this
  have hRemove_t : removeAll (mid3.pool.live token) (ownedSpentPositions 0 pub_t w_t) = some [] := by
    show removeAll [((0, 1), depositedNote)] [((0, 1), depositedNote)] = some []
    decide
  have hNullify_t : markSpent (mid3.pool.spent 0) (List.ofFn pub_t.nullifiers) =
      some (nullifier selfTerm (leavesIndices2 0) :: mid3.pool.spent 0) := by
    show markSpent [nullifier (Term.val nullifyingKey) 0] [nullifier selfTerm (leavesIndices2 0)] =
      some (nullifier selfTerm (leavesIndices2 0) :: [nullifier (Term.val nullifyingKey) 0])
    have hnullseparate : nullifier selfTerm (leavesIndices2 0) ≠ nullifier (Term.val nullifyingKey) 0 := by
      intro heqn
      have h01 := Term.val.inj (Term.hash2_inj heqn).2
      exact absurd h01 (by decide)
    unfold markSpent
    rw [if_neg (by simpa using hnullseparate)]
    rfl
  let s' : AdjudicatorState := { mid3 with
    pool := { mid3.pool with
      live := fun t => if t = token
        then withTreePositionsFrom 0 (insertStartPos mid3.pool.leaves 1)
          [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] ++ []
        else mid3.pool.live t,
      spent := fun n => if n = 0 then nullifier selfTerm (leavesIndices2 0) :: mid3.pool.spent 0
        else mid3.pool.spent n,
      leaves := mid3.pool.leaves ++ [commitment dest.destination token amount],
      roots := treeRoot TreeDepth (mid3.pool.leaves ++ [commitment dest.destination token amount]) ::
        mid3.pool.roots,
      preimageOf := applyRecords mid3.pool.preimageOf (ownedOutputRecords w_t pub_t),
      ownedRandomOf := mid3.pool.ownedRandomOf },
    holdings := update mid3.holdings token (update (mid3.holdings token) cid none),
    channels := update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf [(⟨token, [{ dest with amount := 0 }]⟩ : SingleAssetExit)] } }
  have hcEq : mid3.holdings token cid = some ((0, 1), pub_d.commitmentsOut (0 : Fin 1)) := by
    show (update mid1.holdings token (update (mid1.holdings token) cid
      (some ((0, 1), pub_d.commitmentsOut (0 : Fin 1))))) token cid =
      some ((0, 1), pub_d.commitmentsOut (0 : Fin 1))
    unfold update
    rw [if_pos rfl, if_pos rfl]
  have hospend : PoolOwnedSpendStep mid3.pool selfTerm token (mid3.holdings token cid)
      [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] [] s'.pool := by
    rw [hcEq]
    refine ⟨w_t, pub_t, (by decide), hOC, [], nullifier selfTerm (leavesIndices2 0) :: mid3.pool.spent 0,
      (fun j => j.elim0), hNonZero_t, rfl, rfl, rfl, rfl, rfl, ?_, hRemove_t, hNullify_t,
      (fun j => j.elim0), rfl⟩
    · show rootT ∈ mid3.pool.rootsAt' 0
      show rootT ∈ mid2.pool.rootsAt' 0
      show rootT ∈ mid2.pool.roots
      show rootT ∈ (treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d).map
        hashCommitment) :: mid1.pool.roots)
      exact List.mem_cons_self
  have htransferEffects : transferEffects [dest] amount [] =
      ([{dest with amount := 0}], [dest], amount) := by
    unfold transferEffects afford
    simp [listSum, dest]
  have hguarantee_check : ∀ held : Nat, ∀ a ∈ (transferEffects [dest] held []).2.1,
      a.allocationType ≠ .guarantee := by
    intro held a ha
    simp only [transferEffects, afford, dest] at ha
    simp_all
  have hfold : bulkTransferFold selfTerm cid outcome mid3.pool mid3.holdings
      [(⟨token, [{ dest with amount := 0 }]⟩ : SingleAssetExit)] s'.pool s'.holdings := by
    refine ⟨hguarantee_check _, ?_, 0, ?_⟩
    · show (⟨token, [{ dest with amount := 0 }]⟩ : SingleAssetExit) =
        (⟨token, (transferEffects [dest] amount []).1⟩ : SingleAssetExit)
      rw [htransferEffects]
    · show ∃ midPool,
        PoolOwnedSpendStep mid3.pool selfTerm token (mid3.holdings token cid)
          [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] [] midPool ∧
        (let outputs := [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)]
         let treeNumber := insertTreeNumber mid3.pool.closedTrees mid3.pool.leaves outputs.length
         let pos := insertStartPos mid3.pool.leaves outputs.length + outputs.length - 1
         let midHoldings := update mid3.holdings token
          (update (mid3.holdings token) cid none)
         bulkTransferFold selfTerm cid [] midPool midHoldings [] s'.pool s'.holdings)
      refine ⟨s'.pool, hospend, ⟨rfl, rfl⟩⟩
  have hstep_bulk : Step sig (consensusRelation sig) (Actor.nitro 0) mid3
      (.bulkConcludeAndTransferAllAssets fp candidate) s' := by
    refine ⟨hnotfinalized, rfl, ?_, [(⟨token, [{ dest with amount := 0 }]⟩ : SingleAssetExit)],
      hfold, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    cases hp
  refine ⟨assets, selfInputs, pool0, mid3, s', fp, candidate, 0, hassetIdx, dest,
    Actor.nitro 0, hReachPool, hreach3, hstep_bulk, ?_, ?_, ?_⟩
  · show dest ∈ [dest]
    exact List.mem_singleton_self _
  · decide
  · refine ⟨token, 0, 2, ⟨dest.destination, token, amount⟩, ?_, rfl⟩
    show ((0, 2), (⟨dest.destination, token, amount⟩ : CommitmentPreimage)) ∈
      withTreePositionsFrom 0 (insertStartPos mid3.pool.leaves 1) [(⟨dest.destination, token, amount⟩ :
        CommitmentPreimage)] ++ ([] : List ((Nat × Nat) × CommitmentPreimage))
    apply List.mem_append.mpr
    left
    have hlen : insertStartPos mid3.pool.leaves 1 = 2 := rfl
    rw [hlen]
    simp [withTreePositionsFrom, withPositionsFrom]

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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (asset : Nat) (cid : Term) (pos : Nat × Nat) (c : Term)
    (pre : CommitmentPreimage)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s)
    (hholds : s.holdings asset cid = some (pos, c))
    (hpre : s.pool.preimageOf c = some pre) :
    pre.value ≠ 0 := by
  obtain ⟨⟨pre', hpre', _hconsist, hval', _htok, _hlive, _r, _hnpk, _hown⟩, _, _⟩ :=
    holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach asset cid pos c hholds
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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    heldValue s asset cid = 0 ↔
      s.holdings asset cid = none ∨
      ∃ pos c, s.holdings asset cid = some (pos, c) ∧ s.pool.preimageOf c = none := by
  unfold heldValue
  rcases hc : s.holdings asset cid with _ | ⟨pos, c⟩
  · simp
  · simp only []
    rcases hp : s.pool.preimageOf c with _ | pre
    · constructor
      · intro _
        exact Or.inr ⟨pos, c, rfl, hp⟩
      · intro _
        simp
    · simp only [Option.map_some, Option.getD_some]
      constructor
      · intro hv
        exact absurd hv (holdings_never_zero_valued sig appRel assets selfInputs pool0 s asset cid
          pos c pre hreach hc hp)
      · rintro (h1 | ⟨pos2, c2, hc2, hp2⟩)
        · exact absurd h1 (by simp)
        · have hceq : (pos, c) = (pos2, c2) := Option.some.inj hc2
          rw [(show c = c2 from (congrArg Prod.snd hceq : (pos, c).snd = (pos2, c2).snd)), hp2] at hp
          exact absurd hp (by simp)

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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
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
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) (dest : Allocation)
    (hdest : dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations) (hzero : dest.amount = 0) :
    ¬ ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧ pre.value = 0 ∧
        (∃ pos, (pos, pre) ∈ s'.pool.live pre.token) ∧
        (∀ pos, (pos, pre) ∉ s.pool.live pre.token) := by
  obtain ⟨hassetIdx, hmode, hsh, hoh, hstrict, hinner, _⟩ := hstep
  obtain ⟨hguarantee, hrest⟩ := hinner
  obtain ⟨r, hmatch, hholdseq, hchanseq⟩ := hrest
  rintro ⟨pre, _hnpk, hval, ⟨pos, hin⟩, hnin⟩
  unfold PoolOwnedSpendStep at hmatch
  by_cases htok : pre.token = (outcome.get ⟨assetIndex, hassetIdx⟩).asset
  · rw [htok] at hin
    have hnz := payout_outputs_nonzero
      (transferEffects (outcome.get ⟨assetIndex, hassetIdx⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, hassetIdx⟩).asset cid) indices).2.1
      (heldValue s (outcome.get ⟨assetIndex, hassetIdx⟩).asset cid -
        (transferEffects (outcome.get ⟨assetIndex, hassetIdx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hassetIdx⟩).asset cid) indices).2.2)
      (outcome.get ⟨assetIndex, hassetIdx⟩).asset s.self r
    rcases hc : s.holdings (outcome.get ⟨assetIndex, hassetIdx⟩).asset cid with _ | c0
    · rw [hc] at hmatch
      obtain ⟨w, pub, hM, hC, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes, hroot, hmark,
        hRandomOut, heq⟩ := hmatch
      rw [heq] at hin
      dsimp only at hin
      rw [if_pos rfl] at hin
      rcases List.mem_append.mp hin with hc1 | hc2
      · exact hnz pre (withTreePositionsFrom_snd_mem _ _ _ (pos, pre) hc1) hval
      · exact hnin pos (htok ▸ hc2)
    · rw [hc] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes,
        hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
      rw [heq] at hin
      dsimp only at hin
      rw [if_pos rfl] at hin
      rcases List.mem_append.mp hin with hc1 | hc2
      · exact hnz pre (withTreePositionsFrom_snd_mem _ _ _ (pos, pre) hc1) hval
      · have hperm := removeAll_perm hremove
        have hmem : (pos, pre) ∈ s.pool.live (outcome.get ⟨assetIndex, hassetIdx⟩).asset :=
          (List.Perm.mem_iff hperm).mpr (List.mem_append.mpr (Or.inr hc2))
        exact hnin pos (htok ▸ hmem)
  · have heqlive : s'.pool.live pre.token = s.pool.live pre.token := by
      rcases hc : s.holdings (outcome.get ⟨assetIndex, hassetIdx⟩).asset cid with _ | c0
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes, hroot,
          hmark, hRandomOut, heq⟩ := hmatch
        rw [heq]
        dsimp only
        rw [if_neg htok]
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes,
          hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
        rw [heq]
        dsimp only
        rw [if_neg htok]
    rw [heqlive] at hin
    exact hnin pos hin

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
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length)
    (hfull :
      (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 =
      heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) :
    s'.holdings (outcome.get ⟨assetIndex, h⟩).asset cid = none := by
  obtain ⟨hassetIdx, hmode, hsh, hoh, hstrict, hinner, _⟩ := hstep
  obtain ⟨hguarantee, hrest⟩ := hinner
  obtain ⟨r, hmatch, hholdseq, hchanseq⟩ := hrest
  have hidx_eq : (⟨assetIndex, hassetIdx⟩ : Fin outcome.length) = ⟨assetIndex, h⟩ := rfl
  rw [hidx_eq] at hholdseq
  rw [hholdseq]
  have hgen : ∀ (remainder : Nat) (X : Option ((Nat × Nat) × Term)),
      remainder = 0 →
      (update s.holdings (outcome.get ⟨assetIndex, h⟩).asset
        (update (s.holdings (outcome.get ⟨assetIndex, h⟩).asset) cid
          (if remainder = 0 then none else X)))
        (outcome.get ⟨assetIndex, h⟩).asset cid = none := by
    intro remainder X hr
    rw [hr]
    unfold update
    simp
  refine hgen _ _ ?_
  show heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
      (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 = 0
  omega

/-- Where a `NullifierSet` gets a fresh entry at exactly one key, and the
    fresh entry equals the OLD entry at that key (so nothing actually
    changed), the whole function is unchanged — `nullify_iff_commitment_
    was_some`'s own `none`-case argument, packaged generically over
    `PoolOwnedSpendStep`'s own `spent` update shape. -/
theorem spent_update_eq_self_of_markSpent_nil (f : Nat → NullifierSet) (x : Nat)
    (y : NullifierSet) (hm : markSpent (f x) [] = some y) :
    (fun n => if n = x then y else f n) = f := by
  have hy : f x = y := Option.some.inj hm
  funext n
  by_cases hn : n = x
  · rw [hn, hy, if_pos rfl]
  · rw [if_neg hn]

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
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    (s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid = none) ↔
      s'.pool.spent = s.pool.spent := by
  obtain ⟨hassetIdx, hmode, hsh, hoh, hstrict, hinner, _⟩ := hstep
  obtain ⟨hguarantee, hrest⟩ := hinner
  obtain ⟨r, hmatch, hholdseq, hchanseq⟩ := hrest
  have hidx_eq : (⟨assetIndex, hassetIdx⟩ : Fin outcome.length) = ⟨assetIndex, h⟩ := rfl
  rw [hidx_eq] at hmatch
  unfold PoolOwnedSpendStep at hmatch
  constructor
  · intro hnone
    rw [hnone] at hmatch
    obtain ⟨w, pub, hM, hC, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes, hroot, hmark,
      hRandomOut, heq⟩ := hmatch
    have hofn : List.ofFn pub.nullifiers = ([] : List Term) := by simp
    rw [hofn] at hmark
    rw [heq]
    dsimp only
    exact spent_update_eq_self_of_markSpent_nil s.pool.spent _ spent' hmark
  · intro hpost
    rcases hc : s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid with _ | ⟨⟨spendTreeNumber, pos⟩, cm⟩
    · rfl
    · exfalso
      rw [hc] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes,
        hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
      rw [heq] at hpost
      dsimp only at hpost
      have hspenteq := congrFun hpost spendTreeNumber
      rw [if_pos rfl] at hspenteq
      have hofn1 : List.ofFn pub.nullifiers = [pub.nullifiers 0] := by
        rw [List.ofFn_succ, List.ofFn_zero]
      rw [hofn1, markSpent_single] at hmark
      split at hmark
      · exact absurd hmark (by simp)
      · rename_i hne
        have heq2 : pub.nullifiers 0 :: s.pool.spent spendTreeNumber = spent' :=
          Option.some.inj hmark
        have hlen := congrArg List.length (heq2.trans hspenteq)
        simp at hlen

end ArmadaLean.Adjudicator
