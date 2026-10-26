/-
  ArmadaLean.Adjudicator.Safety — the theorem STATEMENTS stage A asks for.
  `unbeatable_pays`/`unbeatable_pays_after_timeout` carry `sorry`; every
  other theorem below is proved.

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
  sorry

/-- `unbeatable_pays`/`unbeatable_pays_after_timeout`'s own interleaving
    invariant, carried one `Step` at a time: at any state, EITHER (B)
    `fp`'s own channel is not yet finalized and `candidate` still has
    every participant's own signature, OR (A1) it is finalized with a
    TRACKED current outcome at `assetIndex` whose own `destIdx` entry
    is STILL `dest` (never yet selected) and still affords `x`
    (`afford_exchange_sel`, A-02's own generalization, carries this
    through any OTHER index's own payout; a FULL `curOutcome`, not a
    `candidate.outcome`-derived `mapIdx`, since `.reclaim` can rewrite
    an OTHER asset index's own guarantee allocation — `hnoguarantee`
    only restricts `assetIndex` itself), OR (A2) `dest` already holds a
    live note worth `x` (minted the ONE time `destIdx` DOES get
    selected; survives every later step via `appliesAll_note_
    survives`). -/
def UnbeatablePaysInv (sig : SignatureAssumptions) (fp : FixedPart) (candidate : VariablePart)
    (assetIndex destIdx : Nat) (hAssetIdx : assetIndex < candidate.outcome.length) (x : Nat)
    (dest : Allocation) (mid : AdjudicatorState) : Prop :=
  ((mid.channels (channelId fp)).mode mid.now ≠ .finalized ∧ SignedByAll sig mid fp candidate ∧
    x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
      (heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
        (channelId fp))).getD destIdx 0) ∨
  (∃ (curOutcome : Outcome) (hci : assetIndex < curOutcome.length),
    (mid.channels (channelId fp)).mode mid.now = .finalized ∧
    (mid.channels (channelId fp)).outcomeHash = outcomeHashOf curOutcome ∧
    curOutcome.map SingleAssetExit.asset = candidate.outcome.map SingleAssetExit.asset ∧
    (∀ a ∈ (curOutcome.get ⟨assetIndex, hci⟩).allocations, a.allocationType ≠ .guarantee) ∧
    (curOutcome.get ⟨assetIndex, hci⟩).asset = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧
    (curOutcome.get ⟨assetIndex, hci⟩).allocations.getD destIdx Allocation.default = dest ∧
    x ≤ (afford (curOutcome.get ⟨assetIndex, hci⟩).allocations
      (heldValue mid (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset
        (channelId fp))).getD destIdx 0) ∨
  (∃ pre : CommitmentPreimage,
    pre.npk = dest.destination ∧
    pre.token = (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset ∧ x ≤ pre.value ∧
    PoolIsLive mid.pool (commitment pre.npk pre.token pre.value))

/-- `UnbeatablePaysInv`'s own one-step preservation: given an actor OTHER
    than `h`/`h`'s own pool key, and `h`'s `signedBy`/`poolSignedBy` rows
    still exactly their `s0` (anchor) values, the invariant survives. -/
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
  sorry

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
        s'.signedBy h = s0.signedBy h ∧ s'.poolSignedBy pk = s0.poolSignedBy pk := by
  sorry

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
  sorry

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
  sorry

/-- **Placeholder, pending the pool-model rollover change**: the pool's
    own tree always has room for two more leaves, at ANY reachable
    state. On the real chain this holds because the contract rolls the
    tree over to a fresh one once full (`MerkleModule.sol:62-70`); the
    current pool model has one tree with no rollover, so this is not
    yet provable from `Reachable` alone. Replace with the
    `adjudicator_pool_reachable`-lifted fact once the pool model's own
    rollover change lands. -/
theorem pool_leaves_capacity_placeholder (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) (mid : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid) :
    mid.pool.leaves.length + 2 ≤ 2 ^ TreeDepth := by
  sorry

/-- **Placeholder, pending the pool-model `live_values_lt_2pow120` change**:
    a channel's own `heldValue`, at ANY reachable state, is below
    `2 ^ 120` — true because every note ever minted passed the owning
    circuit's own `Num2Bits(120)` range check (`Constrained`/
    `OwnedConstrained`'s own `rangeIn`/`rangeOut` fields) at mint time,
    so every LIVE note's own value is in range, and `heldValue` only
    ever reads a live note's own value (`State.lean`). Replace with the
    `adjudicator_pool_reachable`-lifted `live_values_lt_2pow120` once
    the pool model proves it. -/
theorem heldValue_range_placeholder (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) (mid : AdjudicatorState)
    (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid) :
    RangeChecked120 (heldValue mid asset cid) := by
  sorry

/-- **Placeholder, pending the pool-model tree-rollover change**: a
    channel's own recorded holding position names the EXACT pool leaf
    its own commitment lives at, at ANY reachable state — `leaves` only
    grows by append (never overwrites an existing index), and
    `position := before.leaves.length + idx.val`
    (`DepositStep`/`PoolOwnedSpendStep`, `Notes.lean`) already places
    the note's own `hashCommitment` at exactly that index the moment it
    is written, so this should hold for today's single-tree pool
    model — but the pool model's own rollover change in progress
    reshapes a leaf position to `(tree number, index)`, so a proof
    against today's `leaves : List Term` shape would need redoing once
    that change lands. Replace once the pool model's own "a leaf
    written at a position never changes" fact (in the new shape) is
    available to connect this to. -/
theorem holdings_position_leaf_value_placeholder (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) (mid : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid) :
    ∀ asset cid (pos : Nat × Nat) c, mid.holdings asset cid = some (pos, c) →
      (mid.pool.leavesAt' pos.1).getD pos.2 (Term.val 0) = c := by
  sorry

/-- **Placeholder, pending the pool-model rollover change**: a live,
    owned note's own nullifier is never already spent — true because a
    note leaves `live` the SAME step its nullifier enters `spent`
    (`PoolOwnedSpendStep`'s own `removeAll`/`markSpent` pairing,
    `Notes.lean`), so a note that stays live was never spent. A
    nullifier is derived from the leaf position
    (`ArmadaLean.Nullifier.nullifier`), and the pool model's own
    rollover change in progress reshapes what a position is, so a
    proof against today's shape would need redoing once that change
    lands. Replace with the pool model's own version of this fact (in
    the new shape) once that change lands. -/
theorem live_note_nullifier_unspent_placeholder (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) (mid : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) mid)
    (asset : Nat) (cid : Term) (pos : Nat × Nat) (c ownerField : Term) (r : Nat)
    (hholds : mid.holdings asset cid = some (pos, c))
    (hown : mid.pool.ownedRandomOf c = some ⟨ownerField, r⟩) :
    nullifier ownerField pos.2 ∉ mid.pool.spent pos.1 := by
  sorry

/-- Removing a single already-live element from a pool always succeeds,
    leaving it erased. Generic over `removeAll`'s own `[DecidableEq α]`
    parameter so the `BEq` instance it derives internally stays pinned
    to the SAME one this lemma's own statement uses — what
    `transfer_step_exists` needs for `PoolOwnedSpendStep`'s own
    `removeAll` obligation on a singleton `ownedSpentPositions`. -/
theorem removeAll_singleton_of_mem {α : Type} [DecidableEq α] {l : List α} {x : α}
    (h : x ∈ l) : removeAll l [x] = some (l.erase x) := by
  sorry

/-- The full per-step invariant `holdings_position_live_step` (`Lemmas.lean`)
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
  sorry

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
  sorry

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
  sorry

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
    (`zero_payout_mints_nothing`). -/
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
    (hduration : 0 < fp.challengeDuration)
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
  sorry

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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (token : Nat)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    s.pool.notedValue token = pool0.notedValue token := sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
      (challenger : Nat) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
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
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (cid : Term) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
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
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s (.conclude fp candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .finalized := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- `conclude` finalizes without moving value: `conclude`'s `Step` case
    touches only `s'.channels`; `s'.pool` and `s'.holdings` are provably
    unchanged (`Operations.lean`'s `.conclude` doc comment states and
    explains this Armada-specific rule directly). -/
theorem conclude_moves_no_value
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (hstep : Step sig appRel actor s (.conclude fp candidate) s') :
    s'.pool = s.pool ∧ s'.holdings = s.holdings := sorry

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
  sorry

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
  sorry

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
  sorry

/-- A later `.transfer` call can happen after an earlier `.transfer`
    call on the SAME channel already left a nonzero remainder: paying
    one entry of a finalized two-entry outcome does not lock the
    other. Nitro-2019-219.pdf §5.1's `T(A, B, x)`: "Reduces the funds
    held in channel A by x... Reduces the amount owed to B in the
    outcome of A by x" — only B's own entry changes; every OTHER
    entry's own owed amount, and whatever the channel's own priority-
    order run (§5.2, the Turbo Value Algorithm, `afford`) left
    unpaid, stay exactly where that first call left them, so a later
    `.transfer` can still pay what remains. The second call's own
    spend witness is built the way `ArmadaLean.PoolSafety.
    owned_spend_witness_exists`/`leaf_has_merkle_witness` show one
    always can: the random comes back from `mid.pool.ownedRandomOf`'s
    own public lookup (`hOwnedRandom`), not from the first call's own
    local choice of `r1` — any actor reading `mid.pool` recovers the
    same witness; `.transfer`'s remainder note (`Operations.lean`) is
    disclosed there exactly because it stays contract-owned. -/
theorem transfer_after_transfer_can_happen
    (hashA : HashAssumptions) (sig : SignatureAssumptions)
    (poolSigLive : PoolSignatureLiveness) (ownedComplete : OwnedProofCompleteness) :
    ∃ (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
      (s mid s' : AdjudicatorState) (assetIndex : Nat)
      (cid claimedStateHash claimedStateHash' : Term)
      (outcome outcome1 : Outcome) (actor actor' : Actor)
      (h : assetIndex < outcome.length) (h1 : assetIndex < outcome1.length)
      (dest1 dest2 : Allocation),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets selfInputs pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.transfer assetIndex cid claimedStateHash outcome [0]) mid ∧
      dest1 ∈ (outcome.get ⟨assetIndex, h⟩).allocations ∧ 0 < dest1.amount ∧
      heldValue mid (outcome1.get ⟨assetIndex, h1⟩).asset cid ≠ 0 ∧
      Step sig (consensusRelation sig) actor' mid
        (.transfer assetIndex cid claimedStateHash' outcome1 [1]) s' ∧
      dest2 ∈ (outcome1.get ⟨assetIndex, h1⟩).allocations ∧ 0 < dest2.amount ∧
      PoolIsLive s'.pool
        (commitment dest2.destination (outcome1.get ⟨assetIndex, h1⟩).asset dest2.amount) := by
  sorry

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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState) (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    heldValue s asset cid = 0 ↔
      s.holdings asset cid = none ∨
      ∃ pos c, s.holdings asset cid = some (pos, c) ∧ s.pool.preimageOf c = none := by
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
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    s.configuredAssets = assets := sorry

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
  sorry

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
  sorry

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
  sorry

end ArmadaLean.Adjudicator
