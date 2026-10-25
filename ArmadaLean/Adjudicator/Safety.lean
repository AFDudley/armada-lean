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
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (cid stateH outcomeH : Term)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hfin : ChannelFinalizedWith s cid stateH outcomeH) :
    (∃ fp candidate, channelId fp = cid ∧ candidate.isFinal = true ∧
      SignedByAll sig s fp candidate ∧
      ∃ o, OutcomeDerivedFrom candidate.outcome o ∧ outcomeHashOf o = outcomeH) ∨
    (∃ fp proof candidate challenger actor0 s0 s1,
      channelId fp = cid ∧
      Reachable sig appRel (genesis assets self pool0) s0 ∧
      Step sig appRel actor0 s0 (.challenge fp proof candidate challenger) s1 ∧
      stateHash fp candidate = stateH ∧
      ∃ o, OutcomeDerivedFrom candidate.outcome o ∧ outcomeHashOf o = outcomeH) := by
  have hinv := reachable_preserves
    (P := fun s' => Reachable sig appRel (genesis assets self pool0) s' ∧
      ∀ cid', (s'.channels cid').finalizesAt ≠ 0 →
      (∃ fp candidate, channelId fp = cid' ∧ candidate.isFinal = true ∧
        SignedByAll sig s' fp candidate ∧
        ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
          outcomeHashOf o = (s'.channels cid').outcomeHash) ∨
      (∃ fp proof candidate challenger actor0 s0 s1,
        channelId fp = cid' ∧
        Reachable sig appRel (genesis assets self pool0) s0 ∧
        Step sig appRel actor0 s0 (.challenge fp proof candidate challenger) s1 ∧
        stateHash fp candidate = (s'.channels cid').stateHash ∧
        ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
          outcomeHashOf o = (s'.channels cid').outcomeHash))
    ⟨reachable_refl sig appRel (genesis assets self pool0),
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
              Reachable sig appRel (genesis assets self pool0) s0 ∧
              Step sig appRel actor0 s0 (.challenge fp proof candidate challenger) s1' ∧
              stateHash fp candidate = (s1.channels cid'').stateHash ∧
              ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
                outcomeHashOf o = (s1.channels cid'').outcomeHash)) →
          ((∃ fp candidate, channelId fp = cid'' ∧ candidate.isFinal = true ∧
              SignedByAll sig s2 fp candidate ∧
              ∃ o, OutcomeDerivedFrom candidate.outcome o ∧
                outcomeHashOf o = (s1.channels cid'').outcomeHash) ∨
            (∃ fp proof candidate challenger actor0 s0 s1', channelId fp = cid'' ∧
              Reachable sig appRel (genesis assets self pool0) s0 ∧
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
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
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
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (cid : Term) (expectedHeld asset amount : Nat)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hstep : Step sig appRel actor s (.deposit cid expectedHeld asset amount) s') :
    heldValue s' asset cid = heldValue s asset cid + amount ∧
    (∀ asset' cid', (asset', cid') ≠ (asset, cid) →
      heldValue s' asset' cid' = heldValue s asset' cid') ∧
    s'.channels = s.channels := by
  have hinv := reachable_preserves
    (P := fun s'' => ∀ qasset qcid qpos qc, s''.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s''.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (by intro qasset qcid qpos qc hc; exact absurd hc (by simp [genesis]))
    (fun actor call s1 s2 hP hstep => holdings_preimage_nonzero_step sig appRel actor s1 s2 call hP hstep)
    hreach
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
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call) (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hstep : Step sig appRel actor s call s')
    (hdec : heldValue s' asset cid < heldValue s asset cid) :
    ((∃ assetIndex claimedStateHash outcome indices,
        call = .transfer assetIndex cid claimedStateHash outcome indices) ∧
      (s.channels cid).mode s.now = .finalized) ∨
    (∃ outcome claimedStateHash, call = .bulkTransferAllAssets cid outcome claimedStateHash ∧
      (s.channels cid).mode s.now = .finalized) ∨
    (∃ fp candidate, channelId fp = cid ∧ call = .bulkConcludeAndTransferAllAssets fp candidate) := by
  have hinv := reachable_preserves
    (P := fun s'' => ∀ qasset qcid qpos qc, s''.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s''.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (by intro qasset qcid qpos qc hc; exact absurd hc (by simp [genesis]))
    (fun actor call s1 s2 hP hstep => holdings_preimage_nonzero_step sig appRel actor s1 s2 call hP
      hstep)
    hreach
  cases call with
  | deposit channelId0 expectedHeld asset0 amount =>
    exfalso
    by_cases hp : (asset0, channelId0) = (asset, cid)
    · have ha : asset0 = asset := congrArg Prod.fst hp
      have hc : channelId0 = cid := congrArg Prod.snd hp
      subst ha; subst hc
      have hinc := (deposit_effect sig appRel assets self pool0 actor s s' channelId0 expectedHeld
        asset0 amount hreach hstep).1
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
    finalized (with some stale outcome) at `s` to begin with. `hhonest`
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
    here supplies. -/
theorem unbeatable_pays
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
    (h : Nat) (hPoolKey : Option (Nat × Nat)) (assetIndex : Nat)
    (hAssetIdx : assetIndex < candidate.outcome.length)
    (destIdx : Nat) (x : Nat) (dest : Allocation)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) (hp : h ∈ fp.participants)
    (hfinal : candidate.isFinal = true)
    (hduration : 0 < fp.challengeDuration)
    (hnotfinal : (s.channels (channelId fp)).mode s.now ≠ .finalized)
    (hsigned : SignedByAll sig s fp candidate)
    (hdest : (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations[destIdx]? = some dest)
    (hnoguarantee : ∀ a ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations,
      a.allocationType ≠ .guarantee)
    (pk : Nat × Nat) (nk : Nat) (r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (hxpos : 0 < x)
    (haffordable : x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
      (heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp))).getD destIdx 0)
    (hhonest : ∀ candidate', candidate'.isFinal = true →
      AuthorizedBy sig s h (stateHash fp candidate') →
      stateHash fp candidate' = stateHash fp candidate) :
    ∀ (interleaved : List (Actor × Call)) (mid : AdjudicatorState),
      AppliesAll sig appRel s interleaved mid →
      (∀ actor call, (actor, call) ∈ interleaved →
        actor ≠ Actor.nitro h ∧ ∀ pk', hPoolKey = some pk' → actor ≠ Actor.pool pk') →
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
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (s : AdjudicatorState) (fp : FixedPart) (proof : List VariablePart)
    (candidate : VariablePart) (challenger h : Nat) (hPoolKey : Option (Nat × Nat))
    (assetIndex : Nat)
    (hAssetIdx : assetIndex < candidate.outcome.length)
    (destIdx : Nat) (x : Nat) (dest : Allocation)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) (hp : h ∈ fp.participants)
    (hregistered : (s.channels (channelId fp)).mode s.now = .challenge ∧
      (s.channels (channelId fp)).stateHash = stateHash fp candidate ∧
      (s.channels (channelId fp)).outcomeHash = outcomeHashOf candidate.outcome)
    (hduration : 0 < fp.challengeDuration)
    (hdest : (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations[destIdx]? = some dest)
    (hnoguarantee : ∀ a ∈ (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations,
      a.allocationType ≠ .guarantee)
    (pk : Nat × Nat) (nk : Nat) (r : Nat)
    (hh_dest : dest.destination = npk (masterPublicKey pk nk) r)
    (hxpos : 0 < x)
    (haffordable : x ≤ (afford (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).allocations
      (heldValue s (candidate.outcome.get ⟨assetIndex, hAssetIdx⟩).asset (channelId fp))).getD destIdx 0)
    (hhonest : ∀ candidate', candidate'.isFinal = true →
      AuthorizedBy sig s h (stateHash fp candidate') →
      stateHash fp candidate' = stateHash fp candidate) :
    ∀ (interleaved : List (Actor × Call)) (mid : AdjudicatorState),
      AppliesAll sig appRel s interleaved mid →
      (∀ actor call, (actor, call) ∈ interleaved →
        actor ≠ Actor.nitro h ∧ ∀ pk', hPoolKey = some pk' → actor ≠ Actor.pool pk') →
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
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, hmatch⟩ := hinner
    obtain ⟨_r, _hown, _hcommit, _htoken, _hposition, hN, hM, hC, rest, spent', records, _hCapacity,
      _hRoot, hRemove, _hNullify, _hSublist, _hidxrec, heq⟩ := hdstep
    have hmidConserved : midPool.notedValue token = s.pool.notedValue token := by
      unfold PoolState.notedValue
      rw [heq]
      show listSum ((if token = w.token then
          withPositionsFrom s.pool.leaves.length (transactAllOutputs w) ++ rest
          else s.pool.live token).map (fun p => p.2.value)) =
        listSum ((s.pool.live token).map (fun p => p.2.value))
      by_cases ht : token = w.token
      · rw [if_pos ht, ht]
        have hbal := transact_balance hN hM hC (newNotes := transactAllOutputs w)
          (unshieldTail := []) (by simp)
        simp only [List.map_nil, listSum] at hbal
        have hsum := removeAll_sum (fun p => p.2.value) hRemove
        simp only [List.map_append, listSum_append, withPositionsFrom_map]
        omega
      · rw [if_neg ht]
    rcases hh : s.holdings asset cid with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, _⟩ := hmatch
      rw [hpoolEq]
      exact hmidConserved
    · obtain ⟨oldPos, oldHoldingVal⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergedPos, hmerge, _⟩ := hmatch
      obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity',
        hown', htoken', hnpkOut', hmergedEq, _hleaf0, _hleaf1, hcommitOld, hcommitNew, hroot',
        hremove', hnullify', _hrandomOut', heq'⟩ := hmerge
      have hmergeConserved : s'.pool.notedValue token = midPool.notedValue token := by
        unfold PoolState.notedValue
        rw [heq']
        show listSum ((if token = asset then
            withPositionsFrom midPool.leaves.length (ownedNewNotes w') ++ rest'
            else midPool.live token).map (fun p => p.2.value)) =
          listSum ((midPool.live token).map (fun p => p.2.value))
        by_cases ht : token = asset
        · rw [if_pos ht, ht]
          have hbal := transactOwned_balance (by decide) (by decide) hC'
          have hsum := removeAll_sum (fun p => p.2.value) hremove'
          simp only [List.map_append, listSum_append, withPositionsFrom_map] at hsum ⊢
          omega
        · rw [if_neg ht]
      rw [hmergeConserved]
      exact hmidConserved
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨_r, hmatch, _hholdseq, _hchanseq⟩ := hrest
    unfold PoolState.notedValue
    by_cases ht : token = (outcome.get ⟨assetIndex, hidx⟩).asset
    · rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | c
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
          hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hmatch
        have hbal := transactOwned_balance (Nat.zero_le 8) hM hC
        have hspent0 : listSum ((ownedSpentPositions pub w).map (fun p => p.2.value)) = 0 := by
          have hnil : ownedSpentPositions pub w = [] := by
            apply List.eq_nil_of_length_eq_zero
            unfold ownedSpentPositions
            simp
          rw [hnil]; rfl
        rw [hspent0] at hbal
        rw [heq]
        dsimp only
        rw [← hnewnotes]
        rw [if_pos ht, ht]
        simp only [List.map_append, listSum_append, withPositionsFrom_map]
        omega
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
          hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hmatch
        have hbal := transactOwned_balance (by decide) hM hC
        have hsum := removeAll_sum (fun p => p.2.value) hremove
        rw [heq]
        dsimp only
        rw [← hnewnotes]
        rw [if_pos ht, ht]
        simp only [List.map_append, listSum_append, withPositionsFrom_map] at hsum ⊢
        omega
    · rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | c
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
          hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hmatch
        rw [heq]
        show listSum ((if token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live token).map (fun p => p.2.value)) =
          listSum ((s.pool.live token).map (fun p => p.2.value))
        rw [if_neg ht]
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
          hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hmatch
        rw [heq]
        show listSum ((if token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live token).map (fun p => p.2.value)) =
          listSum ((s.pool.live token).map (fun p => p.2.value))
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
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_notedValue_conserved s.self channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold token
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_notedValue_conserved s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold token
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
    (s : AdjudicatorState) (asset : Nat) (cid : Term) (pos : Nat) (c : Term)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hholds : s.holdings asset cid = some (pos, c)) :
    PoolIsLive s.pool c := by
  have hinv := reachable_preserves
    (P := fun s => ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ s.pool.live qasset ∧ hashCommitment pre = qc ∧
        (pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r)) ∧
      qpos < s.pool.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', s.holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos))
    (by intro qasset qcid qpos qc hc; exact absurd hc (by simp [genesis]))
    (fun actor call s s' hP hstep =>
      (step_self sig appRel actor s s' call hstep ▸
        holdings_position_live_step sig appRel actor s s' call hP hstep : _))
    hreach
  obtain ⟨⟨pre, hpre, hval, _⟩, _, _⟩ := hinv asset cid pos c hholds
  exact ⟨asset, pos, pre, hpre, hval⟩

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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      (s.channels (channelId fp)).mode s.now = .challenge ∧
      Step sig (consensusRelation sig) actor s (.checkpoint fp [] candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .open ∧
      (s'.channels (channelId fp)).turnNumRecord = candidate.turnNum ∧
      (s'.channels (channelId fp)).finalizesAt = 0 := by
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis
  let fp : FixedPart := ⟨[0], 0, 0, 1⟩
  let candidate0 : VariablePart := ⟨[], 0, 0, false⟩
  let candidate : VariablePart := ⟨[], 0, 1, false⟩
  let g := genesis assets self pool0
  let mid1 : AdjudicatorState := { g with
    signedBy := fun p' d' => (p' = 0 ∧ d' = stateHash fp candidate0) ∨ g.signedBy p' d' }
  have hsignstep1 : Step sig (consensusRelation sig) (Actor.nitro 0) g
      (.sign 0 (stateHash fp candidate0)) mid1 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach1 : Reachable sig (consensusRelation sig) g mid1 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep1
  let mid1b : AdjudicatorState := { mid1 with
    signedBy := fun p' d' => (p' = 0 ∧ d' = stateHash fp candidate) ∨ mid1.signedBy p' d' }
  have hsignstep1b : Step sig (consensusRelation sig) (Actor.nitro 0) mid1
      (.sign 0 (stateHash fp candidate)) mid1b :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
  have hsignedAll : SignedByAll sig s fp candidate := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hauth1
  have hturnGt : candidate.turnNum > (s.channels (channelId fp)).turnNumRecord := by
    show (1 : Nat) > ((update mid1b.channels (channelId fp)
      { turnNumRecord := candidate0.turnNum, finalizesAt := mid1b.now + fp.challengeDuration,
        stateHash := stateHash fp candidate0, outcomeHash := outcomeHashOf candidate0.outcome })
      (channelId fp)).turnNumRecord
    unfold update
    rw [if_pos rfl]
    decide
  let s' : AdjudicatorState := { s with
    channels := update s.channels (channelId fp)
      { turnNumRecord := candidate.turnNum, finalizesAt := 0, stateHash := Term.val 0,
        outcomeHash := Term.val 0 } }
  have hckstep : Step sig (consensusRelation sig) (Actor.nitro 0) s
      (.checkpoint fp [] candidate) s' := by
    refine ⟨?_, hturnGt, ⟨rfl, hsignedAll⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [hmodeChallenge]
    simp
  refine ⟨assets, self, pool0, s, s', fp, candidate, Actor.nitro 0,
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


set_option maxRecDepth 2000 in
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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (channelId : Term) (expectedHeld asset amount : Nat) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      s.channels = (genesis assets self pool0).channels ∧
      s.holdings = (genesis assets self pool0).holdings ∧
      channelId = ArmadaLean.Adjudicator.channelId ⟨[], 0, 0, 0⟩ ∧
      Step sig (consensusRelation sig) actor s
        (.deposit channelId expectedHeld asset amount) s' := by
  let self : Nat := 0
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let fp1 : FixedPart := ⟨[], 0, 0, 0⟩
  let channelId : Term := channelId fp1
  -- `pool0` is the real pool, one step past its own genesis: a `shield` that
  -- mints the depositor's own note. `.deposit`'s Transact circuit below spends
  -- this note (base EdDSA path, no owned randomness yet disclosed for it).
  let note : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amount⟩
  let pool0 : PoolState :=
    let leaves' := (_root_.genesis : PoolState).leaves ++ [hashCommitment note]
    { (_root_.genesis : PoolState) with
        live := fun t => if t = token then (0, note) :: (_root_.genesis : PoolState).live t
          else (_root_.genesis : PoolState).live t,
        held := fun t => if t = token then (_root_.genesis : PoolState).held t + note.value
          else (_root_.genesis : PoolState).held t,
        leaves := leaves',
        roots := treeRoot TreeDepth leaves' :: (_root_.genesis : PoolState).roots,
        preimageOf := recordStep (_root_.genesis : PoolState).preimageOf (hashCommitment note) note }
  have hNotPaused0 : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue0 : 0 < amount := by decide
  have hFeeBP0 : (0 : Nat) ≤ BASIS := by decide
  have hCapacity0 : (_root_.genesis : PoolState).leaves.length + 1 ≤ 2 ^ TreeDepth := by decide
  have hshield : _root_.Step (_root_.genesis : PoolState) pool0 :=
    _root_.Step.shield token amount 0 note.npk hNotPaused0 hValue0 hFeeBP0 hCapacity0
  have hReachPool : _root_.Reachable pool0 :=
    _root_.Reachable.step _root_.Reachable.genesis hshield
  have hi : 0 < pool0.leaves.length := by show (0:Nat) < 1; omega
  have hmerkle := leaf_has_merkle_witness hReachPool hi
  have hgetD : pool0.leaves.getD 0 (Term.val 0) = hashCommitment note := rfl
  let root : Term := treeRoot TreeDepth pool0.leaves
  let pathElements : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut : Fin 1 → Term := fun _ => npk (Term.val self) 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let pub : TransactPublic 1 1 :=
    { merkleRoot := root, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey 0,
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
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
      nullifyingKey := nullifyingKey, randomIn := fun _ => 0, valueIn := fun _ => note.value,
      pathElements := pathElements, leavesIndices := fun _ => 0,
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
    { pathLen := fun _ => treePath_length TreeDepth pool0.leaves 0
      merkle := fun _ => by
        rw [show commitment (npk (masterPublicKey w.publicKey w.nullifyingKey)
          (w.randomIn 0)) w.token (w.valueIn 0) = hashCommitment note from rfl, ← hgetD]
        exact hmerkle.1
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp,
        show note.value = bitsVal (true :: List.replicate 119 false) by
          rw [hbitsOne]; show shieldBase 0 amount = 1; decide⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amount)))
        show fieldEq note.value amount
        show fieldEq (shieldBase 0 amount) amount
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove : removeAll (mid.pool.live w.token) (transactSpentPositions w) = some [] := by
    show removeAll [(0, note)] [(0, note)] = some []
    decide
  have hNullify : markSpent mid.pool.spent (List.ofFn pub.nullifiers) =
      some (List.ofFn pub.nullifiers) := rfl
  have hidxrec : (pub.commitmentsOut (0 : Fin 1),
      (⟨w.npkOut 0, w.token, w.valueOut 0⟩ : CommitmentPreimage)) ∈ transactOutputRecords w pub :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  have hCapacity2 : mid.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show pool0.leaves.length + 1 ≤ 2 ^ TreeDepth
    show (1 : Nat) + 1 ≤ 2 ^ TreeDepth
    decide
  let s' : AdjudicatorState := { mid with
    pool := { mid.pool with
      live := fun t => if t = w.token
        then withPositionsFrom mid.pool.leaves.length (transactAllOutputs w) ++
          ([] : List (Nat × CommitmentPreimage))
        else mid.pool.live t,
      spent := List.ofFn pub.nullifiers,
      leaves := mid.pool.leaves ++ (transactAllOutputs w).map hashCommitment,
      roots := treeRoot TreeDepth (mid.pool.leaves ++ (transactAllOutputs w).map hashCommitment) ::
        mid.pool.roots,
      preimageOf := applyRecords mid.pool.preimageOf (transactOutputRecords w pub),
      ownedRandomOf := applyOwnedRecords mid.pool.ownedRandomOf
        [(pub.commitmentsOut (0 : Fin 1), (⟨self, 0⟩ : OwnedDisclosure))] },
    holdings := update mid.holdings token (update (mid.holdings token) channelId
      (some (1, pub.commitmentsOut (0 : Fin 1)))) }
  have hdstep : DepositStep mid.pool self token amount w pub (0 : Fin 1) 1 s'.pool :=
    ⟨0, rfl, rfl, rfl, by show 1 = mid.pool.leaves.length + 0; show (1:Nat) = pool0.leaves.length + 0; rfl,
      by decide, by decide, hC, [], List.ofFn pub.nullifiers,
      transactOutputRecords w pub, hCapacity2, hmerkle.2, hRemove, hNullify,
      List.Sublist.refl _, hidxrec, rfl⟩
  have hstep : Step sig (consensusRelation sig) (Actor.pool publicKey) mid
      (.deposit channelId 0 token amount) s' := by
    refine ⟨rfl, rfl, channelId_not_external fp1, (by decide),
      ⟨1, 1, w, pub, 0, 1, s'.pool, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep
    · exact ⟨rfl, rfl⟩
  exact ⟨assets, self, pool0, mid, s', channelId, 0, token, amount, Actor.pool publicKey,
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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (channelId : Term) (expectedHeld asset amount : Nat) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.deposit channelId expectedHeld asset amount) s' := by
  obtain ⟨assets, self, pool0, s, s', channelId, expectedHeld, asset, amount, actor,
    hReachPool, hReach, _, _, _, hstep⟩ := deposit_can_happen_witness hashA sig poolSigLive
  exact ⟨assets, self, pool0, s, s', channelId, expectedHeld, asset, amount, actor,
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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s1 : AdjudicatorState) (cid : Term) (asset : Nat)
      (outcome outcome' targetOutcome : Outcome)
      (assetIndex indexOfTargetInSource targetAssetIndex dIdx : Nat)
      (claimedTargetStateHash : Term) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      (outcome.getD assetIndex ⟨0, []⟩).asset = asset ∧
      Step sig (consensusRelation sig) actor s
        (.reclaim cid outcome assetIndex indexOfTargetInSource
          targetOutcome targetAssetIndex claimedTargetStateHash) s1 ∧
      (s1.channels cid).outcomeHash = outcomeHashOf outcome' ∧
      (transferEffects (outcome.getD assetIndex ⟨0, []⟩).allocations
          (heldValue s asset cid) [dIdx]).2.2 ≠
      (transferEffects (outcome'.getD assetIndex ⟨0, []⟩).allocations
          (heldValue s1 asset cid) [dIdx]).2.2 := by
  obtain ⟨assets, self, pool0, sPre, sPost, cid, expectedHeld, asset, amount, actor0,
    hReachPool, hReachPre, hChanPre, hHoldPre, hCidEq, hDepStep⟩ :=
    deposit_can_happen_witness hashA sig poolSigLive
  have hamtPos : 0 < amount := hDepStep.2.2.2.1
  have hde := deposit_effect sig (consensusRelation sig) assets self pool0 actor0 sPre sPost cid
    expectedHeld asset amount hReachPre hDepStep
  have hReachPost : Reachable sig (consensusRelation sig) (genesis assets self pool0) sPost :=
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
  have hreach_tick : Reachable sig (consensusRelation sig) (genesis assets self pool0) sPostTick :=
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
    exact absurd hp List.not_mem_nil
  have hreach_c1 : Reachable sig (consensusRelation sig) (genesis assets self pool0) sC1 :=
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
    exact absurd hp List.not_mem_nil
  have hreach_c2 : Reachable sig (consensusRelation sig) (genesis assets self pool0) sC2 :=
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
  have hreach_s : Reachable sig (consensusRelation sig) (genesis assets self pool0) sC2 := hreach_c2
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
  refine ⟨assets, self, pool0, sC2, s1, channelId fp1, asset, outcome, outcome', targetOutcome,
    0, 3, 0, 2, Term.val 0, Actor.nitro 0, hReachPool, hreach_s, rfl, hstep_r, hs1chan, ?_⟩
  rw [hheld_sC2, hheld_s1, hbefore, hafter]
  omega


set_option maxRecDepth 4000 in
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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s mid s' : AdjudicatorState) (cid : Term) (a1 a2 asset amt1 amt2 : Nat) (actor1 actor2 : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor1 s (.deposit cid a1 asset amt1) mid ∧
      Step sig (consensusRelation sig) actor2 mid (.deposit cid a2 asset amt2) s' ∧
      heldValue s' asset cid = heldValue mid asset cid + amt2 := by
  let self : Nat := 0
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amt1 : Nat := 1
  let amt2 : Nat := 1
  let fp1 : FixedPart := ⟨[], 0, 0, 0⟩
  let cid : Term := channelId fp1
  -- `pool0`: two real shields past the pool's own genesis, one depositor note each.
  let note1 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amt1⟩
  let pool_a : PoolState :=
    let leaves' := (_root_.genesis : PoolState).leaves ++ [hashCommitment note1]
    { (_root_.genesis : PoolState) with
        live := fun t => if t = token then (0, note1) :: (_root_.genesis : PoolState).live t
          else (_root_.genesis : PoolState).live t,
        held := fun t => if t = token then (_root_.genesis : PoolState).held t + note1.value
          else (_root_.genesis : PoolState).held t,
        leaves := leaves',
        roots := treeRoot TreeDepth leaves' :: (_root_.genesis : PoolState).roots,
        preimageOf := recordStep (_root_.genesis : PoolState).preimageOf (hashCommitment note1) note1 }
  have hNotPaused_a : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue_a : 0 < amt1 := by decide
  have hFeeBP_a : (0 : Nat) ≤ BASIS := by decide
  have hCapacity_a : (_root_.genesis : PoolState).leaves.length + 1 ≤ 2 ^ TreeDepth := by decide
  have hshield_a : _root_.Step (_root_.genesis : PoolState) pool_a :=
    _root_.Step.shield token amt1 0 note1.npk hNotPaused_a hValue_a hFeeBP_a hCapacity_a
  have hReach_a : _root_.Reachable pool_a :=
    _root_.Reachable.step _root_.Reachable.genesis hshield_a
  let note2 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 1, token, shieldBase 0 amt2⟩
  let pool0 : PoolState :=
    let leaves' := pool_a.leaves ++ [hashCommitment note2]
    { pool_a with
        live := fun t => if t = token then (1, note2) :: pool_a.live t else pool_a.live t,
        held := fun t => if t = token then pool_a.held t + note2.value else pool_a.held t,
        leaves := leaves',
        roots := treeRoot TreeDepth leaves' :: pool_a.roots,
        preimageOf := recordStep pool_a.preimageOf (hashCommitment note2) note2 }
  have hNotPaused_b : pool_a.shieldsPaused = false := rfl
  have hValue_b : 0 < amt2 := by decide
  have hFeeBP_b : (0 : Nat) ≤ BASIS := by decide
  have hCapacity_b : pool_a.leaves.length + 1 ≤ 2 ^ TreeDepth := by decide
  have hshield_b : _root_.Step pool_a pool0 :=
    _root_.Step.shield token amt2 0 note2.npk hNotPaused_b hValue_b hFeeBP_b hCapacity_b
  have hReachPool : _root_.Reachable pool0 := _root_.Reachable.step hReach_a hshield_b
  have hbitsZero : ∀ n, bitsVal (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, bitsVal, ih]
  have hbitsOne : bitsVal (true :: List.replicate 119 false) = 1 := by
    rw [show bitsVal (true :: List.replicate 119 false) =
        1 + 2 * bitsVal (List.replicate 119 false) from rfl, hbitsZero]
  -- Deposit 1's own Transact witness: spends `note1` at position 0.
  let root0 : Term := treeRoot TreeDepth pool0.leaves
  let pathIn1 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut1 : Fin 1 → Term := fun _ => npk (Term.val self) 0
  let valueOut1 : Fin 1 → Nat := fun _ => amt1
  let pub_d1 : TransactPublic 1 1 :=
    { merkleRoot := root0, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey 0,
      commitmentsOut := fun _ => commitment (npkOut1 0) token (valueOut1 0) }
  let firstNote : CommitmentPreimage := ⟨npk (Term.val self) 0, token, amt1⟩
  -- Deposit 2's own Transact witness: spends `note2` at position 1.
  let pathIn2 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 1
  let npkOut2 : Fin 1 → Term := fun _ => npk (Term.val self) 1
  let valueOut2 : Fin 1 → Nat := fun _ => amt2
  let pub_d2 : TransactPublic 1 1 :=
    { merkleRoot := root0, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey 1,
      commitmentsOut := fun _ => commitment (npkOut2 0) token (valueOut2 0) }
  let secondNote : CommitmentPreimage := ⟨npk (Term.val self) 1, token, amt2⟩
  let g := genesis assets self pool0
  let mid0 : AdjudicatorState := { g with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub_d1) ∨ g.poolSignedBy pk' m' }
  have hsignstep1 : Step sig (consensusRelation sig) (Actor.pool publicKey) g
      (.signNote publicKey (msgHashOf pub_d1)) mid0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach0 : Reachable sig (consensusRelation sig) g mid0 :=
    reachable_step (reachable_refl sig (consensusRelation sig) g) hsignstep1
  have hsigned1 : mid0.poolSignedBy publicKey (msgHashOf pub_d1) := Or.inl ⟨rfl, rfl⟩
  obtain ⟨signature1, hveri1⟩ :=
    poolSigLive.eddsaCompleteness mid0.poolSignedBy publicKey (msgHashOf pub_d1) hsigned1
  let mid1 : AdjudicatorState := { mid0 with
    poolSignedBy := fun pk' m' => (pk' = publicKey ∧ m' = msgHashOf pub_d2) ∨ mid0.poolSignedBy pk' m' }
  have hsignstep2 : Step sig (consensusRelation sig) (Actor.pool publicKey) mid0
      (.signNote publicKey (msgHashOf pub_d2)) mid1 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp,
        show note1.value = bitsVal (true :: List.replicate 119 false) by
          rw [hbitsOne]; show shieldBase 0 amt1 = 1; decide⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
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
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp,
        show note2.value = bitsVal (true :: List.replicate 119 false) by
          rw [hbitsOne]; show shieldBase 0 amt2 = 1; decide⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note2.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amt2)))
        show fieldEq note2.value amt2
        show fieldEq (shieldBase 0 amt2) amt2
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri2 }
  have hRemove_d1 : removeAll (mid1.pool.live w_d1.token) (transactSpentPositions w_d1) =
      some [(1, note2)] := by
    show removeAll [(1, note2), (0, note1)] [(0, note1)] = some [(1, note2)]
    decide
  have hNullify_d1 : markSpent mid1.pool.spent (List.ofFn pub_d1.nullifiers) =
      some (List.ofFn pub_d1.nullifiers) := rfl
  have hidxrec_d1 : (pub_d1.commitmentsOut (0 : Fin 1),
      (⟨w_d1.npkOut 0, w_d1.token, w_d1.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d1 pub_d1 :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d1.token
        then withPositionsFrom mid1.pool.leaves.length (transactAllOutputs w_d1) ++ [(1, note2)]
        else mid1.pool.live t,
      spent := List.ofFn pub_d1.nullifiers,
      leaves := mid1.pool.leaves ++ (transactAllOutputs w_d1).map hashCommitment,
      roots := treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d1).map hashCommitment) ::
        mid1.pool.roots,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d1 pub_d1),
      ownedRandomOf := applyOwnedRecords mid1.pool.ownedRandomOf
        [(pub_d1.commitmentsOut (0 : Fin 1), (⟨self, 0⟩ : OwnedDisclosure))] },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some (2, pub_d1.commitmentsOut (0 : Fin 1)))) }
  have hCapacity_d1 : mid1.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show pool0.leaves.length + 1 ≤ 2 ^ TreeDepth
    show (2 : Nat) + 1 ≤ 2 ^ TreeDepth
    decide
  have hdstep1 : DepositStep mid1.pool self token amt1 w_d1 pub_d1 (0 : Fin 1) 2 mid2.pool :=
    ⟨0, rfl, rfl, rfl, by
      show 2 = mid1.pool.leaves.length + 0
      show (2 : Nat) = pool0.leaves.length + 0
      rfl,
      by decide, by decide, hC_d1, [(1, note2)], List.ofFn pub_d1.nullifiers,
      transactOutputRecords w_d1 pub_d1, hCapacity_d1,
      (by show root0 ∈ mid1.pool.roots; show root0 ∈ pool0.roots; exact List.mem_cons_self),
      hRemove_d1, hNullify_d1, List.Sublist.refl _, hidxrec_d1, rfl⟩
  have hstep_d1 : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amt1) mid2 := by
    refine ⟨rfl, rfl, channelId_not_external fp1, (by decide),
      ⟨1, 1, w_d1, pub_d1, 0, 2, mid2.pool, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep1
    · exact ⟨rfl, rfl⟩
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_d1
  have hheld2 : heldValue mid2 token cid = amt1 :=
    deposit_sets_heldValue sig (consensusRelation sig) (Actor.pool publicKey) mid1 mid2 cid 0
      token amt1 hstep_d1 rfl
  have hmid2holds : mid2.holdings token cid = some (2, pub_d1.commitmentsOut (0 : Fin 1)) := rfl
  have hdistinct : firstNote ≠ note2 := by
    intro h
    have hnpkeq : npk (Term.val self) 0 = npk (masterPublicKey publicKey nullifyingKey) 1 :=
      congrArg CommitmentPreimage.npk h
    have h01 := Term.val.inj (Term.hash2_inj hnpkeq).2
    simp at h01
  have hRemove_d2 : removeAll (mid2.pool.live w_d2.token) (transactSpentPositions w_d2) =
      some [(2, firstNote)] := by
    show removeAll [(2, firstNote), (1, note2)] [(1, note2)] = some [(2, firstNote)]
    decide
  have hNullify_d2 : markSpent mid2.pool.spent (List.ofFn pub_d2.nullifiers) =
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
      then withPositionsFrom mid2.pool.leaves.length (transactAllOutputs w_d2) ++ [(2, firstNote)]
      else mid2.pool.live t,
    spent := pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers,
    leaves := mid2.pool.leaves ++ (transactAllOutputs w_d2).map hashCommitment,
    roots := treeRoot TreeDepth (mid2.pool.leaves ++ (transactAllOutputs w_d2).map hashCommitment) ::
      mid2.pool.roots,
    preimageOf := applyRecords mid2.pool.preimageOf (transactOutputRecords w_d2 pub_d2),
    ownedRandomOf := applyOwnedRecords mid2.pool.ownedRandomOf
      [(pub_d2.commitmentsOut (0 : Fin 1), (⟨self, 1⟩ : OwnedDisclosure))] }
  have hCapacity_d2 : mid2.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show mid1.pool.leaves.length + 1 + 1 ≤ 2 ^ TreeDepth
    show pool0.leaves.length + 1 + 1 ≤ 2 ^ TreeDepth
    show (2 : Nat) + 1 + 1 ≤ 2 ^ TreeDepth
    decide
  have hdstep2 : DepositStep mid2.pool self token amt2 w_d2 pub_d2 (0 : Fin 1) 3 midPool2 :=
    ⟨1, rfl, rfl, rfl, by
      show 3 = mid2.pool.leaves.length + 0
      show (3 : Nat) = mid1.pool.leaves.length + 1 + 0
      show (3 : Nat) = pool0.leaves.length + 1 + 0
      rfl,
      by decide, by decide, hC_d2, [(2, firstNote)],
      pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers,
      transactOutputRecords w_d2 pub_d2, hCapacity_d2,
      (by
        show root0 ∈ mid2.pool.roots
        show root0 ∈ (treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d1).map
          hashCommitment) :: mid1.pool.roots)
        exact List.mem_cons_of_mem _ (show root0 ∈ pool0.roots from List.mem_cons_self)),
      hRemove_d2, hNullify_d2, List.Sublist.refl _, hidxrec_d2, rfl⟩
  -- The merge spends `firstNote`@2 and `secondNote`@3 in `midPool2`'s own tree.
  let rootM : Term := treeRoot TreeDepth midPool2.leaves
  let pathM : Fin 2 → List (Term × Bool) :=
    fun i => if i = 0 then treePath TreeDepth midPool2.leaves 2 else treePath TreeDepth midPool2.leaves 3
  let randomInM : Fin 2 → Nat := fun i => if i = 0 then 0 else 1
  let valueInM : Fin 2 → Nat := fun i => if i = 0 then amt1 else amt2
  let leavesIndicesM : Fin 2 → Nat := fun i => if i = 0 then (2 : Nat) else 3
  let npkOutM : Fin 1 → Term := fun _ => npk (Term.val self) 2
  let valueOutM : Fin 1 → Nat := fun _ => amt1 + amt2
  let w_m : TransactOwnedWitness 2 1 :=
    { token := token, randomIn := randomInM, valueIn := valueInM, pathElements := pathM,
      leavesIndices := leavesIndicesM, npkOut := npkOutM, valueOut := valueOutM }
  let pub_m : TransactOwnedPublic 2 1 :=
    { merkleRoot := rootM, boundParamsHash := 0,
      nullifiers := fun i => nullifier self (leavesIndicesM i),
      commitmentsOut := fun _ => commitment (npkOutM 0) token (valueOutM 0),
      ownerField := self }
  have hbitsTwo : bitsVal (false :: true :: List.replicate 118 false) = 2 := by
    rw [show bitsVal (false :: true :: List.replicate 118 false) =
        Bool.toNat false + 2 * (Bool.toNat true + 2 * bitsVal (List.replicate 118 false)) from rfl,
      hbitsZero]
    decide
  have hOC : OwnedConstrained w_m pub_m :=
    { pathLen := fun i => by
        match i with
        | 0 => exact treePath_length TreeDepth midPool2.leaves 2
        | 1 => exact treePath_length TreeDepth midPool2.leaves 3
      merkle := fun i => by
        match i with
        | 0 =>
          show merkleRoot (commitment (npk (Term.val self) 0) token amt1)
            (treePath TreeDepth midPool2.leaves 2) = rootM
          rw [show commitment (npk (Term.val self) 0) token amt1 = hashCommitment firstNote from rfl]
          exact treePath_correct TreeDepth midPool2.leaves 2 (by decide)
        | 1 =>
          show merkleRoot (commitment (npk (Term.val self) 1) token amt2)
            (treePath TreeDepth midPool2.leaves 3) = rootM
          rw [show commitment (npk (Term.val self) 1) token amt2 = hashCommitment secondNote from rfl]
          exact treePath_correct TreeDepth midPool2.leaves 3 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun i => by
        match i with
        | 0 => exact ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
        | 1 => exact ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      rangeOut := fun _ => ⟨false :: true :: List.replicate 118 false, by simp, hbitsTwo.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn valueInM)) (listSum (List.ofFn valueOutM))
        unfold fieldEq
        decide }
  have hNonZero_m : ¬ isZeroPreimage (⟨w_m.npkOut 0, w_m.token, w_m.valueOut 0⟩ : CommitmentPreimage) := by
    unfold isZeroPreimage
    intro ⟨_, hv, _⟩
    exact absurd (show valueOutM 0 = 0 from hv) (by decide)
  have hremove_m : removeAll (midPool2.live token) (ownedSpentPositions pub_m w_m) = some [] := by
    show removeAll [(3, secondNote), (2, firstNote)] [(2, firstNote), (3, secondNote)] = some []
    decide
  have hnullifier_ne : ∀ a b : Nat, a ≠ b → nullifier (0 : Nat) a ≠ nullifier 0 b := by
    intro a b hab heq
    exact hab (Term.val.inj (Term.hash2_inj heq).2)
  have hnotmem_m0 : pub_m.nullifiers (0 : Fin 2) ∉ midPool2.spent := by
    show nullifier self (leavesIndicesM 0) ∉
      (pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers)
    simp only [List.mem_cons, List.mem_ofFn, not_or]
    refine ⟨hnullifier_ne 2 1 (by decide), ?_⟩
    rintro ⟨i, hi⟩
    exact hnullifier_ne 2 0 (by decide) hi.symm
  have hnotmem_m1 : pub_m.nullifiers (1 : Fin 2) ∉ midPool2.spent := by
    show nullifier self (leavesIndicesM 1) ∉
      (pub_d2.nullifiers (0 : Fin 1) :: List.ofFn pub_d1.nullifiers)
    simp only [List.mem_cons, List.mem_ofFn, not_or]
    refine ⟨hnullifier_ne 3 1 (by decide), ?_⟩
    rintro ⟨i, hi⟩
    exact hnullifier_ne 3 0 (by decide) hi.symm
  have hne01 : pub_m.nullifiers (1 : Fin 2) ≠ pub_m.nullifiers (0 : Fin 2) :=
    hnullifier_ne 3 2 (by decide)
  have hmarkspent_m : markSpent midPool2.spent (List.ofFn pub_m.nullifiers) =
      some (pub_m.nullifiers (1 : Fin 2) :: pub_m.nullifiers (0 : Fin 2) :: midPool2.spent) := by
    show markSpent midPool2.spent [pub_m.nullifiers 0, pub_m.nullifiers 1] = _
    unfold markSpent
    rw [if_neg hnotmem_m0]
    unfold markSpent
    rw [if_neg (by
      simp only [List.mem_cons, not_or]
      exact ⟨hne01, hnotmem_m1⟩)]
    rfl
  let mergedCommitment : Term := commitment (npk (Term.val self) 2) token (amt1 + amt2)
  let s' : AdjudicatorState := { mid2 with
    pool := { midPool2 with
      live := fun t => if t = token
        then withPositionsFrom midPool2.leaves.length (ownedNewNotes w_m) ++ []
        else midPool2.live t,
      spent := pub_m.nullifiers (1 : Fin 2) :: pub_m.nullifiers (0 : Fin 2) :: midPool2.spent,
      leaves := midPool2.leaves ++ (ownedNewNotes w_m).map hashCommitment,
      roots := treeRoot TreeDepth (midPool2.leaves ++ (ownedNewNotes w_m).map hashCommitment) ::
        midPool2.roots,
      preimageOf := applyRecords midPool2.preimageOf (ownedOutputRecords w_m pub_m),
      ownedRandomOf := applyOwnedRecords midPool2.ownedRandomOf
        [(pub_m.commitmentsOut 0, (⟨self, 2⟩ : OwnedDisclosure))] },
    holdings := update mid2.holdings token (update (mid2.holdings token) cid (some (4, mergedCommitment))) }
  have hCapacity_m : midPool2.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show mid2.pool.leaves.length + 1 + 1 ≤ 2 ^ TreeDepth
    show mid1.pool.leaves.length + 1 + 1 + 1 ≤ 2 ^ TreeDepth
    show pool0.leaves.length + 1 + 1 + 1 ≤ 2 ^ TreeDepth
    show (2 : Nat) + 1 + 1 + 1 ≤ 2 ^ TreeDepth
    decide
  have hdstep_merge : DepositMergeStep midPool2 self token 2 (pub_d1.commitmentsOut (0 : Fin 1))
      3 (pub_d2.commitmentsOut (0 : Fin 1)) mergedCommitment 4 s'.pool :=
    ⟨by
      show (4 : Nat) = midPool2.leaves.length
      show (4 : Nat) = mid2.pool.leaves.length + 1
      show (4 : Nat) = mid1.pool.leaves.length + 1 + 1
      show (4 : Nat) = pool0.leaves.length + 1 + 1
      rfl,
      w_m, pub_m, hOC, [], pub_m.nullifiers (1 : Fin 2) :: pub_m.nullifiers (0 : Fin 2) :: midPool2.spent,
      2, 2, hNonZero_m, hCapacity_m, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      (by
        show rootM ∈ midPool2.roots
        exact List.mem_cons_self),
      hremove_m, hmarkspent_m, rfl, rfl⟩
  have hstep_d2 : Step sig (consensusRelation sig) (Actor.pool publicKey) mid2
      (.deposit cid amt1 token amt2) s' := by
    refine ⟨rfl, hheld2, channelId_not_external fp1, (by decide),
      ⟨1, 1, w_d2, pub_d2, 0, 3, midPool2, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep2
    · rw [hmid2holds]
      exact ⟨mergedCommitment, 4, hdstep_merge, rfl⟩
  have hreach3 : Reachable sig (consensusRelation sig) g s' :=
    reachable_step hreach2 hstep_d2
  have hinv2 : ∀ qasset qcid qpos qc, mid2.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, mid2.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc :=
    reachable_preserves
      (P := fun s => ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
        ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
      (by intro qasset qcid qpos qc hc; cases hc)
      (fun actor call s s' hP hstep => holdings_preimage_nonzero_step sig (consensusRelation sig)
        actor s s' call hP hstep)
      hreach2
  have hfinal : heldValue s' token cid = heldValue mid2 token cid + amt2 :=
    deposit_merge_sets_heldValue sig (consensusRelation sig) (Actor.pool publicKey) mid2 s' cid
      amt1 token amt2 hstep_d2 hinv2 2 (pub_d1.commitmentsOut (0 : Fin 1)) hmid2holds
  exact ⟨assets, self, pool0, mid1, mid2, s', cid, 0, amt1, token, amt1, amt2,
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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
      (challenger : Nat) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.challenge fp [] candidate challenger) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .challenge := by
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis
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
  refine ⟨assets, self, pool0, mid, s', fp, candidate, 0, Actor.nitro 0,
    _root_.Reachable.genesis, hreach, hstep, ?_⟩
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
      (s s' : AdjudicatorState) (cid : Term) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      (s.channels cid).finalizesAt > 0 ∧
      Step sig (consensusRelation sig) actor s (.tick (s.channels cid).finalizesAt) s' ∧
      (s'.channels cid).mode s'.now = .finalized := by
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis
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
  refine ⟨assets, self, pool0, s, s', channelId fp, Actor.nitro 0,
    _root_.Reachable.genesis, hreach, hfin, htickstep, ?_⟩
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
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s (.conclude fp candidate) s' ∧
      (s'.channels (channelId fp)).mode s'.now = .finalized := by
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
  let pool0 : PoolState := _root_.genesis
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
      { turnNumRecord := 0, finalizesAt := mid.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf candidate.outcome } }
  have hstep : Step sig (consensusRelation sig) (Actor.nitro 0) mid (.conclude fp candidate) s' := by
    refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [mid, g, genesis, ChannelStatus.mode, emptyStatus]
    · intro p hp
      exact absurd hp List.not_mem_nil
  refine ⟨assets, self, pool0, mid, s', fp, candidate, Actor.nitro 0,
    _root_.Reachable.genesis, hreach, hstep, ?_⟩
  show ((update mid.channels (channelId fp)
      { turnNumRecord := 0, finalizesAt := mid.now, stateHash := Term.val 0,
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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
      (outcome : Outcome) (indices : List Nat) (h : assetIndex < outcome.length)
      (dest : Allocation) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.transfer assetIndex cid claimedStateHash outcome indices) s' ∧
      dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations ∧
      0 < dest.amount ∧
      PoolIsLive s'.pool
        (commitment dest.destination (outcome.get ⟨assetIndex, h⟩).asset dest.amount) := by
  let self : Nat := 0
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let fp : FixedPart := ⟨[], 0, 0, 0⟩
  let cid : Term := channelId fp
  -- `pool0`: one real shield past the pool's own genesis, the depositor's own note.
  let note1 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amount⟩
  let pool0 : PoolState :=
    let leaves' := (_root_.genesis : PoolState).leaves ++ [hashCommitment note1]
    { (_root_.genesis : PoolState) with
        live := fun t => if t = token then (0, note1) :: (_root_.genesis : PoolState).live t
          else (_root_.genesis : PoolState).live t,
        held := fun t => if t = token then (_root_.genesis : PoolState).held t + note1.value
          else (_root_.genesis : PoolState).held t,
        leaves := leaves',
        roots := treeRoot TreeDepth leaves' :: (_root_.genesis : PoolState).roots,
        preimageOf := recordStep (_root_.genesis : PoolState).preimageOf (hashCommitment note1) note1 }
  have hNotPaused0 : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue0 : 0 < amount := by decide
  have hFeeBP0 : (0 : Nat) ≤ BASIS := by decide
  have hCapacity0 : (_root_.genesis : PoolState).leaves.length + 1 ≤ 2 ^ TreeDepth := by decide
  have hshield : _root_.Step (_root_.genesis : PoolState) pool0 :=
    _root_.Step.shield token amount 0 note1.npk hNotPaused0 hValue0 hFeeBP0 hCapacity0
  have hReachPool : _root_.Reachable pool0 :=
    _root_.Reachable.step _root_.Reachable.genesis hshield
  have hbitsZero : ∀ n, bitsVal (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, bitsVal, ih]
  have hbitsOne : bitsVal (true :: List.replicate 119 false) = 1 := by
    rw [show bitsVal (true :: List.replicate 119 false) =
        1 + 2 * bitsVal (List.replicate 119 false) from rfl, hbitsZero]
  let root1 : Term := treeRoot TreeDepth pool0.leaves
  let pathElements1 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut : Fin 1 → Term := fun _ => npk (Term.val self) 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let pub_d : TransactPublic 1 1 :=
    { merkleRoot := root1, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey 0,
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let depositedNote : CommitmentPreimage := ⟨npk (Term.val self) 0, token, amount⟩
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
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp,
        show note1.value = bitsVal (true :: List.replicate 119 false) by
          rw [hbitsOne]; show shieldBase 0 amount = 1; decide⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note1.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amount)))
        show fieldEq note1.value amount
        show fieldEq (shieldBase 0 amount) amount
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove_d : removeAll (mid1.pool.live w_d.token) (transactSpentPositions w_d) = some [] := by
    show removeAll [(0, note1)] [(0, note1)] = some []
    decide
  have hNullify_d : markSpent mid1.pool.spent (List.ofFn pub_d.nullifiers) =
      some (List.ofFn pub_d.nullifiers) := rfl
  have hidxrec_d : (pub_d.commitmentsOut (0 : Fin 1),
      (⟨w_d.npkOut 0, w_d.token, w_d.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d pub_d :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d.token
        then withPositionsFrom mid1.pool.leaves.length (transactAllOutputs w_d) ++
          ([] : List (Nat × CommitmentPreimage))
        else mid1.pool.live t,
      spent := List.ofFn pub_d.nullifiers,
      leaves := mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment,
      roots := treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment) ::
        mid1.pool.roots,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d pub_d),
      ownedRandomOf := applyOwnedRecords mid1.pool.ownedRandomOf
        [(pub_d.commitmentsOut (0 : Fin 1), (⟨self, 0⟩ : OwnedDisclosure))] },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some (1, pub_d.commitmentsOut (0 : Fin 1)))) }
  have hCapacity_d : mid1.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show pool0.leaves.length + 1 ≤ 2 ^ TreeDepth
    show (1 : Nat) + 1 ≤ 2 ^ TreeDepth
    decide
  have hdstep : DepositStep mid1.pool self token amount w_d pub_d (0 : Fin 1) 1 mid2.pool :=
    ⟨0, rfl, rfl, rfl, by
      show 1 = mid1.pool.leaves.length + 0
      show (1 : Nat) = pool0.leaves.length + 0
      rfl,
      by decide, by decide, hC_d, [], List.ofFn pub_d.nullifiers,
      transactOutputRecords w_d pub_d, hCapacity_d,
      (by show root1 ∈ mid1.pool.roots; show root1 ∈ pool0.roots; exact List.mem_cons_self),
      hRemove_d, hNullify_d, List.Sublist.refl _, hidxrec_d, rfl⟩
  have hstep_d : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amount) mid2 := by
    refine ⟨rfl, rfl, channelId_not_external fp, (by decide),
      ⟨1, 1, w_d, pub_d, 0, 1, mid2.pool, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
      exact absurd hp List.not_mem_nil
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
  -- The payout: a `PoolOwnedSpendStep` that spends `depositedNote`@1 in `mid4.pool`'s own tree.
  let rootT : Term := treeRoot TreeDepth mid4.pool.leaves
  let pathElements2 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth mid4.pool.leaves 1
  let ownerField : Nat := 0
  let randomIn2 : Fin 1 → Nat := fun _ => 0
  let valueIn2 : Fin 1 → Nat := fun _ => amount
  let leavesIndices2 : Fin 1 → Nat := fun _ => 1
  let npkOut2 : Fin 1 → Term := fun _ => dest.destination
  let valueOut2 : Fin 1 → Nat := fun _ => amount
  let pub_t : TransactOwnedPublic 1 1 :=
    { merkleRoot := rootT, boundParamsHash := 0,
      nullifiers := fun _ => nullifier ownerField (leavesIndices2 0),
      commitmentsOut := fun _ => commitment (npkOut2 0) token (valueOut2 0),
      ownerField := ownerField }
  let w_t : TransactOwnedWitness 1 1 :=
    { token := token, randomIn := randomIn2, valueIn := valueIn2, pathElements := pathElements2,
      leavesIndices := leavesIndices2, npkOut := npkOut2, valueOut := valueOut2 }
  have hOC : OwnedConstrained w_t pub_t :=
    { pathLen := fun _ => treePath_length TreeDepth mid4.pool.leaves 1
      merkle := fun _ => by
        rw [show commitment (npk (Term.val pub_t.ownerField) (w_t.randomIn 0)) w_t.token
          (w_t.valueIn 0) = hashCommitment depositedNote from rfl]
        exact treePath_correct TreeDepth mid4.pool.leaves 1 (by decide)
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
  have hRemove_t : removeAll (mid4.pool.live token) (ownedSpentPositions pub_t w_t) = some [] := by
    show removeAll [(1, depositedNote)] [(1, depositedNote)] = some []
    decide
  have hNullify_t : markSpent mid4.pool.spent (List.ofFn pub_t.nullifiers) =
      some (nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent) := by
    show markSpent [nullifier nullifyingKey 0] [nullifier ownerField (leavesIndices2 0)] =
      some (nullifier ownerField (leavesIndices2 0) :: [nullifier nullifyingKey 0])
    have hnullseparate : nullifier ownerField (leavesIndices2 0) ≠ nullifier nullifyingKey 0 := by
      intro heqn
      have := Term.val.inj (Term.hash2_inj heqn).2
      exact absurd this (by decide)
    unfold markSpent
    rw [if_neg (by simpa using hnullseparate)]
    rfl
  let s' : AdjudicatorState := { mid4 with
    pool := { mid4.pool with
      live := fun t => if t = token
        then withPositionsFrom mid4.pool.leaves.length [(⟨dest.destination, token, amount⟩ :
          CommitmentPreimage)] ++ [] else mid4.pool.live t,
      spent := nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent,
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
  have hcEq : mid4.holdings token cid = some (1, pub_d.commitmentsOut (0 : Fin 1)) := by
    show (update mid1.holdings token (update (mid1.holdings token) cid
      (some (1, pub_d.commitmentsOut (0 : Fin 1))))) token cid = some (1, pub_d.commitmentsOut (0 : Fin 1))
    unfold update
    rw [if_pos rfl, if_pos rfl]
  have hCapacity_t : mid4.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show mid1.pool.leaves.length + 1 + 1 ≤ 2 ^ TreeDepth
    show pool0.leaves.length + 1 + 1 ≤ 2 ^ TreeDepth
    show (1 : Nat) + 1 + 1 ≤ 2 ^ TreeDepth
    decide
  have hospend : PoolOwnedSpendStep mid4.pool self token (mid4.holdings token cid)
      [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] [] s'.pool := by
    rw [hcEq]
    refine ⟨w_t, pub_t, by decide, hOC, [], _, (fun j => j.elim0), hNonZero_t, hCapacity_t, rfl,
      rfl, rfl, rfl, rfl, ?_, hRemove_t, hNullify_t, (fun j => j.elim0), rfl⟩
    · show rootT ∈ mid4.pool.roots
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
    simp [Nat.sub_self, dest, amount]
    exact ⟨hospend, rfl, rfl⟩
  refine ⟨assets, self, pool0, mid4, s', 0, cid, Term.val 0, outcome, [], hassetIdx, dest,
    Actor.nitro 0, hReachPool, hreach4, hstep_t, ?_, ?_, ?_⟩
  · show dest ∈ [dest]
    exact List.mem_singleton_self _
  · decide
  · refine ⟨token, 2, ⟨dest.destination, token, amount⟩, ?_, rfl⟩
    show (2, (⟨dest.destination, token, amount⟩ : CommitmentPreimage)) ∈
      withPositionsFrom mid4.pool.leaves.length [(⟨dest.destination, token, amount⟩ :
        CommitmentPreimage)] ++ ([] : List (Nat × CommitmentPreimage))
    apply List.mem_append.mpr
    left
    have hlen : mid4.pool.leaves.length = 2 := by
      show mid1.pool.leaves.length + 1 = 2
      show pool0.leaves.length + 1 = 2
      show (1 : Nat) + 1 = 2
      rfl
    rw [hlen]
    simp [withPositionsFrom]


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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (sourceChannelId : Term) (sourceOutcome : Outcome)
      (sourceAssetIndex indexOfTargetInSource : Nat) (targetOutcome : Outcome)
      (targetAssetIndex : Nat) (claimedTargetStateHash : Term) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s (.reclaim sourceChannelId sourceOutcome
        sourceAssetIndex indexOfTargetInSource targetOutcome targetAssetIndex
        claimedTargetStateHash) s' ∧
      s'.channels sourceChannelId ≠ s.channels sourceChannelId := by
  let assets : Nat → Prop := fun _ => False
  let self : Nat := 0
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
  let g := genesis assets self pool0
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
      exact absurd hp List.not_mem_nil
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
    exact absurd hp List.not_mem_nil
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
  have hreach4 : Reachable sig (consensusRelation sig) g mid3 := hreach3
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
  exact ⟨assets, self, pool0, mid3, s', sourceChannelId, sourceOutcome, 0, 0, targetOutcome,
    0, Term.val 0, Actor.nitro 0, _root_.Reachable.genesis, hreach4, hstep_r, hneq⟩

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
  obtain ⟨hmode, hsh, hoh, newOutcome, hfold, hchan, _, _, _, _⟩ := hstep
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
  obtain ⟨hmode, hisFinal, hsigned, newOutcome, hfold, hchan, _, _, _, _, _⟩ := hstep
  exact ⟨hmode, hisFinal, hsigned, newOutcome, hfold, hchan⟩

set_option maxRecDepth 4000 in
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
    (poolSigLive : PoolSignatureLiveness)
    (ownedComplete : OwnedProofCompleteness) :
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s s' : AdjudicatorState) (fp : FixedPart) (candidate : VariablePart)
      (assetIndex : Nat) (h : assetIndex < candidate.outcome.length)
      (dest : Allocation) (actor : Actor),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.bulkConcludeAndTransferAllAssets fp candidate) s' ∧
      dest ∈ (candidate.outcome.get ⟨assetIndex, h⟩).allocations ∧
      0 < dest.amount ∧
      PoolIsLive s'.pool
        (commitment dest.destination (candidate.outcome.get ⟨assetIndex, h⟩).asset dest.amount) := by
  let self : Nat := 0
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 1
  let fp : FixedPart := ⟨[], 0, 0, 0⟩
  let cid : Term := channelId fp
  let note1 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amount⟩
  let pool0 : PoolState :=
    let leaves' := (_root_.genesis : PoolState).leaves ++ [hashCommitment note1]
    { (_root_.genesis : PoolState) with
        live := fun t => if t = token then (0, note1) :: (_root_.genesis : PoolState).live t
          else (_root_.genesis : PoolState).live t,
        held := fun t => if t = token then (_root_.genesis : PoolState).held t + note1.value
          else (_root_.genesis : PoolState).held t,
        leaves := leaves',
        roots := treeRoot TreeDepth leaves' :: (_root_.genesis : PoolState).roots,
        preimageOf := recordStep (_root_.genesis : PoolState).preimageOf (hashCommitment note1) note1 }
  have hNotPaused0 : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue0 : 0 < amount := by decide
  have hFeeBP0 : (0 : Nat) ≤ BASIS := by decide
  have hCapacity0 : (_root_.genesis : PoolState).leaves.length + 1 ≤ 2 ^ TreeDepth := by decide
  have hshield : _root_.Step (_root_.genesis : PoolState) pool0 :=
    _root_.Step.shield token amount 0 note1.npk hNotPaused0 hValue0 hFeeBP0 hCapacity0
  have hReachPool : _root_.Reachable pool0 :=
    _root_.Reachable.step _root_.Reachable.genesis hshield
  have hbitsZero : ∀ n, bitsVal (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, bitsVal, ih]
  have hbitsOne : bitsVal (true :: List.replicate 119 false) = 1 := by
    rw [show bitsVal (true :: List.replicate 119 false) =
        1 + 2 * bitsVal (List.replicate 119 false) from rfl, hbitsZero]
  let root1 : Term := treeRoot TreeDepth pool0.leaves
  let pathElements1 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut : Fin 1 → Term := fun _ => npk (Term.val self) 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let pub_d : TransactPublic 1 1 :=
    { merkleRoot := root1, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey 0,
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let depositedNote : CommitmentPreimage := ⟨npk (Term.val self) 0, token, amount⟩
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
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp,
        show note1.value = bitsVal (true :: List.replicate 119 false) by
          rw [hbitsOne]; show shieldBase 0 amount = 1; decide⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note1.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amount)))
        show fieldEq note1.value amount
        show fieldEq (shieldBase 0 amount) amount
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove_d : removeAll (mid1.pool.live w_d.token) (transactSpentPositions w_d) = some [] := by
    show removeAll [(0, note1)] [(0, note1)] = some []
    decide
  have hNullify_d : markSpent mid1.pool.spent (List.ofFn pub_d.nullifiers) =
      some (List.ofFn pub_d.nullifiers) := rfl
  have hidxrec_d : (pub_d.commitmentsOut (0 : Fin 1),
      (⟨w_d.npkOut 0, w_d.token, w_d.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d pub_d :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d.token
        then withPositionsFrom mid1.pool.leaves.length (transactAllOutputs w_d) ++
          ([] : List (Nat × CommitmentPreimage))
        else mid1.pool.live t,
      spent := List.ofFn pub_d.nullifiers,
      leaves := mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment,
      roots := treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment) ::
        mid1.pool.roots,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d pub_d),
      ownedRandomOf := applyOwnedRecords mid1.pool.ownedRandomOf
        [(pub_d.commitmentsOut (0 : Fin 1), (⟨self, 0⟩ : OwnedDisclosure))] },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some (1, pub_d.commitmentsOut (0 : Fin 1)))) }
  have hCapacity_d : mid1.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show pool0.leaves.length + 1 ≤ 2 ^ TreeDepth
    show (1 : Nat) + 1 ≤ 2 ^ TreeDepth
    decide
  have hdstep : DepositStep mid1.pool self token amount w_d pub_d (0 : Fin 1) 1 mid2.pool :=
    ⟨0, rfl, rfl, rfl, by
      show 1 = mid1.pool.leaves.length + 0
      show (1 : Nat) = pool0.leaves.length + 0
      rfl,
      by decide, by decide, hC_d, [], List.ofFn pub_d.nullifiers,
      transactOutputRecords w_d pub_d, hCapacity_d,
      (by show root1 ∈ mid1.pool.roots; show root1 ∈ pool0.roots; exact List.mem_cons_self),
      hRemove_d, hNullify_d, List.Sublist.refl _, hidxrec_d, rfl⟩
  have hstep_d : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amount) mid2 := by
    refine ⟨rfl, rfl, channelId_not_external fp, (by decide),
      ⟨1, 1, w_d, pub_d, 0, 1, mid2.pool, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
  let ownerField : Nat := 0
  let randomIn2 : Fin 1 → Nat := fun _ => 0
  let valueIn2 : Fin 1 → Nat := fun _ => amount
  let leavesIndices2 : Fin 1 → Nat := fun _ => 1
  let npkOut2 : Fin 1 → Term := fun _ => dest.destination
  let valueOut2 : Fin 1 → Nat := fun _ => amount
  let pub_t : TransactOwnedPublic 1 1 :=
    { merkleRoot := rootT, boundParamsHash := 0,
      nullifiers := fun _ => nullifier ownerField (leavesIndices2 0),
      commitmentsOut := fun _ => commitment (npkOut2 0) token (valueOut2 0),
      ownerField := ownerField }
  let w_t : TransactOwnedWitness 1 1 :=
    { token := token, randomIn := randomIn2, valueIn := valueIn2, pathElements := pathElements2,
      leavesIndices := leavesIndices2, npkOut := npkOut2, valueOut := valueOut2 }
  have hOC : OwnedConstrained w_t pub_t :=
    { pathLen := fun _ => treePath_length TreeDepth mid3.pool.leaves 1
      merkle := fun _ => by
        rw [show commitment (npk (Term.val pub_t.ownerField) (w_t.randomIn 0)) w_t.token
          (w_t.valueIn 0) = hashCommitment depositedNote from rfl]
        exact treePath_correct TreeDepth mid3.pool.leaves 1 (by decide)
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
  have hRemove_t : removeAll (mid3.pool.live token) (ownedSpentPositions pub_t w_t) = some [] := by
    show removeAll [(1, depositedNote)] [(1, depositedNote)] = some []
    decide
  have hNullify_t : markSpent mid3.pool.spent (List.ofFn pub_t.nullifiers) =
      some (nullifier ownerField (leavesIndices2 0) :: mid3.pool.spent) := by
    show markSpent [nullifier nullifyingKey 0] [nullifier ownerField (leavesIndices2 0)] =
      some (nullifier ownerField (leavesIndices2 0) :: [nullifier nullifyingKey 0])
    have hnullseparate : nullifier ownerField (leavesIndices2 0) ≠ nullifier nullifyingKey 0 := by
      intro heqn
      have := Term.val.inj (Term.hash2_inj heqn).2
      exact absurd this (by decide)
    unfold markSpent
    rw [if_neg (by simpa using hnullseparate)]
    rfl
  let s' : AdjudicatorState := { mid3 with
    pool := { mid3.pool with
      live := fun t => if t = token
        then withPositionsFrom mid3.pool.leaves.length [(⟨dest.destination, token, amount⟩ :
          CommitmentPreimage)] ++ [] else mid3.pool.live t,
      spent := nullifier ownerField (leavesIndices2 0) :: mid3.pool.spent,
      leaves := mid3.pool.leaves ++ [commitment dest.destination token amount],
      roots := treeRoot TreeDepth (mid3.pool.leaves ++ [commitment dest.destination token amount]) ::
        mid3.pool.roots,
      preimageOf := applyRecords mid3.pool.preimageOf (ownedOutputRecords w_t pub_t),
      ownedRandomOf := mid3.pool.ownedRandomOf },
    holdings := update mid3.holdings token (update (mid3.holdings token) cid none),
    channels := update mid3.channels cid
      { turnNumRecord := 0, finalizesAt := mid3.now, stateHash := Term.val 0,
        outcomeHash := outcomeHashOf [(⟨token, [{ dest with amount := 0 }]⟩ : SingleAssetExit)] } }
  have hcEq : mid3.holdings token cid = some (1, pub_d.commitmentsOut (0 : Fin 1)) := by
    show (update mid1.holdings token (update (mid1.holdings token) cid
      (some (1, pub_d.commitmentsOut (0 : Fin 1))))) token cid = some (1, pub_d.commitmentsOut (0 : Fin 1))
    unfold update
    rw [if_pos rfl, if_pos rfl]
  have hCapacity_t : mid3.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show mid1.pool.leaves.length + 1 + 1 ≤ 2 ^ TreeDepth
    show pool0.leaves.length + 1 + 1 ≤ 2 ^ TreeDepth
    show (1 : Nat) + 1 + 1 ≤ 2 ^ TreeDepth
    decide
  have hospend : PoolOwnedSpendStep mid3.pool self token (mid3.holdings token cid)
      [(⟨dest.destination, token, amount⟩ : CommitmentPreimage)] [] s'.pool := by
    rw [hcEq]
    refine ⟨w_t, pub_t, by decide, hOC, [], _, (fun j => j.elim0), hNonZero_t, hCapacity_t, rfl,
      rfl, rfl, rfl, rfl, ?_, hRemove_t, hNullify_t, (fun j => j.elim0), rfl⟩
    · show rootT ∈ mid3.pool.roots
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
    intro held
    simp [transferEffects, afford, dest]
  have hfold : bulkTransferFold self cid outcome mid3.pool mid3.holdings
      [(⟨token, [{ dest with amount := 0 }]⟩ : SingleAssetExit)] s'.pool s'.holdings := by
    exact ⟨hguarantee_check _, rfl, 0, s'.pool, hospend, rfl, rfl⟩
  have hstep_bulk : Step sig (consensusRelation sig) (Actor.nitro 0) mid3
      (.bulkConcludeAndTransferAllAssets fp candidate) s' := by
    refine ⟨hnotfinalized, rfl, ?_, [(⟨token, [{ dest with amount := 0 }]⟩ : SingleAssetExit)],
      hfold, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro p hp
    exact absurd hp List.not_mem_nil
  refine ⟨assets, self, pool0, mid3, s', fp, candidate, 0, hassetIdx, dest,
    Actor.nitro 0, hReachPool, hreach3, hstep_bulk, ?_, ?_, ?_⟩
  · show dest ∈ [dest]
    exact List.mem_singleton_self _
  · decide
  · refine ⟨token, 2, ⟨dest.destination, token, amount⟩, ?_, rfl⟩
    show (2, (⟨dest.destination, token, amount⟩ : CommitmentPreimage)) ∈
      withPositionsFrom mid3.pool.leaves.length [(⟨dest.destination, token, amount⟩ :
        CommitmentPreimage)] ++ ([] : List (Nat × CommitmentPreimage))
    apply List.mem_append.mpr
    left
    have hlen : mid3.pool.leaves.length = 2 := by
      show mid1.pool.leaves.length + 1 = 2
      show pool0.leaves.length + 1 = 2
      show (1 : Nat) + 1 = 2
      rfl
    rw [hlen]
    simp [withPositionsFrom]

set_option maxRecDepth 4000 in
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
    ∃ (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
      (s mid s' : AdjudicatorState) (assetIndex : Nat)
      (cid claimedStateHash claimedStateHash' : Term)
      (outcome outcome1 : Outcome) (actor actor' : Actor)
      (h : assetIndex < outcome.length) (h1 : assetIndex < outcome1.length)
      (dest1 dest2 : Allocation),
      _root_.Reachable pool0 ∧
      Reachable sig (consensusRelation sig) (genesis assets self pool0) s ∧
      Step sig (consensusRelation sig) actor s
        (.transfer assetIndex cid claimedStateHash outcome [0]) mid ∧
      dest1 ∈ (outcome.get ⟨assetIndex, h⟩).allocations ∧ 0 < dest1.amount ∧
      heldValue mid (outcome1.get ⟨assetIndex, h1⟩).asset cid ≠ 0 ∧
      Step sig (consensusRelation sig) actor' mid
        (.transfer assetIndex cid claimedStateHash' outcome1 [1]) s' ∧
      dest2 ∈ (outcome1.get ⟨assetIndex, h1⟩).allocations ∧ 0 < dest2.amount ∧
      PoolIsLive s'.pool
        (commitment dest2.destination (outcome1.get ⟨assetIndex, h1⟩).asset dest2.amount) := by
  let self : Nat := 0
  let publicKey : Nat × Nat := (0, 0)
  let nullifyingKey : Nat := 0
  let token : Nat := 0
  let assets : Nat → Prop := fun a => a = token
  let amount : Nat := 2
  let fp : FixedPart := ⟨[], 0, 0, 0⟩
  let cid : Term := channelId fp
  let note1 : CommitmentPreimage :=
    ⟨npk (masterPublicKey publicKey nullifyingKey) 0, token, shieldBase 0 amount⟩
  let pool0 : PoolState :=
    let leaves' := (_root_.genesis : PoolState).leaves ++ [hashCommitment note1]
    { (_root_.genesis : PoolState) with
        live := fun t => if t = token then (0, note1) :: (_root_.genesis : PoolState).live t
          else (_root_.genesis : PoolState).live t,
        held := fun t => if t = token then (_root_.genesis : PoolState).held t + note1.value
          else (_root_.genesis : PoolState).held t,
        leaves := leaves',
        roots := treeRoot TreeDepth leaves' :: (_root_.genesis : PoolState).roots,
        preimageOf := recordStep (_root_.genesis : PoolState).preimageOf (hashCommitment note1) note1 }
  have hNotPaused0 : (_root_.genesis : PoolState).shieldsPaused = false := rfl
  have hValue0 : 0 < amount := by decide
  have hFeeBP0 : (0 : Nat) ≤ BASIS := by decide
  have hCapacity0 : (_root_.genesis : PoolState).leaves.length + 1 ≤ 2 ^ TreeDepth := by decide
  have hshield : _root_.Step (_root_.genesis : PoolState) pool0 :=
    _root_.Step.shield token amount 0 note1.npk hNotPaused0 hValue0 hFeeBP0 hCapacity0
  have hReachPool : _root_.Reachable pool0 :=
    _root_.Reachable.step _root_.Reachable.genesis hshield
  have hbitsZero : ∀ n, bitsVal (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, bitsVal, ih]
  have hbitsOne : bitsVal (true :: List.replicate 119 false) = 1 := by
    rw [show bitsVal (true :: List.replicate 119 false) =
        1 + 2 * bitsVal (List.replicate 119 false) from rfl, hbitsZero]
  let root1 : Term := treeRoot TreeDepth pool0.leaves
  let pathElements1 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth pool0.leaves 0
  let npkOut : Fin 1 → Term := fun _ => npk (Term.val self) 0
  let valueOut : Fin 1 → Nat := fun _ => amount
  let pub_d : TransactPublic 1 1 :=
    { merkleRoot := root1, boundParamsHash := 0,
      nullifiers := fun _ => nullifier nullifyingKey 0,
      commitmentsOut := fun _ => commitment (npkOut 0) token (valueOut 0) }
  let depositedNote : CommitmentPreimage := ⟨npk (Term.val self) 0, token, amount⟩
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
  have hbitsOne118 : bitsVal (true :: List.replicate 118 false) = 1 := by
    rw [show bitsVal (true :: List.replicate 118 false) =
        1 + 2 * bitsVal (List.replicate 118 false) from rfl, hbitsZero]
  have hbitsTwo : bitsVal (false :: true :: List.replicate 118 false) = 2 := by
    rw [show bitsVal (false :: true :: List.replicate 118 false) =
        0 + 2 * bitsVal (true :: List.replicate 118 false) from rfl, hbitsOne118]
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
      rangeIn := fun _ => ⟨false :: true :: List.replicate 118 false, by simp,
        show note1.value = bitsVal (false :: true :: List.replicate 118 false) by
          rw [hbitsTwo]; show shieldBase 0 amount = 2; decide⟩
      rangeOut := fun _ => ⟨false :: true :: List.replicate 118 false, by simp, hbitsTwo.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => note1.value)))
          (listSum (List.ofFn (fun _ : Fin 1 => amount)))
        show fieldEq note1.value amount
        show fieldEq (shieldBase 0 amount) amount
        unfold fieldEq
        decide
      distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
      sig := hveri }
  have hRemove_d : removeAll (mid1.pool.live w_d.token) (transactSpentPositions w_d) = some [] := by
    show removeAll [(0, note1)] [(0, note1)] = some []
    decide
  have hNullify_d : markSpent mid1.pool.spent (List.ofFn pub_d.nullifiers) =
      some (List.ofFn pub_d.nullifiers) := rfl
  have hidxrec_d : (pub_d.commitmentsOut (0 : Fin 1),
      (⟨w_d.npkOut 0, w_d.token, w_d.valueOut 0⟩ : CommitmentPreimage)) ∈
      transactOutputRecords w_d pub_d :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  let mid2 : AdjudicatorState := { mid1 with
    pool := { mid1.pool with
      live := fun t => if t = w_d.token
        then withPositionsFrom mid1.pool.leaves.length (transactAllOutputs w_d) ++
          ([] : List (Nat × CommitmentPreimage))
        else mid1.pool.live t,
      spent := List.ofFn pub_d.nullifiers,
      leaves := mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment,
      roots := treeRoot TreeDepth (mid1.pool.leaves ++ (transactAllOutputs w_d).map hashCommitment) ::
        mid1.pool.roots,
      preimageOf := applyRecords mid1.pool.preimageOf (transactOutputRecords w_d pub_d),
      ownedRandomOf := applyOwnedRecords mid1.pool.ownedRandomOf
        [(pub_d.commitmentsOut (0 : Fin 1), (⟨self, 0⟩ : OwnedDisclosure))] },
    holdings := update mid1.holdings token (update (mid1.holdings token) cid
      (some (1, pub_d.commitmentsOut (0 : Fin 1)))) }
  have hCapacity_d : mid1.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show pool0.leaves.length + 1 ≤ 2 ^ TreeDepth
    show (1 : Nat) + 1 ≤ 2 ^ TreeDepth
    decide
  have hdstep : DepositStep mid1.pool self token amount w_d pub_d (0 : Fin 1) 1 mid2.pool :=
    ⟨0, rfl, rfl, rfl, by
      show 1 = mid1.pool.leaves.length + 0
      show (1 : Nat) = pool0.leaves.length + 0
      rfl,
      by decide, by decide, hC_d, [], List.ofFn pub_d.nullifiers,
      transactOutputRecords w_d pub_d, hCapacity_d,
      (by show root1 ∈ mid1.pool.roots; show root1 ∈ pool0.roots; exact List.mem_cons_self),
      hRemove_d, hNullify_d, List.Sublist.refl _, hidxrec_d, rfl⟩
  have hstep_d : Step sig (consensusRelation sig) (Actor.pool publicKey) mid1
      (.deposit cid 0 token amount) mid2 := by
    refine ⟨rfl, rfl, channelId_not_external fp, (by decide),
      ⟨1, 1, w_d, pub_d, 0, 1, mid2.pool, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hdstep
    · exact ⟨rfl, rfl⟩
  have hreach2 : Reachable sig (consensusRelation sig) g mid2 :=
    reachable_step hreach1 hstep_d
  let mid3 : AdjudicatorState := { mid2 with now := 1 }
  have hstep_tick : Step sig (consensusRelation sig) (Actor.nitro 0) mid2 (.tick 1) mid3 :=
    ⟨Nat.zero_le 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreach3 : Reachable sig (consensusRelation sig) g mid3 :=
    reachable_step hreach2 hstep_tick
  let recipientPK1 : Nat × Nat := (2, 2)
  let recipientNK1 : Nat := 2
  let dest1 : Allocation :=
    ⟨npk (masterPublicKey recipientPK1 recipientNK1) 0, 1, .simple, 0⟩
  let recipientPK2 : Nat × Nat := (3, 3)
  let recipientNK2 : Nat := 3
  let dest2 : Allocation :=
    ⟨npk (masterPublicKey recipientPK2 recipientNK2) 0, 1, .simple, 0⟩
  let outcome : Outcome := [⟨token, [dest1, dest2]⟩]
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
      exact absurd hp List.not_mem_nil
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
  -- First transfer: pays dest1 out of the deposited note, leaving a
  -- nonzero remainder note worth dest2.amount.
  let rootT : Term := treeRoot TreeDepth mid4.pool.leaves
  let pathElements2 : Fin 1 → List (Term × Bool) := fun _ => treePath TreeDepth mid4.pool.leaves 1
  let ownerField : Nat := 0
  let randomIn2 : Fin 1 → Nat := fun _ => 0
  let valueIn2 : Fin 1 → Nat := fun _ => amount
  let leavesIndices2 : Fin 1 → Nat := fun _ => 1
  let r1 : Nat := 1
  let npkOut2 : Fin 2 → Term := fun j => if j = 0 then dest1.destination else npk (Term.val self) r1
  let valueOut2 : Fin 2 → Nat := fun j => if j = 0 then dest1.amount else 1
  let pub_t1 : TransactOwnedPublic 1 2 :=
    { merkleRoot := rootT, boundParamsHash := 0,
      nullifiers := fun _ => nullifier ownerField (leavesIndices2 0),
      commitmentsOut := fun j => commitment (npkOut2 j) token (valueOut2 j),
      ownerField := ownerField }
  let w_t1 : TransactOwnedWitness 1 2 :=
    { token := token, randomIn := randomIn2, valueIn := valueIn2, pathElements := pathElements2,
      leavesIndices := leavesIndices2, npkOut := npkOut2, valueOut := valueOut2 }
  have hOC1 : OwnedConstrained w_t1 pub_t1 :=
    { pathLen := fun _ => treePath_length TreeDepth mid4.pool.leaves 1
      merkle := fun _ => by
        rw [show commitment (npk (Term.val pub_t1.ownerField) (w_t1.randomIn 0)) w_t1.token
          (w_t1.valueIn 0) = hashCommitment depositedNote from rfl]
        exact treePath_correct TreeDepth mid4.pool.leaves 1 (by decide)
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => ⟨false :: true :: List.replicate 118 false, by simp, hbitsTwo.symm⟩
      rangeOut := fun j => by
        match j with
        | 0 => exact ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
        | 1 => exact ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => amount)))
          (listSum (List.ofFn valueOut2))
        show fieldEq amount (listSum (List.ofFn valueOut2))
        unfold fieldEq
        decide }
  have hNonZero_t1 : ∀ j : Fin 2, ¬ isZeroPreimage
      (⟨w_t1.npkOut j, w_t1.token, w_t1.valueOut j⟩ : CommitmentPreimage) := by
    intro j hz
    have hcase : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
    rcases hcase with hv | hv
    · have hj0 : j = 0 := Fin.ext hv
      rw [hj0] at hz
      have h1 : dest1.amount = 0 := hz.2.1
      simp [dest1] at h1
    · have hj1 : j = 1 := Fin.ext hv
      rw [hj1] at hz
      have h1 : (1 : Nat) = 0 := hz.2.1
      omega
  have hCapacity_t1 : mid4.pool.leaves.length + 2 ≤ 2 ^ TreeDepth := by
    show mid1.pool.leaves.length + 1 + 2 ≤ 2 ^ TreeDepth
    show pool0.leaves.length + 1 + 2 ≤ 2 ^ TreeDepth
    show (1 : Nat) + 1 + 2 ≤ 2 ^ TreeDepth
    decide
  have hcEq4 : mid4.holdings token cid = some (1, pub_d.commitmentsOut (0 : Fin 1)) := by
    show (update mid1.holdings token (update (mid1.holdings token) cid
      (some (1, pub_d.commitmentsOut (0 : Fin 1))))) token cid = some (1, pub_d.commitmentsOut (0 : Fin 1))
    unfold update
    rw [if_pos rfl, if_pos rfl]
  have hRemove_t1 : removeAll (mid4.pool.live token) (ownedSpentPositions pub_t1 w_t1) = some [] := by
    show removeAll [(1, depositedNote)] [(1, depositedNote)] = some []
    decide
  have hNullify_t1 : markSpent mid4.pool.spent (List.ofFn pub_t1.nullifiers) =
      some (nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent) := by
    show markSpent [nullifier nullifyingKey 0] [nullifier ownerField (leavesIndices2 0)] =
      some (nullifier ownerField (leavesIndices2 0) :: [nullifier nullifyingKey 0])
    have hnullseparate : nullifier ownerField (leavesIndices2 0) ≠ nullifier nullifyingKey 0 := by
      intro heqn
      have := Term.val.inj (Term.hash2_inj heqn).2
      exact absurd this (by decide)
    unfold markSpent
    rw [if_neg (by simpa using hnullseparate)]
    rfl
  let dest1Note : CommitmentPreimage := ⟨dest1.destination, token, 1⟩
  let remainderNote : CommitmentPreimage := ⟨npk (Term.val self) r1, token, 1⟩
  let mid5 : AdjudicatorState := { mid4 with
    pool := { mid4.pool with
      live := fun t => if t = token
        then withPositionsFrom mid4.pool.leaves.length [dest1Note, remainderNote] ++
          ([] : List (Nat × CommitmentPreimage))
        else mid4.pool.live t,
      spent := nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent,
      leaves := mid4.pool.leaves ++ [commitment dest1.destination token 1,
        commitment (npk (Term.val self) r1) token 1],
      roots := treeRoot TreeDepth (mid4.pool.leaves ++ [commitment dest1.destination token 1,
        commitment (npk (Term.val self) r1) token 1]) :: mid4.pool.roots,
      preimageOf := applyRecords mid4.pool.preimageOf (ownedOutputRecords w_t1 pub_t1),
      ownedRandomOf := applyOwnedRecords mid4.pool.ownedRandomOf
        [(pub_t1.commitmentsOut (1 : Fin 2), (⟨ownerField, r1⟩ : OwnedDisclosure))] },
    holdings := update mid4.holdings token (update (mid4.holdings token) cid
      (some (mid4.pool.leaves.length + 1, commitment (npk (Term.val self) r1) token 1))),
    channels := update mid4.channels cid
      { mid4.channels cid with
        outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
          if i ≠ 0 then exit else { exit with allocations := [{ dest1 with amount := 0 }, dest2] }) } }
  have hospend1 : PoolOwnedSpendStep mid4.pool self token (mid4.holdings token cid)
      [dest1Note] [remainderNote] mid5.pool := by
    rw [hcEq4]
    refine ⟨w_t1, pub_t1, by decide, hOC1, [], _, (fun _ => r1), hNonZero_t1, hCapacity_t1, rfl,
      rfl, rfl, rfl, rfl, ?_, hRemove_t1, hNullify_t1,
      (fun j => by
        obtain ⟨jv, hjv⟩ := j
        have hjv0 : jv = 0 := by simp at hjv; omega
        subst hjv0
        rfl), rfl⟩
    · show rootT ∈ mid4.pool.roots
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
  have htransferEffects1 : transferEffects [dest1, dest2] amount [0] =
      ([{ dest1 with amount := 0 }, dest2], [dest1], 1) := by
    unfold transferEffects afford
    decide
  have hstep_t1 : Step sig (consensusRelation sig) (Actor.nitro 0) mid4
      (.transfer 0 cid (Term.val 0) outcome [0]) mid5 := by
    refine ⟨hassetIdx, hfinalized, hstateHash, houtcomeHash, trivial, ?_, rfl, rfl, rfl, rfl, rfl⟩
    have hget : outcome.get ⟨0, hassetIdx⟩ = ⟨token, [dest1, dest2]⟩ := rfl
    rw [hget, hheld4, htransferEffects1]
    refine ⟨by decide, r1, ?_⟩
    simp only [Nat.sub_self]
    exact ⟨hospend1, rfl, rfl⟩
  -- Second transfer: spends the remainder note, paying dest2. The
  -- random comes back from `mid5.pool.ownedRandomOf`'s own public
  -- lookup, not from the first call's own local `r1`.
  have hOwnedRandom : mid5.pool.ownedRandomOf
      (commitment (npk (Term.val self) r1) token 1) = some ⟨ownerField, r1⟩ := by
    show recordOwnedStep mid4.pool.ownedRandomOf
      (pub_t1.commitmentsOut (1 : Fin 2)) (⟨ownerField, r1⟩ : OwnedDisclosure)
      (commitment (npk (Term.val self) r1) token 1) = some ⟨ownerField, r1⟩
    unfold recordOwnedStep
    exact if_pos rfl
  have hmid4Len : mid4.pool.leaves.length = 2 := by
    show mid1.pool.leaves.length + 1 = 2
    show pool0.leaves.length + 1 = 2
    show (1 : Nat) + 1 = 2
    rfl
  let remainderPos : Nat := mid4.pool.leaves.length + 1
  have hRemainderPosVal : remainderPos = 3 := by
    show mid4.pool.leaves.length + 1 = 3
    rw [hmid4Len]
  have hRemainderPosRange : remainderPos < 2 ^ TreeDepth := by
    rw [hRemainderPosVal]
    decide
  let pathElements3 : Fin 1 → List (Term × Bool) :=
    fun _ => treePath TreeDepth mid5.pool.leaves remainderPos
  let randomIn3 : Fin 1 → Nat := fun _ => r1
  let valueIn3 : Fin 1 → Nat := fun _ => 1
  let leavesIndices3 : Fin 1 → Nat := fun _ => remainderPos
  let npkOut3 : Fin 1 → Term := fun _ => dest2.destination
  let valueOut3 : Fin 1 → Nat := fun _ => dest2.amount
  let rootT2 : Term := treeRoot TreeDepth mid5.pool.leaves
  let pub_t2 : TransactOwnedPublic 1 1 :=
    { merkleRoot := rootT2, boundParamsHash := 0,
      nullifiers := fun _ => nullifier ownerField remainderPos,
      commitmentsOut := fun _ => commitment (npkOut3 0) token (valueOut3 0),
      ownerField := ownerField }
  let w_t2 : TransactOwnedWitness 1 1 :=
    { token := token, randomIn := randomIn3, valueIn := valueIn3, pathElements := pathElements3,
      leavesIndices := leavesIndices3, npkOut := npkOut3, valueOut := valueOut3 }
  have hOC2 : OwnedConstrained w_t2 pub_t2 :=
    { pathLen := fun _ => treePath_length TreeDepth mid5.pool.leaves remainderPos
      merkle := fun _ => by
        rw [show commitment (npk (Term.val pub_t2.ownerField) (w_t2.randomIn 0)) w_t2.token
          (w_t2.valueIn 0) = commitment (npk (Term.val self) r1) token 1 from rfl]
        show merkleRoot (commitment (npk (Term.val self) r1) token 1)
          (treePath TreeDepth mid5.pool.leaves remainderPos) = rootT2
        rw [show commitment (npk (Term.val self) r1) token 1 =
          mid5.pool.leaves.getD remainderPos (Term.val 0) from rfl]
        exact treePath_correct TreeDepth mid5.pool.leaves remainderPos hRemainderPosRange
      nullifiers := fun _ => rfl
      outputs := fun _ => rfl
      rangeIn := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      rangeOut := fun _ => ⟨true :: List.replicate 119 false, by simp, hbitsOne.symm⟩
      balance := by
        show fieldEq (listSum (List.ofFn (fun _ : Fin 1 => (1 : Nat))))
          (listSum (List.ofFn valueOut3))
        show fieldEq 1 (listSum (List.ofFn valueOut3))
        unfold fieldEq
        decide }
  have hNonZero_t2 : ∀ j : Fin 1, ¬ isZeroPreimage
      (⟨w_t2.npkOut j, w_t2.token, w_t2.valueOut j⟩ : CommitmentPreimage) := by
    intro j hz
    have h1 : dest2.amount = 0 := hz.2.1
    simp [dest2] at h1
  have hCapacity_t2 : mid5.pool.leaves.length + 1 ≤ 2 ^ TreeDepth := by
    show (mid4.pool.leaves ++ [commitment dest1.destination token 1,
      commitment (npk (Term.val self) r1) token 1]).length + 1 ≤ 2 ^ TreeDepth
    rw [List.length_append, hmid4Len]
    decide
  have hc5Eq : mid5.holdings token cid = some (remainderPos,
      commitment (npk (Term.val self) r1) token 1) := by
    show (update mid4.holdings token (update (mid4.holdings token) cid
      (some (mid4.pool.leaves.length + 1, commitment (npk (Term.val self) r1) token 1))))
      token cid = some (remainderPos, commitment (npk (Term.val self) r1) token 1)
    unfold update
    rw [if_pos rfl, if_pos rfl]
  have hRemove_t2 : removeAll (mid5.pool.live token)
      (ownedSpentPositions pub_t2 w_t2) = some [(mid4.pool.leaves.length, dest1Note)] := by
    show removeAll [(mid4.pool.leaves.length, dest1Note), (remainderPos, remainderNote)]
      [(remainderPos, remainderNote)] = some [(mid4.pool.leaves.length, dest1Note)]
    rw [hmid4Len, hRemainderPosVal]
    decide
  have hNullify_t2 : markSpent mid5.pool.spent (List.ofFn pub_t2.nullifiers) =
      some (nullifier ownerField remainderPos :: mid5.pool.spent) := by
    show markSpent (nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent)
      [nullifier ownerField remainderPos] =
      some (nullifier ownerField remainderPos ::
        (nullifier ownerField (leavesIndices2 0) :: mid4.pool.spent))
    have hnullseparate : nullifier ownerField remainderPos ≠ nullifier ownerField (leavesIndices2 0) := by
      intro heqn
      have hv := Term.val.inj (Term.hash2_inj heqn).2
      rw [hRemainderPosVal] at hv
      exact absurd hv (by decide)
    have hnullseparate2 : nullifier ownerField remainderPos ∉ mid4.pool.spent := by
      show nullifier ownerField remainderPos ∉ [nullifier nullifyingKey 0]
      rw [List.mem_singleton]
      intro heqn
      have hv := Term.val.inj (Term.hash2_inj heqn).2
      rw [hRemainderPosVal] at hv
      exact absurd hv (by decide)
    unfold markSpent
    rw [if_neg (by
      simp only [List.mem_cons]
      exact fun h => h.elim hnullseparate hnullseparate2)]
    rfl
  let dest2Note : CommitmentPreimage := ⟨dest2.destination, token, 1⟩
  let s' : AdjudicatorState := { mid5 with
    pool := { mid5.pool with
      live := fun t => if t = token
        then withPositionsFrom mid5.pool.leaves.length [dest2Note] ++ [(mid4.pool.leaves.length, dest1Note)]
        else mid5.pool.live t,
      spent := nullifier ownerField remainderPos :: mid5.pool.spent,
      leaves := mid5.pool.leaves ++ [commitment dest2.destination token 1],
      roots := treeRoot TreeDepth (mid5.pool.leaves ++ [commitment dest2.destination token 1]) ::
        mid5.pool.roots,
      preimageOf := applyRecords mid5.pool.preimageOf (ownedOutputRecords w_t2 pub_t2),
      ownedRandomOf := mid5.pool.ownedRandomOf },
    holdings := update mid5.holdings token (update (mid5.holdings token) cid none),
    channels := update mid5.channels cid
      { mid5.channels cid with
        outcomeHash := outcomeHashOf ((outcome.mapIdx fun i exit =>
          if i ≠ 0 then exit else { exit with allocations := [{ dest1 with amount := 0 }, dest2] }).mapIdx
          fun i exit => if i ≠ 0 then exit
            else { exit with allocations := [{ dest1 with amount := 0 }, { dest2 with amount := 0 }] }) } }
  have hospend2 : PoolOwnedSpendStep mid5.pool self token (mid5.holdings token cid)
      [dest2Note] [] s'.pool := by
    rw [hc5Eq]
    refine ⟨w_t2, pub_t2, by decide, hOC2, _, _, (fun j => j.elim0), hNonZero_t2, hCapacity_t2, rfl,
      rfl, rfl, rfl, rfl, ?_, hRemove_t2, hNullify_t2, (fun j => j.elim0), rfl⟩
    · show rootT2 ∈ mid5.pool.roots
      exact List.mem_cons_self
  let outcome1 : Outcome := outcome.mapIdx fun i exit =>
    if i ≠ 0 then exit else { exit with allocations := [{ dest1 with amount := 0 }, dest2] }
  have hassetIdx1 : (0 : Nat) < outcome1.length := by decide
  have hstateHash2 : (mid5.channels cid).stateHash = Term.val 0 := by
    show ((update mid4.channels cid
      { mid4.channels cid with
        outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
          if i ≠ 0 then exit else { exit with allocations := [{ dest1 with amount := 0 }, dest2] }) })
      cid).stateHash = Term.val 0
    unfold update
    rw [if_pos rfl]
    exact hstateHash
  have houtcomeHash2 : (mid5.channels cid).outcomeHash = outcomeHashOf outcome1 := by
    show ((update mid4.channels cid
      { mid4.channels cid with
        outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
          if i ≠ 0 then exit else { exit with allocations := [{ dest1 with amount := 0 }, dest2] }) })
      cid).outcomeHash = outcomeHashOf outcome1
    unfold update
    rw [if_pos rfl]
  have hfinalized2 : (mid5.channels cid).mode mid5.now = .finalized := by
    show ((update mid4.channels cid
      { mid4.channels cid with
        outcomeHash := outcomeHashOf (outcome.mapIdx fun i exit =>
          if i ≠ 0 then exit else { exit with allocations := [{ dest1 with amount := 0 }, dest2] }) })
      cid).mode mid5.now = .finalized
    unfold update
    rw [if_pos rfl]
    exact hfinalized
  have hget1 : outcome1.get ⟨0, hassetIdx1⟩ = ⟨token, [{ dest1 with amount := 0 }, dest2]⟩ := rfl
  have hheld5 : heldValue mid5 token cid = 1 := by
    unfold heldValue
    rw [hc5Eq]
    show ((mid5.pool.preimageOf (commitment (npk (Term.val self) r1) token 1)).map
      CommitmentPreimage.value).getD 0 = 1
    show ((applyRecords mid4.pool.preimageOf (ownedOutputRecords w_t1 pub_t1)
      (commitment (npk (Term.val self) r1) token 1)).map CommitmentPreimage.value).getD 0 = 1
    rfl
  have htransferEffects2 : transferEffects [{ dest1 with amount := 0 }, dest2] 1 [1] =
      ([{ dest1 with amount := 0 }, { dest2 with amount := 0 }], [dest2], 1) := by
    unfold transferEffects afford
    decide
  have hstep_t2 : Step sig (consensusRelation sig) (Actor.nitro 0) mid5
      (.transfer 0 cid (Term.val 0) outcome1 [1]) s' := by
    refine ⟨hassetIdx1, hfinalized2, hstateHash2, houtcomeHash2, trivial, ?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [hget1, hheld5, htransferEffects2]
    refine ⟨by decide, r1, ?_⟩
    simp only [Nat.sub_self]
    exact ⟨hospend2, rfl, rfl⟩
  refine ⟨assets, self, pool0, mid4, mid5, s', 0, cid, Term.val 0, Term.val 0, outcome, outcome1,
    Actor.nitro 0, Actor.nitro 0, hassetIdx, hassetIdx1, dest1, dest2,
    hReachPool, hreach4, hstep_t1, ?_, (by decide), ?_, hstep_t2, ?_, (by decide), ?_⟩
  · show dest1 ∈ [dest1, dest2]
    exact List.mem_cons_self
  · rw [hget1]; rw [hheld5]; decide
  · show dest2 ∈ [{ dest1 with amount := 0 }, dest2]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · refine ⟨token, remainderPos + 1, dest2Note, ?_, rfl⟩
    show (mid4.pool.leaves.length + 1 + 1, dest2Note) ∈
      withPositionsFrom mid5.pool.leaves.length [dest2Note] ++
        [(mid4.pool.leaves.length, dest1Note)]
    apply List.mem_append.mpr
    left
    have hlen5 : mid5.pool.leaves.length = mid4.pool.leaves.length + 1 + 1 := by
      show (mid4.pool.leaves ++ [commitment dest1.destination token 1,
        commitment (npk (Term.val self) r1) token 1]).length = mid4.pool.leaves.length + 1 + 1
      rw [List.length_append, hmid4Len]
      rfl
    rw [hlen5]
    simp [withPositionsFrom]


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
    (s : AdjudicatorState) (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (held : Nat) (hheld : heldValue s asset cid = held) (hpos : 0 < held) :
    ∃ pos c, s.holdings asset cid = some (pos, c) ∧ PoolIsLive s.pool c ∧
      (s.pool.preimageOf c).map CommitmentPreimage.value = some held := by
  unfold heldValue at hheld
  rcases hc : s.holdings asset cid with _ | ⟨pos, cm⟩
  · simp only [hc] at hheld; omega
  · refine ⟨pos, cm, ?_, ?_, ?_⟩
    · rfl
    · exact holdings_point_to_live_notes sig appRel assets self pool0 s asset cid pos cm hreach hc
    · simp only [hc] at hheld
      rcases hp : s.pool.preimageOf cm with _ | pre
      · rw [hp] at hheld; simp at hheld; omega
      · rw [hp] at hheld; simp at hheld; simp [hheld]

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
    (s : AdjudicatorState) (asset : Nat) (cid : Term) (pos : Nat) (c : Term)
    (pre : CommitmentPreimage)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (hholds : s.holdings asset cid = some (pos, c))
    (hpre : s.pool.preimageOf c = some pre) :
    pre.value ≠ 0 := by
  have hinv := reachable_preserves
    (P := fun s => ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (by intro qasset qcid qpos qc hc; exact absurd hc (by simp [genesis]))
    (fun actor call s s' hP hstep => holdings_preimage_nonzero_step sig appRel actor s s' call hP hstep)
    hreach
  obtain ⟨pre', hpre', hval', _⟩ := hinv asset cid pos c hholds
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
    (s : AdjudicatorState) (asset : Nat) (cid : Term)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) :
    heldValue s asset cid = 0 ↔
      s.holdings asset cid = none ∨
      ∃ pos c, s.holdings asset cid = some (pos, c) ∧ s.pool.preimageOf c = none := by
  unfold heldValue
  rcases hc : s.holdings asset cid with _ | ⟨pos, c⟩
  · simp [hc]
  · simp only [hc]
    rcases hp : s.pool.preimageOf c with _ | pre
    · constructor
      · intro _
        exact Or.inr ⟨pos, c, rfl, hp⟩
      · intro _
        simp [hp]
    · simp only [hp, Option.map_some, Option.getD_some]
      constructor
      · intro hv
        exact absurd hv (holdings_never_zero_valued sig appRel assets self pool0 s asset cid pos c
          pre hreach hc hp)
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
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) (dest : Allocation)
    (hdest : dest ∈ (outcome.get ⟨assetIndex, h⟩).allocations) (hzero : dest.amount = 0) :
    ¬ ∃ pre : CommitmentPreimage, pre.npk = dest.destination ∧ pre.value = 0 ∧
        (∃ pos, (pos, pre) ∈ s'.pool.live pre.token) ∧
        (∀ pos, (pos, pre) ∉ s.pool.live pre.token) := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨r, hmatch, _hholdseq, _hchanseq⟩ := hrest
  rintro ⟨pre, _hnpk, hval, ⟨pos, hin⟩, hnin⟩
  by_cases htok : pre.token = (outcome.get ⟨assetIndex, hidx⟩).asset
  · rw [htok] at hin
    have hnz := payout_outputs_nonzero
      (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
        (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1
      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
        (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2)
      (outcome.get ⟨assetIndex, hidx⟩).asset s.self r
    rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | ⟨oldPos, c⟩
    · rw [hc] at hmatch
      obtain ⟨w, pub, hM, hC, spent', randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
        _hnewnotes, _hroot, _hmarkspent, _hrandomOut, heq⟩ := hmatch
      rw [heq] at hin
      simp only [htok] at hin
      rcases List.mem_append.mp hin with hc1 | hc2
      · exact hnz pre (withPositionsFrom_mem_snd hc1) hval
      · exact hnin pos (htok ▸ hc2)
    · rw [hc] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
        _hnewnotes, _hleavesIdx, _hcommit, _hroot, hremove, _hmarkspent, _hrandomOut, heq⟩ := hmatch
      rw [heq] at hin
      simp only [htok] at hin
      rcases List.mem_append.mp hin with hc1 | hc2
      · exact hnz pre (withPositionsFrom_mem_snd hc1) hval
      · have hperm := removeAll_perm hremove
        have hmem : (pos, pre) ∈ s.pool.live (outcome.get ⟨assetIndex, hidx⟩).asset :=
          (List.Perm.mem_iff hperm).mpr (List.mem_append.mpr (Or.inr hc2))
        exact hnin pos (htok ▸ hmem)
  · have heqlive : s'.pool.live pre.token = s.pool.live pre.token := by
      rcases hc : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | ⟨oldPos, c⟩
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, spent', randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
          _hnewnotes, _hroot, _hmarkspent, _hrandomOut, heq⟩ := hmatch
        rw [heq]
        show (if pre.token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live pre.token) = s.pool.live pre.token
        rw [if_neg htok]
      · rw [hc] at hmatch
        obtain ⟨w, pub, hM, hC, rest, spent', randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
          _hnewnotes, _hleavesIdx, _hcommit, _hroot, hremove, _hmarkspent, _hrandomOut, heq⟩ := hmatch
        rw [heq]
        show (if pre.token = (outcome.get ⟨assetIndex, hidx⟩).asset then _
            else s.pool.live pre.token) = s.pool.live pre.token
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
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨r, _hpoolstep, hholdseq, _hchanseq⟩ := hrest
  have hidx_eq : (⟨assetIndex, hidx⟩ : Fin outcome.length) = ⟨assetIndex, h⟩ := rfl
  rw [hidx_eq] at hholdseq
  change s'.holdings = update s.holdings (outcome.get ⟨assetIndex, h⟩).asset
      (update (s.holdings (outcome.get ⟨assetIndex, h⟩).asset) cid
        (if heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
            (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 = 0
         then none
         else some (s.pool.leaves.length +
             ((transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.1.filterMap (fun a =>
                 if a.amount = 0 then none
                 else some (⟨a.destination, (outcome.get ⟨assetIndex, h⟩).asset, a.amount⟩ :
                   CommitmentPreimage)) ++
               (if heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
                   (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
                     (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 = 0
                then []
                else [(⟨npk (Term.val s.self) r, (outcome.get ⟨assetIndex, h⟩).asset,
                  heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
                    (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
                      (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2⟩ :
                    CommitmentPreimage)])).length - 1,
           commitment (npk (Term.val s.self) r) (outcome.get ⟨assetIndex, h⟩).asset
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
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s
      (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    (s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid = none) ↔
      s'.pool.spent = s.pool.spent := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨_hguarantee, hrest⟩ := hinner
  obtain ⟨_r, hmatch, _hholdseq, _hchanseq⟩ := hrest
  have hidx_eq : (⟨assetIndex, hidx⟩ : Fin outcome.length) = ⟨assetIndex, h⟩ := rfl
  rw [hidx_eq] at hmatch
  constructor
  · intro hnone
    rw [hnone] at hmatch
    obtain ⟨w, pub, hM, hC, spent', randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
      _hnewnotes, _hroot, hmarkspent, _hrandomOut, heq⟩ := hmatch
    rw [heq]
    show spent' = s.pool.spent
    have hofn : List.ofFn pub.nullifiers = ([] : List Term) := List.ofFn_zero
    rw [hofn] at hmarkspent
    unfold markSpent at hmarkspent
    exact (Option.some.inj hmarkspent).symm
  · intro hpost
    rcases hcase : s.holdings (outcome.get ⟨assetIndex, h⟩).asset cid with _ | ⟨oldPos, c⟩
    · rfl
    · exfalso
      rw [hcase] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
        _hnewnotes, _hleavesIdx, _hcommit, _hroot, _hremove, hmarkspent, _hrandomOut, heq⟩ := hmatch
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
