# SUCCESSOR HANDOFF — adjudicator-model-v4, step 2a reconnaissance done, no chunk pushed yet

## State

- Repo: `~/code/git_puller/repos/armada-lean-adjudicator-v4`, branch `adjudicator-model-v4`.
- Head: `02f757d` (unchanged this session — no new commit). `lake build` exits 0.
- Sorry count: 67 (`lake build 2>&1 | grep -c 'uses .sorry.'`). 17 `Lemmas.lean`, 50
  `Safety.lean`. `wc -l`: `Lemmas.lean` 3747, `Safety.lean` 1688.
- This session read the brief chain (`ADJUDICATOR-proofs-successor.md`,
  `-successor-3.md`, `-successor-4.md`) and the full text of the current handoff,
  then did reconnaissance for step 2a (the consolidated owned-spend effect lemma).
  It did NOT write or push a new lemma: see "Why no chunk landed" below.

## Step 2a reconnaissance: exact status of the 9 target lemmas

All 9 live in `ArmadaLean/Adjudicator/Lemmas.lean`, each taking the SAME core
argument shape — `(pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term)
(remainder r : Nat) (payoutOutputs : List CommitmentPreimage) (holdings : Nat → Term
→ Option ((Nat × Nat) × Term))`, `htokPayout`, and `hmatch : PoolOwnedSpendStep pool
self asset (holdings asset cid) payoutOutputs (if remainder = 0 then [] else
[⟨npk self r, asset, remainder⟩]) pool'` — so a single consolidated lemma over that
same hypothesis set is the right shape. Two outliers take a narrower hypothesis set
(see below); the consolidated lemma needs to carry their hypotheses too, as extra
optional/separate arguments, or those two stay separate.

**Already fully proved (real proofs, no `sorry`), safe to fold into the new lemma
as-is — their proof bodies can be copied/merged directly, no rework owed:**
1. `PoolOwnedSpend_update_preimage_nonzero` (line 1630, needs `hinv`: every
   known-holding preimage nonzero/consistent) — conclusion: every holding after the
   update still resolves to a nonzero consistent preimage.
2. `PoolOwnedSpendStep_frame` (line 1828, needs `hinv` + `qasset ≠ asset ∨ qcid ≠
   cid`) — conclusion: `heldValue` at any OTHER `(asset, cid)` pair is unchanged.
3. `PoolOwnedSpendStep_sets_heldValue` (line 1962, no `hinv` needed) — conclusion:
   `heldValue` at the TOUCHED pair becomes exactly `remainder`.
4. `PoolOwnedSpendStep_live_frame` (line 2652, OUTLIER shape — takes `nullified`
   directly, `self`/`token` instead of `self`/`asset`/`cid`/`remainder`/`r`/
   `payoutOutputs`, plus `ht : t ≠ token`) — conclusion: `.live` at a DIFFERENT
   token is unchanged. Already proved, 14 lines, no rework.
5. `PoolOwnedSpendStep_preimageOf_known` (line 3093, needs `hpre`/`hconsist` for ONE
   named `qc`) — conclusion: an already-known preimage at `qc` survives.

**Still `sorry`-stubbed (real proof rework owed, not mechanical) — folding these
into the new lemma means first doing the rework the 2026-10-25/26 sessions already
scoped, then writing the proof once instead of twice:**
6. `PoolOwnedSpendStep_ownedRandom_known` (line 1800) — needs the `randomOut : Fin M
   → Nat` → `ownedOutputs : List (Fin _ × OwnedDisclosure)` convention rework (cause
   A in the prior handoff).
7. `PoolOwnedSpend_update_position_live` (line 2502) — needs `withTreePositionsFrom_
   append` (does not exist yet; derive from `withPositionsFrom_append` +
   `List.map_append`, mirroring `withTreePositionsFrom`'s own `.map`-over-
   `withPositionsFrom` definition, `Pool.lean:287-289`) and `withTreePositionsFrom_
   nodup` (cause B).
8. `PoolOwnedSpendStep_notedValue_conserved` (line 2605, OUTLIER shape — takes
   `nullified`/`ownedPreimages` directly, no `holdings`/`cid`/`remainder`/`r`
   arguments at all) — needs the tree-aware analogue of `withPositionsFrom_map`
   (cause B).
9. `PoolOwnedSpendStep_preserves_user_note` (line 2626, OUTLIER shape — takes
   `selfInputs : List Term` with `self := Term.keccak selfInputs`, `nullified`
   directly, a `masterPublicKey pk nk` ownership witness) — needs the same tree-aware
   rework as #7/#8, matched against `withTreePositionsFrom treeNumber position
   outputs` instead of the bare-Nat tag (cause B).

## Why no chunk landed this session

The brief (step 2a) asks for ONE lemma stating the union of all 9 conjuncts, proved
once. Two structural facts make that lemma, done honestly, as much work as finishing
all 4 remaining `Lemmas.lean` sorries above PLUS re-deriving the 5 already-proved
ones against a merged hypothesis set, in one sitting:

1. **3 of the 9 (`live_frame`, `notedValue_conserved`, `preserves_user_note`) take a
   narrower/different hypothesis set than the other 6** (no `cid`/`remainder`/`r`/
   `holdings` — they only need `nullified` directly, since they reason about
   `.live`/`.notedValue` globally, not about the `holdings`-keyed update). A single
   lemma over the union needs either (a) the full 6-lemma hypothesis set PLUS these
   3's own extra pieces (`t`, `ht`/`token`, `selfInputs`, `pk`/`nk`/`r`, `hnpk`,
   `hmem`) all as further arguments of one signature, or (b) dropping the `holdings`-
   indexed framing from the consolidated lemma and re-deriving `_frame`/`_sets_
   heldValue`/`_update_preimage_nonzero` purely from `nullified`/`pool`/`pool'` the
   way `_live_frame` already does — which is a genuine redesign of 3 of the 5
   ALREADY-WORKING proofs, not an additive change, and risks breaking callers the
   brief's own "additive" instruction (line 12 of `-successor-4.md`) says to avoid.
2. **4 of the 9 are still real `sorry`s needing un-scoped proof work** (the
   `withTreePositionsFrom_append`/`_nodup` lemmas do not exist yet and are
   themselves non-trivial — `withTreePositionsFrom` is a `.map` over
   `withPositionsFrom`, so each derived lemma needs its own short induction, not a
   one-line `simp`). Folding them into the new consolidated lemma without first
   finishing them independently means debugging 4 genuinely new proofs AND a 5-way
   signature merge in the same `lake build` cycle — exactly the "half-migrated,
   nothing provable" failure mode `-successor-4.md` itself warns against (line 10-12).

Spending this session's remaining budget attempting the merge in one shot risked a
large, unbuildable diff with no safe rollback-free way to tell which of the two
changes (the 4 new proofs vs. the 5-way signature merge) broke the build. The safer
additive path, below, lets each piece build independently before the merge commit.

## Next steps for the successor, in order (revised from the prior handoff)

1. **First**, finish the 4 still-`sorry` lemmas (#6-9 above) IN PLACE, unmerged,
   each its own small push, using the fixes the prior two handoffs already scoped
   (cause A for #6, cause B + the new `withTreePositionsFrom_append`/`_nodup` helper
   lemmas for #7-9). This retires 4 of the 17 `Lemmas.lean` sorries on its own and
   de-risks the later merge (nothing left to debug there except the signature
   merge itself).
2. **Then** write the ONE consolidated lemma (`PoolOwnedSpendStep_effects`, suggested
   name) next to the 9, option (a) above — full hypothesis union, not a `.live`-only
   redesign of the 3 outliers — and prove it by literally invoking the (now all
   real) 9 old proofs' bodies conjoined, OR by inlining the shared `hvalid_outputs`/
   `hrecordseq`/`hpre0` scaffolding once and re-deriving each conjunct against it
   (less duplication, same risk profile as today's 9 separate near-identical
   `hvalid_outputs` blocks — worth doing once, not twice, for the SAME reason the
   brief orders this step). Push.
3. **Then** 2b: re-prove each of the 9 old lemmas as a short corollary of the new
   one (one-line `exact` extracting the matching conjunct, for the 6 that share the
   full hypothesis set; the 3 outliers need their own thin wrapper supplying the
   missing pieces from their own narrower signature). Push after each few.
4. **Then** 2c: the `bulkTransferFold_*` counterparts, same corollary pattern.
5. **Then** steps 3-5 exactly as `-successor-4.md` §3a-5 states (holding-wellformed
   invariant, execution constructors, the 52 `Safety.lean` statements, then
   `unbeatable_pays`/`unbeatable_pays_after_timeout`).

Report after each push: sha, `sorry` count (`lake build 2>&1 | grep -c "uses .sorry."`),
and line counts of `Lemmas.lean`/`Safety.lean`, per the brief.

## Rules carried forward unchanged

No statement text changes without the coordinator's approval. No new axioms. Pool
facts go through the pool builder, never written directly in this branch. Integrate
pool-model with `git merge`, never rebase/force-push. Use `.scratch/` in the
worktree for scratch files. Write in ASD-STE100.

---

(Prior handoff sections — TransferOnlyDerivedFrom restore, the tree-rollover fix
session, the PRIOR pre-rollover handoff — kept below, still accurate, trimmed only
where this session's step-2a reconnaissance above supersedes the stale "steps 2-5
not started" summary.)

The 4 real placeholders (`heldValue_range_placeholder` → `live_values_lt_2pow120`,
`holdings_position_leaf_value_placeholder` → `leaf_stable`,
`live_note_nullifier_unspent_placeholder` → `live_note_unspent`,
`pool_leaves_capacity_placeholder` → delete) are still untouched; re-grep their
current line numbers before swapping, per the prior handoff's own caution.

`TransferOnlyDerivedFrom` is restored (verbatim `inductive` from `1fa40c6`, commit
`be21402`). No further action owed there.
