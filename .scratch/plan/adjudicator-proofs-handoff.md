# SUCCESSOR HANDOFF — HoldingWellFormed built and proved, old four
# lemmas not yet rewired/deleted (the remaining work is mechanical)

## State

- Repo: `~/code/git_puller/repos/armada-lean-adjudicator-v4`, branch `adjudicator-model-v4`.
- Head: `ce6f4ad`. `lake build` exits 0 (full project, 26 jobs).
- Sorry count: 63, UNCHANGED (`lake build 2>&1 | grep -c 'uses .sorry.'`). The
  four target lemmas (task: merge them into `HoldingWellFormed`) still
  carry their OWN original `sorry` bodies, untouched. The new proof this
  session makes deleting their `sorry`s a mechanical rewiring job, not a
  proof-engineering one. Read the task brief's four line items again
  (merge, prove at genesis, prove the one step lemma, restate the four
  as corollaries or delete) — items 1 and 2 are DONE; item 3 is NOT done.
- `ArmadaLean/Adjudicator/Lemmas.lean`: 5456 lines (was 4520).

## Done this session: `HoldingWellFormed` and its proof, in full

Added, all sorry-free, each individually compiled against the full
project (`lake build ArmadaLean.Adjudicator.Lemmas` exit 0):

- `HoldingWellFormed` (line 4532): the one per-holding invariant,
  bundling what the four old lemmas stated piecewise — preimageOf
  known/nonzero/consistent, `pre.token`, live membership, position
  bound, key uniqueness, and owned-random disclosure — behind ONE
  shared `pre` witness per holding (unified across sub-facts via
  `hashCommitment_inj`, never carried as two separate witnesses).
- `holdingWellFormed_genesis` (4544): trivial, no channel holds
  anything at genesis.
- `PoolOwnedSpend_update_wellFormed` (4560) / `bulkTransferFold_
  wellFormed` (4671): the `.transfer`/bulk-call case, built on the
  already-proved `PoolOwnedSpend_update_preimage_nonzero`, `PoolOwnedSpend_
  update_position_live`, `PoolOwnedSpendStep_ownedRandom_known` (NOT on
  `PoolOwnedSpendStep_effects` directly — gluing its six conjuncts back
  into one record needed more surgery than calling the three
  already-proved lemmas it itself calls). The two separately-obtained
  `pre` witnesses are unified via `hashCommitment_inj` at each use.
- `DepositStep_frame_wellFormed` (4729) / `DepositStep_update_
  wellFormed` (4821): the `.deposit` FIRST-TIME case — tree-rollover-
  aware, NEW work (the old four lemmas all had `sorry` here; the
  pre-rollover git history, commit `4884305` and `eb47c31`, had the
  pre-rollover reasoning but in the bare-`position`/`withPositionsFrom`
  shape, not the `(treeNumber, position)`/`withTreePositionsFrom` one —
  ported, not reused verbatim). Depositor's own spent inputs are
  USER-keyed (`user_npk_ne_contract_npk`), so they can never collide
  with a contract-owned held note's own position — `userDisjoint`,
  mirrors the old `holdings_position_live_step`'s own argument.
- `DepositMergeStep_update_wellFormed` (4991): the `.deposit` TOP-UP
  (merge) case — also new work, also previously all-`sorry`. Nullifies
  TWO positions (old holding, `DepositStep`'s own fresh note, both read
  off `midPool` via `DepositStep_frame_wellFormed`), mints one merged
  note. The merged note's own `value ≠ 0` needs `transactOwned_value_
  conserved` (the two nullified values are each already known nonzero,
  so their sum is), since `¬isZeroPreimage` alone does not give
  `value ≠ 0` (it is a 3-way disjunction's negation, not a value
  projection). WATCH THE CONJUNCT ORDER inside `DepositMergeStep`
  (`Notes.lean`): the THIRD conjunct (`hnpkOut0'` in this proof) is
  `w.npkOut 0 = npk self r` (the EXISTENTIAL `r`, NOT `randomOut`); the
  conjunct actually naming `randomOut` (`hrandomOut'`) is the
  SECOND-TO-LAST, `npk pub.ownerField randomOut = w.npkOut 0`. A first
  attempt this session assumed the wrong one at the wrong slot and cost
  several failed-build iterations to find; `r = randomOut'` only holds
  derived (`npk_inj` on the two conjuncts composed), not by construction.
- `holdingWellFormed_step` (5277): the ONE step lemma over all 11
  `Call` cases — `.deposit` via the two lemmas above, `.transfer`/bulk
  via `PoolOwnedSpend_update_wellFormed`/`bulkTransferFold_wellFormed`,
  the other 7 trivial (pool/holdings both unchanged).
- `holdingWellFormed_reachable` (5446): the `reachable_preserves` lift.

## NOT done: rewiring the four old lemmas, and the Safety.lean wrapper

The old four step lemmas are UNCHANGED, still present, still `sorry` in
exactly the branches they always were:
- `holdings_preimage_nonzero_step` (2447)
- `ownedRandom_known_step` (4038)
- `held_note_owned_disclosure_step` (4171)
- `holdings_position_live_step` (4296)

Do this, in order, each ending with `lake build` exit 0, each its own
commit, pushed:

1. Check EVERY caller of each of the four (already done this session,
   not yet acted on): `holdings_preimage_nonzero_step` and
   `ownedRandom_known_step` have NO callers anywhere outside their own
   declarations — DELETE both outright (with their own doc comments).
   `held_note_owned_disclosure_step` is called by `held_note_owned_
   disclosure_reachable` (Lemmas.lean, unchanged, keep). `holdings_
   position_live_step` is called by `holdings_position_live_reachable`
   (Safety.lean, line ~836, currently `sorry`).
2. Rewrite `held_note_owned_disclosure_step`'s BODY (keep its exact
   signature/statement — the task forbids touching statements) to:
   `have h := holdingWellFormed_step sig appRel actor s s' call hinv hstep
   qasset qcid qpos qc hc` (first unfold `HoldingWellFormed` on `hinv`
   itself — its OWN hypothesis is already in the right per-holding
   shape modulo the `ownerField` existential, which collapses to `s.self`
   directly), then project `h.1` into the five-tuple
   `⟨pre, ownerField := s.self, r, ...⟩` the old statement names.
3. Rewrite `holdings_position_live_step`'s BODY the same way, projecting
   `holdingWellFormed_step`'s output into the old statement's shape
   (drop the `pre.token`/disclosure conjuncts the old statement does not
   ask for).
4. Delete `PoolOwnedSpend_update_owned_disclosure` (1583, itself
   `sorry`), `bulkTransferFold_owned_disclosure` (2328),
   `bulkTransferFold_preimage_nonzero` (2283), `bulkTransferFold_
   position_live` (3099), `bulkTransferFold_ownedRandom_known` (3942) —
   confirmed this session: each has ZERO callers once steps 1-3 land
   (every one was only ever called from inside the four old lemmas).
   `bulkTransferFold_preserves_user_note` and `bulkTransferFold_frame`
   are DIFFERENT lemmas (not part of this list) — do not touch them.
5. Fill `holdings_position_live_reachable`'s `sorry` (Safety.lean
   ~836-848, target in scope per the task's own "Safety.lean
   reachability wrappers... if any" line): it is a direct
   `reachable_preserves (P := ...) (base) (step) hreach` call mirroring
   `held_note_owned_disclosure_reachable`'s own shape (Lemmas.lean
   ~4251), with `step := fun actor call s1 s2 hP hstep => holdings_
   position_live_step sig appRel actor s1 s2 call hP hstep`.
6. Re-run `lake build 2>&1 | grep -c 'uses .sorry.'`: expect 63 − 4 (the
   four, now proved or deleted) − 1 (`holdings_position_live_reachable`,
   step 5) = 58, PLUS whichever of the five deleted helpers (step 4)
   were themselves silently unsound (built on the `sorry`d `PoolOwnedSpend_
   update_owned_disclosure`) without showing their own `sorry` warning —
   deleting them does not change the COUNT (they never showed a
   warning) but does remove a real soundness gap the count never
   reflected. Report the exact sha, final sorry count, and `Lemmas.lean`
   line count in the completion message, per the task's own acceptance
   criteria.

# SUCCESSOR HANDOFF — adjudicator-model-v4, model fix done, ownedRandom_known
# proved, step 2a done, steps 2b/2c not started

## State

- Repo: `~/code/git_puller/repos/armada-lean-adjudicator-v4`, branch `adjudicator-model-v4`.
- Head: `1821222`. `lake build` exits 0.
- Sorry count: 63 (`lake build 2>&1 | grep -c 'uses .sorry.'`), down from 64.
- `ArmadaLean/Adjudicator/Lemmas.lean`: 4520 lines.
- `ArmadaLean/Adjudicator/Safety.lean`: 1688 lines, untouched this session.

## Done this session

1. **Model fix** (`ArmadaLean/Adjudicator/Notes.lean`, commit `b04be64`):
   `PoolOwnedSpendStep`'s `ownedOutputs : List (Fin ownedPreimages.length ×
   OwnedDisclosure)` free witness is replaced by `ownedRandom : Fin
   ownedPreimages.length → Nat`, with a new conjunct `∀ j, w.npkOut
   (Fin.natAdd payoutPreimages.length j) = npk self (ownedRandom j)` and the
   `ownedRandomOf` update built from `(List.finRange ownedPreimages.length).map`
   instead of the free list. Every index of `ownedPreimages` is now
   MANDATORILY disclosed; `ownedOutputs := []` no longer satisfies the step.
   The existential/conjunct COUNT and ORDER are unchanged, so every
   positional `obtain` in `Lemmas.lean` kept typechecking with no caller
   edits. `DepositStep`/`DepositMergeStep` already disclosed their kept
   output unconditionally; they needed no change.

2. **`PoolOwnedSpendStep_ownedRandom_known` proved** (commit `b0a39b2`), on the
   fixed model. First conjunct: `applyOwnedRecords_preserves_known` against
   `pool'.preimageOf`, built per-index via `applyRecords_returns` on
   `ownedOutputRecords w pub`. Second conjunct (`remainder ≠ 0`): the fresh
   remainder note's own position is located by a `getElem?`/`Fin.natAdd`
   index extraction from `ownedNewNotes w = outputs`
   (`List.getElem?_concat_length`), then disclosed via `applyOwnedRecords_
   reads`, with `npk_inj` pinning the disclosed random back to `r`. Needed
   `(reg := pool'.preimageOf)` explicit at both `applyOwnedRecords_
   preserves_known`/`_reads` call sites — Lean cannot infer `reg` from the
   `hvalid` lambda alone since `hvalid`'s own type doesn't pin it until a
   later positional argument does.

3. **Step 2a** (commits `3693f6c`, `1821222`): `PoolOwnedSpendStep_effects`,
   next to the nine, states in one conjunction everything `PoolOwnedSpendStep_
   frame`, `_sets_heldValue`, `_ownedRandom_known`, `_preimageOf_known`,
   `PoolOwnedSpend_update_preimage_nonzero`, and `_update_position_live`
   establish — the SIX lemmas that share the `holdings`/`cid`/`remainder`/`r`
   specialized signature. `htokPayout` and each lemma's own holdings
   invariant (`PoolOwnedSpendStep_frame`/`PoolOwnedSpend_update_preimage_
   nonzero` share one shape; `PoolOwnedSpend_update_position_live` needs a
   different one) are premises of the INDIVIDUAL conjuncts that need them,
   not global hypotheses — `PoolOwnedSpend_update_position_live`'s own proof
   never used `htokPayout`, so its conjunct doesn't require it either.
   Proved by direct delegation to the six already-proved lemmas.

## Why `notedValue_conserved`/`preserves_user_note`/`live_frame` are NOT in
## `PoolOwnedSpendStep_effects`

The operator's nine named lemmas split into two signature SHAPES:

- SIX take `(holdings, cid, remainder, r, payoutOutputs)` and a step at
  `nullified := holdings asset cid`, `ownedPreimages := (if remainder = 0
  then [] else [⟨npk self r, asset, remainder⟩])` — the shape `.transfer`/
  `bulkTransferFold` actually call. `PoolOwnedSpendStep_effects` covers
  these six.
- THREE (`PoolOwnedSpendStep_notedValue_conserved`, `_preserves_user_note`,
  `_live_frame`) take a fully generic `nullified : Option (...)`,
  `payoutPreimages`/`ownedPreimages : List CommitmentPreimage` — no
  `holdings`/`cid`/`remainder`/`r` at all.

A single conjunction covering all nine would need the generic shape, but the
SIX lemmas' own conclusions are stated in terms of `update holdings asset
(update (holdings asset) cid ...)` — bookkeeping that doesn't exist at the
generic level. Unifying all nine under one signature is a genuine
re-design, not a one-line generalization. Left as is: the three generic
lemmas stay separate, unchanged, already short.

## What's NOT done: steps 2b and 2c

**2b** (re-prove each of the nine as a short corollary of `PoolOwnedSpendStep_
effects`) is NOT done for the six it covers. The blocker is DEFINITION
ORDER, not proof difficulty: `PoolOwnedSpendStep_effects` is defined AFTER
the six (its own proof currently CALLS them), so turning the six into
one-line corollaries of it requires the OPPOSITE order — `PoolOwnedSpendStep_
effects` would need to move BEFORE the six, with its OWN proof built
directly (porting in the six lemmas' real proof bodies, merged under one
shared `rcases hc0 : holdings asset cid with _ | c0` / one shared `obtain
⟨w, pub, ...⟩ := hmatch` per branch, instead of each lemma re-destructuring
`hmatch` separately). This is real proof-engineering work (the six
proofs run several hundred lines combined), not a mechanical move. Do it
as ONE commit per lemma folded in (six total), each ending with `lake
build` exit 0, in this order: move `PoolOwnedSpendStep_effects` first
with a `sorry` body, confirm the six's existing `exact
PoolOwnedSpendStep_effects ...`-style one-liners don't exist yet (they
currently don't — the six keep their own full proofs), then migrate one
lemma's proof body into `PoolOwnedSpendStep_effects`'s matching conjunct
and replace that lemma's own body with the one-line corollary, per
lemma, six times.

**2c** (one `bulkTransferFold` fold lemma over `PoolOwnedSpendStep_effects`,
then each `bulkTransferFold_*` counterpart as a corollary) is NOT started.
It depends on 2b being done first (the fold lemma should iterate
`PoolOwnedSpendStep_effects`, not the nine individually, per the operator's
own instruction), so do 2b before 2c.

## Rules (unchanged, carry forward)

- No statement text changes in `Safety.lean` without the coordinator's
  approval. If a statement looks false, report a concrete counterexample
  and move to the next item.
- No new axioms.
- Commit and push (`git push AFDudley.github.com adjudicator-model-v4`)
  after each item with `lake build` exit 0. Never rebase, never force-push.
- Use `.scratch/` in the worktree for scratch files, never `/tmp`.
