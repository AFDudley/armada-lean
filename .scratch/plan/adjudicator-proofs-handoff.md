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
