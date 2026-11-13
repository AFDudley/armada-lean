/-
  ArmadaLean.Pool — the privacy pool's state and operations.

  Why this model exists: the
  Armada pool holds other people's tokens. Its central promise is that value in the pool
  exists only as notes, and every token the pool holds backs exactly one unspent note.
  armada-lean already proves the cryptographic core (ArmadaLean.Transact,
  ArmadaLean.TransactOwned): one valid proof spends distinct notes and conserves value,
  and a contract-owned spend is bound to its owner. This module adds the bookkeeping the
  pool performs across many calls: which notes are live, which nullifiers are spent,
  which roots are valid, and which tokens the pool holds.

  The symbolic layer holds no contract layout and no encoding (findings P-1 to
  P-11). Hashes and addresses are Dolev-Yao terms (`ArmadaLean.Poseidon`). A token is a
  `Token`, not a number. "Absent" is `Option` or an empty list, never a zero value. The
  trees are a list of trees, as the protocol defines them, not the contract's storage
  split. Note values are numbers; the 120-bit width stays in the circuit layer
  (`Spendable`, `ArmadaLean.RangeCheck`). `docs/pool-symbolic-changes.md` records each
  change.

  A note is identified by its tree number and Merkle leaf position, not by its content:
  the circuit derives a spend's nullifier as `Poseidon(nullifyingKey, leafIndex)`
  (Transact.circom:97-101) or `Poseidon(ownerField, leafIndex)`
  (TransactOwned.circom:89-97) — a leaf position within the tree that the transaction's
  bound parameters name (`BoundParams.treeNumber`). Two live notes can carry the
  identical preimage; they can never share a `(treeNumber, position)` pair.
  `PoolState.live t` lists `((treeNumber, position), preimage)` entries, one per unspent
  note of token `t`, and a spend removes exactly the positions its witness names
  (`ArmadaLean.Nullifier.nullifier_pos_inj`: distinct positions never collapse onto one
  nullifier).

  The pool cannot see a note's value; it reads only a note's commitment. `PoolState.live`
  is therefore GHOST state: the model's own knowledge of every live note's preimage.
  `PoolState.preimageOf` mirrors the public `PrivacyPoolStorage.preimageOf` mapping
  (PrivacyPoolStorage.sol:248). `PoolState.published` and `PoolState.payouts` are ghost
  records of public data: the owned-note openings that transactions publish
  (`ArmadaLean.PoolOwned`, decision 11) and
  the unshield payouts.

  Scope: local `shield` (ShieldModule.sol:45-90), local `transact` including a local
  unshield (TransactModule.sol:43-96), and `transactOwned` (an open pull
  request, not yet merged into `main`; `ArmadaLean.PoolOwned`'s header gives
  the PR). Out of scope: `processIncomingShield` and
  `atomicCrossChainUnshield` (CCTP-mediated token movement) and the yield vault.
  Nullifier marking, Merkle insertion and the preimage registry follow the same
  shape on every entry point.

  A spend's circuit-level facts (Merkle membership, nullifier derivation, value
  conservation) come from `ArmadaLean.Transact.Constrained` /
  `ArmadaLean.TransactOwned.OwnedConstrained`. Every root a `Step` pushes is
  `ArmadaLean.Merkle.treeRoot TreeDepth` of the leaf list it just extended, computed,
  not chosen. ABDK's 2021-04-01 audit of Railgun's `Commitments.sol` spends findings
  CVF-33, CVF-34, CVF-41 and CVF-42 on the gas-optimized incremental insertion; every one
  is about gas, not soundness.

  S-RG: RAILGUN Project Whitepaper, 2021-07-14.
  <https://resources.cryptocompare.com/asset-management/1823/1674569706520.pdf>,
  sha256 `84ab2207efbbf689503652c42b4861bca5562549961f69fe648feb6dedb83aa8`. Section
  "RAILGUN Core System & Protocol" splits the checks between the circuit and the
  contract; this model cites only the contract's share, at the definitions below. S-RG is
  a 2021 pre-launch design: Armada's contracts, not S-RG, are the source wherever they
  differ. Armada charges a shield-in fee only (`ArmadaLean.Fee`) and no withdrawal fee
  (TransactModule.sol:32, "Unshields are always free").

  The shield fee is pool behaviour (finding P-9). The pool
  splits the gross amount with `_getFee` (ShieldModule.sol:353-371) and pays the fee to
  the treasury: from the caller's wallet on the local path (`_transferTokenIn`,
  ShieldModule.sol:324-340), from the pool's balance on the cross-chain path
  (`_applyShieldFee`, ShieldModule.sol:209-218). `Step.shield` takes the gross amount,
  creates one note of `shieldBase`, records `shieldFee` in `PoolState.treasuryFees`, and
  grows custody by `shieldBase` only. No fee note is created. Separately, `_recognizeFee`
  (PrivacyPoolStorage.sol:280-285) recognizes ANY output whose `npk` equals the
  governance `feeRecipient`.

  HISTORICAL (contract, `testingMode`, now removed): earlier builds of
  `PrivacyPool.verify`/`verifyOwned` returned `true` with no witness when `testingMode`
  was on (ABDK finding CVF-58, Critical, Fixed, on Railgun's `Snark.sol`). armada-poc
  PR #633 removed `testingMode` and the `tx.origin` verification bypass; the pinned
  commit `64436c14` has neither. `Step.transact`/`Step.transactOwned` require a genuine
  `Constrained`/`OwnedConstrained` witness, matching the pinned contract directly; this
  is no longer a departure.

  DEPARTURE (contract → design, no pause and no admin): the merged contract lets the
  owner install a pause controller (`PrivacyPool.setShieldPauseContract`,
  PrivacyPool.sol:466-470) that can block shields (`_requireShieldsNotPaused`,
  ShieldModule.sol:394-399), every spend (`_requireNotEmergencyPaused`) and every
  transfer (`_requireNotWithdrawOnly`, TransactModule.sol:460-475). The deployed pool
  has no admin. This model has no pause of any kind and no admin step: the
  pool-layout audit (finding P-3) found no pause or admin path worth modeling.
  `ArmadaLean.PoolSafety.spend_not_blocked` states that no step by any
  caller disables a pending spend unless it spends one of the same notes.
-/
import ArmadaLean.PoolOwned
import ArmadaLean.Transact
import ArmadaLean.BoundParams
import ArmadaLean.Fee
import Mathlib.Tactic.Says

namespace ArmadaLean

/-! ### Removing a sub-multiset of live notes, by key

A spend names its inputs by leaf position (the model's own `live` entries are
`(position, preimage)` pairs); `removeAll` is generic over the key type so the SAME
function and lemmas serve both `live`'s keyed pairs here and
`ArmadaLean.PoolOwned.markSpent`'s `Term` nullifiers. `removeAll` mirrors `markSpent`'s
shape (fail the first time a requested element is missing) at the multiset level, using
`List.erase` to drop one matching occurrence at a time. -/

/-- Remove one occurrence of each of `wanted` from `pool`, in order, failing (`none`) the
    first time an element is not present. This is the ghost-state analogue of a spend: the
    pool contract itself performs no such removal (it only ever marks nullifiers, via
    `ArmadaLean.PoolOwned.markSpent`); this function removes the *notes* those nullifiers
    name from the model's own live-note bookkeeping. -/
def removeAll {α : Type} [DecidableEq α] : List α → List α → Option (List α)
  | pool, [] => some pool
  | pool, n :: ns => if pool.elem n then removeAll (pool.erase n) ns else none

/-- A successful `removeAll` splits the pool's total `g`-value exactly into the removed
    elements' value and the remaining elements' value. The multiset identity underlying
    both `removeAll_sum` and `removeAll_perm`: removing `n` from `pool` is a reordering
    (`List.perm_cons_erase`) followed by dropping the head, so `listSum` (which only sees
    values, not positions) cannot tell the two apart. -/
theorem removeAll_sum {α : Type} [DecidableEq α] (g : α → Nat)
    {pool wanted pool' : List α} (h : removeAll pool wanted = some pool') :
    listSum (pool.map g) = listSum (wanted.map g) + listSum (pool'.map g) := by
  induction wanted generalizing pool with
  | nil =>
    unfold removeAll at h
    cases h
    (simp? [listSum] says simp only [List.map_nil, listSum, Nat.zero_add])
  | cons n ns ih =>
    unfold removeAll at h
    by_cases hmem : pool.elem n
    · rw [if_pos hmem] at h
      have hmem' : n ∈ pool := List.elem_iff.mp hmem
      have hperm : pool.Perm (n :: pool.erase n) := List.perm_cons_erase hmem'
      have heq : listSum (pool.map g) = listSum ((n :: pool.erase n).map g) :=
        listSum_perm (List.Perm.map g hperm)
      have ihh := ih h
      simp only [List.map_cons, listSum] at heq ⊢
      omega
    · rw [if_neg hmem] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- A successful `removeAll` is a reordering: `pool` is exactly the removed elements plus
    the remainder, as a multiset. This is "a spend removes exactly the notes it spends
    from the live set" at the list level. -/
theorem removeAll_perm {α : Type} [DecidableEq α] {pool wanted pool' : List α}
    (h : removeAll pool wanted = some pool') : pool.Perm (wanted ++ pool') := by
  induction wanted generalizing pool with
  | nil =>
    unfold removeAll at h
    cases h
    exact List.Perm.refl _
  | cons n ns ih =>
    unfold removeAll at h
    by_cases hmem : pool.elem n
    · rw [if_pos hmem] at h
      have hmem' : n ∈ pool := List.elem_iff.mp hmem
      have step1 : pool.Perm (n :: pool.erase n) := List.perm_cons_erase hmem'
      have step2 : (n :: pool.erase n).Perm (n :: (ns ++ pool')) :=
        List.Perm.cons n (ih h)
      exact step1.trans step2
    · rw [if_neg hmem] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- A successful `removeAll`'s remainder only ever loses elements: every entry of
    `pool'` was already an entry of `pool`. The membership half of `removeAll_perm`. -/
theorem removeAll_subset {α : Type} [DecidableEq α] {pool wanted pool' : List α}
    (h : removeAll pool wanted = some pool') : ∀ x ∈ pool', x ∈ pool :=
  fun _x hx => (removeAll_perm h).mem_iff.mpr (List.mem_append_right _ hx)

/-- A successful `removeAll` never introduces a duplicate: if `pool` has no element
    repeated, neither does the remainder. -/
theorem removeAll_nodup {α : Type} [DecidableEq α] {pool wanted pool' : List α}
    (hpool : pool.Nodup) (h : removeAll pool wanted = some pool') : pool'.Nodup := by
  induction wanted generalizing pool with
  | nil =>
    unfold removeAll at h
    cases h
    exact hpool
  | cons w ws ih =>
    unfold removeAll at h
    by_cases hmem : pool.elem w
    · rw [if_pos hmem] at h
      exact ih (List.Nodup.erase w hpool) h
    · rw [if_neg hmem] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- **A successful `removeAll` removes exactly what it names: no requested element can
    still be found in the remainder.** Given `pool` has no duplicate entries,
    `removeAll`'s own recursion erases each `wanted` entry's one and only occurrence —
    `List.Nodup.not_mem_erase` closes it immediately once erased. Needed to rule out a
    live position surviving a spend that also names it (`PoolSafety.live_note_unspent`):
    without `pool`'s own no-duplicates fact this does not hold (two copies of one
    position, one erased, would still leave the other). -/
theorem removeAll_disjoint {α : Type} [DecidableEq α] {pool wanted pool' : List α}
    (hpool : pool.Nodup) (h : removeAll pool wanted = some pool') :
    ∀ w ∈ wanted, w ∉ pool' := by
  induction wanted generalizing pool with
  | nil => exact fun w hw => absurd hw List.not_mem_nil
  | cons w ws ih =>
    unfold removeAll at h
    by_cases hmem : pool.elem w
    · rw [if_pos hmem] at h
      intro x hx hxrest
      rcases List.eq_or_mem_of_mem_cons hx with heq | hx
      · subst heq
        exact (List.Nodup.not_mem_erase hpool) (removeAll_subset h x hxrest)
      · exact ih (List.Nodup.erase w hpool) h x hx hxrest
    · rw [if_neg hmem] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- `removeAll` cannot find an element that is absent from `pool`: wherever `wanted`
    names it, that occurrence's lookup fails, so the whole call returns `none`. The
    subtractive half of `removeAll`'s completeness story; `removeAll_of_subset` is the
    additive converse, and `removeAll_wanted_nodup` below uses this to show a repeated
    `wanted` entry cannot survive a `Nodup` `pool`. -/
theorem removeAll_none_of_not_mem {α : Type} [DecidableEq α] {pool wanted : List α}
    {w : α} (hpool : w ∉ pool) (hwanted : w ∈ wanted) : removeAll pool wanted = none := by
  induction wanted generalizing pool with
  | nil => exact absurd hwanted (by (simp? says simp only [List.not_mem_nil, not_false_eq_true]))
  | cons w0 ws ih =>
    unfold removeAll
    rcases List.eq_or_mem_of_mem_cons hwanted with heq | hw
    · subst heq
      exact if_neg (fun hmem => hpool (List.elem_iff.mp hmem))
    · by_cases hmem : pool.elem w0
      · rw [if_pos hmem]
        exact ih (fun hc => hpool (List.mem_of_mem_erase hc)) hw
      · rw [if_neg hmem]

/-- A successful `removeAll`'s `wanted` list has no duplicate entries: a repeated entry
    would need two matching copies in `pool`, but `pool.Nodup` leaves none once the
    first copy is erased (`removeAll_none_of_not_mem` on `Nodup.not_mem_erase`). Needed
    by `PoolSafety.spend_not_blocked` to re-run `removeAll` against a later pool state
    via `removeAll_of_subset`, which itself needs `wanted.Nodup`. -/
theorem removeAll_wanted_nodup {α : Type} [DecidableEq α] {pool wanted pool' : List α}
    (hpool : pool.Nodup) (h : removeAll pool wanted = some pool') : wanted.Nodup := by
  induction wanted generalizing pool with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold removeAll at h
    by_cases hmem : pool.elem w
    · rw [if_pos hmem] at h
      have hnotin : w ∉ ws := by
        intro hw
        rw [removeAll_none_of_not_mem (List.Nodup.not_mem_erase hpool) hw] at h
        exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
      exact List.nodup_cons.mpr ⟨hnotin, ih (List.Nodup.erase w hpool) h⟩
    · rw [if_neg hmem] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- **`removeAll` completeness: every `wanted` sublist of a `Nodup` pool can be
    removed.** The converse of `removeAll_perm`'s membership half
    (`removeAll_subset`/`removeAll_disjoint`): given enough distinct copies, the
    recursion that fails only when an occurrence is missing never does. Needed by
    `PoolSafety.spend_not_blocked`, which only has (via `Spends`) that `entries` stays
    pointwise live after a disjoint step — not the step's own `removeAll` structure. -/
theorem removeAll_of_subset {α : Type} [DecidableEq α] {pool wanted : List α}
    (hpool : pool.Nodup) (hwanted : wanted.Nodup) (hsub : ∀ w ∈ wanted, w ∈ pool) :
    ∃ pool', removeAll pool wanted = some pool' := by
  induction wanted generalizing pool with
  | nil => exact ⟨pool, rfl⟩
  | cons w ws ih =>
    have hmem : w ∈ pool := hsub w List.mem_cons_self
    have hwne : w ∉ ws := (List.nodup_cons.mp hwanted).1
    have hsub' : ∀ x ∈ ws, x ∈ pool.erase w := by
      intro x hx
      have hxne : x ≠ w := by
        intro heq
        rw [heq] at hx
        exact hwne hx
      exact (List.mem_erase_of_ne hxne).mpr (hsub x (List.mem_cons_of_mem w hx))
    obtain ⟨pool', hpool'⟩ := ih (List.Nodup.erase w hpool) (List.nodup_cons.mp hwanted).2 hsub'
    refine ⟨pool', ?_⟩
    unfold removeAll
    rw [if_pos (List.elem_iff.mpr hmem)]
    exact hpool'

/-! ### Tagging a batch of new notes with the leaf positions they land at

`MerkleModule.insertLeaves` assigns a batch's leaf positions in insertion order,
starting right after whatever was already in its tree (MerkleModule.sol:54-121): the
first new leaf lands at the tree's current leaf count, the next right after, and so on.
`withPositionsFrom` is the one place that reads this off; `withTreePositionsFrom` pairs
that with the tree number the batch actually landed in, since `PoolState.live`'s keys
are now `(treeNumber, position)` pairs. Reused by every `Step` constructor below that
inserts notes into `live`. -/

/-- Tag `l`'s elements with ascending positions starting at `start`. -/
def withPositionsFrom {α : Type} (start : Nat) : List α → List (Nat × α)
  | [] => []
  | a :: rest => (start, a) :: withPositionsFrom (start + 1) rest

/-- Tagging with positions does not touch values: mapping any function `f` over the
    tagged list's second components is the same as mapping `f` over the original list.
    The value-sum bridge every `Step` constructor's `HeldInvariant` proof needs. -/
theorem withPositionsFrom_map {α β : Type} (f : α → β) (start : Nat) (l : List α) :
    (withPositionsFrom start l).map (fun p => f p.2) = l.map f := by
  induction l generalizing start with
  | nil => rfl
  | cons a rest ih => (simp? [withPositionsFrom, ih] says simp only [withPositionsFrom, List.map_cons, ih])

/-- Tag `l`'s elements with ascending `(treeNumber, position)` keys, positions starting
    at `start` within tree `treeNumber`. -/
def withTreePositionsFrom {α : Type} (treeNumber start : Nat) (l : List α) :
    List ((Nat × Nat) × α) :=
  (withPositionsFrom start l).map (fun p => ((treeNumber, p.1), p.2))

/-- The value-sum bridge for `withTreePositionsFrom`, composing `withPositionsFrom_map`
    with the tree-number tag, which never touches values either. -/
theorem withTreePositionsFrom_map {α β : Type} (f : α → β) (treeNumber start : Nat)
    (l : List α) :
    (withTreePositionsFrom treeNumber start l).map (fun p => f p.2) = l.map f := by
  unfold withTreePositionsFrom
  rw [List.map_map]
  exact withPositionsFrom_map f start l

/-- `withTreePositionsFrom` always tags with the SAME `treeNumber` — the fact every
    "which tree did my new note land in" theorem reads off. -/
theorem withTreePositionsFrom_treeNumber {α : Type} (treeNumber start : Nat) (l : List α)
    (p : (Nat × Nat) × α) (hp : p ∈ withTreePositionsFrom treeNumber start l) :
    p.1.1 = treeNumber := by
  unfold withTreePositionsFrom at hp
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hp
  rw [← hq]

/-- `withPositionsFrom`'s tags never go below `start`: every assigned position is at
    least `start`. Half of `live_note_unspent`'s fresh-position argument (the other
    half is `insertStart_eq`). -/
theorem withPositionsFrom_pos_ge {α : Type} (start : Nat) (l : List α) (p : Nat × α)
    (hp : p ∈ withPositionsFrom start l) : start ≤ p.1 := by
  induction l generalizing start with
  | nil => (simp? [withPositionsFrom] at hp says simp only [withPositionsFrom, List.not_mem_nil] at hp)
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp
    rcases hp with heq | hp
    · (simp? [heq] says simp only [heq, Std.le_refl])
    · have := ih (start + 1) hp
      omega

/-- `withPositionsFrom` never tags two different elements with the same position: the
    position a pair carries already determines its value, within one call. Used by
    `PoolSafety`'s per-tree live-position uniqueness invariant to rule out a batch of
    fresh notes colliding with itself. -/
theorem withPositionsFrom_unique {α : Type} (start : Nat) (l : List α) (p1 p2 : Nat × α)
    (hp1 : p1 ∈ withPositionsFrom start l) (hp2 : p2 ∈ withPositionsFrom start l)
    (heq : p1.1 = p2.1) : p1.2 = p2.2 := by
  induction l generalizing start with
  | nil => (simp? [withPositionsFrom] at hp1 says simp only [withPositionsFrom, List.not_mem_nil] at hp1)
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp1 hp2
    rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
    · rw [h1, h2]
    · exfalso
      have hge := withPositionsFrom_pos_ge (start + 1) rest p2 h2
      rw [h1] at heq
      (simp? at heq says simp only at heq)
      omega
    · exfalso
      have hge := withPositionsFrom_pos_ge (start + 1) rest p1 h1
      rw [h2] at heq
      (simp? at heq says simp only at heq)
      omega
    · exact ih (start + 1) h1 h2

/-- The tree-tagged counterpart of `withPositionsFrom_pos_ge`. -/
theorem withTreePositionsFrom_pos_ge {α : Type} (treeNumber start : Nat) (l : List α)
    (p : (Nat × Nat) × α) (hp : p ∈ withTreePositionsFrom treeNumber start l) :
    start ≤ p.1.2 := by
  unfold withTreePositionsFrom at hp
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
  rw [← heq]
  exact withPositionsFrom_pos_ge start l q hq

/-- The tree-tagged counterpart of `withPositionsFrom_unique`. -/
theorem withTreePositionsFrom_unique {α : Type} (treeNumber start : Nat) (l : List α)
    (p1 p2 : (Nat × Nat) × α) (hp1 : p1 ∈ withTreePositionsFrom treeNumber start l)
    (hp2 : p2 ∈ withTreePositionsFrom treeNumber start l) (heq : p1.1 = p2.1) :
    p1.2 = p2.2 := by
  unfold withTreePositionsFrom at hp1 hp2
  obtain ⟨q1, hq1, heq1⟩ := List.mem_map.mp hp1
  obtain ⟨q2, hq2, heq2⟩ := List.mem_map.mp hp2
  rw [← heq1, ← heq2]
  rw [← heq1, ← heq2] at heq
  simp only [Prod.mk.injEq] at heq
  exact withPositionsFrom_unique start l q1 q2 hq1 hq2 heq.2

/-- `withPositionsFrom`'s tags never reach `start + l.length`: the upper-bound
    counterpart of `withPositionsFrom_pos_ge`. Together they pin a freshly-inserted
    batch's positions to the exact slice `[start, start + l.length)` — needed to show
    a batch cannot land on a position any surviving live entry already occupies. -/
theorem withPositionsFrom_pos_lt {α : Type} (start : Nat) (l : List α) (p : Nat × α)
    (hp : p ∈ withPositionsFrom start l) : p.1 < start + l.length := by
  induction l generalizing start with
  | nil => (simp? [withPositionsFrom] at hp says simp only [withPositionsFrom, List.not_mem_nil] at hp)
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp
    rcases hp with heq | hp
    · (simp? [heq] says simp only [heq, List.length_cons, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ])
    · have := ih (start + 1) hp
      simp only [List.length_cons]
      omega

/-- The tree-tagged counterpart of `withPositionsFrom_pos_lt`. -/
theorem withTreePositionsFrom_pos_lt {α : Type} (treeNumber start : Nat) (l : List α)
    (p : (Nat × Nat) × α) (hp : p ∈ withTreePositionsFrom treeNumber start l) :
    p.1.2 < start + l.length := by
  unfold withTreePositionsFrom at hp
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
  rw [← heq]
  exact withPositionsFrom_pos_lt start l q hq

/-- `withPositionsFrom`'s tags never repeat: the strictly-increasing positions it
    assigns are pairwise distinct, so the tagged list carries no duplicate entry. -/
theorem withPositionsFrom_nodup {α : Type} (start : Nat) (l : List α) :
    (withPositionsFrom start l).Nodup := by
  induction l generalizing start with
  | nil => (simp? [withPositionsFrom] says simp only [withPositionsFrom, List.nodup_nil])
  | cons a rest ih =>
    simp only [withPositionsFrom, List.nodup_cons]
    refine ⟨?_, ih (start + 1)⟩
    intro hmem
    have := withPositionsFrom_pos_ge (start + 1) rest (start, a) hmem
    omega

/-- The tree-tagged counterpart of `withPositionsFrom_nodup`. Needed, together with
    `removeAll_nodup`/`removeAll_disjoint`, to show a spend's freshly-inserted batch
    never collides with a surviving live position
    (`ArmadaLean.PoolSafety.live_note_unspent`). -/
theorem withTreePositionsFrom_nodup {α : Type} (treeNumber start : Nat) (l : List α) :
    (withTreePositionsFrom treeNumber start l).Nodup := by
  induction l generalizing start with
  | nil => (simp? [withTreePositionsFrom, withPositionsFrom] says simp only [withTreePositionsFrom, withPositionsFrom, List.map_nil, List.nodup_nil])
  | cons a rest ih =>
    have hunfold : withTreePositionsFrom treeNumber start (a :: rest) =
        ((treeNumber, start), a) :: withTreePositionsFrom treeNumber (start + 1) rest := by
      (simp? [withTreePositionsFrom, withPositionsFrom] says simp only [withTreePositionsFrom, withPositionsFrom, List.map_cons])
    rw [hunfold, List.nodup_cons]
    refine ⟨?_, ih (start + 1)⟩
    intro hmem
    have hge := withTreePositionsFrom_pos_ge treeNumber (start + 1) rest ((treeNumber, start), a) hmem
    simp only at hge
    omega

/-- Every element `withPositionsFrom` tags came from the original list — the position
    tag never changes which values are present, only labels them. Used to trace a live
    note's value back to the circuit output it came from
    (`ArmadaLean.PoolSafety.live_values_spendable`). -/
theorem withPositionsFrom_snd_mem {α : Type} (start : Nat) (l : List α) (p : Nat × α)
    (hp : p ∈ withPositionsFrom start l) : p.2 ∈ l := by
  induction l generalizing start with
  | nil => (simp? [withPositionsFrom] at hp says simp only [withPositionsFrom, List.not_mem_nil] at hp)
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp
    rcases hp with heq | hp
    · rw [heq]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih (start + 1) hp)

/-- The tree-tagged counterpart of `withPositionsFrom_snd_mem`. -/
theorem withTreePositionsFrom_snd_mem {α : Type} (treeNumber start : Nat) (l : List α)
    (p : (Nat × Nat) × α) (hp : p ∈ withTreePositionsFrom treeNumber start l) : p.2 ∈ l := by
  unfold withTreePositionsFrom at hp
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
  rw [← heq]
  exact withPositionsFrom_snd_mem start l q hq

/-- The element at index `j` of `l` is tagged with position `start + j`. -/
theorem withPositionsFrom_mem_of_getElem? {α : Type} (start : Nat) (l : List α) (j : Nat)
    {a : α} (h : l[j]? = some a) : (start + j, a) ∈ withPositionsFrom start l := by
  induction l generalizing start j with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at h
  | cons x rest ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have := ih (start + 1) j h
      rw [show start + (j + 1) = start + 1 + j by omega]
      exact List.mem_cons_of_mem _ this

/-- The tree-tagged counterpart of `withPositionsFrom_mem_of_getElem?`. -/
theorem withTreePositionsFrom_mem_of_getElem? {α : Type} (treeNumber start : Nat) (l : List α)
    (j : Nat) {a : α} (h : l[j]? = some a) :
    ((treeNumber, start + j), a) ∈ withTreePositionsFrom treeNumber start l := by
  unfold withTreePositionsFrom
  exact List.mem_map.mpr ⟨(start + j, a), withPositionsFrom_mem_of_getElem? start l j h, rfl⟩

/-- `(l ++ l').getD i d = l.getD i d` once `i` is within `l`'s own length: appending
    never disturbs an existing index. `insertLeaves_leavesAt_stable` ("a leaf, once
    placed, never moves") rests on this. -/
theorem List.getD_append_of_lt {α : Type} (l l' : List α) (i : Nat) (d : α)
    (h : i < l.length) : (l ++ l').getD i d = l.getD i d := by
  induction l generalizing i with
  | nil => (simp? at h says simp only [List.length_nil, Nat.not_lt_zero] at h)
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih i' (by (simp? at h says simp only [List.length_cons, Nat.add_lt_add_iff_right] at h); omega)

/-! ### The on-chain preimage registry

`PrivacyPoolStorage.preimageOf` (PrivacyPoolStorage.sol:248) is written by three call
sites: `ShieldModule.shield`/`processIncomingShield` write one entry per shielded note,
unconditionally (ShieldModule.sol:71, :136); `TransactModule._recordPreimages`
(TransactModule.sol:590-604) writes one entry per non-zero `publicOutputs` entry, for
both `transact` (optional) and `transactOwned` (mandatory). `ArmadaLean.PoolOwned`
already proves the per-call consistency lemma (`recordStep_preserves_consistency`); this
section lifts it to an arbitrary batch of records so one lemma covers all three call
sites. -/

/-- Apply a batch of `(commitment, preimage)` records to a registry, in order — the
    pool-level generalization of `ArmadaLean.PoolOwned.recordPreimages` that does not
    assume the batch comes from one transaction's `Fin K` output indexing. -/
def applyRecords (reg : PreimageRegistry) : List (Term × CommitmentPreimage) → PreimageRegistry
  | [] => reg
  | (c, p) :: rest => applyRecords (recordStep reg c p) rest

/-- `applyRecords` preserves registry consistency, given every record is valid (hashes to
    the commitment it is recorded under) — the same hypothesis
    `ArmadaLean.PoolOwned.preimageOf_consistent` takes per-transaction, here taken per
    batch. -/
theorem applyRecords_preserves_consistency {reg : PreimageRegistry}
    (hreg : RegistryConsistent reg) {records : List (Term × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1) :
    RegistryConsistent (applyRecords reg records) := by
  induction records generalizing reg with
  | nil => exact hreg
  | cons cp rest ih =>
    obtain ⟨c, p⟩ := cp
    apply ih
    · exact recordStep_preserves_consistency hreg
        (hvalid (c, p) List.mem_cons_self)
    · intro cp' hcp'
      exact hvalid cp' (List.mem_cons_of_mem (c, p) hcp')

/-- `applyRecords` distributes over `++`: folding two batches in sequence is the same
    as folding their concatenation. -/
@[simp]
theorem applyRecords_append (reg : PreimageRegistry) (l1 l2 : List (Term × CommitmentPreimage)) :
    applyRecords reg (l1 ++ l2) = applyRecords (applyRecords reg l1) l2 := by
  induction l1 generalizing reg with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.cons_append]
    obtain ⟨c, p⟩ := hd
    show applyRecords (recordStep reg c p) (tl ++ l2) = _
    rw [ih (recordStep reg c p)]
    rfl

/-- `hashCommitment` is injective: two preimages with the same commitment are the same
    preimage. Collision resistance of `Term.hash3` (by construction,
    `ArmadaLean.Poseidon`), the same fact `ArmadaLean.TransactOwned.commitment_owner_inj`
    and `ArmadaLean.Transact.commitment_mpk_inj` already rest on, applied to the
    preimage's own `(npk, token, value)` triple. -/
theorem hashCommitment_inj {p1 p2 : CommitmentPreimage} (h : hashCommitment p1 = hashCommitment p2) :
    p1 = p2 := by
  obtain ⟨h1, h2, h3⟩ := Term.hash3_inj h
  have ht := tokenId_inj h2
  cases p1; cases p2
  (simp_all? [Term.val.injEq] says simp_all only [Term.val.injEq])

/-- Once `reg` already answers key `c` with `p`, folding a batch through it cannot
    change that answer, provided every later record touching key `c` agrees with `p` —
    the invariant `applyRecords_returns` below bootstraps and carries through a whole
    batch. -/
theorem applyRecords_preserves_key {reg : PreimageRegistry} {records : List (Term × CommitmentPreimage)}
    {c : Term} {p : CommitmentPreimage} (hreg : reg c = some p)
    (hagree : ∀ cp ∈ records, cp.1 = c → cp.2 = p) :
    applyRecords reg records c = some p := by
  induction records generalizing reg with
  | nil => exact hreg
  | cons hd tl ih =>
    obtain ⟨c', p'⟩ := hd
    unfold applyRecords
    refine ih ?_ (fun cp hcp => hagree cp (List.mem_cons_of_mem _ hcp))
    show recordStep reg c' p' c = some p
    unfold recordStep
    by_cases hcc : c = c'
    · rw [if_pos hcc]
      have := hagree (c', p') List.mem_cons_self hcc.symm
      simp only [] at this
      rw [this]
    · rw [if_neg hcc]; exact hreg

/-- **A valid batch is recoverable from the registry it produces.** If every record in a
    batch hashes to its own key, then `applyRecords` settles on `p` at key `c` for every
    record `(c, p)` of the batch: a later record sharing key `c` must, by
    `hashCommitment_inj`, carry the identical preimage `p`. The key lemma behind
    `transactOwned_records_all`. -/
theorem applyRecords_returns {reg : PreimageRegistry} {records : List (Term × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    {c : Term} {p : CommitmentPreimage} (hmem : (c, p) ∈ records) :
    applyRecords reg records c = some p := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  rw [hsplit, applyRecords_append]
  unfold applyRecords
  apply applyRecords_preserves_key
  · unfold recordStep
    (simp? says simp only [↓reduceIte])
  · intro cp hcp hcpeq
    have hcpmem : cp ∈ records := by
      rw [hsplit]
      exact List.mem_append_right pre (List.mem_cons_of_mem _ hcp)
    have hcpval := hvalid cp hcpmem
    have hpval := hvalid (c, p) hmem
    rw [hcpeq] at hcpval
    exact hashCommitment_inj (hcpval.trans hpval.symm)

/-- The output records of a transact batch: for each output `j`, its commitment paired
    with its preimage. Shared by `transactOutputRecords` and `ownedOutputRecords`. -/
def outputRecords {M : Nat} (commitmentsOut : Fin M → Term) (npkOut : Fin M → Term)
    (token : Token) (valueOut : Fin M → Nat) : List (Term × CommitmentPreimage) :=
  List.ofFn fun j => (commitmentsOut j, (⟨npkOut j, token, valueOut j⟩ : CommitmentPreimage))

/-- The `(commitment, preimage)` pair a plain `Transact` output would record, if
    disclosed — the full candidate batch `Step.transact`'s `records` is a sublist of. -/
def transactOutputRecords {N M : Nat} (w : TransactWitness N M)
    (pub : TransactPublic N M) : List (Term × CommitmentPreimage) :=
  outputRecords pub.commitmentsOut w.npkOut w.token w.valueOut

/-- Every candidate record a plain `Transact` could disclose is valid: its commitment
    key is exactly its own `hashCommitment` (`Constrained.outputs`). -/
theorem transactOutputRecords_valid {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M}
    (hC : Constrained w pub) :
    ∀ cp ∈ transactOutputRecords w pub, hashCommitment cp.2 = cp.1 := by
  intro cp hcp
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
  rw [← hj]
  exact (hC.outputs j).symm

/-- The `(commitment, preimage)` pair an owned `TransactOwned` output records —
    `transactOwned` discloses every one (`_validatePublicOutputs(requireAll = true)`,
    TransactModule.sol:630-634), so this is `Step.transactOwned`'s whole batch, not a
    candidate list a caller trims. -/
def ownedOutputRecords {N M : Nat} (w : TransactOwnedWitness N M)
    (pub : TransactOwnedPublic N M) : List (Term × CommitmentPreimage) :=
  outputRecords pub.commitmentsOut w.npkOut w.token w.valueOut

/-- Every owned output's record is valid: its commitment key is exactly its own
    `hashCommitment` (`OwnedConstrained.outputs`). -/
theorem ownedOutputRecords_valid {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (hC : OwnedConstrained w pub) :
    ∀ cp ∈ ownedOutputRecords w pub, hashCommitment cp.2 = cp.1 := by
  intro cp hcp
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
  rw [← hj]
  exact (hC.outputs j).symm

/-- A record list is valid when every record hashes to the commitment it is recorded
    under. `transactOutputRecords_valid` and `ownedOutputRecords_valid` give it for a
    witness's own records; `recordsMatch`/`recordsComplete` give it for a call's records. -/
structure RecordsValid (l : List (Term × CommitmentPreimage)) : Prop where
  valid : ∀ cp ∈ l, hashCommitment cp.2 = cp.1

/-- A commitment that no record names keeps its registry entry. -/
theorem applyRecords_of_not_mem (reg : PreimageRegistry) (l : List (Term × CommitmentPreimage))
    (c : Term) (hc : c ∉ l.map Prod.fst) : applyRecords reg l c = reg c := by
  induction l generalizing reg with
  | nil => rfl
  | cons cp rest ih =>
    obtain ⟨c0, p0⟩ := cp
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    simp only [applyRecords]
    rw [ih _ hc.2]
    simp only [recordStep, if_neg hc.1]

/-- Two valid record lists with one set of commitments give one registry. The contract
    applies the records of a call; the model applies the witness's own records. The two
    lists agree on their commitments, so the registries agree. A valid list sets the
    entry of each of its commitments to the one preimage that hashes to it, whatever the
    order and the repetitions (`key` below). -/
theorem applyRecords_eq_of_keys (reg : PreimageRegistry)
    (l₁ l₂ : List (Term × CommitmentPreimage)) (h₁ : RecordsValid l₁) (h₂ : RecordsValid l₂)
    (hkeys : ∀ c, c ∈ l₁.map Prod.fst ↔ c ∈ l₂.map Prod.fst) :
    applyRecords reg l₁ = applyRecords reg l₂ := by
  have key : ∀ (l : List (Term × CommitmentPreimage)), RecordsValid l →
      ∀ (reg : PreimageRegistry) (c : Term) (p : CommitmentPreimage), (c, p) ∈ l →
        applyRecords reg l c = some p := by
    intro l
    induction l with
    | nil => intro _ _ _ _ hmem; exact absurd hmem List.not_mem_nil
    | cons cp rest ih =>
      intro hl reg c p hmem
      obtain ⟨c0, p0⟩ := cp
      have hrest : RecordsValid rest := ⟨fun cp hcp => hl.valid cp (List.mem_cons_of_mem _ hcp)⟩
      simp only [applyRecords]
      rcases List.mem_cons.mp hmem with heq | hmem
      · injection heq with hc0 hp0
        subst hc0; subst hp0
        by_cases hc : c ∈ rest.map Prod.fst
        · obtain ⟨⟨c', p'⟩, hmem', hc'⟩ := List.mem_map.mp hc
          simp only at hc'
          subst hc'
          have e₁ := hl.valid (c', p') (List.mem_cons_of_mem _ hmem')
          have e₂ := hl.valid (c', p) List.mem_cons_self
          simp only at e₁ e₂
          have hp : p' = p := hashCommitment_inj (e₁.trans e₂.symm)
          subst hp
          exact ih hrest _ _ _ hmem'
        · rw [applyRecords_of_not_mem _ _ _ hc]
          simp only [recordStep, ↓reduceIte]
      · exact ih hrest _ _ _ hmem
  funext c
  by_cases hc : c ∈ l₁.map Prod.fst
  · obtain ⟨⟨c', p₁⟩, hm₁, hc₁⟩ := List.mem_map.mp hc
    obtain ⟨⟨c'', p₂⟩, hm₂, hc₂⟩ := List.mem_map.mp ((hkeys c).mp hc)
    simp only at hc₁ hc₂
    subst hc₁; subst hc₂
    rw [key l₁ h₁ reg _ _ hm₁, key l₂ h₂ reg _ _ hm₂]
    have e₁ := h₁.valid _ hm₁
    have e₂ := h₂.valid _ hm₂
    simp only at e₁ e₂
    rw [hashCommitment_inj (e₁.trans e₂.symm)]
  · rw [applyRecords_of_not_mem reg l₁ c hc,
      applyRecords_of_not_mem reg l₂ c (fun h => hc ((hkeys c).mpr h))]

/-! ### The Merkle tree forest

The protocol keeps a sequence of Merkle trees. Each tree holds at most `2 ^ TreeDepth`
leaves (`ArmadaLean.Merkle`). New leaves go into the last tree; a batch that does not
fit starts a new tree (`MerkleModule.insertLeaves`, MerkleModule.sol:62-70; an exactly
full tree does not roll over). Every tree keeps every root it ever had
(`rootHistory`, PrivacyPoolStorage.sol:171, S-RG: "the current or a previous Merkle
root"). The model is a list of trees, numbered by position. The contract's split into a
current-tree pointer and per-tree maps (`treeNumber`, `nextLeafIndex`, `rootHistory`,
PrivacyPoolStorage.sol:150-171) is storage layout; audit finding P-11 records the
earlier `closedTrees`/`leaves`/`roots` copy of it. -/

/-- One tree: its leaves, in insertion order, and every root it has had, newest first. -/
structure TreeState where
  leaves : List Term
  roots : List Term

/-- A tree with no leaves and no roots: the starting point of a tree that a batch opens. -/
def TreeState.empty : TreeState := ⟨[], []⟩

/-- Append `newLeaves` to a tree and record the new root, `treeRoot` of the new leaf
    list (computed, not chosen). -/
def TreeState.extend (t : TreeState) (newLeaves : List Term) : TreeState :=
  ⟨t.leaves ++ newLeaves, treeRoot TreeDepth (t.leaves ++ newLeaves) :: t.roots⟩

/-- The leaves of tree `tn`. A tree that does not exist has no leaves. -/
def leavesAt (trees : List TreeState) (tn : Nat) : List Term :=
  match trees[tn]? with
  | some t => t.leaves
  | none => []

/-- The root history of tree `tn`. A tree that does not exist has no roots, so no proof
    can name a root of it. -/
def rootsAt (trees : List TreeState) (tn : Nat) : List Term :=
  match trees[tn]? with
  | some t => t.roots
  | none => []

/-- The tree that a batch of `count` new leaves goes into: the last tree if the batch
    fits, else a new tree after it (MerkleModule.sol:66). -/
def insertTree (trees : List TreeState) (count : Nat) : Nat :=
  match trees.getLast? with
  | some cur => if cur.leaves.length + count ≤ 2 ^ TreeDepth then trees.length - 1 else trees.length
  | none => trees.length

/-- The position of the first leaf of a batch: the current leaf count of its tree. -/
def insertStart (trees : List TreeState) (count : Nat) : Nat :=
  (leavesAt trees (insertTree trees count)).length

/-- `MerkleModule.insertLeaves` (MerkleModule.sol:54-121), non-incrementally: extend the
    last tree, or start a new tree when the batch does not fit. -/
def insertLeaves (trees : List TreeState) (newLeaves : List Term) : List TreeState :=
  match trees.getLast? with
  | some cur =>
    if cur.leaves.length + newLeaves.length ≤ 2 ^ TreeDepth then
      trees.dropLast ++ [cur.extend newLeaves]
    else trees ++ [TreeState.empty.extend newLeaves]
  | none => [TreeState.empty.extend newLeaves]

theorem insertTree_nil (count : Nat) : insertTree [] count = 0 := rfl

@[simp]
theorem insertLeaves_nil (newLeaves : List Term) :
    insertLeaves [] newLeaves = [TreeState.empty.extend newLeaves] := rfl

theorem insertTree_concat (init : List TreeState) (cur : TreeState) (count : Nat) :
    insertTree (init ++ [cur]) count =
      if cur.leaves.length + count ≤ 2 ^ TreeDepth then init.length else init.length + 1 := by
  (simp? [insertTree] says simp only [insertTree, List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_one_sub_one])

theorem insertLeaves_concat (init : List TreeState) (cur : TreeState) (newLeaves : List Term) :
    insertLeaves (init ++ [cur]) newLeaves =
      if cur.leaves.length + newLeaves.length ≤ 2 ^ TreeDepth then init ++ [cur.extend newLeaves]
      else init ++ [cur, TreeState.empty.extend newLeaves] := by
  (simp? [insertLeaves] says simp only [insertLeaves, List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq, List.cons_ne_self, not_false_eq_true, List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil, List.append_assoc, List.cons_append, List.nil_append])

theorem List.getElem?_concat_eq {α : Type} (l : List α) (x : α) (i : Nat) :
    (l ++ [x])[i]? = if i < l.length then l[i]? else if i = l.length then some x else none := by
  by_cases h1 : i < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : i = l.length
    · subst h2; (simp? says simp only [Nat.sub_self, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, ↓reduceIte])
    · rw [if_neg h2]; (simp? says simp only [_root_.getElem?_eq_none_iff, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff]); omega

theorem List.getElem?_concat2_eq {α : Type} (l : List α) (x y : α) (i : Nat) :
    (l ++ [x, y])[i]? = if i < l.length then l[i]? else if i = l.length then some x
      else if i = l.length + 1 then some y else none := by
  by_cases h1 : i < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : i = l.length
    · subst h2; (simp? says simp only [Nat.sub_self, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, ↓reduceIte])
    · rw [if_neg h2]
      by_cases h3 : i = l.length + 1
      · subst h3; (simp? says simp only [Nat.add_sub_cancel_left, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Nat.add_left_cancel_iff, ↓reduceIte])
      · rw [if_neg h3]; (simp? says simp only [_root_.getElem?_eq_none_iff, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.not_lt]); omega

/-- **An insertion changes only the target tree, and it extends that tree.** The one
    equation every other forest lemma below follows from. A target tree that does not
    exist yet (a new tree) starts from `TreeState.empty`. -/
@[simp]
theorem insertLeaves_getElem? (trees : List TreeState) (newLeaves : List Term) (tn : Nat) :
    (insertLeaves trees newLeaves)[tn]? =
      if tn = insertTree trees newLeaves.length then
        some ((match trees[tn]? with | some t => t | none => TreeState.empty).extend newLeaves)
      else trees[tn]? := by
  rcases List.eq_nil_or_concat trees with h | ⟨init, cur, h⟩
  · subst h
    rw [insertLeaves_nil, insertTree_nil]
    cases tn <;> simp
  · rw [List.concat_eq_append] at h
    subst h
    rw [insertLeaves_concat, insertTree_concat]
    by_cases hfit : cur.leaves.length + newLeaves.length ≤ 2 ^ TreeDepth
    · rw [if_pos hfit, if_pos hfit, List.getElem?_concat_eq, List.getElem?_concat_eq]
      by_cases h1 : tn < init.length
      · rw [if_pos h1, if_neg (by omega), if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : tn = init.length
        · subst h2; (simp? says simp only [↓reduceIte, Nat.lt_irrefl])
        · rw [if_neg h2, if_neg h2, if_neg h1, if_neg h2]
    · rw [if_neg hfit, if_neg hfit, List.getElem?_concat2_eq, List.getElem?_concat_eq]
      by_cases h1 : tn < init.length
      · rw [if_pos h1, if_neg (by omega), if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : tn = init.length
        · rw [if_pos h2, if_neg (by omega), if_pos h2]
        · rw [if_neg h2, if_neg h2]

/-- The leaves of tree `tn` after an insertion: the target tree gains the batch at its
    end; every other tree is unchanged. -/
@[simp]
theorem insertLeaves_leavesAt (trees : List TreeState) (newLeaves : List Term) (tn : Nat) :
    leavesAt (insertLeaves trees newLeaves) tn =
      if tn = insertTree trees newLeaves.length then leavesAt trees tn ++ newLeaves
      else leavesAt trees tn := by
  unfold leavesAt
  rw [insertLeaves_getElem?]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h, if_pos h]
    cases trees[tn]? <;> simp [TreeState.extend, TreeState.empty]
  · rw [if_neg h, if_neg h]

/-- The roots of tree `tn` after an insertion: the target tree gains exactly the root of
    its new leaf list; every other tree is unchanged. -/
@[simp]
theorem insertLeaves_rootsAt (trees : List TreeState) (newLeaves : List Term) (tn : Nat) :
    rootsAt (insertLeaves trees newLeaves) tn =
      if tn = insertTree trees newLeaves.length then
        treeRoot TreeDepth (leavesAt trees tn ++ newLeaves) :: rootsAt trees tn
      else rootsAt trees tn := by
  unfold rootsAt leavesAt
  rw [insertLeaves_getElem?]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h, if_pos h]
    cases trees[tn]? <;> simp [TreeState.extend, TreeState.empty]
  · rw [if_neg h, if_neg h]

/-- The target tree has room for a batch that fits in one tree. -/
theorem insertLeaves_target_fits (trees : List TreeState) (newLeaves : List Term)
    (hNew : newLeaves.length ≤ 2 ^ TreeDepth) :
    (leavesAt trees (insertTree trees newLeaves.length)).length + newLeaves.length ≤
      2 ^ TreeDepth := by
  rcases List.eq_nil_or_concat trees with h | ⟨init, cur, h⟩
  · subst h; (simp? [leavesAt, insertTree_nil, hNew] says simp only [leavesAt, insertTree_nil, List.length_nil, Nat.lt_irrefl, not_false_eq_true, getElem?_neg, Nat.zero_add, hNew])
  · rw [List.concat_eq_append] at h
    subst h
    rw [insertTree_concat]
    by_cases hfit : cur.leaves.length + newLeaves.length ≤ 2 ^ TreeDepth
    · rw [if_pos hfit]
      (simp? [leavesAt, hfit] says simp only [leavesAt, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, hfit])
    · rw [if_neg hfit]
      (simp? [leavesAt, hNew] says simp only [leavesAt, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_irrefl, not_false_eq_true, getElem?_neg, hNew])

/-- `insertStart` is the target tree's leaf count, by definition. -/
theorem insertStart_eq (trees : List TreeState) (count : Nat) :
    insertStart trees count = (leavesAt trees (insertTree trees count)).length := rfl

/-- One insertion either leaves tree `tn`'s roots unchanged or prepends exactly one new
    root. -/
theorem insertLeaves_rootsAt_shape (trees : List TreeState) (newLeaves : List Term) (tn : Nat) :
    rootsAt (insertLeaves trees newLeaves) tn = rootsAt trees tn ∨
      ∃ r, rootsAt (insertLeaves trees newLeaves) tn = r :: rootsAt trees tn := by
  rw [insertLeaves_rootsAt]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h]; exact Or.inr ⟨_, rfl⟩
  · rw [if_neg h]; exact Or.inl rfl

/-- **One insertion's new root is `treeRoot TreeDepth` of the tree's new leaf list.**
    Tree `tn` either sees no change, or its root history gains exactly that root. -/
theorem insertLeaves_rootsAt_matches_leavesAt (trees : List TreeState) (newLeaves : List Term)
    (tn : Nat) :
    (leavesAt (insertLeaves trees newLeaves) tn = leavesAt trees tn ∧
      rootsAt (insertLeaves trees newLeaves) tn = rootsAt trees tn) ∨
    rootsAt (insertLeaves trees newLeaves) tn =
      treeRoot TreeDepth (leavesAt (insertLeaves trees newLeaves) tn) :: rootsAt trees tn := by
  rw [insertLeaves_rootsAt, insertLeaves_leavesAt]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h, if_pos h]; exact Or.inr rfl
  · rw [if_neg h, if_neg h]; exact Or.inl ⟨rfl, rfl⟩

/-- **A tree's leaf list never exceeds the one-tree capacity, after any insertion** —
    given it did not before, and the batch itself fits in one tree. -/
theorem insertLeaves_leavesAt_capacity (trees : List TreeState) (newLeaves : List Term)
    (tn : Nat) (hNewCap : newLeaves.length ≤ 2 ^ TreeDepth)
    (hOldCap : ∀ k, (leavesAt trees k).length ≤ 2 ^ TreeDepth) :
    (leavesAt (insertLeaves trees newLeaves) tn).length ≤ 2 ^ TreeDepth := by
  rw [insertLeaves_leavesAt]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h, List.length_append, h]
    exact insertLeaves_target_fits trees newLeaves hNewCap
  · rw [if_neg h]; exact hOldCap tn

/-- **A leaf, once placed at a position, never moves.** Insertion only appends. -/
theorem insertLeaves_leavesAt_stable (trees : List TreeState) (newLeaves : List Term)
    (tn pos : Nat) (d : Term) (hpos : pos < (leavesAt trees tn).length) :
    (leavesAt (insertLeaves trees newLeaves) tn).getD pos d = (leavesAt trees tn).getD pos d := by
  rw [insertLeaves_leavesAt]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h]; exact List.getD_append_of_lt _ _ pos d hpos
  · rw [if_neg h]

/-- A tree's leaf list only grows. -/
theorem insertLeaves_leavesAt_length_ge (trees : List TreeState) (newLeaves : List Term)
    (tn : Nat) :
    (leavesAt trees tn).length ≤ (leavesAt (insertLeaves trees newLeaves) tn).length := by
  rw [insertLeaves_leavesAt]
  by_cases h : tn = insertTree trees newLeaves.length
  · rw [if_pos h, List.length_append]; omega
  · rw [if_neg h]; omega

/-- **The target tree's leaves after an insertion are `base ++ newLeaves`, with `base` of
    length `insertStart`.** Connects a step's reported position to the leaf it stores. -/
theorem insertLeaves_leavesAt_new_matches (trees : List TreeState) (newLeaves : List Term)
    (tn : Nat) (htn : tn = insertTree trees newLeaves.length) :
    ∃ base : List Term, base.length = insertStart trees newLeaves.length ∧
      leavesAt (insertLeaves trees newLeaves) tn = base ++ newLeaves := by
  refine ⟨leavesAt trees tn, by rw [htn]; rfl, ?_⟩
  rw [insertLeaves_leavesAt, if_pos htn]

/-- The target tree's leaf count after an insertion is `insertStart` plus the batch
    size. -/
theorem insertLeaves_target_length (trees : List TreeState) (newLeaves : List Term) :
    (leavesAt (insertLeaves trees newLeaves) (insertTree trees newLeaves.length)).length
      = insertStart trees newLeaves.length + newLeaves.length := by
  rw [insertLeaves_leavesAt, if_pos rfl, List.length_append]
  rfl

/-- `(l ++ [x]).getD l.length d = x`: the element just appended sits at the position
    right past the original list's own length. Used to locate a shield's new leaf
    (`ArmadaLean.PoolSafety.step_live_leaf_matches`). -/
theorem List.getD_concat_length {α : Type} (l : List α) (x : α) (d : α) :
    (l ++ [x]).getD l.length d = x := by
  induction l with
  | nil => rfl
  | cons a rest ih => (simp? says simp only [List.cons_append, List.length_cons, List.getD_eq_getElem?_getD, List.length_append, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, Option.getD_some])

/-- A `getD` lookup that returns a value other than the default found that value at
    the index. -/
theorem List.getElem?_eq_some_of_getD {α : Type} (l : List α) (i : Nat) (d : α)
    (hne : l.getD i d ≠ d) : l[i]? = some (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD] at hne ⊢
  cases hl : l[i]? with
  | none => rw [hl] at hne; exact absurd rfl hne
  | some y => rfl

/-- A batch tagged by `withPositionsFrom` always lands, in the appended leaf list, at
    exactly the leaf `f` of its own preimage — no other value could appear there.
    `base` is whatever already sat before the batch (the target tree's prior leaves,
    empty for a new tree); `hstart` pins `base`'s length to the batch's own starting
    position, matching `insertStart`. -/
theorem withPositionsFrom_leaf_matches {α β : Type} (f : α → β) (base : List β) (start : Nat)
    (l : List α) (hstart : base.length = start) (d : β)
    (p : Nat × α) (hp : p ∈ withPositionsFrom start l) :
    (base ++ l.map f).getD p.1 d = f p.2 := by
  induction l generalizing start base with
  | nil => (simp? [withPositionsFrom] at hp says simp only [withPositionsFrom, List.not_mem_nil] at hp)
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp
    rcases hp with heq | hp
    · rw [heq]
      simp only [List.map_cons]
      have hassoc : base ++ (f a :: rest.map f) = (base ++ [f a]) ++ rest.map f := by (simp? says simp only [List.append_assoc, List.cons_append, List.nil_append])
      rw [hassoc]
      rw [List.getD_append_of_lt (base ++ [f a]) (rest.map f) start d (by (simp? [hstart] says simp only [List.length_append, hstart, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one]))]
      rw [← hstart]
      exact List.getD_concat_length base (f a) d
    · have hassoc : base ++ (a :: rest).map f = (base ++ [f a]) ++ rest.map f := by (simp? says simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append])
      rw [hassoc]
      exact ih (base ++ [f a]) (start + 1) (by (simp? [hstart] says simp only [List.length_append, hstart, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff])) hp

/-- The tree-tagged counterpart of `withPositionsFrom_leaf_matches`. -/
theorem withTreePositionsFrom_leaf_matches {α : Type} (f : α → Term) (base : List Term)
    (treeNumber start : Nat) (l : List α) (hstart : base.length = start) (d : Term)
    (p : (Nat × Nat) × α) (hp : p ∈ withTreePositionsFrom treeNumber start l) :
    (base ++ l.map f).getD p.1.2 d = f p.2 := by
  unfold withTreePositionsFrom at hp
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
  rw [← heq]
  exact withPositionsFrom_leaf_matches f base start l hstart d q hq

/-! ### Pool state -/

/-- One unshield payout: the pool sent `value` of `token` to the address `recipient`
    (`_transferTokenOut`, TransactModule.sol:418-436). A ghost record of public data
    (the `Unshield` event). -/
structure Payout where
  token : Token
  recipient : Term
  value : Nat
  deriving DecidableEq

/-- The pool's state, at the level this model needs.
    * `live t`: ghost knowledge of every unspent note of token `t`, as
      `((treeNumber, position), preimage)` entries (module comment).
    * `spent tn`: the nullifier set of tree `tn` (`PrivacyPoolStorage.nullifiers`,
      PrivacyPoolStorage.sol:174, per tree: the same `(key, leafIndex)` in two trees
      gives the same nullifier value).
    * `trees`: the Merkle trees (`TreeState`, `insertLeaves`).
    * `held t`: the pool's custody of token `t` — the ledger the modeled operations
      keep, not `IERC20.balanceOf`, which a raw `transfer` can inflate.
    * `preimageOf`: `PrivacyPoolStorage.preimageOf` (PrivacyPoolStorage.sol:248).
    * `published`: ghost record of the owned-note openings that transactions
      published (`ArmadaLean.PoolOwned.OwnedOpening`, decision 11).
    * `payouts`: ghost record of unshield payouts (`Payout`).
    * `feeRatio`: the shield fee rate. The deployment sets it. Only `Step.setFeeRatio`,
      called by `feeAdmin`, changes it (`step_feeRatio_frame`).
    * `treasuryFees t`: ghost record of the shield fees of token `t` paid to the
      treasury (`_transferTokenIn`, ShieldModule.sol:324-340; `_applyShieldFee`,
      ShieldModule.sol:209-218).
    * `feeAdmin`: the one address that can change `feeRatio`. The deployment fixes it:
      no step changes it (`step_feeAdmin`).
    * `treasury`: the treasury address. The deployment
      fixes it: no step changes it (`step_treasury`). No step reads it; the model does
      not model treasury behaviour. -/
structure PoolState where
  live : Token → List ((Nat × Nat) × CommitmentPreimage)
  spent : Nat → NullifierSet
  trees : List TreeState
  held : Token → Nat
  preimageOf : PreimageRegistry
  published : List (Term × OwnedOpening)
  payouts : List Payout
  feeRatio : FeeRatio
  treasuryFees : Token → Nat
  feeAdmin : Term
  treasury : Term

/-- The pool contract's own on-chain storage (docs/pool-executable.md, rule PE1):
    the eight fields of `PoolState` a real pool contract actually keeps — the Merkle
    trees, the nullifier set of each tree, the custody of each token, the preimage
    registry, the treasury fees of each token, the fee rate, the fee-admin address and
    the treasury address — and nothing else.
    `live`, `published` and `payouts` are the model's own ghost bookkeeping
    (`PoolState` docstring above); no contract storage slot backs them. -/
structure Pool.ContractState where
  trees : List TreeState
  spent : Nat → NullifierSet
  held : Token → Nat
  preimageOf : PreimageRegistry
  treasuryFees : Token → Nat
  feeRatio : FeeRatio
  feeAdmin : Term
  treasury : Term

/-- The contract state a `PoolState` reduces to: its eight `Pool.ContractState`
    fields, dropping the ghost fields `live`, `published` and `payouts` (PE1). -/
def PoolState.contract (s : PoolState) : Pool.ContractState :=
  ⟨s.trees, s.spent, s.held, s.preimageOf, s.treasuryFees, s.feeRatio, s.feeAdmin,
    s.treasury⟩

/-- A call a caller sends to the pool (docs/pool-executable.md, rule PE2): only
    calldata, never a circuit witness and never the model's own ghost state.
    `Pool.apply` (a later rule) reads one of these against a `Pool.ContractState`.
    * `shield`: local `ShieldModule.shield` (ShieldModule.sol:45-90) — the token,
      the gross amount and the note key the shielder names.
    * `transact`: local `TransactModule.transact` (TransactModule.sol:43-96) — the
      caller, the proof's public inputs, the bound parameters, the proof itself
      (a `Term`: the model holds no Groth16 proof objects, the same way
      `VerifyAccepts` is left abstract over the public inputs alone), the token of
      the unshield if the bound parameters name one (read from calldata and
      checked against the last output commitment, `UnshieldRefines`; `Unshield`
      itself carries no token), the disclosed records (a sublist of the output
      batch a caller chooses to reveal, `_validatePublicOutputs (requireAll =
      false)`) and the published owned-note openings (decision 11).
    * `transactOwned`: `TransactModule.transactOwned` (TransactModule.sol:488-519)
      — the same data as `transact`, with no unshield token (`transactOwned`
      never unshields, TransactModule.sol:619-623).
    * `setFeeRatio`: the fee-admin setter — the caller
      and the new fee rate. -/
inductive Pool.Call where
  | shield (token : Token) (x : Nat) (npk : Term)
  | transact {N M : Nat} (caller : Term) (pub : TransactPublic N M) (bp : BoundParams)
      (proof : Term) (unshieldToken : Option Token)
      (records : List (Term × CommitmentPreimage)) (openings : List (Term × OwnedOpening))
  | transactOwned {N M : Nat} (caller : Term) (pub : TransactOwnedPublic N M)
      (bp : BoundParams) (proof : Term) (records : List (Term × CommitmentPreimage))
      (openings : List (Term × OwnedOpening))
  | setFeeRatio (caller : Term) (r : FeeRatio)

/-- The root history of tree `treeNumber`. -/
def PoolState.rootsAt' (s : PoolState) (treeNumber : Nat) : List Term :=
  rootsAt s.trees treeNumber

/-- The leaf list of tree `treeNumber`. -/
def PoolState.leavesAt' (s : PoolState) (treeNumber : Nat) : List Term :=
  leavesAt s.trees treeNumber

/-- The trees right after deployment (`MerkleModule.initializeMerkle`,
    MerkleModule.sol:26-38): one empty tree whose one root is the empty-tree root
    (`treeRoot TreeDepth []`, computed). -/
def genesisTrees : List TreeState := [⟨[], [treeRoot TreeDepth []]⟩]

/-- The state right after deployment with fee rate `r`, fee admin `feeAdmin` and treasury
    address `treasury` (`PrivacyPool.initialize`, PrivacyPool.sol:81-127,
    for the two addresses): the genesis trees, no spent nullifiers, no custody,
    an empty registry, no published openings, no payouts and no fees paid. -/
def genesis (r : FeeRatio) (feeAdmin treasury : Term) : PoolState :=
  { live := fun _ => [], spent := fun _ => [], trees := genesisTrees,
    held := fun _ => 0, preimageOf := fun _ => none, published := [], payouts := [],
    feeRatio := r, treasuryFees := fun _ => 0, feeAdmin := feeAdmin, treasury := treasury }

/-! ### Deriving notes from a witness

A spend's input and output notes are never free choices: they are read off the witness
that a `Constrained`/`OwnedConstrained` proof pins down. These definitions are the one
place that reads them off. -/

/-- The `(treeNumber, position)`-keyed positions and preimages of a plain
    `TransactWitness`'s `N` inputs, within the one tree `treeNumber` that the bound
    parameters name (all inputs of one transaction share it; the circuit has no
    per-input tree field). Input `i` names leaf position `w.leavesIndices i` (the
    position `nullifier nk (leavesIndices i)` is derived from, Transact.circom:97-101)
    and opens it as the commitment of `npk (masterPublicKey w.publicKey
    w.nullifyingKey) (w.randomIn i)` (Transact.circom:74-84). -/
def transactSpentPositions {N M : Nat} (treeNumber : Nat) (w : TransactWitness N M) :
    List ((Nat × Nat) × CommitmentPreimage) :=
  List.ofFn fun i =>
    ((treeNumber, w.leavesIndices i),
      (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
        w.valueIn i⟩ : CommitmentPreimage))

/-- The commitment preimages of a plain `TransactWitness`'s `M` outputs, in witness
    order (Transact.circom:105-113). -/
def transactAllOutputs {N M : Nat} (w : TransactWitness N M) : List CommitmentPreimage :=
  List.ofFn fun j => (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)

/-- **Refinement: how the circuit's outputs carry the bound unshield.** The circuit has
    no unshield; it has `M` uniform outputs. The contract reads the last output
    commitment as the unshield note, with the recipient address in its `npk`
    (TransactModule.sol:357-360: "Hash must match last commitment"; PoolTypes.sol:74:
    "For unshield outputs, `npk` encodes the recipient address"). That is an encoding
    of the protocol's "withdraw this amount to this address" (`Unshield`, finding P-7).
    This definition is the one place where the encoding appears. `newNotes` are the
    outputs that stay in the pool as notes. -/
def UnshieldRefines {N M : Nat} (w : TransactWitness N M) :
    Option Unshield → List CommitmentPreimage → Prop
  | none, newNotes => transactAllOutputs w = newNotes
  | some u, newNotes => transactAllOutputs w = newNotes ++ [⟨u.recipient, w.token, u.value⟩]

/-- The `(treeNumber, position)`-keyed positions and preimages of an owned
    `TransactOwnedWitness`'s `N` inputs, the same convention as
    `transactSpentPositions`. Input `i` opens the commitment of `npk pub.ownerField
    (w.randomIn i)` (TransactOwned.circom:66-76). -/
def ownedSpentPositions {N M : Nat} (treeNumber : Nat) (pub : TransactOwnedPublic N M)
    (w : TransactOwnedWitness N M) :
    List ((Nat × Nat) × CommitmentPreimage) :=
  List.ofFn fun i =>
    ((treeNumber, w.leavesIndices i),
      (⟨npk pub.ownerField (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage))

/-- The commitment preimages of an owned `TransactOwnedWitness`'s `M` outputs. All of
    them stay live: `transactOwned` never unshields
    (`_validateOwnedTransaction`, TransactModule.sol:619-623). -/
def ownedNewNotes {N M : Nat} (w : TransactOwnedWitness N M) : List CommitmentPreimage :=
  List.ofFn fun j => (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)

/-! ### Operations

Each constructor takes, as explicit hypotheses, exactly the checks the named contract
function performs before it changes state. The circuit-level facts
(`Constrained`/`OwnedConstrained`) are hypotheses that the builder of a `Step` value
discharges. The caller of a step is the constructor argument `caller`; a shield's caller
does not appear, because no check reads it. -/

/-- One valid transition of the pool. -/
inductive Step : PoolState → PoolState → Prop where
  /-- Local `ShieldModule.shield` (ShieldModule.sol:45-90). One `ShieldRequest` of the
      gross amount `x` creates exactly one note. The pool splits `x` with the deployment
      fee rate `s.feeRatio` (`_getFee`, ShieldModule.sol:353-371): the note gets
      `shieldBase s.feeRatio x` and the treasury gets `shieldFee s.feeRatio x`
      (`_transferTokenIn`, ShieldModule.sol:324-340, called at :62; the cross-chain
      path `_applyShieldFee` does the same, ShieldModule.sol:209-218). The pool's
      custody grows by the note value only; the fee is recorded in `treasuryFees`. The
      fee-module and privileged-caller branches (ShieldModule.sol:286-323) are not
      modeled. `npk` is the note's public key, which the shielder names. The
      commitment goes into the last tree, or a new tree if the last is full
      (`insertLeaves`). `hValue` is `_validateCommitmentPreimage`'s `value > 0` check
      on the gross request (ShieldModule.sol:244, called at :59 before the fee is
      taken). `hSpendable` says the note's value passes the circuit's input range check
      (`Spendable`). The contract gets this from the ABI type `uint120 value`
      (PoolTypes.sol:82), since `base ≤ x`. Safety does not need it; spendability of
      every live note does (`ArmadaLean.PoolSafety.live_values_spendable`, finding
      P-6). S-RG, "RAILGUN Core System & Protocol": "Then the smart contract transfers
      tokens from the user wallet to itself, if a deposit amount is specified ... The
      hashes of the output UTXOs are then added to the Merkle tree so they can be spent
      in the future." -/
  | shield {s : PoolState} (token : Token) (x : Nat) (npk : Term)
      (hValue : 0 < x) (hSpendable : Spendable (shieldBase s.feeRatio x)) :
      Step s
        (let note : CommitmentPreimage := ⟨npk, token, shieldBase s.feeRatio x⟩
         let tn := insertTree s.trees 1
         let pos := insertStart s.trees 1
         { s with
             live := fun t => if t = token then ((tn, pos), note) :: s.live t else s.live t,
             held := fun t => if t = token then s.held t + note.value else s.held t,
             trees := insertLeaves s.trees [hashCommitment note],
             preimageOf := recordStep s.preimageOf (hashCommitment note) note,
             treasuryFees := fun t => if t = token
               then s.treasuryFees t + shieldFee s.feeRatio x else s.treasuryFees t })
  /-- Local `TransactModule.transact` (TransactModule.sol:43-96): a transfer, with an
      optional local unshield. `hC` is soundness ("an accepted proof means its circuit
      constraints hold"). `hBound` is the proof's binding of the bound parameters `bp`
      (`_boundParamsHash`); `hAdapt` is the adapt-contract check on `caller`
      (TransactModule.sol:530-532). `hN`/`hM` are the registered circuit shapes
      (`main_{1x1,…,8x4}.circom`, all `N ≤ 8 ∧ M ≤ 4`). `hOutputs` splits the outputs
      into new notes and the optional unshield (`UnshieldRefines`). `hRoot`, `hRemove`
      and `hNullify` are the only checks that read the pool state: the root is one of
      tree `bp.treeNumber`'s roots (TransactModule.sol:538), the spent positions are live
      in that tree, and the nullifiers are fresh in that tree (`_accumulateAndNullify`,
      TransactModule.sol:373-399). `records` is the optional disclosure
      (`_validatePublicOutputs (requireAll = false)`/`_recordPreimages`,
      TransactModule.sol:544-604): a sublist of the outputs' own records. `openings` are
      owned-note openings that the transaction publishes (decision 11); the pool does
      not check them. The custody of the token falls by the unshield amount, and the
      payout record gains the payout. S-RG: "The contract checks to make sure: ... That
      it hasn't seen the nullifiers before ... The Merkle root is the current or a
      previous Merkle root". -/
  | transact {s : PoolState} {N M : Nat} (caller : Term) (w : TransactWitness N M)
      (pub : TransactPublic N M) (bp : BoundParams)
      (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
      (hBound : pub.boundParamsHash = hashBoundParams bp) (hAdapt : AdaptAllows bp caller)
      (newNotes : List CommitmentPreimage) (hOutputs : UnshieldRefines w bp.unshield newNotes)
      (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
      (records : List (Term × CommitmentPreimage)) (openings : List (Term × OwnedOpening))
      (hRoot : pub.merkleRoot ∈ s.rootsAt' bp.treeNumber)
      (hRemove : removeAll (s.live w.token) (transactSpentPositions bp.treeNumber w) = some rest)
      (hNullify : markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent')
      (hRecords : records.Sublist (transactOutputRecords w pub)) :
      Step s
        (let tn := insertTree s.trees newNotes.length
         let pos := insertStart s.trees newNotes.length
         { s with
            live := fun t => if t = w.token
                then withTreePositionsFrom tn pos newNotes ++ rest else s.live t,
            spent := fun n => if n = bp.treeNumber then spent' else s.spent n,
            held := fun t => if t = w.token then s.held t - withdrawn bp.unshield else s.held t,
            trees := insertLeaves s.trees (newNotes.map hashCommitment),
            preimageOf := applyRecords s.preimageOf records,
            published := s.published ++ openings,
            payouts := s.payouts ++
              (bp.unshield.map fun u => (⟨w.token, u.recipient, u.value⟩ : Payout)).toList })
  /-- `TransactModule.transactOwned` (TransactModule.sol:488-519): the same bookkeeping
      as `transact`, with no unshield (`hNoUnshield`, `_validateOwnedTransaction`,
      TransactModule.sol:619-623) and every output disclosed
      (`_validatePublicOutputs(requireAll = true)`, TransactModule.sol:630-634), so the
      registry update is the whole output batch `ownedOutputRecords w pub`. `hCaller` is
      the authorization check (`ownerField == msg.sender`, TransactModule.sol:636-639).
      `hBound`, `hAdapt`, `hRoot`, `hRemove` and `hNullify` are as for `transact`. The
      registered owned shapes (`main_{1x1,1x2,1x3}_owned.circom`) have `N = 1` and
      `M ≤ 3`; the model uses the plain bound `N ≤ 8 ∧ M ≤ 4`, which
      `transactOwned_value_conserved` needs. `openings` are as for `transact`. -/
  | transactOwned {s : PoolState} {N M : Nat} (w : TransactOwnedWitness N M)
      (pub : TransactOwnedPublic N M) (bp : BoundParams) (hN : N ≤ 8) (hM : M ≤ 4)
      (hC : OwnedConstrained w pub) (caller : Term) (hCaller : caller = pub.ownerField)
      (hBound : pub.boundParamsHash = hashBoundParams bp) (hAdapt : AdaptAllows bp caller)
      (hNoUnshield : bp.unshield = none)
      (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
      (openings : List (Term × OwnedOpening))
      (hRoot : pub.merkleRoot ∈ s.rootsAt' bp.treeNumber)
      (hRemove : removeAll (s.live w.token) (ownedSpentPositions bp.treeNumber pub w) = some rest)
      (hNullify : markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers) = some spent') :
      Step s
        (let tn := insertTree s.trees (ownedNewNotes w).length
         let pos := insertStart s.trees (ownedNewNotes w).length
         { s with
            live := fun t => if t = w.token
                then withTreePositionsFrom tn pos (ownedNewNotes w) ++ rest else s.live t,
            spent := fun n => if n = bp.treeNumber then spent' else s.spent n,
            trees := insertLeaves s.trees ((ownedNewNotes w).map hashCommitment),
            preimageOf := applyRecords s.preimageOf (ownedOutputRecords w pub),
            published := s.published ++ openings })
  /-- The fee-admin setter. `hCaller` is the one check: the
      caller is the fee admin that the deployment fixes (`s.feeAdmin`). The step sets the
      fee rate to `r` and changes no other field. -/
  | setFeeRatio {s : PoolState} (caller : Term) (hCaller : caller = s.feeAdmin)
      (r : FeeRatio) : Step s { s with feeRatio := r }

/-- Every state the pool can reach from deployment with some fee rate `r`, fee admin
    `feeAdmin` and treasury address `treasury`, by any sequence of calls from any caller. -/
inductive Reachable : PoolState → Prop where
  | genesis (r : FeeRatio) (feeAdmin treasury : Term) : Reachable (genesis r feeAdmin treasury)
  | step {s s' : PoolState} (hs : Reachable s) (hstep : Step s s') :
      Reachable s'

/-- **The fee admin's setter changes only the fee rate.** The setter call of the fee admin
    `s.feeAdmin` with rate `r` is a step from `s` to `{ s with feeRatio := r }`: every
    other field, the fee admin and the treasury address included, keeps its value
    (design decision 2026-11-06, item (a)). The caller is `s.feeAdmin` itself, not a
    caller binder with an equation (`docs/lean/type-doctrine.md` §3,
    rule 3). -/
theorem step_setFeeRatio_frame {s : PoolState} (r : FeeRatio) : Step s { s with feeRatio := r } :=
  .setFeeRatio s.feeAdmin rfl r

/-- **No other step changes the fee rate.** For every step, the fee rate stays the same,
    or the post-state is the pre-state with only the fee rate replaced. Only
    `Step.setFeeRatio` gives the second case (design decision 2026-11-06, item (c)). -/
theorem step_feeRatio_frame {s s' : PoolState} (h : Step s s') :
    s'.feeRatio = s.feeRatio ∨ s' = { s with feeRatio := s'.feeRatio } := by
  cases h with
  | shield => exact Or.inl rfl
  | transact => exact Or.inl rfl
  | transactOwned => exact Or.inl rfl
  | setFeeRatio => exact Or.inr rfl

/-- **The deployment fixes the fee admin.** No step changes `feeAdmin` (design decision
    2026-11-06). -/
theorem step_feeAdmin {s s' : PoolState} (h : Step s s') : s'.feeAdmin = s.feeAdmin := by
  cases h <;> rfl

/-- **The deployment fixes the treasury address.** No step changes `treasury`
    (design decision 2026-11-06). -/
theorem step_treasury {s s' : PoolState} (h : Step s s') : s'.treasury = s.treasury := by
  cases h <;> rfl

/-! ### The pool as an executable operation (docs/pool-executable.md, rule PE3)

`Pool.Step` stays as it is (rule PE6), with one addition: the fee-admin setter
`Step.setFeeRatio`. The definitions below read only a
`Pool.ContractState` and a `Pool.Call`, never a circuit witness and never `live`,
`published` or `payouts`. Each precondition is `Decidable`, so `Pool.apply` is a plain
computable function, in the dependent-`if` form of `ArmadaLean/Nitro/OpEquations.lean`:
`if h : Pre then some (Effect ⟨_, h⟩) else none`. `Pool.Verifier.Realizes`
(`ArmadaLean/PoolSafety.lean`, next to `VerifyAccepts`) ties the `verify` parameter back
to the model's trusted verifier; `Pool.apply` itself takes no such hypothesis. -/

/-- The token of an unshield, checked against the last output commitment the way the
    contract does: it reads the token from calldata (`unshieldToken`) and recomputes the
    commitment `UnshieldRefines` expects, matching it against `commitmentsOut`'s last
    entry (TransactModule.sol:357-360, "Hash must match last commitment"). No unshield
    needs no token. -/
def unshieldCommitted {M : Nat} (commitmentsOut : Fin M → Term) (unshieldToken : Option Token)
    (unshield : Option Unshield) : Bool :=
  match unshield, unshieldToken with
  | none, none => true
  | some u, some token =>
      decide ((List.ofFn commitmentsOut).getLast? = some (hashCommitment ⟨u.recipient, token, u.value⟩))
  | _, _ => false

/-- A disclosed record is valid when its hash matches its commitment and that commitment
    is one of the proof's own output commitments (`_recordPreimages`,
    TransactModule.sol:544-604). A plain transact discloses any sublist. -/
def recordsMatch {M : Nat} (commitmentsOut : Fin M → Term)
    (records : List (Term × CommitmentPreimage)) : Bool :=
  records.all fun cp => decide (hashCommitment cp.2 = cp.1) && (List.ofFn commitmentsOut).elem cp.1

/-- An owned transact discloses every output, in order (`_validatePublicOutputs
    (requireAll = true)`, TransactModule.sol:630-634): the disclosed commitments are
    exactly the proof's output commitments, and every hash matches. -/
def recordsComplete {M : Nat} (commitmentsOut : Fin M → Term)
    (records : List (Term × CommitmentPreimage)) : Bool :=
  decide (records.map Prod.fst = List.ofFn commitmentsOut) &&
    records.all fun cp => decide (hashCommitment cp.2 = cp.1)

/-- The pool's two proof checks, handed to `Pool.apply` rather than fixed inside it: the
    proof check is a parameter, not an axiom (rule PE3). `PrivacyPool.verify` and
    `PrivacyPool.verifyOwned`. -/
structure Pool.Verifier where
  transact : ∀ {N M : Nat}, TransactPublic N M → Term → Bool
  owned : ∀ {N M : Nat}, TransactOwnedPublic N M → Term → Bool

/-- The precondition of a `shield` call: the gross amount is positive (`hValue` of
    `Step.shield`) and the note's value after the shield fee is below `2 ^ 120`, the
    circuit's input range check (`Spendable`/`RangeChecked120`, `Step.shield`'s
    `hSpendable`; `rangeCheck120_sound` turns `hSpendable` straight into this bound).
    Stated over the computed note value, not the ABI bound on `x` directly: a gross
    amount can exceed `2 ^ 120` while its fee-reduced note value still passes the range
    check, so `x < 2 ^ 120` alone is not implied by `hSpendable` — `PE4`'s forward
    refinement needs the weaker bound this precondition states. -/
def Pool.ContractState.ShieldPre (s : Pool.ContractState) (_token : Token) (x : Nat)
    (_npk : Term) : Prop :=
  0 < x ∧ shieldBase s.feeRatio x < 2 ^ 120

instance (s : Pool.ContractState) (token : Token) (x : Nat) (npk : Term) :
    Decidable (s.ShieldPre token x npk) :=
  inferInstanceAs (Decidable (0 < x ∧ shieldBase s.feeRatio x < 2 ^ 120))

/-- The effect of a `shield` call (`Step.shield`): the note gets `shieldBase`, the
    treasury gets `shieldFee`, and custody grows by the note value only. -/
def Pool.ContractState.shieldEffect (s : Pool.ContractState) (token : Token) (x : Nat)
    (npk : {t : Term // s.ShieldPre token x t}) : Pool.ContractState :=
  let note : CommitmentPreimage := ⟨npk.1, token, shieldBase s.feeRatio x⟩
  { s with
      held := fun t => if t = token then s.held t + note.value else s.held t,
      trees := insertLeaves s.trees [hashCommitment note],
      preimageOf := recordStep s.preimageOf (hashCommitment note) note,
      treasuryFees := fun t => if t = token
        then s.treasuryFees t + shieldFee s.feeRatio x else s.treasuryFees t }

/-- The precondition of a `transact` call: every check a contract with no witness can
    perform (`Step.transact`'s `hN`, `hM`, `hBound`, `hAdapt`, `hRoot`, `hNullify`), the
    proof check `verify.transact`, the disclosed records (`recordsMatch`), and the
    unshield token (`unshieldCommitted`). `Step.transact`'s `hRemove` reads `live`, which
    `Pool.ContractState` does not carry; nullifier freshness and the Merkle root take its
    place (`docs/pool-executable.md`, "Notes for the work"). -/
def Pool.ContractState.TransactPre (s : Pool.ContractState) (verify : Pool.Verifier)
    (caller : Term) {N M : Nat} (pub : TransactPublic N M) (bp : BoundParams) (proof : Term)
    (unshieldToken : Option Token) (records : List (Term × CommitmentPreimage))
    (_openings : List (Term × OwnedOpening)) : Prop :=
  N ≤ 8 ∧ M ≤ 4 ∧ verify.transact pub proof = true ∧
    pub.boundParamsHash = hashBoundParams bp ∧ AdaptAllows bp caller ∧
    pub.merkleRoot ∈ rootsAt s.trees bp.treeNumber ∧
    (markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome = true ∧
    recordsMatch pub.commitmentsOut records = true ∧
    unshieldCommitted pub.commitmentsOut unshieldToken bp.unshield = true

instance (s : Pool.ContractState) (verify : Pool.Verifier) (caller : Term) {N M : Nat}
    (pub : TransactPublic N M) (bp : BoundParams) (proof : Term)
    (unshieldToken : Option Token) (records : List (Term × CommitmentPreimage))
    (openings : List (Term × OwnedOpening)) :
    Decidable (s.TransactPre verify caller pub bp proof unshieldToken records openings) :=
  inferInstanceAs (Decidable (N ≤ 8 ∧ M ≤ 4 ∧ verify.transact pub proof = true ∧
    pub.boundParamsHash = hashBoundParams bp ∧ AdaptAllows bp caller ∧
    pub.merkleRoot ∈ rootsAt s.trees bp.treeNumber ∧
    (markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome = true ∧
    recordsMatch pub.commitmentsOut records = true ∧
    unshieldCommitted pub.commitmentsOut unshieldToken bp.unshield = true))

/-- The effect of a `transact` call (`Step.transact`): the proof's own output
    commitments become the new leaves — except the last one when there is an unshield,
    the unshield's virtual commitment (`unshieldCommitted`), which `Step.transact` never
    inserts as a leaf (its `trees` field uses `newNotes`, not `transactAllOutputs w`) —
    the nullifiers are marked spent, custody falls by the unshield amount of its token,
    and the disclosed records are recorded. -/
def Pool.ContractState.transactEffect (s : Pool.ContractState) (verify : Pool.Verifier)
    (caller : Term) {N M : Nat} (pub : TransactPublic N M) (bp : BoundParams) (proof : Term)
    (unshieldToken : Option Token) (records : List (Term × CommitmentPreimage))
    (_openings : {o : List (Term × OwnedOpening) //
      s.TransactPre verify caller pub bp proof unshieldToken records o}) :
    Pool.ContractState :=
  let spent' :=
    (markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers)).getD (s.spent bp.treeNumber)
  let newLeaves := match unshieldToken with
    | some _ => (List.ofFn pub.commitmentsOut).dropLast
    | none => List.ofFn pub.commitmentsOut
  { s with
      trees := insertLeaves s.trees newLeaves,
      spent := fun n => if n = bp.treeNumber then spent' else s.spent n,
      held := match unshieldToken with
        | some tok => fun t => if t = tok then s.held t - withdrawn bp.unshield else s.held t
        | none => s.held,
      preimageOf := applyRecords s.preimageOf records }

/-- The precondition of a `transactOwned` call: the same as `TransactPre`, with the
    owner-binding check (`Step.transactOwned`'s `hCaller`), no unshield
    (`hNoUnshield`), `verify.owned` in place of `verify.transact`, and full disclosure
    (`recordsComplete`) in place of a sublist. -/
def Pool.ContractState.TransactOwnedPre (s : Pool.ContractState) (verify : Pool.Verifier)
    (caller : Term) {N M : Nat} (pub : TransactOwnedPublic N M) (bp : BoundParams)
    (proof : Term) (records : List (Term × CommitmentPreimage))
    (_openings : List (Term × OwnedOpening)) : Prop :=
  N ≤ 8 ∧ M ≤ 4 ∧ caller = pub.ownerField ∧ verify.owned pub proof = true ∧
    pub.boundParamsHash = hashBoundParams bp ∧ AdaptAllows bp caller ∧ bp.unshield = none ∧
    pub.merkleRoot ∈ rootsAt s.trees bp.treeNumber ∧
    (markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome = true ∧
    recordsComplete pub.commitmentsOut records = true

instance (s : Pool.ContractState) (verify : Pool.Verifier) (caller : Term) {N M : Nat}
    (pub : TransactOwnedPublic N M) (bp : BoundParams) (proof : Term)
    (records : List (Term × CommitmentPreimage)) (openings : List (Term × OwnedOpening)) :
    Decidable (s.TransactOwnedPre verify caller pub bp proof records openings) :=
  inferInstanceAs (Decidable (N ≤ 8 ∧ M ≤ 4 ∧ caller = pub.ownerField ∧
    verify.owned pub proof = true ∧ pub.boundParamsHash = hashBoundParams bp ∧
    AdaptAllows bp caller ∧ bp.unshield = none ∧
    pub.merkleRoot ∈ rootsAt s.trees bp.treeNumber ∧
    (markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers)).isSome = true ∧
    recordsComplete pub.commitmentsOut records = true))

/-- The effect of a `transactOwned` call (`Step.transactOwned`): the same as
    `transactEffect`, with no unshield and the whole output batch recorded. -/
def Pool.ContractState.transactOwnedEffect (s : Pool.ContractState) (verify : Pool.Verifier)
    (caller : Term) {N M : Nat} (pub : TransactOwnedPublic N M) (bp : BoundParams)
    (proof : Term) (records : List (Term × CommitmentPreimage))
    (_openings : {o : List (Term × OwnedOpening) //
      s.TransactOwnedPre verify caller pub bp proof records o}) :
    Pool.ContractState :=
  let spent' :=
    (markSpent (s.spent bp.treeNumber) (List.ofFn pub.nullifiers)).getD (s.spent bp.treeNumber)
  { s with
      trees := insertLeaves s.trees (List.ofFn pub.commitmentsOut),
      spent := fun n => if n = bp.treeNumber then spent' else s.spent n,
      preimageOf := applyRecords s.preimageOf records }

/-- The precondition of a `setFeeRatio` call: the caller is the fee admin that the
    deployment fixes (`Step.setFeeRatio`'s `hCaller`). -/
def Pool.ContractState.SetFeeRatioPre (s : Pool.ContractState) (caller : Term)
    (_r : FeeRatio) : Prop :=
  caller = s.feeAdmin

instance (s : Pool.ContractState) (caller : Term) (r : FeeRatio) :
    Decidable (s.SetFeeRatioPre caller r) :=
  inferInstanceAs (Decidable (caller = s.feeAdmin))

/-- The effect of a `setFeeRatio` call (`Step.setFeeRatio`): the fee rate becomes `r`,
    and no other field changes. -/
def Pool.ContractState.setFeeRatioEffect (s : Pool.ContractState) (caller : Term)
    (r : {r : FeeRatio // s.SetFeeRatioPre caller r}) : Pool.ContractState :=
  { s with feeRatio := r.1 }

/-- The pool contract as a computable function (rule PE3): it reads only its call and
    its state, takes the proof check as the parameter `verify`, and states each call in
    the dependent-`if` form of `ArmadaLean/Nitro/OpEquations.lean`. -/
def Pool.apply (verify : Pool.Verifier) (s : Pool.ContractState) :
    Pool.Call → Option Pool.ContractState
  | .shield token x npk =>
    if h : s.ShieldPre token x npk then some (s.shieldEffect token x ⟨npk, h⟩) else none
  | .transact caller pub bp proof unshieldToken records openings =>
    if h : s.TransactPre verify caller pub bp proof unshieldToken records openings then
      some (s.transactEffect verify caller pub bp proof unshieldToken records ⟨openings, h⟩)
    else none
  | .transactOwned caller pub bp proof records openings =>
    if h : s.TransactOwnedPre verify caller pub bp proof records openings then
      some (s.transactOwnedEffect verify caller pub bp proof records ⟨openings, h⟩)
    else none
  | .setFeeRatio caller r =>
    if h : s.SetFeeRatioPre caller r then some (s.setFeeRatioEffect caller ⟨r, h⟩) else none

/-- The `shield` equation: `Pool.apply` is already in the dependent-`if` form, so this
    holds by `rfl`. -/
theorem Pool.apply_shield_equation (verify : Pool.Verifier) (s : Pool.ContractState)
    (token : Token) (x : Nat) (npk : Term) :
    Pool.apply verify s (.shield token x npk) =
      if h : s.ShieldPre token x npk then some (s.shieldEffect token x ⟨npk, h⟩) else none :=
  rfl

/-- The `transact` equation, by `rfl` (as `Pool.apply_shield_equation`). -/
theorem Pool.apply_transact_equation (verify : Pool.Verifier) (s : Pool.ContractState)
    {N M : Nat} (caller : Term) (pub : TransactPublic N M) (bp : BoundParams) (proof : Term)
    (unshieldToken : Option Token) (records : List (Term × CommitmentPreimage))
    (openings : List (Term × OwnedOpening)) :
    Pool.apply verify s (.transact caller pub bp proof unshieldToken records openings) =
      if h : s.TransactPre verify caller pub bp proof unshieldToken records openings then
        some (s.transactEffect verify caller pub bp proof unshieldToken records ⟨openings, h⟩)
      else none :=
  rfl

/-- The `transactOwned` equation, by `rfl` (as `Pool.apply_shield_equation`). -/
theorem Pool.apply_transactOwned_equation (verify : Pool.Verifier) (s : Pool.ContractState)
    {N M : Nat} (caller : Term) (pub : TransactOwnedPublic N M) (bp : BoundParams)
    (proof : Term) (records : List (Term × CommitmentPreimage))
    (openings : List (Term × OwnedOpening)) :
    Pool.apply verify s (.transactOwned caller pub bp proof records openings) =
      if h : s.TransactOwnedPre verify caller pub bp proof records openings then
        some (s.transactOwnedEffect verify caller pub bp proof records ⟨openings, h⟩)
      else none :=
  rfl

/-- The `setFeeRatio` equation, by `rfl` (as `Pool.apply_shield_equation`). -/
theorem Pool.apply_setFeeRatio_equation (verify : Pool.Verifier) (s : Pool.ContractState)
    (caller : Term) (r : FeeRatio) :
    Pool.apply verify s (.setFeeRatio caller r) =
      if h : s.SetFeeRatioPre caller r then some (s.setFeeRatioEffect caller ⟨r, h⟩)
      else none :=
  rfl

/-- **An accepted fee-admin call changes only the fee rate.** If `Pool.apply` accepts the
    call `setFeeRatio caller r`, the result is `{ s with feeRatio := r }`: every other
    contract field, the fee admin and the treasury address included, keeps its value
    (design decision 2026-11-06, item (a)). -/
theorem Pool.apply_setFeeRatio_frame (verify : Pool.Verifier) (s : Pool.ContractState)
    (caller : Term) (r : FeeRatio) {t : Pool.ContractState}
    (h : Pool.apply verify s (.setFeeRatio caller r) = some t) :
    t = { s with feeRatio := r } := by
  rw [Pool.apply_setFeeRatio_equation] at h
  by_cases hc : s.SetFeeRatioPre caller r
  · rw [dif_pos hc] at h
    exact (Option.some.inj h).symm
  · rw [dif_neg hc] at h
    exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- **No other caller can change the fee rate.** If the caller is not the fee admin
    `s.feeAdmin`, `Pool.apply` rejects the call `setFeeRatio caller r` (design decision
    2026-11-06, item (b)). The model `Step` keeps no caller identity in its states, so
    this contract-level statement is where item (b) has content: at the model level,
    `Step.setFeeRatio` takes `caller = s.feeAdmin` as its hypothesis. -/
theorem Pool.apply_setFeeRatio_not_admin (verify : Pool.Verifier) (s : Pool.ContractState)
    (caller : Term) (r : FeeRatio) (hne : caller ≠ s.feeAdmin) :
    Pool.apply verify s (.setFeeRatio caller r) = none := by
  rw [Pool.apply_setFeeRatio_equation]
  exact dif_neg hne

/-! ### The pool contract over a run of calls (rule PE7) -/

/-- `Pool.apply`, folded over a list of calls in order (rule PE7): `none` as soon as one call is
    rejected, the contract state left after every call is accepted when the whole list is. -/
def Pool.applyRun (verify : Pool.Verifier) (s : Pool.ContractState) :
    List Pool.Call → Option Pool.ContractState
  | [] => some s
  | c :: cs => (Pool.apply verify s c).bind (fun s' => Pool.applyRun verify s' cs)

/-- The empty-list equation: `Pool.applyRun` accepts no calls and leaves `s` unchanged, by
    `rfl` (as `Pool.apply_shield_equation`). -/
theorem Pool.applyRun_nil (verify : Pool.Verifier) (s : Pool.ContractState) :
    Pool.applyRun verify s [] = some s := rfl

/-- The cons equation: `Pool.applyRun` accepts the head call, then the rest from the state it
    leaves, by `rfl` (as `Pool.apply_shield_equation`). -/
theorem Pool.applyRun_cons (verify : Pool.Verifier) (s : Pool.ContractState) (c : Pool.Call)
    (cs : List Pool.Call) :
    Pool.applyRun verify s (c :: cs) =
      (Pool.apply verify s c).bind (fun s' => Pool.applyRun verify s' cs) := rfl

end ArmadaLean
