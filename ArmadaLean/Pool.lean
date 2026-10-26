/-
  ArmadaLean.Pool — the privacy pool contract's state and operations.

  Why this model exists (see `.scratch/rewrite-B/POOL-model.md` in armada-laconic): the
  Armada pool holds other people's tokens. Its central promise is that value in the pool
  exists only as notes, and every token the pool holds backs exactly one unspent note.
  armada-lean already proves the cryptographic core (ArmadaLean.Transact,
  ArmadaLean.TransactOwned): one valid proof spends distinct notes and conserves value,
  and a contract-owned spend is bound to its owner. This module adds the bookkeeping the
  pool contract itself performs across many calls: which notes are live, which nullifiers
  are spent, which roots are valid, and which tokens the pool holds.

  A note is identified by its tree number and Merkle leaf position, not by its content:
  the circuit derives a spend's nullifier as `Poseidon(nullifyingKey, leafIndex)`
  (Transact.circom:97-101) or `Poseidon(ownerField, leafIndex)`
  (TransactOwned.circom:89-97) — a leaf position within a tree the proof also names
  (`boundParams.treeNumber`, PrivacyPoolStorage.sol:48, `BoundParamsCore.treeNumber`),
  never a scan for a matching value. Two live notes can carry the identical preimage
  (two separate shields of the same amount to the same recipient); they can never share
  a `(treeNumber, position)` pair. `PoolState.live` is keyed accordingly: `live t` is a
  list of `((treeNumber, position), preimage)` entries, one per currently-unspent note of
  token `t`, and a spend removes exactly the positions its witness names within the one
  tree its proof is against (`ArmadaLean.Nullifier.nullifier_pos_inj`: distinct positions
  can never collapse onto one nullifier, so this removal is never ambiguous).

  The pool cannot see a note's value; it only ever reads a note's commitment (a Poseidon
  hash, modeled symbolically — `ArmadaLean.Poseidon.Term`). `PoolState.live` is therefore
  GHOST state: the model's own knowledge of every live note's real preimage, which the
  contract itself never stores for an encrypted output. This is what lets the theorems in
  ArmadaLean.PoolSafety state the value invariant at all. `PoolState.preimageOf`, by
  contrast, mirrors the real public `PrivacyPoolStorage.preimageOf` mapping
  (PrivacyPoolStorage.sol:248): the pool writes an entry there only for a commitment it
  has itself hashed and matched to a proof. `PoolState.ownedRandomOf` is a second public
  registry the approved design adds on top: see `ArmadaLean.PoolOwned`'s module comment
  on `OwnedDisclosure` for the departure this closes (the real contract records no
  random value at all) and `ArmadaLean.PoolSafety.owned_spend_witness_exists` for what it
  buys — a live owned note's whole spend witness, built from public data alone.

  Scope: local `shield` (ShieldModule.sol:45-90), local `transact` including a local
  unshield (TransactModule.sol:43-96), and `transactOwned` (TransactModule.sol:488-519).
  Out of scope, per the brief: `processIncomingShield` and `atomicCrossChainUnshield`
  (CCTP-mediated token movement; CCTP is out of scope and these two entry points' only
  pool-relevant difference from the local paths is where the moved tokens come from or
  go, which this model does not represent) and the yield vault. The pool's own books do
  not otherwise depend on CCTP: nullifier marking, Merkle insertion and the preimage
  registry follow the same shape on every entry point, and the local paths exercise that
  shape in full.

  A spend's circuit-level facts (Merkle membership, nullifier derivation, value
  conservation) come from `ArmadaLean.Transact.Constrained` /
  `ArmadaLean.TransactOwned.OwnedConstrained`, exactly as ArmadaLean.PoolOwned already
  takes them. `PoolState.leaves`/`.roots` are the CURRENT tree's leaf list and root
  history; `PoolState.closedTrees` holds every earlier tree, frozen — the ordered list of
  every commitment `MerkleModule.insertLeaves` (MerkleModule.sol:54-121) has ever
  inserted, public exactly as the real leaves are (`Shield`/`Transact`/`TransactOwned`
  events carry every commitment hash). Every root a `Step` pushes is
  `ArmadaLean.Merkle.treeRoot TreeDepth` of whichever tree's leaf list it just extended,
  computed from that list, not chosen — so a step cannot name a root that does not match
  what it actually inserted, and `ArmadaLean.PoolSafety.leaf_has_merkle_witness` proves
  every inserted leaf has a real Merkle path to a root the pool produced, in the tree it
  actually landed in. ABDK's 2021-04-01 audit of Railgun's `Commitments.sol`
  (`.scratch/rewrite-B/sources/railgun-audit-2021-04-01-ABDK.pdf`, sha256
  `3b2129ab6440272f8dbe70f843a8a9e61068d644d1a860b61c36ce93339e380a`) spends findings
  CVF-33, CVF-34, CVF-41 and CVF-42 entirely on the gas-optimized incremental-insertion
  algorithm (the same `filledSubTrees`/rollover shape `MerkleModule.insertLeaves` uses);
  every one of those findings is about gas, not soundness — `ArmadaLean.Merkle.treeRoot`
  computes the same final value that algorithm does, non-incrementally.

  DEPARTURE, now closed: an earlier version of this model represented one tree only, with
  an explicit capacity hypothesis on every leaf-inserting `Step` (a step that would
  overflow the tree simply had no witness). That is not what the contract does: a batch
  that cannot fit the current tree rolls over to a fresh one instead
  (`MerkleModule.insertLeaves`, MerkleModule.sol:62-70, `nextLeafIndex + count >
  2 ** TREE_DEPTH`; an exactly-full tree does not roll over). Capped capacity meant an
  adversary who fills the tree could block every later spend in this model, which the
  real contract's rollover prevents. `PoolState.closedTrees` plus the `insert` helper
  below model rollover exactly, and every leaf-inserting `Step` constructor below carries
  no capacity hypothesis at all: a step is never blocked by a full tree.

  S-RG: RAILGUN Project Whitepaper, 2021-07-14.
  <https://resources.cryptocompare.com/asset-management/1823/1674569706520.pdf>,
  sha256 `84ab2207efbbf689503652c42b4861bca5562549961f69fe648feb6dedb83aa8`. Section
  "RAILGUN Core System & Protocol" splits the checks between the circuit and the
  contract; this model cites only the contract's share, at the definitions below. S-RG is
  a 2021 pre-launch design: Armada's contracts, not S-RG, are the source wherever they
  differ. S-RG's ADD/SPLIT/REMOVE names are not used here (Armada's contracts say
  `shield`/`transact`/`transactOwned`); S-RG's 25-basis-point deposit AND withdrawal fees
  do not match Armada, which charges a shield-in fee only (`shieldFee`, Fee.lean,
  ShieldModule.sol:343-371) and no withdrawal fee (TransactModule.sol:32, "Unshields are
  always free").

  DEPARTURE (contract, confirmed by reading the source): the brief that commissioned this
  model expected a shield to create "one fee note for the fee", matching the design at
  `labbook/2026-10-18-treasury-governance-baal-safe-shielded.md` decision 15 ("ShieldModule
  creates the fee note to the Safe's npk"). The merged `ShieldModule.sol` does not do this.
  `_transferTokenIn`'s flat-fee branch (ShieldModule.sol:324-340) and fee-module branch
  (ShieldModule.sol:295-323) both pay the fee leg with
  `token.safeTransferFrom(msg.sender, treasury, ...)` — straight from the caller's wallet
  to `treasury`, never through the pool's own balance and never as a commitment. No fee
  note is created on the `shield` path; `Step.shield` below models this (one note, of the
  post-fee value, and no second note). Separately, `_recognizeFee`
  (PrivacyPoolStorage.sol:280-285) recognizes ANY output — shield, transact or
  transactOwned — whose `npk` equals the governance `feeRecipient`, which is the already-
  named departure (brief, "transact outputs counted as fees"): `TransactModule
  ._recordPreimages` (TransactModule.sol:587-604) calls `_recognizeFee` for every
  transact/transactOwned public output, not only a genuine shield-in fee, against
  labbook T9.

  DEPARTURE (contract, `testingMode`): `PrivacyPool.verify`/`verifyOwned`
  (PrivacyPool.sol:506-601) return `true` unconditionally when `testingMode` is on, with
  no witness at all. `Step.transact`/`Step.transactOwned` below always require a genuine
  `Constrained`/`OwnedConstrained` witness to transition, i.e. they model the pool exactly
  when `testingMode` is off (or, equivalently, whenever the submitted proof happens to be
  genuine regardless of the flag); the safety theorems in ArmadaLean.PoolSafety hold under
  that same restriction, stated at each theorem, not as a global axiom. This mirrors a
  historical Railgun defect: ABDK finding CVF-58 (Critical, Fixed) on `Snark.sol`: "The
  function always returns true. It should return (out[0] != 0)" — an unconditional-accept
  verifier bug, fixed before Railgun's launch. Armada's `testingMode`/`VERIFICATION_BYPASS`
  (PrivacyPool.sol:508-510, 547-549, 564-566, 596-598) is the same defect, kept
  intentionally for testing and never removed from the merged contract (the sibling
  labbook entry's R8 calls for its removal; it is still present).

  DEPARTURE (contract → design, owner-controlled freeze removed): the merged contract
  lets the owner block every spend and unshield at any time. `PrivacyPool
  .setShieldPauseContract` (PrivacyPool.sol:466-470) is owner-gated with no restriction
  on when or to what address it is called, and it installs an `IShieldPauseController`
  whose `emergencyPaused()` or `withdrawOnlyMode()` `TransactModule` reads before every
  `transact` and `transactOwned` (`_requireNotEmergencyPaused`/`_requireNotWithdrawOnly`,
  TransactModule.sol:460-475, called at :48, :52, :491-492): an emergency pause blocks
  every spend outright, and withdraw-only mode blocks a pure transfer (a `transact` with
  no unshield output) and blocks every owned transaction unconditionally (the owned
  path's `unshield` is always `NONE`, so it can never satisfy
  `_requireNotWithdrawOnly`'s `unshield != NONE` escape). The Armada design removes this
  owner power entirely: `Step.transact` and `Step.transactOwned` below carry no pause
  check of any kind, so no step any caller — the owner included — can take ever blocks
  an otherwise-valid spend
  (`ArmadaLean.PoolSafety.transact_cannot_be_blocked`/`.transactOwned_cannot_be_blocked`).
  `PoolState` below therefore drops `emergencyPaused` and `withdrawOnlyMode`; only
  `shieldsPaused` remains, and it gates `Step.shield` alone — a shield pause, if the
  design keeps one, blocks only new value entering the pool, never an existing note's
  owner from spending or exiting it.
-/
import ArmadaLean.PoolOwned
import ArmadaLean.Transact
import ArmadaLean.Fee

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
    simp [listSum]
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
      exact absurd h (by simp)

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
      exact absurd h (by simp)

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
      exact absurd h (by simp)

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
      exact absurd h (by simp)

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
  | cons a rest ih => simp [withPositionsFrom, ih]

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
    half is `insertStartPos_eq_leavesAt_length`). -/
theorem withPositionsFrom_pos_ge {α : Type} (start : Nat) (l : List α) (p : Nat × α)
    (hp : p ∈ withPositionsFrom start l) : start ≤ p.1 := by
  induction l generalizing start with
  | nil => simp [withPositionsFrom] at hp
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp
    rcases hp with heq | hp
    · simp [heq]
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
  | nil => simp [withPositionsFrom] at hp1
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp1 hp2
    rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
    · rw [h1, h2]
    · exfalso
      have hge := withPositionsFrom_pos_ge (start + 1) rest p2 h2
      rw [h1] at heq
      simp at heq
      omega
    · exfalso
      have hge := withPositionsFrom_pos_ge (start + 1) rest p1 h1
      rw [h2] at heq
      simp at heq
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
  | nil => simp [withPositionsFrom] at hp
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp
    rcases hp with heq | hp
    · simp [heq]
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
  | nil => simp [withPositionsFrom]
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
  | nil => simp [withTreePositionsFrom, withPositionsFrom]
  | cons a rest ih =>
    have hunfold : withTreePositionsFrom treeNumber start (a :: rest) =
        ((treeNumber, start), a) :: withTreePositionsFrom treeNumber (start + 1) rest := by
      simp [withTreePositionsFrom, withPositionsFrom]
    rw [hunfold, List.nodup_cons]
    refine ⟨?_, ih (start + 1)⟩
    intro hmem
    have hge := withTreePositionsFrom_pos_ge treeNumber (start + 1) rest ((treeNumber, start), a) hmem
    simp only at hge
    omega

/-- Every element `withPositionsFrom` tags came from the original list — the position
    tag never changes which values are present, only labels them. Used to trace a live
    note's value back to the circuit output it came from
    (`ArmadaLean.PoolSafety.live_values_lt_2pow120`). -/
theorem withPositionsFrom_snd_mem {α : Type} (start : Nat) (l : List α) (p : Nat × α)
    (hp : p ∈ withPositionsFrom start l) : p.2 ∈ l := by
  induction l generalizing start with
  | nil => simp [withPositionsFrom] at hp
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

/-- `(l ++ l').getD i d = l.getD i d` once `i` is within `l`'s own length: appending
    never disturbs an existing index. The "a leaf, once placed, never moves" fact
    (`ArmadaLean.PoolSafety.leaf_stable`) rests on this. -/
theorem List.getD_append_of_lt {α : Type} (l l' : List α) (i : Nat) (d : α)
    (h : i < l.length) : (l ++ l').getD i d = l.getD i d := by
  induction l generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih i' (by simp at h; omega)

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
  cases p1; cases p2
  simp_all [Term.val.injEq]

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
    by_cases hz : isZeroPreimage p'
    · rw [if_pos hz]; exact hreg
    · rw [if_neg hz]
      by_cases hcc : c = c'
      · rw [if_pos hcc]
        have := hagree (c', p') List.mem_cons_self hcc.symm
        simp only [] at this
        rw [this]
      · rw [if_neg hcc]; exact hreg

/-- **A valid, non-zero batch is recoverable from the registry it produces.** If every
    record in a batch hashes to its own key, and the looked-up record itself is never
    the zero preimage (so `recordStep` never skips writing it — `_validatePublicOutputs`'s
    non-zero requirement), then `applyRecords` settles on `p` at key `c`, whatever else
    is in the batch: a later record sharing key `c` must, by `hashCommitment_inj`, carry
    the identical preimage `p`, so even an overwrite leaves the answer unchanged. Only
    the looked-up record's own non-zero-ness is needed — the batch may contain other,
    possibly-zero records elsewhere (a plain `transact`'s disclosure, unlike
    `transactOwned`'s, does not require every output non-zero). The key lemma behind
    `transactOwned_records_all` and `pool_ownedRandomOf_consistent`. -/
theorem applyRecords_returns {reg : PreimageRegistry} {records : List (Term × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    {c : Term} {p : CommitmentPreimage} (hmem : (c, p) ∈ records) (hNonZero : ¬ isZeroPreimage p) :
    applyRecords reg records c = some p := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  rw [hsplit, applyRecords_append]
  unfold applyRecords
  apply applyRecords_preserves_key
  · unfold recordStep
    rw [if_neg hNonZero]
    simp
  · intro cp hcp hcpeq
    have hcpmem : cp ∈ records := by
      rw [hsplit]
      exact List.mem_append_right pre (List.mem_cons_of_mem _ hcp)
    have hcpval := hvalid cp hcpmem
    have hpval := hvalid (c, p) hmem
    rw [hcpeq] at hcpval
    exact hashCommitment_inj (hcpval.trans hpval.symm)

/-- `recordStep` leaves any OTHER already-consistent key's answer unchanged: a write at
    `newc` can only coincide with `c` if the written preimage genuinely hashes to `c`
    too, in which case — since `pre` is ALREADY known to hash to `c`
    (`hashCommitment_inj`) — the write is a no-op value-wise. The one-record case of
    `applyRecords_preserves_other`, used directly by `Step.shield` (which calls
    `recordStep`, not `applyRecords`). -/
theorem recordStep_preserves_other {reg : PreimageRegistry}
    {c newc : Term} {newpre pre : CommitmentPreimage}
    (hc : hashCommitment pre = c) (hcreg : reg c = some pre) (hvalid : hashCommitment newpre = newc) :
    recordStep reg newc newpre c = some pre := by
  unfold recordStep
  by_cases hz : isZeroPreimage newpre
  · rw [if_pos hz]; exact hcreg
  · rw [if_neg hz]
    by_cases heq : c = newc
    · rw [if_pos heq]
      rw [heq] at hc
      have hveq := hashCommitment_inj (hc.trans hvalid.symm)
      rw [hveq]
    · rw [if_neg heq]; exact hcreg

/-- `applyRecords` leaves any OTHER already-consistent key's answer unchanged — the
    batch generalization of `recordStep_preserves_other`, used by `Step.transact`'s
    optional owned-disclosure batch. -/
theorem applyRecords_preserves_other {reg : PreimageRegistry}
    {records : List (Term × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    {c : Term} {pre : CommitmentPreimage} (hc : hashCommitment pre = c) (hcreg : reg c = some pre) :
    applyRecords reg records c = some pre := by
  induction records generalizing reg with
  | nil => exact hcreg
  | cons cp rest ih =>
    obtain ⟨c', p'⟩ := cp
    apply ih (fun cp' hcp' => hvalid cp' (List.mem_cons_of_mem _ hcp'))
    exact recordStep_preserves_other hc hcreg (hvalid (c', p') List.mem_cons_self)

/-- The `(commitment, preimage)` pair a plain `Transact` output would record, if
    disclosed — the full candidate batch `Step.transact`'s `records` is a sublist of. -/
def transactOutputRecords {N M : Nat} (w : TransactWitness N M)
    (pub : TransactPublic N M) : List (Term × CommitmentPreimage) :=
  List.ofFn fun j => (pub.commitmentsOut j, (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))

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
  List.ofFn fun j => (pub.commitmentsOut j, (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))

/-- Every owned output's record is valid: its commitment key is exactly its own
    `hashCommitment` (`OwnedConstrained.outputs`). -/
theorem ownedOutputRecords_valid {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (hC : OwnedConstrained w pub) :
    ∀ cp ∈ ownedOutputRecords w pub, hashCommitment cp.2 = cp.1 := by
  intro cp hcp
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
  rw [← hj]
  exact (hC.outputs j).symm

/-! ### The public owned-random registry

`ArmadaLean.PoolOwned`'s module comment on `OwnedDisclosure` records the departure: the
real contract never stores a note's random value, so only its creator can spend it. The
approved design closes this for contract-owned notes; `applyOwnedRecords` lifts one
commitment's disclosure (`ArmadaLean.PoolOwned.recordOwnedStep`) to a whole batch, the
same way `applyRecords` lifts `recordStep`. -/

/-- Apply a batch of `(commitment, disclosure)` records to the owned-random registry,
    in order. -/
def applyOwnedRecords (rreg : OwnedRandomRegistry) :
    List (Term × OwnedDisclosure) → OwnedRandomRegistry
  | [] => rreg
  | (c, d) :: rest => applyOwnedRecords (recordOwnedStep rreg c d) rest

/-- `applyOwnedRecords` preserves `OwnedRandomConsistent` against a FIXED preimage
    registry `reg`, given every record's random genuinely reconstructs the npk of
    whatever `reg` already holds at that key — exactly the shape
    `applyRecords_preserves_consistency` has for `PreimageRegistry` alone. -/
theorem applyOwnedRecords_preserves_consistency {reg : PreimageRegistry} {rreg : OwnedRandomRegistry}
    (hconsistent : OwnedRandomConsistent reg rreg)
    {records : List (Term × OwnedDisclosure)}
    (hvalid : ∀ cd ∈ records, ∃ pre, reg cd.1 = some pre ∧
      npk cd.2.ownerField cd.2.random = pre.npk) :
    OwnedRandomConsistent reg (applyOwnedRecords rreg records) := by
  induction records generalizing rreg with
  | nil => exact hconsistent
  | cons cd rest ih =>
    obtain ⟨c, d⟩ := cd
    apply ih
    · obtain ⟨pre, hreg, hnpk⟩ := hvalid (c, d) List.mem_cons_self
      exact recordOwnedStep_preserves_consistency hconsistent hreg hnpk
    · intro cd' hcd'
      exact hvalid cd' (List.mem_cons_of_mem (c, d) hcd')

/-- Applying a valid owned-disclosure batch to a registry that already
    reads `⟨self, r⟩` at `c` (consistently, `reg c = some pre` with
    `pre.npk = npk (Term.val self) r`) still reads `⟨self, r⟩` at `c`
    afterward: any entry in the batch sharing key `c` must, by `hvalid`
    and `npk_inj`, carry the SAME pair back — the `ownedRandomOf`
    sibling of `applyRecords_preserves_known`. -/
theorem applyOwnedRecords_preserves_known {reg : PreimageRegistry}
    {records : List (Term × OwnedDisclosure)}
    (hvalid : ∀ cd ∈ records, ∃ pre, reg cd.1 = some pre ∧
      npk cd.2.ownerField cd.2.random = pre.npk)
    (rreg : OwnedRandomRegistry) (c : Term) (self : Term) (r : Nat) (pre : CommitmentPreimage)
    (hknown : rreg c = some ⟨self, r⟩) (hreg : reg c = some pre)
    (hnpk : pre.npk = npk self r) :
    applyOwnedRecords rreg records c = some ⟨self, r⟩ := by
  induction records generalizing rreg with
  | nil => exact hknown
  | cons cd rest ih =>
    obtain ⟨c0, d0⟩ := cd
    unfold applyOwnedRecords
    apply ih (fun cd' hcd' => hvalid cd' (List.mem_cons_of_mem _ hcd'))
    exact recordOwnedStep_preserves_known (hvalid (c0, d0) List.mem_cons_self) hknown hreg hnpk

/-- Applying a valid owned-disclosure batch that names `(c, d)` reads back
    `d` at key `c` afterward — the `ownedRandomOf` sibling of
    `applyRecords_reads` (no zero-skip here: `recordOwnedStep` skips
    nothing, `recordOwnedStep`'s own module comment). -/
theorem applyOwnedRecords_reads {reg : PreimageRegistry}
    {records : List (Term × OwnedDisclosure)}
    (hvalid : ∀ cd ∈ records, ∃ pre, reg cd.1 = some pre ∧
      npk cd.2.ownerField cd.2.random = pre.npk)
    (rreg : OwnedRandomRegistry) (c : Term) (d : OwnedDisclosure)
    (hmem : (c, d) ∈ records) :
    applyOwnedRecords rreg records c = some d := by
  induction records generalizing rreg with
  | nil => simp at hmem
  | cons cd0 rest ih =>
    obtain ⟨c0, d0⟩ := cd0
    unfold applyOwnedRecords
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hc hd
      subst hc; subst hd
      obtain ⟨pre, hreg, hnpk⟩ := hvalid (c, d) List.mem_cons_self
      have hstep : recordOwnedStep rreg c d c = some d := by
        unfold recordOwnedStep; rw [if_pos rfl]
      have := applyOwnedRecords_preserves_known
        (fun cd' hcd' => hvalid cd' (List.mem_cons_of_mem _ hcd'))
        (recordOwnedStep rreg c d) c d.ownerField d.random pre hstep hreg hnpk.symm
      exact this
    · exact ih (fun cd' hcd' => hvalid cd' (List.mem_cons_of_mem _ hcd')) (recordOwnedStep rreg c0 d0)
        hmem'



/-! ### The Merkle tree forest

One tree holds at most `2 ^ TreeDepth` leaves (`ArmadaLean.Merkle`'s module comment); the
contract rolls over to a fresh tree rather than refusing an insertion that would overflow
the current one (`MerkleModule.insertLeaves`, MerkleModule.sol:62-70). `TreeState` is one
tree's leaf list and root history — exactly the two fields `PoolState` used to carry
directly, for the single tree the earlier version of this model assumed. -/

/-- One tree's leaves and the root history it has produced — `ArmadaLean.Merkle.treeRoot
    TreeDepth leaves` is always `roots.head?` once any leaf has been inserted, the same
    invariant the single-tree model already proved, now per tree
    (`ArmadaLean.PoolSafety.reachable_rootAt_matches_leavesAt`). -/
structure TreeState where
  leaves : List Term
  roots : List Term

/-- The root history of tree `treeNumber`: every tree before the current one is frozen
    in `closedTrees[k]` = tree `k` (`closedTrees.length` is the current tree's own
    number, still open to new insertions, `PoolState.leaves`/`.roots` directly).
    `s.roots` if it is the current tree, otherwise whatever `s.closedTrees` recorded
    for it (the empty list if `treeNumber` names a tree that does not exist yet — no
    proof can ever name a root from a not-yet-existing tree, since `[].contains _` is
    always `False`). -/
def PoolState.rootsAt (closedTrees : List TreeState) (_curLeaves curRoots : List Term)
    (treeNumber : Nat) : List Term :=
  if treeNumber = closedTrees.length then curRoots
  else (closedTrees.getD treeNumber ⟨[], []⟩).roots

/-- The leaf list of tree `treeNumber`, the same convention as `rootsAt`. -/
def PoolState.leavesAt (closedTrees : List TreeState) (curLeaves _curRoots : List Term)
    (treeNumber : Nat) : List Term :=
  if treeNumber = closedTrees.length then curLeaves
  else (closedTrees.getD treeNumber ⟨[], []⟩).leaves

/-- Where a batch of `count` new leaves lands: the current tree, unless it would
    overflow (`MerkleModule.sol:66`, `nextLeafIndex + count > 2 ^ TREE_DEPTH` — an
    exactly-full tree does not roll over), in which case a fresh tree, numbered one past
    the last closed tree. -/
def insertTreeNumber (closedTrees : List TreeState) (curLeaves : List Term) (count : Nat) :
    Nat :=
  if curLeaves.length + count > 2 ^ TreeDepth then closedTrees.length + 1 else closedTrees.length

/-- The leaf position the first of a new batch lands at: `0` on rollover (a fresh tree
    starts empty), otherwise right after the current tree's existing leaves. -/
def insertStartPos (curLeaves : List Term) (count : Nat) : Nat :=
  if curLeaves.length + count > 2 ^ TreeDepth then 0 else curLeaves.length

/-- The resulting `(closedTrees, leaves, roots)` after inserting `newLeaves`:
    `MerkleModule.insertLeaves`'s rollover-then-insert, modeled non-incrementally
    (`ArmadaLean.Merkle.treeRoot`'s own module comment). On rollover, the current tree
    is frozen into `closedTrees` exactly as it stood, and the new tree starts from
    `newLeaves` alone. -/
def insertResult (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (newLeaves : List Term) : List TreeState × List Term × List Term :=
  if curLeaves.length + newLeaves.length > 2 ^ TreeDepth then
    (closedTrees ++ [⟨curLeaves, curRoots⟩], newLeaves, [treeRoot TreeDepth newLeaves])
  else
    let leaves' := curLeaves ++ newLeaves
    (closedTrees, leaves', treeRoot TreeDepth leaves' :: curRoots)

/-- `(l ++ [x]).getD l.length d = x`: the element just appended sits at the position
    right past the original list's own length. The "what landed in the frozen tree"
    half of `insertResult`'s own root/leaf shape lemmas below. -/
theorem List.getD_concat_length {α : Type} (l : List α) (x : α) (d : α) :
    (l ++ [x]).getD l.length d = x := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp

/-- `l.getD i d = d` once `i` is past `l`'s own length — the out-of-range half of
    `List.getD`'s definition, made explicit for `insertResult`'s shape lemmas. -/
theorem List.getD_eq_default {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  induction l generalizing i with
  | nil => rfl
  | cons a rest ih =>
    cases i with
    | zero => simp at h
    | succ i' =>
      simp only [List.getD_cons_succ]
      exact ih i' (by simp at h; omega)

/-- One insertion either leaves tree `tn`'s root history unchanged (`tn` is neither the
    tree extended nor the tree just rolled into) or prepends exactly one new root —
    the uniform fact `rootsAt_grounded`/`transact_root_was_produced` need, true whether
    `tn` is a closed tree, the current tree being extended, the current tree just frozen
    by a rollover, or the fresh tree a rollover just opened: `PoolState.rootsAt`'s own
    `getD`-with-empty-default convention makes "a tree that does not exist yet has no
    roots" and "a tree that was just rolled past keeps exactly what it had" fall out of
    the same case split, with no separate argument for rollover. -/
theorem insertResult_rootsAt (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (newLeaves : List Term) (tn : Nat) :
    let res := insertResult closedTrees curLeaves curRoots newLeaves
    PoolState.rootsAt res.1 res.2.1 res.2.2 tn = PoolState.rootsAt closedTrees curLeaves curRoots tn ∨
      ∃ r, PoolState.rootsAt res.1 res.2.1 res.2.2 tn =
        r :: PoolState.rootsAt closedTrees curLeaves curRoots tn := by
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · have hres1 : (insertResult closedTrees curLeaves curRoots newLeaves).1
        = closedTrees ++ [⟨curLeaves, curRoots⟩] := by unfold insertResult; rw [if_pos hover]
    have hres22 : (insertResult closedTrees curLeaves curRoots newLeaves).2.2
        = [treeRoot TreeDepth newLeaves] := by unfold insertResult; rw [if_pos hover]
    have hlen : (closedTrees ++ [(⟨curLeaves, curRoots⟩ : TreeState)]).length = closedTrees.length + 1 := by
      simp
    simp only
    rw [hres1, hres22]
    unfold PoolState.rootsAt
    rw [hlen]
    by_cases htn : tn = closedTrees.length + 1
    · right
      refine ⟨treeRoot TreeDepth newLeaves, ?_⟩
      rw [if_pos htn, if_neg (by omega : tn ≠ closedTrees.length)]
      rw [List.getD_eq_default closedTrees tn ⟨[], []⟩ (by omega)]
    · left
      rw [if_neg htn]
      by_cases htn2 : tn = closedTrees.length
      · rw [if_pos htn2, htn2]
        rw [List.getD_concat_length]
      · rw [if_neg htn2]
        by_cases hlt : tn < closedTrees.length
        · rw [List.getD_append_of_lt closedTrees [(⟨curLeaves, curRoots⟩ : TreeState)] tn ⟨[], []⟩ hlt]
        · rw [List.getD_eq_default (closedTrees ++ [(⟨curLeaves, curRoots⟩ : TreeState)]) tn ⟨[], []⟩
            (by rw [hlen]; omega)]
          rw [List.getD_eq_default closedTrees tn ⟨[], []⟩ (by omega)]
  · have hres1 : (insertResult closedTrees curLeaves curRoots newLeaves).1 = closedTrees := by
      unfold insertResult; rw [if_neg hover]
    have hres22 : (insertResult closedTrees curLeaves curRoots newLeaves).2.2
        = treeRoot TreeDepth (curLeaves ++ newLeaves) :: curRoots := by
      unfold insertResult; rw [if_neg hover]
    simp only
    rw [hres1, hres22]
    unfold PoolState.rootsAt
    by_cases htn : tn = closedTrees.length
    · right
      exact ⟨treeRoot TreeDepth (curLeaves ++ newLeaves), by rw [if_pos htn, if_pos htn]⟩
    · left
      rw [if_neg htn, if_neg htn]

/-- The precise leaf list of tree `tn` after an insertion: unchanged unless `tn` is the
    tree the batch actually landed in (the current tree, extended, or — on rollover —
    the fresh tree, which starts exactly at `newLeaves`). The equational form
    `insertResult_rootsAt`'s disjunction is built from a weaker version of; stated as an
    equation here because `insertResult_leavesAt_capacity`/`_stable` both need to know
    exactly which branch, not just that one happened. -/
theorem insertResult_leavesAt (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (newLeaves : List Term) (tn : Nat) :
    PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
      (insertResult closedTrees curLeaves curRoots newLeaves).2.1
      (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn =
      if curLeaves.length + newLeaves.length > 2 ^ TreeDepth then
        (if tn = closedTrees.length + 1 then newLeaves
         else PoolState.leavesAt closedTrees curLeaves curRoots tn)
      else
        (if tn = closedTrees.length then curLeaves ++ newLeaves
         else PoolState.leavesAt closedTrees curLeaves curRoots tn) := by
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · have hres1 : (insertResult closedTrees curLeaves curRoots newLeaves).1
        = closedTrees ++ [⟨curLeaves, curRoots⟩] := by unfold insertResult; rw [if_pos hover]
    have hres21 : (insertResult closedTrees curLeaves curRoots newLeaves).2.1 = newLeaves := by
      unfold insertResult; rw [if_pos hover]
    have hlen : (closedTrees ++ [(⟨curLeaves, curRoots⟩ : TreeState)]).length = closedTrees.length + 1 := by
      simp
    rw [hres1, hres21]
    unfold PoolState.leavesAt
    rw [hlen, if_pos hover]
    by_cases htn : tn = closedTrees.length + 1
    · rw [if_pos htn, if_pos htn]
    · rw [if_neg htn, if_neg htn]
      by_cases htn2 : tn = closedTrees.length
      · rw [if_pos htn2, htn2, List.getD_concat_length]
      · rw [if_neg htn2]
        by_cases hlt : tn < closedTrees.length
        · rw [List.getD_append_of_lt closedTrees [(⟨curLeaves, curRoots⟩ : TreeState)] tn ⟨[], []⟩ hlt]
        · rw [List.getD_eq_default (closedTrees ++ [(⟨curLeaves, curRoots⟩ : TreeState)]) tn ⟨[], []⟩
            (by rw [hlen]; omega)]
          rw [List.getD_eq_default closedTrees tn ⟨[], []⟩ (by omega)]
  · have hres1 : (insertResult closedTrees curLeaves curRoots newLeaves).1 = closedTrees := by
      unfold insertResult; rw [if_neg hover]
    have hres21 : (insertResult closedTrees curLeaves curRoots newLeaves).2.1 = curLeaves ++ newLeaves := by
      unfold insertResult; rw [if_neg hover]
    rw [hres1, hres21]
    unfold PoolState.leavesAt
    rw [if_neg hover]
    by_cases htn : tn = closedTrees.length
    · simp only [if_pos htn]
    · simp only [if_neg htn]

/-- **A tree's leaf list never exceeds the one-tree capacity, after any insertion** —
    given it did not before, and the batch itself does not (`hNewCap`: at most `M ≤ 4`
    leaves per step, module comment, far below `2 ^ TreeDepth`). No capacity hypothesis
    is needed on `Step`'s own constructors (the rollover departure): this is instead an
    invariant proved once, over every reachable state
    (`ArmadaLean.PoolSafety.reachable_leavesAt_capacity`). -/
theorem insertResult_leavesAt_capacity (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (newLeaves : List Term) (tn : Nat) (hNewCap : newLeaves.length ≤ 2 ^ TreeDepth)
    (hOldCap : ∀ k, (PoolState.leavesAt closedTrees curLeaves curRoots k).length ≤ 2 ^ TreeDepth) :
    (PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
      (insertResult closedTrees curLeaves curRoots newLeaves).2.1
      (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn).length ≤ 2 ^ TreeDepth := by
  rw [insertResult_leavesAt]
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · rw [if_pos hover]
    by_cases htn : tn = closedTrees.length + 1
    · rw [if_pos htn]; exact hNewCap
    · rw [if_neg htn]; exact hOldCap tn
  · rw [if_neg hover]
    by_cases htn : tn = closedTrees.length
    · rw [if_pos htn]; simp; omega
    · rw [if_neg htn]; exact hOldCap tn

/-- **A leaf, once placed at a position, never moves.** Insertion only ever appends: a
    position already within tree `tn`'s leaf list keeps the exact same value after any
    later insertion, whichever tree that insertion actually lands in. The structural
    fact `ArmadaLean.PoolSafety.leaf_stable` lifts to every later reachable state. -/
theorem insertResult_leavesAt_stable (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (newLeaves : List Term) (tn pos : Nat) (d : Term)
    (hpos : pos < (PoolState.leavesAt closedTrees curLeaves curRoots tn).length) :
    (PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
      (insertResult closedTrees curLeaves curRoots newLeaves).2.1
      (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn).getD pos d =
      (PoolState.leavesAt closedTrees curLeaves curRoots tn).getD pos d := by
  rw [insertResult_leavesAt]
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · rw [if_pos hover]
    by_cases htn : tn = closedTrees.length + 1
    · exfalso
      unfold PoolState.leavesAt at hpos
      rw [htn, if_neg (by omega : closedTrees.length + 1 ≠ closedTrees.length)] at hpos
      rw [List.getD_eq_default closedTrees (closedTrees.length + 1) ⟨[], []⟩ (by omega)] at hpos
      simp at hpos
    · rw [if_neg htn]
  · rw [if_neg hover]
    by_cases htn : tn = closedTrees.length
    · rw [if_pos htn]
      have hcur : (PoolState.leavesAt closedTrees curLeaves curRoots tn) = curLeaves := by
        unfold PoolState.leavesAt; rw [if_pos htn]
      rw [hcur]
      rw [hcur] at hpos
      exact List.getD_append_of_lt curLeaves newLeaves pos d hpos
    · rw [if_neg htn]

/-- A batch tagged by `withPositionsFrom` always lands, in the appended leaf list, at
    exactly the leaf `f` of its own preimage — no other value could appear there.
    `base` is whatever already sat before the batch (the current tree's own prior
    leaves, or empty on a fresh roll); `hstart` pins `base`'s length to the batch's own
    starting position, matching `insertStartPos`'s own convention. -/
theorem withPositionsFrom_leaf_matches {α β : Type} (f : α → β) (base : List β) (start : Nat)
    (l : List α) (hstart : base.length = start) (d : β)
    (p : Nat × α) (hp : p ∈ withPositionsFrom start l) :
    (base ++ l.map f).getD p.1 d = f p.2 := by
  induction l generalizing start base with
  | nil => simp [withPositionsFrom] at hp
  | cons a rest ih =>
    simp only [withPositionsFrom, List.mem_cons] at hp
    rcases hp with heq | hp
    · rw [heq]
      simp only [List.map_cons]
      have hassoc : base ++ (f a :: rest.map f) = (base ++ [f a]) ++ rest.map f := by simp
      rw [hassoc]
      rw [List.getD_append_of_lt (base ++ [f a]) (rest.map f) start d (by simp [hstart])]
      rw [← hstart]
      exact List.getD_concat_length base (f a) d
    · have hassoc : base ++ (a :: rest).map f = (base ++ [f a]) ++ rest.map f := by simp
      rw [hassoc]
      exact ih (base ++ [f a]) (start + 1) (by simp [hstart]) hp

/-- The tree-tagged counterpart of `withPositionsFrom_leaf_matches`. -/
theorem withTreePositionsFrom_leaf_matches {α : Type} (f : α → Term) (base : List Term)
    (treeNumber start : Nat) (l : List α) (hstart : base.length = start) (d : Term)
    (p : (Nat × Nat) × α) (hp : p ∈ withTreePositionsFrom treeNumber start l) :
    (base ++ l.map f).getD p.1.2 d = f p.2 := by
  unfold withTreePositionsFrom at hp
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
  rw [← heq]
  exact withPositionsFrom_leaf_matches f base start l hstart d q hq

/-- **A freshly-inserted batch's leaves, in the tree it actually lands in, are exactly
    `base ++ newLeaves` for some `base` of length `insertStartPos`.** The precise
    "what is this tree's leaf list now" fact `withPositionsFrom_leaf_matches` needs to
    connect a `Step`'s own reported position to the leaf the pool actually stored
    there (`ArmadaLean.PoolSafety.live_leaf_matches`). -/
theorem insertResult_leavesAt_new_matches (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (newLeaves : List Term) (tn : Nat)
    (htn : tn = insertTreeNumber closedTrees curLeaves newLeaves.length) :
    ∃ base : List Term, base.length = insertStartPos curLeaves newLeaves.length ∧
      PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn = base ++ newLeaves := by
  rw [insertResult_leavesAt]
  unfold insertStartPos
  unfold insertTreeNumber at htn
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · rw [if_pos hover, if_pos hover]
    rw [htn, if_pos hover, if_pos rfl]
    exact ⟨[], rfl, by simp⟩
  · rw [if_neg hover, if_neg hover]
    rw [htn, if_neg hover, if_pos rfl]
    exact ⟨curLeaves, rfl, rfl⟩

/-- **One insertion's new root is always `treeRoot TreeDepth` of its own, post-insertion
    leaf list.** Tree `tn` either sees no change at all, or its root history gains
    exactly `treeRoot TreeDepth` of whatever its leaf list now is — combining
    `insertResult_rootsAt`'s disjunction with `insertResult_leavesAt`'s exact equation
    to pin the pushed root's VALUE down, not just its existence. The invariant
    `ArmadaLean.PoolSafety.reachable_rootAt_matches_leavesAt` needs this exact match to
    carry through induction. -/
theorem insertResult_rootsAt_matches_leavesAt (closedTrees : List TreeState)
    (curLeaves curRoots : List Term) (newLeaves : List Term) (tn : Nat) :
    (PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn
      = PoolState.leavesAt closedTrees curLeaves curRoots tn ∧
     PoolState.rootsAt (insertResult closedTrees curLeaves curRoots newLeaves).1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn
      = PoolState.rootsAt closedTrees curLeaves curRoots tn) ∨
    PoolState.rootsAt (insertResult closedTrees curLeaves curRoots newLeaves).1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn
      = treeRoot TreeDepth
          (PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
            (insertResult closedTrees curLeaves curRoots newLeaves).2.1
            (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn)
        :: PoolState.rootsAt closedTrees curLeaves curRoots tn := by
  rw [insertResult_leavesAt]
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · have hres1 : (insertResult closedTrees curLeaves curRoots newLeaves).1
        = closedTrees ++ [⟨curLeaves, curRoots⟩] := by unfold insertResult; rw [if_pos hover]
    have hres22 : (insertResult closedTrees curLeaves curRoots newLeaves).2.2
        = [treeRoot TreeDepth newLeaves] := by unfold insertResult; rw [if_pos hover]
    have hlen : (closedTrees ++ [(⟨curLeaves, curRoots⟩ : TreeState)]).length = closedTrees.length + 1 := by
      simp
    rw [if_pos hover]
    unfold PoolState.rootsAt
    rw [hres1, hres22, hlen]
    by_cases htn : tn = closedTrees.length + 1
    · right
      rw [if_pos htn, if_pos htn, if_neg (by omega : tn ≠ closedTrees.length)]
      rw [List.getD_eq_default closedTrees tn ⟨[], []⟩ (by omega)]
    · left
      rw [if_neg htn, if_neg htn]
      refine ⟨rfl, ?_⟩
      by_cases htn2 : tn = closedTrees.length
      · rw [if_pos htn2, htn2, List.getD_concat_length]
      · rw [if_neg htn2]
        by_cases hlt : tn < closedTrees.length
        · rw [List.getD_append_of_lt closedTrees [(⟨curLeaves, curRoots⟩ : TreeState)] tn ⟨[], []⟩ hlt]
        · rw [List.getD_eq_default (closedTrees ++ [(⟨curLeaves, curRoots⟩ : TreeState)]) tn ⟨[], []⟩
            (by rw [hlen]; omega)]
          rw [List.getD_eq_default closedTrees tn ⟨[], []⟩ (by omega)]
  · have hres1 : (insertResult closedTrees curLeaves curRoots newLeaves).1 = closedTrees := by
      unfold insertResult; rw [if_neg hover]
    have hres22 : (insertResult closedTrees curLeaves curRoots newLeaves).2.2
        = treeRoot TreeDepth (curLeaves ++ newLeaves) :: curRoots := by
      unfold insertResult; rw [if_neg hover]
    rw [if_neg hover]
    unfold PoolState.rootsAt
    rw [hres1, hres22]
    by_cases htn : tn = closedTrees.length
    · right
      rw [if_pos htn, if_pos htn, if_pos htn]
    · left
      rw [if_neg htn, if_neg htn]
      exact ⟨rfl, by rw [if_neg htn]⟩

/-- A tree's leaf list only ever grows: `leaf_stable`'s companion fact — a position
    already in range stays in range forever, not just unchanged in value. -/
theorem insertResult_leavesAt_length_ge (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (newLeaves : List Term) (tn : Nat) :
    (PoolState.leavesAt closedTrees curLeaves curRoots tn).length ≤
      (PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.2 tn).length := by
  rw [insertResult_leavesAt]
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · rw [if_pos hover]
    by_cases htn : tn = closedTrees.length + 1
    · rw [if_pos htn]
      unfold PoolState.leavesAt
      rw [htn, if_neg (by omega : closedTrees.length + 1 ≠ closedTrees.length)]
      rw [List.getD_eq_default closedTrees (closedTrees.length + 1) ⟨[], []⟩ (by omega)]
      simp
    · rw [if_neg htn]; omega
  · rw [if_neg hover]
    by_cases htn : tn = closedTrees.length
    · rw [if_pos htn]
      unfold PoolState.leavesAt
      rw [htn, if_pos rfl]
      simp
    · rw [if_neg htn]; omega

/-- A fresh insertion's starting position is exactly the target tree's current leaf
    count (whichever tree `insertTreeNumber` picks: the current tree extended, or a new
    tree rolled into). Used by `PoolSafety.live_note_unspent` to show a just-inserted
    position was never live before, hence never spent before either. -/
theorem insertStartPos_eq_leavesAt_length (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (count : Nat) :
    insertStartPos curLeaves count =
      (PoolState.leavesAt closedTrees curLeaves curRoots (insertTreeNumber closedTrees curLeaves count)).length := by
  unfold insertStartPos insertTreeNumber PoolState.leavesAt
  by_cases hover : curLeaves.length + count > 2 ^ TreeDepth
  · rw [if_pos hover, if_pos hover]
    rw [if_neg (by omega : closedTrees.length + 1 ≠ closedTrees.length)]
    rw [List.getD_eq_default closedTrees (closedTrees.length + 1) ⟨[], []⟩ (by omega)]
    simp
  · rw [if_neg hover, if_neg hover, if_pos rfl]

/-- A fresh batch's resulting leaf list, in the tree it actually lands in, has exactly
    `insertStartPos` plus the batch size many leaves — the exact end-of-range
    counterpart to `insertStartPos_eq_leavesAt_length`'s start-of-range fact. Pins a
    fresh batch's positions to exactly `[insertStartPos, insertStartPos +
    newLeaves.length)`, matching what `withTreePositionsFrom_pos_ge`/
    `_pos_lt` give for the batch itself. -/
theorem insertResult_leavesAt_target_length (closedTrees : List TreeState)
    (curLeaves curRoots newLeaves : List Term) :
    (PoolState.leavesAt (insertResult closedTrees curLeaves curRoots newLeaves).1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.1
        (insertResult closedTrees curLeaves curRoots newLeaves).2.2
        (insertTreeNumber closedTrees curLeaves newLeaves.length)).length
      = insertStartPos curLeaves newLeaves.length + newLeaves.length := by
  rw [insertResult_leavesAt]
  unfold insertStartPos insertTreeNumber
  by_cases hover : curLeaves.length + newLeaves.length > 2 ^ TreeDepth
  · rw [if_pos hover, if_pos hover, if_pos rfl, if_pos hover]
    omega
  · rw [if_neg hover, if_neg hover, if_pos rfl, if_neg hover]
    simp

/-! ### Pool state -/

/-- The pool's state, at the level this model needs. `live t` is the model's ghost
    knowledge of every currently-unspent note of token `t`, as `((treeNumber, position),
    preimage)` entries keyed by tree number and leaf position (module comment: a note is
    identified by where it sits in the forest, never by a content scan). `spent tn` is
    the nullifier set of tree `tn` (`ArmadaLean.PoolOwned.NullifierSet`,
    `PrivacyPoolStorage.nullifiers`, PrivacyPoolStorage.sol:174, `mapping(uint256 =>
    mapping(bytes32 => bool))` — genuinely per-tree, since the same `(nk, leafIndex)`
    pair reused across two different trees derives the identical nullifier VALUE, and
    only per-tree bookkeeping keeps that harmless). `closedTrees`/`leaves`/`roots` are
    the tree forest (module comment on `TreeState`/`insertResult`) — always
    `ArmadaLean.Merkle.treeRoot TreeDepth` of whichever leaves were pushed, never a free
    choice. `held t` is the pool's own custody of token `t` — not `IERC20.balanceOf`,
    which a caller can inflate with a raw, pool-unmediated `transfer` that credits no
    note (sibling labbook entry §3a, the surplus/R4 discussion); `held` is the ledger the
    three modeled operations maintain, which is exactly what the core invariant is about.
    `preimageOf` mirrors `PrivacyPoolStorage.preimageOf`. `ownedRandomOf` is the second,
    approved-design public registry (`ArmadaLean.PoolOwned`'s module comment on
    `OwnedDisclosure`). `shieldsPaused` mirrors `IShieldPauseController.shieldsPaused`,
    read by `ShieldModule._requireShieldsNotPaused` — the one freeze the Armada design
    keeps, and it gates `Step.shield` alone (module comment, freeze-removal
    departure). -/
structure PoolState where
  live : Nat → List ((Nat × Nat) × CommitmentPreimage)
  spent : Nat → NullifierSet
  closedTrees : List TreeState
  leaves : List Term
  roots : List Term
  held : Nat → Nat
  preimageOf : PreimageRegistry
  ownedRandomOf : OwnedRandomRegistry
  shieldsPaused : Bool

/-- The total value of `token`'s currently-live notes: the pool's own ghost
    bookkeeping (`live`) read as a sum, not the custody ledger (`held`) — the
    quantity a caller's step must leave unchanged for one token to say "this
    step moved no value in or out of the pool" (`ArmadaLean.Adjudicator.
    notedValue_conserved`). `HeldInvariant` (`PoolSafety.lean`) proves this
    equals `held t` at every reachable state; the two are definitionally
    different quantities (one a ghost sum, one the on-chain custody field),
    kept apart so a one-step claim about this sum does not silently lean on
    reachability to hold. -/
def PoolState.notedValue (s : PoolState) (token : Nat) : Nat :=
  listSum ((s.live token).map (fun p => p.2.value))
/-- The root history of tree `treeNumber`, read off `s`'s own fields. -/
def PoolState.rootsAt' (s : PoolState) (treeNumber : Nat) : List Term :=
  PoolState.rootsAt s.closedTrees s.leaves s.roots treeNumber

/-- The leaf list of tree `treeNumber`, read off `s`'s own fields. -/
def PoolState.leavesAt' (s : PoolState) (treeNumber : Nat) : List Term :=
  PoolState.leavesAt s.closedTrees s.leaves s.roots treeNumber

/-- The state right after deployment (`PrivacyPool.initialize`, PrivacyPool.sol:81-127,
    which calls `MerkleModule.initializeMerkle`, MerkleModule.sol:26-38): no trees
    closed, tree 0 empty, no spent nullifiers in any tree, the one root of the empty
    tree (`ArmadaLean.Merkle.treeRoot TreeDepth []`, computed — not a free parameter
    standing for the real pinned `ZERO_VALUE`-derived constant, PrivacyPoolStorage.sol
    :150; see the module comment on `Term.val 0` as this model's stand-in zero value),
    no custody, empty registries, not paused. -/
def genesis : PoolState :=
  { live := fun _ => [], spent := fun _ => [], closedTrees := [],
    leaves := [], roots := [treeRoot TreeDepth []],
    held := fun _ => 0, preimageOf := fun _ => none, ownedRandomOf := fun _ => none,
    shieldsPaused := false }

/-! ### Deriving notes from a witness

A spend's input and output notes are never free choices: they are read off the witness
a `Constrained`/`OwnedConstrained` proof already pins down. These definitions are
the single place that reads them off, reused by every `Step` constructor and every
`can_happen` theorem below, so "which notes did this spend touch" has exactly one
answer, derived, not asserted. -/

/-- The `(treeNumber, position)`-keyed positions and preimages of a plain
    `TransactWitness`'s `N` inputs, within the one tree `treeNumber` the proof's
    `boundParams.treeNumber` names (PrivacyPoolStorage.sol:48,
    `BoundParamsCore.treeNumber`; all `N` inputs of one transaction share this one
    value — the circuit has no per-input tree field). Input `i` names leaf position
    `w.leavesIndices i` (the same position `nullifier nk (leavesIndices i)` is derived
    from, Transact.circom:97-101) and opens it as the commitment of `npk
    (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i)` (Transact.circom
    :74-84). -/
def transactSpentPositions {N M : Nat} (treeNumber : Nat) (w : TransactWitness N M) :
    List ((Nat × Nat) × CommitmentPreimage) :=
  List.ofFn fun i =>
    ((treeNumber, w.leavesIndices i),
      (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
        w.valueIn i⟩ : CommitmentPreimage))

/-- The commitment preimages of a plain `TransactWitness`'s `M` outputs, in witness
    order (Transact.circom:105-113). The circuit does not distinguish a kept note from
    an unshield payout; `Step.transact` below splits this list into the two. -/
def transactAllOutputs {N M : Nat} (w : TransactWitness N M) : List CommitmentPreimage :=
  List.ofFn fun j => (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)

/-- The `(treeNumber, position)`-keyed positions and preimages of an owned
    `TransactOwnedWitness`'s `N` inputs, within the one tree `treeNumber` the proof
    names, the same convention as `transactSpentPositions`. Input `i` names leaf
    position `w.leavesIndices i` (the same position `nullifier ownerField
    (leavesIndices i)` is derived from, TransactOwned.circom:89-97) and opens it as the
    commitment of `npk (Term.val pub.ownerField) (w.randomIn i)` (TransactOwned.circom
    :66-76). -/
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

Each constructor below takes, as explicit hypotheses, exactly the checks the named
contract function performs before it changes state — "an accepted proof means its
circuit constraints hold" is not reached for directly; the circuit-level facts
(`Constrained`/`OwnedConstrained`) are discharged by the caller who builds a `Step` value,
the same way `ArmadaLean.PoolOwned.owned_owner_binding` takes `OwnedConstrained` as a
hypothesis rather than a global fact. -/

/-- One valid transition of the pool. -/
inductive Step : PoolState → PoolState → Prop where
  /-- Local `ShieldModule.shield` (ShieldModule.sol:45-90).
      One `ShieldRequest` creates exactly one note of the shielded amount minus the fee
      (`_transferTokenIn`/`_getFee`, ShieldModule.sol:277-371, reusing
      `ArmadaLean.Fee.shieldBase`); see the module comment for why no second, fee, note
      is created. `npk` is the shielded note's public key, a term the caller supplies
      directly (the shield circuit does not derive it — the recipient computes their own
      `npk` off-chain and the shielder just names it, same role as `npkOut` in a
      `transact`). The note's commitment is appended to whichever tree currently has
      room — `insertResult` rolls over to a fresh tree first if it does not
      (`MerkleModule.insertLeaves`, MerkleModule.sol:54-121, rollover at :62-70); the
      note lands at the position `live` records it under, in the tree it actually
      landed in. The pushed root is `ArmadaLean.Merkle.treeRoot TreeDepth` of the
      result — computed, not a free parameter — so a shield cannot name a root that
      does not match the leaf it just inserted. No capacity hypothesis gates this
      constructor: a full tree rolls over instead of blocking the shield (module
      comment, rollover departure). `hNotPaused` is `_requireShieldsNotPaused`
      (ShieldModule.sol:393-397). `hValue` is `_validateCommitmentPreimage`'s
      `_note.value > 0` check (ShieldModule.sol:243-244) — the blocklist and
      field-range checks on the same line are elided (Pool module comment: they gate
      *which* shields succeed, not the value invariant). `hRange` is the note value's
      own field width: `CommitmentPreimage.value` is `uint120`
      (`PoolTypes.sol:79-83`), so every value the contract ever stores already fits —
      `ArmadaLean.PoolSafety.live_values_lt_2pow120` is this fact lifted to every live
      note, pool-wide. S-RG, "RAILGUN Core System & Protocol": "Then the smart contract
      transfers tokens from the user wallet to itself, if a deposit amount is specified
      ... The hashes of the output UTXOs are then added to the Merkle tree so they can
      be spent in the future." -/
  | shield {s : PoolState} (token grossAmount feeBP : Nat) (npk : Term)
      (hNotPaused : s.shieldsPaused = false)
      (hValue : 0 < grossAmount) (hFeeBP : feeBP ≤ BASIS)
      (hRange : RangeChecked120 (shieldBase feeBP grossAmount)) :
      Step s
        (let note : CommitmentPreimage := ⟨npk, token, shieldBase feeBP grossAmount⟩
         let tn := insertTreeNumber s.closedTrees s.leaves 1
         let pos := insertStartPos s.leaves 1
         let res := insertResult s.closedTrees s.leaves s.roots [hashCommitment note]
         { s with
             live := fun t => if t = token then ((tn, pos), note) :: s.live t else s.live t,
             held := fun t => if t = token then s.held t + note.value else s.held t,
             closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
             preimageOf := recordStep s.preimageOf (hashCommitment note) note })
  /-- Local `TransactModule.transact` (TransactModule.sol:43-96), covering both a pure
      transfer and a transfer with a local unshield. `w`/`pub` are the proof's own
      witness and public inputs; `hC : Constrained w pub` is the soundness hypothesis
      ("an accepted proof means its circuit constraints hold") — this is what ties
      `transactSpentPositions treeNumber w` to notes the spender actually derived from
      keys it holds, not a free choice (see
      `ArmadaLean.PoolSafety.transact_spends_only_owned`). `treeNumber` is the proof's
      own `boundParams.treeNumber` (PrivacyPoolStorage.sol:48,
      `BoundParamsCore.treeNumber`): the one tree every one of this transaction's
      inputs' membership proofs and nullifiers are checked against — `hRoot`/
      `hRemove`/`hNullify` all key off it, exactly as `_validateCommonContext`
      (TransactModule.sol:538) and `_accumulateAndNullify` (TransactModule.sol
      :381-385) do. `hN`/`hM` are the registered circuit shapes:
      `VerifierModule.setVerificationKey` (VerifierModule.sol:32-47) registers one key
      per `(nullifierCount, commitmentCount)` pair, and an unregistered shape reverts
      (`verifyingKey.alpha1.x != 0` check, PrivacyPool.sol:519); the 19 registered plain
      shapes (`armada-circuits/src/main/main_{1x1,1x2,1x3,2x1,2x2,2x3,3x1,3x2,3x3,4x1,
      4x2,4x3,5x1,5x2,6x1,6x2,7x1,8x1,8x4}.circom`) all satisfy `N ≤ 8 ∧ M ≤ 4`, the
      exact bound `transact_value_conserved` needs. `hSplit`/`hUnshieldLen` separate the
      circuit's uniform `M` outputs (`transactAllOutputs`) into the notes that stay
      live and, at most, one unshield payout — the circuit itself draws no such line
      (TransactOwned.circom/Transact.circom treat every output alike); the pool does,
      via `boundParams.unshield`/`commitmentCiphertext.length` (TransactModule.sol
      :289-337). `hRemove` is the ghost-level half of "spend these inputs", keyed by
      the leaf positions the witness names within tree `treeNumber`
      (`transactSpentPositions`) — a spend of a position that is not live in that tree
      has no step, since `removeAll` fails (`none`) the moment a requested position is
      missing. `hNullify` is its on-chain half, `_accumulateAndNullify`
      (TransactModule.sol:373-399), against tree `treeNumber`'s own nullifier set
      (`s.spent treeNumber`). The kept outputs land wherever the CURRENT tree has room
      (never necessarily tree `treeNumber` itself — a rollover may have moved on since
      the spent inputs were created), at the positions `live` records them under. Every
      output value's own `uint120` field width (`hRangeOut`'s role, `OwnedConstrained
      .rangeOut`/`Constrained.rangeOut`, folded into `hC`) is already part of
      `Constrained`, so no separate hypothesis is needed here for
      `live_values_lt_2pow120`. `hRecords` is `_validatePublicOutputs (requireAll =
      false)`/`_recordPreimages` (TransactModule.sol:544-604): disclosure is optional,
      so `records` is any sublist of the outputs' own `(commitment, preimage)` pairs
      (`transactOutputRecords`), in witness order — never an unrelated list, since
      `List.Sublist` forces every disclosed entry to be one of the circuit's own
      outputs (`transactOutputRecords_valid` then gives `hashCommitment` correctness
      for free, not as a separate hypothesis). `ownedRecords`/`hOwnedRecords` are the
      approved design's optional extra: for any disclosed output the discloser
      additionally claims is contract-owned, it supplies `(ownerField, random)` and the
      pool checks `npk (ownerField) random` matches that output's own `npk` —
      `hOwnedRecords` requires every such claim to point at an already-disclosed,
      matching entry (a deposit to the adjudicator is one scenario this covers;
      `ArmadaLean.PoolOwned`'s module comment on `OwnedDisclosure` records the
      departure). The balance fact itself is not a hypothesis here:
      `ArmadaLean.PoolSafety.step_preserves_invariant` derives it from
      `transact_value_conserved hN hM hC` at the point it is needed, exactly as the
      contract's own guarantee rests on the circuit constraints and nothing else. S-RG:
      "The contract checks to make sure: ... That it hasn't seen the nullifiers
      before, eliminating any double spends[;] The Merkle root is the current or a
      previous Merkle root, to prevent users from making up UTXOs." Zokyo's 2022-12-21
      audit of `RailgunLogic.sol`
      (`.scratch/rewrite-B/sources/railgun-audit-2022-12-21-Zokyo.pdf`, sha256
      `b974caa94f7eee9f3f52e7996e4251ac1581523af161a5c83b7468cb06f3a9a9`), finding #1
      ("Transaction validation is out of the scope", Medium, Resolved): "the current
      implementation ... does not validate unshieldPreimage to contain a correct value
      [;] anyone could call a function providing its own address and get all tokens."
      Armada's `_validateTransaction` already carries this fix (TransactModule.sol
      :295-331, the unshield npk/value/token checks and the
      `_hashCommitment(unshieldPreimage) == commitments[last]` check), which is what
      licenses `hSplit` reading the unshield payout off the circuit's own output. The
      same audit, finding #2 ("Possible re-entrancy", Medium, Resolved), recommends
      marking a transaction processed before any token moves; `_accumulateAndNullify`
      already runs for every transaction in the batch (TransactModule.sol:63-73) before
      any unshield payout (TransactModule.sol:76-80) — `hNullify` is taken before `held`
      changes below for the same reason.

      DEPARTURE (contract, owner-controlled freeze removed): the merged contract checks
      `_requireNotEmergencyPaused`/`_requireNotWithdrawOnly` before every `transact`
      (called at TransactModule.sol:48, :52; the checks themselves at :460-475), which
      can revert the whole call whenever the owner has installed a controller
      (`PrivacyPool.setShieldPauseContract`, owner-gated, no restriction on when,
      PrivacyPool.sol:466-470) whose `emergencyPaused()` or `withdrawOnlyMode()` returns
      true. This constructor carries no such check: the Armada design removes the
      owner's power to block a spend. `hRoot`, `hRemove` and `hNullify` are the only
      preconditions that gate a `transact`, and none of them reads `s.shieldsPaused` —
      `ArmadaLean.PoolSafety.transact_cannot_be_blocked` proves no step any caller can
      take, the owner included, changes whether they hold. -/
  | transact {s : PoolState} {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M)
      (treeNumber : Nat)
      (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
      (newNotes unshieldTail : List CommitmentPreimage)
      (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
      (records : List (Term × CommitmentPreimage))
      (ownedRecords : List (Term × OwnedDisclosure))
      (hRoot : pub.merkleRoot ∈ s.rootsAt' treeNumber)
      (hSplit : transactAllOutputs w = newNotes ++ unshieldTail)
      (hUnshieldLen : unshieldTail.length ≤ 1)
      (hRemove : removeAll (s.live w.token) (transactSpentPositions treeNumber w) = some rest)
      (hNullify : markSpent (s.spent treeNumber) (List.ofFn pub.nullifiers) = some spent')
      (hRecords : records.Sublist (transactOutputRecords w pub))
      (hOwnedRecords : ∀ cd ∈ ownedRecords, ∃ pre, (cd.1, pre) ∈ records ∧
        npk cd.2.ownerField cd.2.random = pre.npk) :
      Step s
        (let res := insertResult s.closedTrees s.leaves s.roots (newNotes.map hashCommitment)
         let tn := insertTreeNumber s.closedTrees s.leaves newNotes.length
         let pos := insertStartPos s.leaves newNotes.length
         { s with
            live := fun t => if t = w.token
                then withTreePositionsFrom tn pos newNotes ++ rest else s.live t,
            spent := fun n => if n = treeNumber then spent' else s.spent n,
            held := fun t => if t = w.token
                then s.held t - listSum (unshieldTail.map CommitmentPreimage.value)
                else s.held t,
            closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
            preimageOf := applyRecords s.preimageOf records,
            ownedRandomOf := applyOwnedRecords s.ownedRandomOf ownedRecords })
  /-- `TransactModule.transactOwned` (TransactModule.sol:488-519): the same bookkeeping
      shape as `transact`, with no unshield (`_validateOwnedTransaction` rejects any
      `unshield != NONE`, TransactModule.sol:619-623) and every output's preimage
      mandatory (`_validatePublicOutputs(requireAll = true)`, TransactModule.sol:630-634):
      every owned output is disclosed, so the registry update is fixed to
      `ownedOutputRecords w pub` — the circuit's whole output batch, not a candidate
      list a caller trims (unlike `transact`, where disclosure is optional). `hNonZero`
      is `_validatePublicOutputs(requireAll = true)`'s own check that no owned output
      may be the zero preimage (TransactModule.sol:567-571, "Missing public output").
      `hC : OwnedConstrained w pub` is the soundness hypothesis; `caller`/`hCaller` is
      the authorization check (`ownerField == msg.sender`,
      TransactModule.sol:636-639) — together these are exactly what
      `ArmadaLean.PoolSafety.transactOwned_spends_only_owned`
      (`ArmadaLean.PoolOwned.owned_owner_binding`) needs. `hN`/`hM`: the registered owned
      shapes (`armada-circuits/src/main/main_{1x1,1x2,1x3}_owned.circom`) all have
      `N = 1 ≤ 8` and `M ≤ 3 ≤ 4`, well inside the bound
      `transactOwned_value_conserved` needs; this model uses the same `N ≤ 8 ∧ M ≤ 4`
      bound as the plain path rather than the tighter true one, since that is the bound
      the existing proof already supplies. `treeNumber` is the proof's own
      `boundParams.treeNumber`, the same role it plays for `Step.transact`. The spent
      positions come from `ownedSpentPositions`; the spend removes exactly those
      positions from `live`, within tree `treeNumber`, and a position that is not live
      there has no step. The new outputs land wherever the current tree has room
      (`insertResult`, rolling over first if needed), at the positions `live` records
      them under. No capacity hypothesis gates this constructor (module comment,
      rollover departure). `randomOut`/`hRandomOut`... no: `ownedOutputs`/
      `hOwnedOutputs` are the approved design's owned-random disclosure, applied per
      output, the same way `Step.transact`'s `ownedRecords` applies it: an owned spend
      legitimately pays OUT to a recipient's own note key, not only re-mints notes to
      itself (an adjudicator's payout output is one such case), so the random
      disclosure cannot be mandatory for every output the way the preimage itself is
      (`ownedOutputRecords w pub`, `requireAll = true`, unaffected). For each `(j,
      ownerField, random)` the caller lists, output `j`'s own `npkOut` must equal
      `npk (ownerField) random`; that output is then recorded into `ownedRandomOf`
      alongside the `ownerField` claimed for it. An output whose index is not listed
      is a plain user note — no owned disclosure, same as a `transact` output nobody
      claims as owned.

      DEPARTURE (contract, owner-controlled freeze removed): the merged contract checks
      `_requireNotEmergencyPaused`/`_requireNotWithdrawOnly` before `transactOwned` too
      (called at TransactModule.sol:491-492; the checks themselves at :460-475) —
      withdraw-only mode in particular always blocks an owned transaction outright,
      since the owned path's `unshield` is always `NONE` and `_requireNotWithdrawOnly`
      demands `unshield != NONE` for every transaction while withdraw-only mode is on.
      This constructor carries no such check: the Armada design removes the owner's
      power to block a spend, owned included. `hRoot`, `hRemove` and `hNullify` are the
      only preconditions that gate a `transactOwned`, and none of them reads
      `s.shieldsPaused` — `ArmadaLean.PoolSafety.transactOwned_cannot_be_blocked` proves
      no step any caller can take, the owner included, changes whether they hold. -/
  | transactOwned {s : PoolState} {N M : Nat} (w : TransactOwnedWitness N M)
      (pub : TransactOwnedPublic N M) (treeNumber : Nat) (hN : N ≤ 8) (hM : M ≤ 4)
      (hC : OwnedConstrained w pub) (caller : Term) (hCaller : caller = pub.ownerField)
      (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
      (ownedOutputs : List (Fin M × OwnedDisclosure))
      (hRoot : pub.merkleRoot ∈ s.rootsAt' treeNumber)
      (hRemove : removeAll (s.live w.token) (ownedSpentPositions treeNumber pub w) = some rest)
      (hNullify : markSpent (s.spent treeNumber) (List.ofFn pub.nullifiers) = some spent')
      (hNonZero : ∀ j, ¬ isZeroPreimage
        (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
      (hOwnedOutputs : ∀ x ∈ ownedOutputs, npk x.2.ownerField x.2.random = w.npkOut x.1) :
      Step s
        (let res := insertResult s.closedTrees s.leaves s.roots ((ownedNewNotes w).map hashCommitment)
         let tn := insertTreeNumber s.closedTrees s.leaves (ownedNewNotes w).length
         let pos := insertStartPos s.leaves (ownedNewNotes w).length
         { s with
            live := fun t => if t = w.token
                then withTreePositionsFrom tn pos (ownedNewNotes w) ++ rest else s.live t,
            spent := fun n => if n = treeNumber then spent' else s.spent n,
            closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
            preimageOf := applyRecords s.preimageOf (ownedOutputRecords w pub),
            ownedRandomOf := applyOwnedRecords s.ownedRandomOf
              (ownedOutputs.map fun x => (pub.commitmentsOut x.1, x.2)) })
  /-- The one remaining administrative path that changes pool state at all:
      `setShieldPauseContract` installs a controller whose `IShieldPauseController
      .shieldsPaused` this model reads (`ShieldModule._requireShieldsNotPaused`,
      ShieldModule.sol:393-397) — the Armada design keeps this one freeze, and only
      this one: it blocks `Step.shield` alone (module comment, freeze-removal
      departure). Every other owner function (`setShieldFee`, `setFeeRecipient`,
      `addToBlocklist`, `setVerificationKey`, `setVerificationKeyOwned`,
      `setTestingMode`, ...) changes configuration this model does not represent and is
      not modeled individually: none of them touches `live`, `spent`, `roots`, `held`,
      `preimageOf` or `ownedRandomOf`, so every one of them is this same no-op on the
      fields the safety theorems are about. -/
  | admin {s : PoolState} (shieldsPaused : Bool) :
      Step s { s with shieldsPaused := shieldsPaused }

/-- Every state the pool can reach from deployment, by any sequence of calls from any
    caller — the quantifier the brief's four promises range over. `genesis` is now a
    concrete value (the empty-tree root is computed, not a free parameter — see
    `genesis`'s doc comment), so `Reachable` no longer needs to be indexed by it. -/
inductive Reachable : PoolState → Prop where
  | genesis : Reachable genesis
  | step {s s' : PoolState} (hs : Reachable s) (hstep : Step s s') :
      Reachable s'
