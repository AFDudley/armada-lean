/-
  ArmadaLean.Merkle — binary Poseidon Merkle membership proofs.

  Mirrors merkle.circom:39-54 exactly. The circuit computes, per level, with
  `sel` the path bit and `deltaLR = sel * (sibling - current)`:
    left  = current + deltaLR
    right = sibling - deltaLR
  so bit = 0 → hash(current, sibling) and bit = 1 → hash(sibling, current)
  (merkle.circom:43-49). Bits are read LSB-first (merkle.circom:14), which is
  why we simply fold over the path list in order. Production depth is 16
  (Transact.circom:87), but the model and proofs are general over the path.

  A leaf, a sibling and a root are all terms (`ArmadaLean.Poseidon.Term`): a leaf is a
  commitment (itself a Poseidon output), siblings are other tree nodes, and the root is
  the symbolic Poseidon hash of the path, computed exactly as `merkleStep` folds.
-/
import ArmadaLean.Poseidon

/-- One Merkle level: `false` → the current node is the left child,
    `true` → the current node is the right child (merkle.circom:43-49). -/
def merkleStep (cur sib : Term) (bit : Bool) : Term :=
  if bit then Term.hash2 sib cur else Term.hash2 cur sib

/-- The root computed by a membership proof: fold `merkleStep` from the leaf
    up through `(sibling, directionBit)` pairs (merkle.circom:31-54, with the
    `levelHash` chain unrolled as a fold). -/
def merkleRoot (leaf : Term) (path : List (Term × Bool)) : Term :=
  path.foldl (fun cur (sib, bit) => merkleStep cur sib bit) leaf

/--
A Merkle membership proof binds exactly one leaf to the root (Poseidon collision
resistance, by construction — `ArmadaLean.Poseidon`). Together with the on-chain root
check (Transact.circom:95), a prover cannot move a proof to a different commitment:
any two leaves yielding the same computed root along the same path are equal. -/
theorem merkleRoot_inj_leaf (path : List (Term × Bool)) {l₁ l₂ : Term}
    (h : merkleRoot l₁ path = merkleRoot l₂ path) : l₁ = l₂ := by
  induction path generalizing l₁ l₂ with
  | nil => exact h
  | cons p ps ih =>
    obtain ⟨sib, bit⟩ := p
    simp only [merkleRoot, List.foldl_cons] at h
    have hstep : merkleStep l₁ sib bit = merkleStep l₂ sib bit := ih h
    cases bit with
    | false => exact (Term.hash2_inj hstep).1
    | true => exact (Term.hash2_inj hstep).2

/-! ### The incremental tree, as one static binary tree over its leaf list

`MerkleModule.insertLeaves` (MerkleModule.sol:54-121) computes updates to the pool's
tree incrementally, using `filledSubTrees` as memoized partial roots, for gas (module
comment there: "deliberately mutates `leafHashes` in place to save gas"). Whatever
shortcuts the gas-optimized algorithm takes, the FINAL value it produces is the root of
the standard binary Merkle tree over `2^TreeDepth` leaf slots, with the real leaves in
insertion order at the low positions and the zero node (`ZERO_VALUE`,
PrivacyPoolStorage.sol:150, modeled here as `Term.val 0` — the model does not recompute
the real pinned constant, the same choice `ArmadaLean.Pool`'s module comment on `roots`
already makes) filling every unused slot — that tree is what `treeRoot`/`treePath`
define directly, non-incrementally, since this project only needs the tree's final
value and leaf-membership facts, never a gas analysis. `TreeDepth` mirrors
`PrivacyPoolStorage.TREE_DEPTH` (PrivacyPoolStorage.sol:144).

DEPARTURE, now closed: an earlier version of this model represented exactly one tree,
with no rollover, taking an explicit capacity hypothesis on every leaf-inserting step.
`MerkleModule.insertLeaves` actually rolls over to a fresh tree, `treeNumber += 1`, when
a batch would overflow the current one (MerkleModule.sol:62-70); `PrivacyPoolStorage
.rootHistory` and `nullifiers` are then keyed by `treeNumber` (PrivacyPoolStorage.sol
:171,174), so a later tree's roots and nullifier space are independent of an earlier
tree's. `ArmadaLean.Pool`'s `TreeState`/`insertResult`/`PoolState.closedTrees` model
this forest directly: a `shield`/`transact`/`transactOwned` step that would overflow
the current tree rolls into a fresh one instead of having no witness, and no capacity
hypothesis gates any of the three any more
(`ArmadaLean.PoolSafety.reachable_leavesAt_capacity` proves every tree, including a
freshly-rolled-into one, stays within `2 ^ TreeDepth` leaves on its own, by induction,
not by hypothesis). -/

/-- The production Merkle tree depth (`PrivacyPoolStorage.TREE_DEPTH`,
    PrivacyPoolStorage.sol:144): `2^16 = 65536` leaves per tree. -/
def TreeDepth : Nat := 16

/-- The root of the depth-`d` binary tree whose leaves, left to right, are `leaves`,
    padded on the right with the zero node wherever `leaves` runs out. Defined by
    splitting the `2^d` leaf slots into a left half (`leaves.take (2^(d-1))`) and a
    right half (`leaves.drop (2^(d-1))`), recursively rooting each, and combining —
    the standard top-down definition of a binary Merkle tree, which computes the same
    value the bottom-up incremental algorithm does (module comment above). At `d = 0`
    there is one leaf slot, filled by `leaves`' head if present or the zero sentinel
    `Term.val 0` otherwise. -/
def treeRoot : Nat → List Term → Term
  | 0, leaves => leaves.headD (Term.val 0)
  | d + 1, leaves =>
    let half := 2 ^ d
    merkleStep (treeRoot d (leaves.take half)) (treeRoot d (leaves.drop half)) false

/-- The Merkle membership path (`merkleRoot`'s `(sibling, bit)` list) from leaf position
    `i` up to the root of the depth-`d` tree over `leaves`, mirroring `treeRoot`'s own
    split: if `i` is in the left half, recurse there and append the right half's root
    as the top-level (sibling, `false`) entry (`i` is on the left, bit `false` matches
    `merkleStep`'s "current is left" case); symmetrically for the right half. -/
def treePath : Nat → List Term → Nat → List (Term × Bool)
  | 0, _, _ => []
  | d + 1, leaves, i =>
    let half := 2 ^ d
    if i < half then
      treePath d (leaves.take half) i ++ [(treeRoot d (leaves.drop half), false)]
    else
      treePath d (leaves.drop half) (i - half) ++ [(treeRoot d (leaves.take half), true)]

theorem treeRoot_succ (d : Nat) (leaves : List Term) :
    treeRoot (d + 1) leaves =
      merkleStep (treeRoot d (leaves.take (2 ^ d))) (treeRoot d (leaves.drop (2 ^ d))) false := rfl

theorem treePath_succ_lt (d : Nat) (leaves : List Term) (i : Nat) (h : i < 2 ^ d) :
    treePath (d + 1) leaves i =
      treePath d (leaves.take (2 ^ d)) i ++ [(treeRoot d (leaves.drop (2 ^ d)), false)] := by
  show (if i < 2 ^ d then
      treePath d (leaves.take (2 ^ d)) i ++ [(treeRoot d (leaves.drop (2 ^ d)), false)]
    else
      treePath d (leaves.drop (2 ^ d)) (i - 2 ^ d) ++ [(treeRoot d (leaves.take (2 ^ d)), true)]) = _
  rw [if_pos h]

theorem treePath_succ_ge (d : Nat) (leaves : List Term) (i : Nat) (h : ¬ i < 2 ^ d) :
    treePath (d + 1) leaves i =
      treePath d (leaves.drop (2 ^ d)) (i - 2 ^ d) ++ [(treeRoot d (leaves.take (2 ^ d)), true)] := by
  show (if i < 2 ^ d then
      treePath d (leaves.take (2 ^ d)) i ++ [(treeRoot d (leaves.drop (2 ^ d)), false)]
    else
      treePath d (leaves.drop (2 ^ d)) (i - 2 ^ d) ++ [(treeRoot d (leaves.take (2 ^ d)), true)]) = _
  rw [if_neg h]

theorem List.getD_take_of_lt {α} (l : List α) (i half : Nat) (h : i < half) (d : α) :
    (l.take half).getD i d = l.getD i d := by
  induction l generalizing i half with
  | nil => simp
  | cons a l ih =>
    cases half with
    | zero => omega
    | succ half' =>
      cases i with
      | zero => simp
      | succ i' =>
        simp only [List.take_succ_cons, List.getD_cons_succ]
        exact ih i' half' (by omega)

theorem List.getD_drop_eq {α} (l : List α) (half i : Nat) (d : α) :
    (l.drop half).getD i d = l.getD (half + i) d := by
  induction half generalizing l with
  | zero => simp
  | succ half' ih =>
    cases l with
    | nil => simp
    | cons a l =>
      simp only [List.drop_succ_cons]
      rw [ih]
      have hswap : half' + 1 + i = (half' + i) + 1 := by omega
      rw [hswap, List.getD_cons_succ]

/--
**A Merkle path computed by `treePath` against a leaf list reconstructs the real
`treeRoot` of that list, for any in-range position.** Proved by induction on the depth,
splitting exactly as `treeRoot`/`treePath` do: the leaf at position `i` in the left half
(`i < 2^d`) folds, by the induction hypothesis on `leaves.take (2^d)`, to that half's
root, and the one remaining `(sibling, bit)` entry `treePath` appends — the right
half's root, paired with `false` — combines it with the right half exactly as
`treeRoot`'s own `merkleStep` does; symmetrically on the right. This is the proof-
construction half of "every leaf ever inserted has a Merkle witness to a root the pool
produced" (`ArmadaLean.PoolSafety.leaf_has_merkle_witness`): the witness is `treePath`
itself, not a free choice. -/
theorem treePath_correct (d : Nat) (leaves : List Term) (i : Nat) (hi : i < 2 ^ d) :
    merkleRoot (leaves.getD i (Term.val 0)) (treePath d leaves i) = treeRoot d leaves := by
  induction d generalizing leaves i with
  | zero =>
    simp only [Nat.pow_zero] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    show merkleRoot (leaves.getD 0 (Term.val 0)) [] = leaves.headD (Term.val 0)
    unfold merkleRoot
    cases leaves <;> rfl
  | succ d ih =>
    by_cases hlt : i < 2 ^ d
    · rw [treePath_succ_lt d leaves i hlt, treeRoot_succ]
      unfold merkleRoot
      rw [List.foldl_append]
      have hget : (leaves.take (2 ^ d)).getD i (Term.val 0) = leaves.getD i (Term.val 0) :=
        List.getD_take_of_lt leaves i (2 ^ d) hlt (Term.val 0)
      rw [← hget]
      have hind := ih (leaves.take (2 ^ d)) i hlt
      unfold merkleRoot at hind
      rw [hind]
      rfl
    · rw [treePath_succ_ge d leaves i hlt, treeRoot_succ]
      unfold merkleRoot
      rw [List.foldl_append]
      have hi2 : i - 2 ^ d < 2 ^ d := by
        simp only [Nat.pow_succ] at hi
        omega
      have hget : (leaves.drop (2 ^ d)).getD (i - 2 ^ d) (Term.val 0) = leaves.getD i (Term.val 0) := by
        rw [List.getD_drop_eq]
        congr 1
        omega
      rw [← hget]
      have hind := ih (leaves.drop (2 ^ d)) (i - 2 ^ d) hi2
      unfold merkleRoot at hind
      rw [hind]
      rfl

/-- A `treePath` at depth `d` always has exactly `d` entries — one `(sibling, bit)`
    pair per level, matching `Constrained.pathLen`/`OwnedConstrained.pathLen`'s own
    `= 16` requirement once `d = TreeDepth`. -/
theorem treePath_length (d : Nat) (leaves : List Term) (i : Nat) :
    (treePath d leaves i).length = d := by
  induction d generalizing leaves i with
  | zero => rfl
  | succ d ih =>
    by_cases hlt : i < 2 ^ d
    · rw [treePath_succ_lt d leaves i hlt]
      simp [ih]
    · rw [treePath_succ_ge d leaves i hlt]
      simp [ih]
