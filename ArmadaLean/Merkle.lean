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

  `TransactOwned.circom` is an open pull request, not yet merged into `main`:
  ship-armada/armada-circuits#7 (see `ArmadaLean.TransactOwned`'s header for
  the head commit). Citations below to it describe that PR branch, used as
  the owned path's design source.
-/
import ArmadaLean.Poseidon
import ArmadaLean.RangeCheck
import Mathlib.Tactic.Says

namespace ArmadaLean

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

/-- Two membership proofs with one length and one list of direction bits that compute
    one root open one leaf. The sibling terms may differ; `Term.hash2_inj` forces them
    equal level by level. -/
theorem merkleRoot_inj_bits (path path' : List (Term × Bool)) {l l' : Term}
    (hlen : path.length = path'.length) (hbits : path.map Prod.snd = path'.map Prod.snd)
    (h : merkleRoot l path = merkleRoot l' path') : l = l' := by
  induction path generalizing path' l l' with
  | nil =>
    cases path' with
    | nil => exact h
    | cons _ _ => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_one_ne_zero] at hlen
  | cons p ps ih =>
    cases path' with
    | nil => simp only [List.length_cons, List.length_nil, Nat.add_one_ne_zero] at hlen
    | cons p' ps' =>
      obtain ⟨sib, bit⟩ := p
      obtain ⟨sib', bit'⟩ := p'
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons, List.cons.injEq] at hbits
      obtain ⟨hbit, hbits⟩ := hbits
      subst hbit
      simp only [merkleRoot, List.foldl_cons] at h
      have hstep : merkleStep l sib bit = merkleStep l' sib' bit := ih ps' hlen hbits h
      cases bit with
      | false => exact (Term.hash2_inj hstep).1
      | true => exact (Term.hash2_inj hstep).2

/-- `MerkleTreeProof(depth)` (merkle.circom:20-55) as one input of `Transact.circom:86-95`
    and `TransactOwned.circom:78-87` instantiates it, with `depth = 16`. The circuit takes
    the siblings `pathElements[depth]` and the packed leaf index `pathIndices`
    (merkle.circom:22-23). `Num2Bits(depth)` constrains `pathIndices` to the sum of its
    `depth` boolean output bits (merkle.circom:28-29). Bit `i` selects the order of the
    level-`i` hash: `0` puts the current node left, `1` puts it right (merkle.circom:44-49,
    `merkleStep`). The bits are read LSB first (merkle.circom:14): bit `0` is the leaf
    level. The model keeps the path as `(sibling, bit)` pairs; this structure ties the bits
    to the index. The model states this tie, which the circuit
    enforces. Before, a witness could open one leaf and name another index. -/
structure MerkleProof (depth : Nat) (leaf : Term) (path : List (Term × Bool)) (index : Nat)
    (root : Term) : Prop where
  /-- One `(sibling, bit)` pair per level: `pathElements[depth]` (merkle.circom:22). -/
  len : path.length = depth
  /-- `Num2Bits(depth)`: `pathIndices === Σ bits[i] * 2^i` (merkle.circom:28-29, circomlib
      bitify.circom), with the direction bits as the output bits. With `len`, this also
      bounds `index < 2 ^ depth` (`bitsVal_lt_two_pow`). -/
  bits : bitsVal (path.map Prod.snd) = index
  /-- The fold from `leaf` reaches `root` (`root <== levelHash[depth]`, merkle.circom:54),
      and the public root equals it (Transact.circom:95, TransactOwned.circom:87). -/
  root_eq : merkleRoot leaf path = root

/-- The index of a `MerkleProof` is below `2 ^ depth`: `Num2Bits(depth)` admits no other
    value. -/
theorem MerkleProof.index_lt {depth : Nat} {leaf : Term} {path : List (Term × Bool)}
    {index : Nat} {root : Term} (h : MerkleProof depth leaf path index root) :
    index < 2 ^ depth := by
  have hlt := bitsVal_lt_two_pow (path.map Prod.snd)
  rw [h.bits, List.length_map, h.len] at hlt
  exact hlt

/-! ### The incremental tree, as one static binary tree over its leaf list

`MerkleModule.insertLeaves` (MerkleModule.sol:54-121) computes updates to the pool's
tree incrementally, using `filledSubTrees` as memoized partial roots, for gas (module
comment there: "deliberately mutates `leafHashes` in place to save gas"). Whatever
shortcuts the gas-optimized algorithm takes, the FINAL value it produces is the root of
the standard binary Merkle tree over `2^TreeDepth` leaf slots, with the real leaves in
insertion order at the low positions and the empty leaf (`ZERO_VALUE`,
PrivacyPoolStorage.sol:150, the constant `emptyLeaf` below) filling
every unused slot — that tree is what `treeRoot`/`treePath` define directly,
non-incrementally, since this project only needs the tree's final value and
leaf-membership facts, never a gas analysis. `TreeDepth` mirrors
`PrivacyPoolStorage.TREE_DEPTH` (PrivacyPoolStorage.sol:144).

An earlier version of this model used `Term.val 0` as the empty leaf. The same term
also served as the "absent" default of a leaf lookup and as the "no disclosure"
sentinel. The empty leaf is now its own named constant, and a leaf lookup
returns an `Option`.

`ArmadaLean.Pool` models the forest of trees (`TreeState`, `insertLeaves`):
`MerkleModule.insertLeaves` starts a fresh tree, `treeNumber += 1`, when a batch would
overflow the current one (MerkleModule.sol:62-70). No capacity hypothesis gates a step
(`ArmadaLean.PoolSafety.reachable_leavesAt_capacity` proves every tree stays within
`2 ^ TreeDepth` leaves by induction). -/

/-- The production Merkle tree depth (`PrivacyPoolStorage.TREE_DEPTH`,
    PrivacyPoolStorage.sol:144): `2^16 = 65536` leaves per tree. -/
def TreeDepth : Nat := 16

/-- The empty leaf `ZERO_VALUE` (armada-poc PrivacyPoolStorage.sol:150, `bytes32 public
    constant ZERO_VALUE = 0x0488f89b25bc7011eaf6a5edce71aeafb9fe706faa3c0a5cd9cbe868ae3b9ffc`,
    on `fork/main`, last changed in commit `4081579b`). It fills every unused leaf slot
    of a tree. The value is `keccak256("Railgun") mod p` over the BN254 scalar field,
    RAILGUN's derivation of its zero value, recomputed against the pin on 2026-11-08.
    Design decision 2026-11-08: the model states the contract's real constant. An
    earlier version kept it `opaque`. A `Term.val`, so it is never a hash term
    (`emptyLeaf_ne_hash`): no note commitment is the empty leaf. -/
def emptyLeaf : Term :=
  Term.val 0x0488f89b25bc7011eaf6a5edce71aeafb9fe706faa3c0a5cd9cbe868ae3b9ffc

/-- The empty leaf is never a hash term, so it is never a commitment
    (`PoolOwned.emptyLeaf_ne_hashCommitment` states the commitment form). By constructor
    disjointness of `Term`. -/
theorem emptyLeaf_ne_hash (fn : HashFn) (l : List Term) : emptyLeaf ≠ Term.hash fn l :=
  Term.val_ne_hash _ fn l

/-- The root of the depth-`d` binary tree whose leaves, left to right, are `leaves`,
    padded on the right with `emptyLeaf` wherever `leaves` runs out. Defined by
    splitting the `2^d` leaf slots into a left half (`leaves.take (2^(d-1))`) and a
    right half (`leaves.drop (2^(d-1))`), recursively rooting each, and combining —
    the standard top-down definition of a binary Merkle tree, which computes the same
    value the bottom-up incremental algorithm does (module comment above). At `d = 0`
    there is one leaf slot, filled by `leaves`' head if present or by `emptyLeaf`
    otherwise. -/
def treeRoot : Nat → List Term → Term
  | 0, leaves => leaves.headD emptyLeaf
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
  | nil => (simp? says simp only [List.take_nil, List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none])
  | cons a l ih =>
    cases half with
    | zero => omega
    | succ half' =>
      cases i with
      | zero => (simp? says simp only [List.take_succ_cons, List.getD_eq_getElem?_getD, List.length_cons, List.length_take, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.getD_some])
      | succ i' =>
        simp only [List.take_succ_cons, List.getD_cons_succ]
        exact ih i' half' (by omega)

theorem List.getD_drop_eq {α} (l : List α) (half i : Nat) (d : α) :
    (l.drop half).getD i d = l.getD (half + i) d := by
  induction half generalizing l with
  | zero => (simp? says simp only [List.drop_zero, List.getD_eq_getElem?_getD, Nat.zero_add])
  | succ half' ih =>
    cases l with
    | nil => (simp? says simp only [List.drop_nil, List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none])
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
    merkleRoot (leaves.getD i emptyLeaf) (treePath d leaves i) = treeRoot d leaves := by
  induction d generalizing leaves i with
  | zero =>
    simp only [Nat.pow_zero] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    show merkleRoot (leaves.getD 0 emptyLeaf) [] = leaves.headD emptyLeaf
    unfold merkleRoot
    cases leaves <;> rfl
  | succ d ih =>
    by_cases hlt : i < 2 ^ d
    · rw [treePath_succ_lt d leaves i hlt, treeRoot_succ]
      unfold merkleRoot
      rw [List.foldl_append]
      have hget : (leaves.take (2 ^ d)).getD i emptyLeaf = leaves.getD i emptyLeaf :=
        List.getD_take_of_lt leaves i (2 ^ d) hlt emptyLeaf
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
      have hget : (leaves.drop (2 ^ d)).getD (i - 2 ^ d) emptyLeaf = leaves.getD i emptyLeaf := by
        rw [List.getD_drop_eq]
        congr 1
        omega
      rw [← hget]
      have hind := ih (leaves.drop (2 ^ d)) (i - 2 ^ d) hi2
      unfold merkleRoot at hind
      rw [hind]
      rfl

/-- `treePath_correct` for a leaf that exists: if position `i` of `leaves` holds `leaf`,
    the path from `leaf` reconstructs the tree's root. The form that a pool theorem
    states, with no default value (audit finding P-8). -/
theorem treePath_correct_of_getElem? (d : Nat) (leaves : List Term) (i : Nat)
    (hi : i < 2 ^ d) {leaf : Term} (hleaf : leaves[i]? = some leaf) :
    merkleRoot leaf (treePath d leaves i) = treeRoot d leaves := by
  have hget : leaves.getD i emptyLeaf = leaf := by
    rw [List.getD_eq_getElem?_getD, hleaf, Option.getD_some]
  rw [← hget]
  exact treePath_correct d leaves i hi

/-- A `treePath` at depth `d` always has exactly `d` entries — one `(sibling, bit)`
    pair per level, matching `MerkleProof.len`'s `= 16` requirement in
    `Constrained.merkle`/`OwnedConstrained.merkle` once `d = TreeDepth`. -/
theorem treePath_length (d : Nat) (leaves : List Term) (i : Nat) :
    (treePath d leaves i).length = d := by
  induction d generalizing leaves i with
  | zero => rfl
  | succ d ih =>
    by_cases hlt : i < 2 ^ d
    · rw [treePath_succ_lt d leaves i hlt]
      (simp? [ih] says simp only [List.length_append, ih, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff])
    · rw [treePath_succ_ge d leaves i hlt]
      (simp? [ih] says simp only [List.length_append, ih, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff])

/-- `bitsVal` of a bit list with one more bit at the top: the new bit weighs
    `2 ^ bs.length`. -/
theorem bitsVal_append_single (bs : List Bool) (b : Bool) :
    bitsVal (bs ++ [b]) = bitsVal bs + b.toNat * 2 ^ bs.length := by
  induction bs with
  | nil => simp only [List.nil_append, bitsVal, List.length_nil, Nat.pow_zero, Nat.mul_one,
      Nat.zero_add, Nat.mul_zero, Nat.add_zero]
  | cons c bs ih =>
    simp only [List.cons_append, bitsVal, ih, List.length_cons, Nat.pow_succ]
    have h2 : b.toNat * (2 ^ bs.length * 2) = 2 * (b.toNat * 2 ^ bs.length) := by
      rw [Nat.mul_comm (2 ^ bs.length) 2, ← Nat.mul_assoc, Nat.mul_comm b.toNat 2, Nat.mul_assoc]
    omega

/-- The direction bits of `treePath d leaves i` are the `d` bits of `i`, LSB first: the
    path `treePath` computes is the one the circuit's `Num2Bits(d)` on the leaf index
    selects (`MerkleProof.bits`). For an in-range position, `bitsVal` of the bits is `i`. -/
theorem treePath_bitsVal (d : Nat) (leaves : List Term) (i : Nat) (hi : i < 2 ^ d) :
    bitsVal ((treePath d leaves i).map Prod.snd) = i := by
  induction d generalizing leaves i with
  | zero =>
    simp only [Nat.pow_zero] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rfl
  | succ d ih =>
    by_cases hlt : i < 2 ^ d
    · rw [treePath_succ_lt d leaves i hlt, List.map_append, List.map_cons, List.map_nil,
        bitsVal_append_single, ih (leaves.take (2 ^ d)) i hlt]
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
    · have hi2 : i - 2 ^ d < 2 ^ d := by
        simp only [Nat.pow_succ] at hi
        omega
      rw [treePath_succ_ge d leaves i hlt, List.map_append, List.map_cons, List.map_nil,
        bitsVal_append_single, ih (leaves.drop (2 ^ d)) (i - 2 ^ d) hi2, List.length_map,
        treePath_length]
      simp only [Bool.toNat_true, Nat.one_mul]
      omega

/-- `treePath` is a `MerkleProof`: the path from a leaf that exists at position `i` has
    `d` levels, carries the bits of `i`, and reconstructs the tree's root. The one
    constructor every pool witness uses (`PoolSafety.owned_spend_witness_exists`, the
    fixtures of `PoolNonVacuity`). -/
theorem treePath_merkleProof (d : Nat) (leaves : List Term) (i : Nat)
    (hi : i < 2 ^ d) {leaf : Term} (hleaf : leaves[i]? = some leaf) :
    MerkleProof d leaf (treePath d leaves i) i (treeRoot d leaves) where
  len := treePath_length d leaves i
  bits := treePath_bitsVal d leaves i hi
  root_eq := treePath_correct_of_getElem? d leaves i hi hleaf

/-- **Opening soundness.** A `MerkleProof` against the root of the tree over `leaves`
    opens the leaf that `leaves` holds at its index (`emptyLeaf` past the end). The
    proof's direction bits are the bits of the index (`MerkleProof.bits`), so they equal
    the bits of `treePath` (`treePath_bitsVal`, `bitsVal_inj`), and `merkleRoot_inj_bits`
    then forces the leaf. This is the fact a contract relies on when it checks a root
    against its history: the proof names a leaf of that tree. -/
theorem MerkleProof.opens_treeRoot {d : Nat} {leaf : Term} {path : List (Term × Bool)}
    {i : Nat} {leaves : List Term} (h : MerkleProof d leaf path i (treeRoot d leaves)) :
    leaves.getD i emptyLeaf = leaf := by
  have hi : i < 2 ^ d := h.index_lt
  have hbits : path.map Prod.snd = (treePath d leaves i).map Prod.snd := by
    apply bitsVal_inj
    · rw [List.length_map, List.length_map, h.len, treePath_length]
    · rw [h.bits, treePath_bitsVal d leaves i hi]
  have hroot : merkleRoot leaf path =
      merkleRoot (leaves.getD i emptyLeaf) (treePath d leaves i) := by
    rw [h.root_eq, treePath_correct d leaves i hi]
  exact (merkleRoot_inj_bits path (treePath d leaves i)
    (by rw [h.len, treePath_length]) hbits hroot).symm

end ArmadaLean
