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
