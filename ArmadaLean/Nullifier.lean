/-
  ArmadaLean.Nullifier — nullifier derivation and double-spend resistance.

  Mirrors Transact.circom:97-101 (nullifier = Poseidon(nullifyingKey, leafIndex))
  and the input-distinctness block at Transact.circom:145-161, which constrains
  every pair of leaf indices to be different (`IsEqual(...).out === 0`).

  The theorem formalizes the SECURITY_REVIEW.md Finding 2 fix: because the leaf
  indices are pairwise distinct and Poseidon(2,·) is collision resistant, the
  published nullifiers are pairwise distinct — the same note cannot be spent
  twice within one transaction.
-/
import ArmadaLean.Poseidon

/-- The nullifier of a note at Merkle leaf index `leafIdx` spent under
    nullifying key `nk` (Transact.circom:97-101). -/
noncomputable def nullifier (nk leafIdx : Nat) : Nat := poseidon2 nk leafIdx

/--
**Distinct leaves give distinct nullifiers** (SECURITY_REVIEW.md Finding 2 fix).

The circuit's pairwise `IsEqual`-out-`===0` checks (Transact.circom:145-161)
force all input leaf indices to differ; injectivity of `poseidon2` then lifts
that to the published nullifiers, so a transaction cannot list the same note
twice (which would count its value twice toward `sumIn`). -/
theorem distinct_leaves_distinct_nullifiers (nk : Nat) (leaves : List Nat)
    (h : leaves.Pairwise (· ≠ ·)) :
    (leaves.map (nullifier nk)).Pairwise (· ≠ ·) := by
  rw [List.pairwise_map]
  exact h.imp fun {a b} hab hcon => hab (poseidon2_inj hcon).2
