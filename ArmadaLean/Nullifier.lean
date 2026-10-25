/-
  ArmadaLean.Nullifier — nullifier derivation and double-spend resistance.

  Mirrors Transact.circom:97-101 (nullifier = Poseidon(nullifyingKey, leafIndex))
  and the input-distinctness block at Transact.circom:145-161, which constrains
  every pair of leaf indices to be different (`IsEqual(...).out === 0`).

  The theorem formalizes the SECURITY_REVIEW.md Finding 2 fix: because the leaf
  indices are pairwise distinct and Poseidon(2,·) is collision resistant, the
  published nullifiers are pairwise distinct — the same note cannot be spent
  twice within one transaction. `nullifier`'s output and `Term.hash2`'s
  collision resistance are symbolic (`ArmadaLean.Poseidon`, Dolev-Yao style): the
  nullifying key `nk` and leaf index `leafIdx` are raw values an attacker/prover
  chose (`Term.val`), and the nullifier is the symbolic hash of the pair.
-/
import ArmadaLean.Poseidon

/-- The nullifier of a note at Merkle leaf index `leafIdx` spent under
    nullifying key `nk` (Transact.circom:97-101). `nk`/`leafIdx` are raw values
    (a secret key or address, and a tree position), embedded as `Term.val` before
    hashing. -/
def nullifier (nk leafIdx : Nat) : Term := Term.hash2 (Term.val nk) (Term.val leafIdx)

/--
**Distinct leaves give distinct nullifiers** (SECURITY_REVIEW.md Finding 2 fix).

The circuit's pairwise `IsEqual`-out-`===0` checks (Transact.circom:145-161)
force all input leaf indices to differ; collision resistance of `Term.hash2`
(by construction, `ArmadaLean.Poseidon`) then lifts that to the published
nullifiers, so a transaction cannot list the same note twice (which would count
its value twice toward `sumIn`). -/
theorem distinct_leaves_distinct_nullifiers (nk : Nat) (leaves : List Nat)
    (h : leaves.Pairwise (· ≠ ·)) :
    (leaves.map (nullifier nk)).Pairwise (· ≠ ·) := by
  rw [List.pairwise_map]
  refine h.imp fun {a b} hab hcon => hab ?_
  exact Term.val.inj (Term.hash2_inj hcon).2

/--
**Two different leaf positions never share a nullifier**, for a fixed nullifying
key/owner field: `nullifier`'s two raw arguments are embedded separately
(`Term.val nk`, `Term.val leafIdx`) before one `Term.hash2` call, so a nullifier
collision forces BOTH embedded arguments equal (`Term.hash2_inj`), not merely one.
This is the pool-level fact behind identifying a live note by its leaf position: no
two distinct positions a spend removes can ever collapse onto the one nullifier a
`markSpent` call marks. -/
theorem nullifier_pos_inj {nk a b : Nat} (h : nullifier nk a = nullifier nk b) : a = b :=
  Term.val.inj (Term.hash2_inj h).2
