/-
  ArmadaLean.Nullifier — nullifier derivation and double-spend resistance.

  Mirrors Transact.circom:97-101 (nullifier = Poseidon(nullifyingKey, leafIndex)) and
  TransactOwned.circom:89-97 (nullifier = Poseidon(ownerField, leafIndex)), and the
  input-distinctness block at Transact.circom:145-161, which constrains every pair of
  leaf indices to be different (`IsEqual(...).out === 0`).

  The theorem formalizes the SECURITY_REVIEW.md Finding 2 fix: because the leaf
  indices are pairwise distinct and Poseidon(2,·) is collision resistant, the
  published nullifiers are pairwise distinct — the same note cannot be spent
  twice within one transaction. `nullifier`'s output and `Term.hash2`'s
  collision resistance are symbolic (`ArmadaLean.Poseidon`, Dolev-Yao style): the
  nullifying key `nk` is already a term — a raw secret value an attacker/prover
  chose, embedded as `Term.val`, on the plain path (`Transact.circom:97-101`), or a
  contract address, itself a Keccak hash term, on the owned path
  (`TransactOwned.circom:89-97`, `ArmadaLean.PoolOwned`'s module comment on address
  terms) — and the leaf index `leafIdx` is a raw tree position, embedded as `Term.val`;
  the nullifier is the symbolic hash of the pair.
-/
import ArmadaLean.Poseidon

/-- The nullifier of a note at Merkle leaf index `leafIdx` spent under nullifying key
    `nk` (Transact.circom:97-101, TransactOwned.circom:89-97). `nk` is already a term
    — `Term.val` of a raw secret on the plain path, or a contract's address term on
    the owned path; `leafIdx` is a raw tree position, embedded as `Term.val` before
    hashing. -/
def nullifier (nk : Term) (leafIdx : Nat) : Term := Term.hash2 nk (Term.val leafIdx)

/--
**Distinct leaves give distinct nullifiers** (SECURITY_REVIEW.md Finding 2 fix).

The circuit's pairwise `IsEqual`-out-`===0` checks (Transact.circom:145-161)
force all input leaf indices to differ; collision resistance of `Term.hash2`
(by construction, `ArmadaLean.Poseidon`) then lifts that to the published
nullifiers, so a transaction cannot list the same note twice (which would count
its value twice toward `sumIn`). -/
theorem distinct_leaves_distinct_nullifiers (nk : Term) (leaves : List Nat)
    (h : leaves.Pairwise (· ≠ ·)) :
    (leaves.map (nullifier nk)).Pairwise (· ≠ ·) := by
  rw [List.pairwise_map]
  refine h.imp fun {a b} hab hcon => hab ?_
  exact Term.val.inj (Term.hash2_inj hcon).2

/--
**Two different leaf positions never share a nullifier**, for a fixed nullifying
key/owner field: `nullifier`'s two arguments are combined in one `Term.hash2` call,
so a nullifier collision forces BOTH arguments equal (`Term.hash2_inj`), not merely
one. This is the pool-level fact behind identifying a live note by its leaf position:
no two distinct positions a spend removes can ever collapse onto the one nullifier a
`markSpent` call marks. -/
theorem nullifier_pos_inj {nk : Term} {a b : Nat} (h : nullifier nk a = nullifier nk b) :
    a = b :=
  Term.val.inj (Term.hash2_inj h).2

/--
**A nullifier collision forces both the key and the position equal.** The full
injectivity `nullifier_pos_inj` only states for one fixed key: `Term.hash2_inj`
already gives both halves, this just surfaces the first one too (the
nullifying key, read back out of `Term.hash2`'s left argument). Used by
`ArmadaLean.PoolSafety.live_note_unspent`: a live position's nullifier, under
any key, cannot coincide with a different spend's nullifier unless that spend
named the exact same key and position. -/
theorem nullifier_inj {nk1 nk2 : Term} {a b : Nat}
    (h : nullifier nk1 a = nullifier nk2 b) : nk1 = nk2 ∧ a = b :=
  ⟨(Term.hash2_inj h).1, Term.val.inj (Term.hash2_inj h).2⟩
