/-
  The owned path is an open pull request, not yet merged into `main`:
  ship-armada/armada-poc#653 ("Add the contract-owned spend path
  (transactOwned, verifyOwned)", head commit
  `ac99ca1c44eb80cbd258bec1064fe078416cc36e`). `transactOwned`, `verifyOwned`,
  `ownerField` and the public preimage registry (`preimageOf`) do not exist on
  `main` (`contracts/privacy-pool/modules/TransactModule.sol` is 498 lines
  there), only on that PR branch. This module models the PR branch directly:
  every `TransactModule.sol:N` citation below with `N` past line 498, and
  every `PrivacyPoolStorage.sol:N` citation with `N` past line 236, names a
  line on PR #653's branch, not on `main`.
-/

/-
  ArmadaLean.PoolOwned — the pool contract's owned path and its storage.

  Models the design of `TransactModule.transactOwned` (PR #653,
  TransactModule.sol:513-544) and the state it reads and writes:
  `PrivacyPoolStorage.nullifiers` (:174, on `main`), `PrivacyPoolStorage.preimageOf`
  (:261, PR #653 only), and `PrivacyPool.verifyOwned` (PrivacyPool.sol:588-624,
  PR #653 only).
  Imports `ArmadaLean.TransactOwned` and builds on `OwnedConstrained` — "the
  accepted proof's witness satisfies every circuit constraint" is the named
  hypothesis every theorem below takes (the brief's soundness assumption:
  Poseidon cannot be inverted or collided — modeled symbolically,
  `ArmadaLean.Poseidon` — and an accepted proof means its circuit constraints
  hold). Only `owned_spend_can_happen` additionally takes an explicit
  `OwnedProofCompleteness` hypothesis, the converse assumption.

  Theorems proved here:
  * `owned_owner_binding` — no one except the owning contract can spend its
    note (TransactModule.sol:636-639, `ownerField == msg.sender`).
  * `owned_no_double_spend` — no note is spent twice
    (`_accumulateAndNullify`, TransactModule.sol:385-411 on `main`; the owned
    path reuses this mechanism, PR #653).
  * `preimageOf_consistent` — every preimage the pool records hashes to the
    commitment it is recorded for (`_recordPreimages`, TransactModule.sol
    :619-630, gated by `_validatePublicOutputs`, :578-606).
  DEPARTURE: an earlier design called for a public `balance[owner]` registry.
  The merged code never builds one; `preimageOf` (below) is what actually
  gives a caller the data that design wanted — one entry per commitment, not
  a running balance. `preimageOf_consistent` is the guarantee that entry is
  trustworthy.

  ### Address terms

  The owned path's `ownerField` is a 160-bit address.
  `TransactOwnedPublic.owner : Address` (`ArmadaLean.Types.Address`) is a number below
  `2^160`, and `TransactOwnedPublic.ownerField` is its field element `Term.val owner`
  (`ownerField = uint256(uint160(owner))`, TransactOwned.circom:13-14). So `ownerField`
  is never a hash term (`Address.val_ne_hash`): a contract's note key
  `npk ownerField r` never equals a user's note key `npk (masterPublicKey pk nk) r'`
  (`user_npk_ne_contract_npk`, `ArmadaLean.TransactOwned`). The model does not track
  how the address was derived (`CREATE`, `CREATE2`): no theorem below needs to
  recompute one from a creator and a nonce.

  Every other address value stays a plain `Term`: `OwnedOpening.ownerField`,
  `Token.address`, and every `caller`/fee-admin/treasury value in this file and
  `ArmadaLean.Pool` / `ArmadaLean.PoolSafety`. A caller of an owned spend equals
  `pub.ownerField` (`hCaller` of `Step.transactOwned`), so it is a `Term.val` of an
  address. An earlier version of this model represented every address as a
  Keccak hash term `Term.keccak inputs` and rested the
  user/contract note-key separation on the hash-function tag. `Term.keccak` stays in
  use for the bound-parameters hash (`ArmadaLean.BoundParams`) and for the fee-admin
  and treasury terms of the fixtures. `addressOf` (EVM's `address(uint160(x))`
  truncation) and every `% 2 ^ 160` bound on a `Term` are deleted: a `Term` has no
  numeric interpretation to truncate. The bound lives in `Address` alone. See
  `ArmadaLean.TransactOwned`'s module comment for the authorization-check departure
  (the current contract's truncating comparison accepts a broader set of `ownerField`
  values than this model's plain term equality does; the rewrite rejects them).
-/
import ArmadaLean.TransactOwned
import Mathlib.Tactic.Says

namespace ArmadaLean

/-- The data committed into a Merkle leaf (`PoolTypes.sol:79-83`, `struct
    CommitmentPreimage`). `npk` is a term (a note public key); `token` is a symbolic
    `Token` (`ArmadaLean.Token`), the same as `TransactOwnedWitness.token`; `value` is
    the note value, a number. -/
structure CommitmentPreimage where
  npk : Term
  token : Token
  value : Nat
  deriving DecidableEq

/-- `_hashCommitment` (TransactModule.sol:441-443, ShieldModule.sol:376-378):
    `PoseidonT4.poseidon([npk, tokenID, value])`, the same 3-argument
    Poseidon as `commitment` in ArmadaLean.Transact — reused directly, no
    second commitment hash is defined here. -/
def hashCommitment (pre : CommitmentPreimage) : Term := commitment pre.npk pre.token pre.value

/-- The empty leaf is no note's commitment: `emptyLeaf` is a `Term.val` (the contract's
    `ZERO_VALUE`, `ArmadaLean.Merkle`) and a commitment is a Poseidon hash term
    (`Term.hash3`), so the two never agree, by constructor disjointness
    (`emptyLeaf_ne_hash`). A Merkle opening of a padding slot therefore opens no note. -/
theorem emptyLeaf_ne_hashCommitment (pre : CommitmentPreimage) :
    emptyLeaf ≠ hashCommitment pre :=
  emptyLeaf_ne_hash .poseidon _

/- An output that stays ciphertext-only has no disclosed preimage. The contract encodes
   "no preimage" as an all-zero `publicOutputs` entry (`_isZeroPreimage`,
   TransactModule.sol:582-585). This model has no such sentinel: a disclosure is a list
   of the outputs that are disclosed (`ArmadaLean.Step.transact`, `records`), and
   the owned path discloses every output. Audit finding P-4 records the removal of the
   earlier `isZeroPreimage`. -/

/-! ### `verifyOwned` acceptance (PrivacyPool.sol:562-601)

Soundness — "an accepted proof's witness satisfies `OwnedConstrained`" — is
the hypothesis every theorem below takes directly as `OwnedConstrained w
pub`, exactly as `ArmadaLean.Transact` takes `Constrained w pub`. Rule PE5
(`docs/pool-executable.md`, `Pool.apply_backward_refinement`) takes
soundness as the structure `OwnedProofSoundness` instead. The reverse
direction, completeness, is a separate assumption used only by
`owned_spend_can_happen`. -/

/-- `VerifyOwnedAccepts pub` holds iff some Groth16 proof over `pub`'s public
    inputs makes `PrivacyPool.verifyOwned` return `true`
    (PrivacyPool.sol:562-601). Left abstract: this model does not represent
    Groth16 proof objects, the same way `EdDSAVerify` is left abstract in
    ArmadaLean.Transact. -/
axiom VerifyOwnedAccepts : {N M : Nat} → TransactOwnedPublic N M → Prop

/--
Groth16 completeness, named as an explicit hypothesis rather than a global
axiom: for a witness/public pair that together satisfy every TransactOwned
.circom constraint (`OwnedConstrained`), a prover can build a proof that
`PrivacyPool.verifyOwned` accepts. This is the converse of soundness: the
owned verifying-key set never rejects a real satisfying witness.
`owned_spend_can_happen` takes one instance of this record as an explicit
argument, so the assumption is visible at its call site and nowhere else —
no other theorem in this file can reach for it. -/
structure OwnedProofCompleteness where
  complete : ∀ {N M : Nat} {w : TransactOwnedWitness N M} {pub : TransactOwnedPublic N M},
    OwnedConstrained w pub → VerifyOwnedAccepts pub

/--
Groth16 knowledge soundness over the deployed verifying key, named as an
explicit hypothesis rather than a global axiom: every public input that
`PrivacyPool.verifyOwned` accepts has a witness that satisfies every
TransactOwned.circom constraint (`OwnedConstrained`). This is the
trusted-verifier assumption: the proof system itself is sound, so an
accepted proof always has a satisfying witness.
It is the converse of `OwnedProofCompleteness`. `Pool.apply_backward_refinement`
(rule PE5) takes one instance of this record as an explicit argument, so
the assumption is visible at its call site and nowhere else. -/
structure OwnedProofSoundness where
  sound : ∀ {N M : Nat} {pub : TransactOwnedPublic N M},
    VerifyOwnedAccepts pub → ∃ w : TransactOwnedWitness N M, OwnedConstrained w pub

/-! ### Owner binding (TransactModule.sol:636-639) -/

/--
**Owner binding**: no one except the owning contract can spend its note.

Take a note truly created for owner `trueOwner` with randomness
`trueRandom` (its commitment is `commitment (npk trueOwner trueRandom) token
value`, by construction — ArmadaLean.TransactOwned's `outputs` field, read at
the transaction that minted it). If an accepted owned spend's input `i`
opens the same commitment value (`hSameNote`), `commitment_owner_inj` forces
its `ownerField` to equal `trueOwner`; the pool's own authorization check
(`ownerField == msg.sender`, TransactModule.sol:636-639, `hAuth` — the
canonical, untruncated form this model represents, see `ArmadaLean
.TransactOwned`'s module comment on the truncation departure) then forces
the caller to be `trueOwner` itself. A caller that is not the owning
contract can never satisfy both, so it can never produce an accepted spend
of that note. -/
theorem owned_owner_binding {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (_h : OwnedConstrained w pub) (i : Fin N)
    {trueOwner : Term} {trueRandom : Nat}
    (hSameNote :
      commitment (npk pub.ownerField (w.randomIn i)) w.token (w.valueIn i) =
      commitment (npk trueOwner trueRandom) w.token (w.valueIn i))
    {caller : Term} (hAuth : caller = pub.ownerField) :
    caller = trueOwner := by
  rw [hAuth, commitment_owner_inj hSameNote]

/-! ### No double spend (`_accumulateAndNullify`, TransactModule.sol:379-386) -/

/-- The pool's spent-nullifier set for one Merkle tree
    (`PrivacyPoolStorage.sol:174`, `mapping(uint256 => mapping(bytes32 =>
    bool)) public nullifiers`, one tree's slice). `treeNumber` is a further
    key of the real mapping that this model elides: the freshness/
    distinctness argument below holds the same way inside any one tree.
    Nullifiers are terms. -/
abbrev NullifierSet := List Term

/-- Marking one call's nullifiers spent (`_accumulateAndNullify`,
    TransactModule.sol:379-386): each nullifier must not already be in
    `spent`; the pool reverts the whole call (`"Note already spent"`, :384)
    the first time one already is, returning `none` here. -/
def markSpent (spent : NullifierSet) : List Term → Option NullifierSet
  | [] => some spent
  | n :: ns => if n ∈ spent then none else markSpent (n :: spent) ns

/--
**No note is spent twice.** If a call's nullifier-marking succeeds
(`markSpent spent ns = some _`, i.e. the pool did not revert), the
nullifiers `ns` it just marked are pairwise distinct from each other and
none of them was already in `spent` beforehand. Applied to a whole history
of calls (each one's `spent` is the previous call's `spent'`), this is
exactly "no nullifier is ever marked twice": a note's nullifier can only
ever pass this check once, in the one call that first spends it.
Source: TransactModule.sol:379-386. -/
theorem owned_no_double_spend {spent spent' : NullifierSet} {ns : List Term}
    (h : markSpent spent ns = some spent') :
    ns.Pairwise (· ≠ ·) ∧ ∀ n ∈ ns, n ∉ spent := by
  induction ns generalizing spent with
  | nil => exact ⟨List.Pairwise.nil, fun n hn => absurd hn List.not_mem_nil⟩
  | cons n ns ih =>
    unfold markSpent at h
    by_cases hn : n ∈ spent
    · rw [if_pos hn] at h
      exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
    · rw [if_neg hn] at h
      obtain ⟨hpw, hfresh⟩ := ih h
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
      · intro a ha heq
        exact hfresh a ha (List.mem_cons.mpr (Or.inl heq.symm))
      · intro m hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact hm ▸ hn
        · exact fun hmspent => hfresh m hm (List.mem_cons_of_mem n hmspent)

/-- Converse of `owned_no_double_spend`, used by `owned_spend_can_happen`: a
    batch of pairwise-distinct, previously-unspent nullifiers always marks
    cleanly (the pool never reverts `_accumulateAndNullify` on a genuinely
    fresh batch). -/
theorem markSpent_succeeds {spent : NullifierSet} {ns : List Term}
    (hpw : ns.Pairwise (· ≠ ·)) (hfresh : ∀ n ∈ ns, n ∉ spent) :
    ∃ spent', markSpent spent ns = some spent' := by
  induction ns generalizing spent with
  | nil => exact ⟨spent, rfl⟩
  | cons n ns ih =>
    obtain ⟨ha, hpw'⟩ := List.pairwise_cons.mp hpw
    have hn : n ∉ spent := hfresh n List.mem_cons_self
    have hfresh' : ∀ m ∈ ns, m ∉ (n :: spent) := by
      intro m hm hmem
      rcases List.mem_cons.mp hmem with hmem | hmem
      · exact ha m hm hmem.symm
      · exact hfresh m (List.mem_cons_of_mem n hm) hmem
    obtain ⟨spent', hspent'⟩ := ih hpw' hfresh'
    refine ⟨spent', ?_⟩
    unfold markSpent
    rw [if_neg hn]
    exact hspent'

/-! ### Preimage consistency (`_recordPreimages`, TransactModule.sol:590-604) -/

/-- The pool's preimage registry (`PrivacyPoolStorage.sol:248`, `mapping
    (bytes32 => CommitmentPreimage) public preimageOf`): `none` means no
    preimage was ever recorded for that commitment. Keyed by commitment term. -/
abbrev PreimageRegistry := Term → Option CommitmentPreimage

/-- The registry invariant: every recorded preimage hashes to the
    commitment key it is recorded under. -/
def RegistryConsistent (reg : PreimageRegistry) : Prop :=
  ∀ c pre, reg c = some pre → hashCommitment pre = c

/-- Recording one disclosed output (TransactModule.sol:593-599): the registry entry
    at `c` becomes `preimage` (:598). The contract skips an all-zero entry (:594-596);
    this model passes only disclosed outputs (module comment on finding P-4). -/
def recordStep (reg : PreimageRegistry) (c : Term) (preimage : CommitmentPreimage) :
    PreimageRegistry :=
  fun c' => if c' = c then some preimage else reg c'

/-- Recording every output of one transaction (`_recordPreimages`'s loop,
    TransactModule.sol:590-604), `commitments` and `publicOutputs` running
    in parallel, index for index. -/
def recordPreimages {K : Nat} (commitments : Fin K → Term)
    (publicOutputs : Fin K → CommitmentPreimage) (reg : PreimageRegistry) : PreimageRegistry :=
  (List.finRange K).foldl (fun r i => recordStep r (commitments i) (publicOutputs i)) reg

/-- A property preserved by every step of a left fold is preserved by the
    whole fold. -/
theorem foldl_preserves {α β : Type} (f : α → β → α) (P : α → Prop)
    (hstep : ∀ a b, P a → P (f a b)) : ∀ (l : List β) (a : α), P a → P (l.foldl f a)
  | [], _, ha => ha
  | b :: bs, a, ha => foldl_preserves f P hstep bs (f a b) (hstep a b ha)

theorem recordStep_preserves_consistency {reg : PreimageRegistry} (hreg : RegistryConsistent reg)
    {c : Term} {preimage : CommitmentPreimage} (hvalid : hashCommitment preimage = c) :
    RegistryConsistent (recordStep reg c preimage) := by
  intro c' pre' hc'
  unfold recordStep at hc'
  by_cases heq : c' = c
  · rw [if_pos heq] at hc'
    cases hc'
    rw [heq]
    exact hvalid
  · rw [if_neg heq] at hc'
    exact hreg c' pre' hc'

theorem recordPreimages_preserves_consistency {K : Nat} (commitments : Fin K → Term)
    (publicOutputs : Fin K → CommitmentPreimage)
    (hvalid : ∀ i, hashCommitment (publicOutputs i) = commitments i)
    {reg : PreimageRegistry} (hreg : RegistryConsistent reg) :
    RegistryConsistent (recordPreimages commitments publicOutputs reg) := by
  unfold recordPreimages
  exact foldl_preserves (fun r i => recordStep r (commitments i) (publicOutputs i)) RegistryConsistent
    (fun r i hr => recordStep_preserves_consistency hr (hvalid i)) (List.finRange K) reg hreg

/--
**Preimage consistency**: every preimage the pool records hashes to the
commitment it is recorded for. `_validatePublicOutputs` (TransactModule.sol
:550-578) requires `hashCommitment (publicOutputs i) = commitments i` for
every non-zero entry *before* `_recordPreimages` (:590-604) ever runs
(`transactOwned`, :500-506); starting from the empty registry (deployment)
and folding every transaction ever processed through `recordPreimages`
preserves that one fact by induction, so it holds of the live `preimageOf`
mapping at every block. -/
theorem preimageOf_consistent {K : Nat} (commitments : Fin K → Term)
    (publicOutputs : Fin K → CommitmentPreimage)
    (hvalid : ∀ i, hashCommitment (publicOutputs i) = commitments i) :
    RegistryConsistent (recordPreimages commitments publicOutputs (fun _ => none)) :=
  recordPreimages_preserves_consistency commitments publicOutputs hvalid
    (fun _ _ h => by (simp? at h says simp only [reduceCtorEq] at h))

/-! ### The published opening of a contract-owned note

A contract-owned note has `npk = Poseidon(ownerField, random)`
(TransactOwned.circom:66-70). The merged contract records only `npk`, `token` and
`value` (`preimageOf`, `PoolTypes.sol:79-83`). Without `random`, only the creator of the
note can build the proof that spends it. The design fixes this: the creator
publishes the opening in the creating transaction, inside `adaptParams`, and the
adjudicator checks it against the proof's output commitment. An off-chain indexer
extracts it. The pool keeps no storage for it.

This model puts the opening in the step's public data (`ArmadaLean.Step.transact`
and `.transactOwned`, argument `openings`). The ghost record `PoolState.published`
keeps every opening that a step carried. The pool does not check an opening; a reader
checks it against the note's `npk` (`ArmadaLean.PoolSafety.owned_spend_witness_exists`).
Audit finding P-10 records the removal of the earlier storage map `ownedRandomOf`. -/

/-- The opening of a contract-owned note: the owner address and the note's random.
    `npk ownerField random` is the note's public key when the opening is correct. -/
structure OwnedOpening where
  ownerField : Term
  random : Nat
  deriving DecidableEq

/-! ### Can happen (proof completeness) -/

/--
**Can happen**: an owned spend by the real owner, with an accepted proof,
succeeds. `owner`, `token`, `randomIn`, `valueIn`, `leavesIndices`,
`pathElements`, `npkOut`, `valueOut` are the real owner's own data — the
witness for `N` notes it genuinely holds at Merkle root `root`, re-minted
into `M` fresh outputs of equal total value. `boundParamsHash` is the hash of the
transaction's bound parameters (`ArmadaLean.BoundParams.hashBoundParams`).
`owned_spend_can_happen` clears every pool-level gate this model covers: the circuit
constraints hold (`OwnedConstrained`, by construction), `verifyOwned` accepts
(`hComplete.complete`, the one completeness assumption), the caller
`Term.val owner` is the owner (the authorization check, `owned_owner_binding`), every
output's preimage hashes to its commitment so
`_validatePublicOutputs(requireAll = true)` (TransactModule.sol:630-634)
passes, and the nullifiers are fresh so `_accumulateAndNullify` does not
revert (`markSpent_succeeds`, using `distinct_leaves_distinct_nullifiers`
from ArmadaLean.Nullifier to turn the owner's genuinely-distinct note
positions into pairwise-distinct nullifiers). -/
theorem owned_spend_can_happen {N M : Nat} (hComplete : OwnedProofCompleteness)
    (owner : Address) (token : Token) (boundParamsHash : Term) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool))
    (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hMerkle : ∀ i,
      MerkleProof 16 (commitment (npk (Term.val owner) (randomIn i)) token (valueIn i))
        (pathElements i) (leavesIndices i) root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (spent : NullifierSet) (hFresh : ∀ i, nullifier (Term.val owner) (leavesIndices i) ∉ spent) :
    ∃ (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M),
      OwnedConstrained w pub ∧
      VerifyOwnedAccepts pub ∧
      pub.boundParamsHash = boundParamsHash ∧
      Term.val owner = pub.ownerField ∧
      (∀ j, hashCommitment ⟨npkOut j, token, valueOut j⟩ = pub.commitmentsOut j) ∧
    ∃ spent', markSpent spent (List.ofFn pub.nullifiers) = some spent' := by
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier (Term.val owner) (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      owner := owner }
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  have hConstrained : OwnedConstrained w pub :=
    { merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance }
  obtain ⟨spent', hNullify⟩ :
      ∃ spent', markSpent spent (List.ofFn pub.nullifiers) = some spent' := by
    apply markSpent_succeeds
    · have hmap := distinct_leaves_distinct_nullifiers (Term.val owner)
        (List.ofFn leavesIndices) hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier (Term.val owner))
          = List.ofFn pub.nullifiers := List.map_ofFn
      rwa [heq] at hmap
    · intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i
  exact ⟨w, pub, hConstrained, hComplete.complete hConstrained, rfl, rfl,
    fun _ => rfl, spent', hNullify⟩

end ArmadaLean
