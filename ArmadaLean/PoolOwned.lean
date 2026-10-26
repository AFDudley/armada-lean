/-
  ArmadaLean.PoolOwned — the pool contract's owned path and its storage.

  Models `TransactModule.transactOwned` (armada-poc
  contracts/privacy-pool/modules/TransactModule.sol:488-519) and the state it
  reads and writes: `PrivacyPoolStorage.nullifiers` (:174), `PrivacyPoolStorage
  .preimageOf` (:248), and `PrivacyPool.verifyOwned` (PrivacyPool.sol:562-601).
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
    (`_accumulateAndNullify`, TransactModule.sol:379-386).
  * `preimageOf_consistent` — every preimage the pool records hashes to the
    commitment it is recorded for (`_recordPreimages`, TransactModule.sol
    :590-604, gated by `_validatePublicOutputs`, :550-578).
  * `owned_spend_can_happen` — an owned spend by the real owner, with an
    accepted proof, succeeds.

  DEPARTURE (decision 2 of labbook/2026-10-18-contract-owned-notes-and-zk-
  channel-apps.md, recorded as open in its §3a): the design called for a
  public `balance[owner]` registry. The merged code never builds one;
  `preimageOf` (below) is what actually gives a caller the data decision 2
  wanted — one entry per commitment, not a running balance. `preimageOf_
  consistent` is the guarantee that entry is trustworthy.

  ### Address terms (operator ruling)

  An EVM contract address is itself a hash output: the low 160 bits of
  `keccak256` of the creator's address and a nonce (`CREATE`), or of the
  creator, a salt and the init-code hash (`CREATE2`) — not a raw number a
  contract independently "has". `Term.keccak` (`ArmadaLean.Poseidon`) is the
  model's Keccak primitive; this project represents an address as `Term.keccak
  inputs` directly, for whatever `inputs` its real derivation uses, with no
  separate wrapper constructor. Two reasons: first, the ONLY place this project
  needs Keccak at all is address derivation — there is no second Keccak-tagged
  term category a wrapper would need to distinguish addresses FROM; second, the
  property every theorem here actually needs — an address can never equal a
  Poseidon output — already follows from the function TAG alone
  (`Term.poseidon_ne_keccak`), so a further wrapper buys no additional
  separation. If a later model needs a second Keccak-derived term family (a
  storage slot, say), that is the point to introduce a narrower constructor;
  nothing here depends on `Term.keccak`'s output being exclusively addresses.
  The model does not track WHICH concrete `inputs` produced a given address (no
  theorem below needs to recompute one from a creator and a nonce) — only that
  it is Keccak-shaped, i.e. of the form `Term.keccak _` for SOME argument list,
  which is what `user_npk_ne_contract_npk` (`ArmadaLean.TransactOwned`) and
  every theorem below that touches `ownerField` are stated against.

  `TransactOwnedPublic.ownerField`, `OwnedOpening.ownerField`, `Token.address`, and every
  `caller`/owning-party value in this file and `ArmadaLean.Pool` /
  `ArmadaLean.PoolSafety` are address terms accordingly — `Term`, never `Nat`.
  `addressOf` (EVM's `address(uint160(x))` truncation) is deleted along with
  every `% 2 ^ 160` bound: a `Term` has no numeric interpretation to truncate.
  See `ArmadaLean.TransactOwned`'s module comment for the resulting
  authorization-check departure (the real contract's truncating comparison
  accepts a broader set of `ownerField` values than this model's plain term
  equality does).
-/
import ArmadaLean.TransactOwned

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

/- An output that stays ciphertext-only has no disclosed preimage. The contract encodes
   "no preimage" as an all-zero `publicOutputs` entry (`_isZeroPreimage`,
   TransactModule.sol:582-585). This model has no such sentinel: a disclosure is a list
   of the outputs that are disclosed (`ArmadaLean.Pool.Step.transact`, `records`), and
   the owned path discloses every output. Audit finding P-4 records the removal of the
   earlier `isZeroPreimage`. -/

/-! ### `verifyOwned` acceptance (PrivacyPool.sol:562-601)

Soundness — "an accepted proof's witness satisfies `OwnedConstrained`" — is
the hypothesis every theorem below already takes directly as
`OwnedConstrained w pub`, exactly as `ArmadaLean.Transact` takes `Constrained
w pub`. The reverse direction, completeness, is a separate assumption used
only by `owned_spend_can_happen`. -/

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
ever pass this check once, in the one call that first spends it. -/
theorem owned_no_double_spend {spent spent' : NullifierSet} {ns : List Term}
    (h : markSpent spent ns = some spent') :
    ns.Pairwise (· ≠ ·) ∧ ∀ n ∈ ns, n ∉ spent := by
  induction ns generalizing spent with
  | nil => exact ⟨List.Pairwise.nil, fun n hn => absurd hn List.not_mem_nil⟩
  | cons n ns ih =>
    unfold markSpent at h
    by_cases hn : n ∈ spent
    · rw [if_pos hn] at h
      exact absurd h (by simp)
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
    (fun _ _ h => by simp at h)

/-! ### The published opening of a contract-owned note

A contract-owned note has `npk = Poseidon(ownerField, random)`
(TransactOwned.circom:66-70). The merged contract records only `npk`, `token` and
`value` (`preimageOf`, `PoolTypes.sol:79-83`). Without `random`, only the creator of the
note can build the proof that spends it. Armada decision 11 (labbook
`2026-10-18-contract-owned-notes-and-zk-channel-apps.md`) fixes this: the creator
publishes the opening in the creating transaction, inside `adaptParams`, and the
adjudicator checks it against the proof's output commitment. An off-chain indexer
extracts it. The pool keeps no storage for it.

This model puts the opening in the step's public data (`ArmadaLean.Pool.Step.transact`
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
succeeds. `ownerField`, `token`, `randomIn`, `valueIn`, `leavesIndices`,
`pathElements`, `npkOut`, `valueOut` are the real owner's own data — the
witness for `N` notes it genuinely holds at Merkle root `root`, re-minted
into `M` fresh outputs of equal total value. `boundParamsHash` is the hash of the
transaction's bound parameters (`ArmadaLean.BoundParams.hashBoundParams`).
`owned_spend_can_happen` clears every pool-level gate this model covers: the circuit
constraints hold (`OwnedConstrained`, by construction), `verifyOwned` accepts
(`hComplete.complete`, the one completeness assumption), the caller is
authorized (`hCaller`), every output's preimage hashes to its commitment so
`_validatePublicOutputs(requireAll = true)` (TransactModule.sol:630-634)
passes, and the nullifiers are fresh so `_accumulateAndNullify` does not
revert (`markSpent_succeeds`, using `distinct_leaves_distinct_nullifiers`
from ArmadaLean.Nullifier to turn the owner's genuinely-distinct note
positions into pairwise-distinct nullifiers). -/
theorem owned_spend_can_happen {N M : Nat} (hComplete : OwnedProofCompleteness)
    (ownerField : Term) (token : Token) (boundParamsHash : Term) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool))
    (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot (commitment (npk ownerField (randomIn i)) token (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (spent : NullifierSet) (hFresh : ∀ i, nullifier ownerField (leavesIndices i) ∉ spent)
    (caller : Term) (hCaller : caller = ownerField) :
    ∃ (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M),
      OwnedConstrained w pub ∧
      VerifyOwnedAccepts pub ∧
      pub.boundParamsHash = boundParamsHash ∧
      caller = pub.ownerField ∧
      (∀ j, hashCommitment ⟨npkOut j, token, valueOut j⟩ = pub.commitmentsOut j) ∧
      ∃ spent', markSpent spent (List.ofFn pub.nullifiers) = some spent' := by
  sorry
