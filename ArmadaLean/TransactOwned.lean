/-
  The owned circuit is an open pull request, not yet merged into `main`:
  ship-armada/armada-circuits#7 ("Add the owned Transact circuit
  (TransactOwned)", head commit
  `6d405abf97dd0eb73fb5a55f0064d701427e6498`). `TransactOwned.circom` does not
  exist on `main`, only on that PR branch. Every `TransactOwned.circom:N`
  citation below models that PR branch directly. `TransactModule.sol:N`
  citations with `N` past line 498 name the matching owned-path contract PR,
  ship-armada/armada-poc#653 (head commit
  `ac99ca1c44eb80cbd258bec1064fe078416cc36e`) — see `ArmadaLean.PoolOwned`'s
  header for that PR.
-/

/-
  ArmadaLean.TransactOwned — constraint model of the TransactOwned circuit.

  TransactOwned.circom (armada-circuits src/operations/TransactOwned.circom) is
  a Transact variant for a note owned by a contract instead of a user keypair
  (file doc comment, TransactOwned.circom:1-24). It reuses this project's
  `npk`, `commitment` (ArmadaLean.Transact), `nullifier` (ArmadaLean.Nullifier)
  and `merkleRoot` (ArmadaLean.Merkle) exactly as the circuit reuses the same
  Poseidon formulas: this module defines no second note, commitment or
  nullifier.

  What differs from Transact.circom (TransactOwned.circom:1-24):
  * `npk[i] = Poseidon(ownerField, randomIn[i])` (:66-70) replaces the
    master-public-key chain. `masterPublicKey` and `EdDSAVerify`
    (ArmadaLean.Transact) do not apply to this circuit.
  * `nullifier = Poseidon(ownerField, leafIndex)` (:89-97) replaces
    `Poseidon(nullifyingKey, leafIndex)` — the same `nullifier` function
    (ArmadaLean.Nullifier), with `ownerField` where Transact.circom carried a
    free `nullifyingKey`.
  * Authorization is `ownerField == msg.sender` (TransactModule.sol:637), checked
    by the pool (modeled in ArmadaLean.PoolOwned), not an EdDSA signature: this
    circuit carries no signature witness and proves no `sig` field.
  * `ownerField` and the per-input `npk` are circuit public inputs/outputs
    (:32-39), so the pool and the owning contract can read them back.

  DEPARTURE (circuit, confirmed by reading the source files): Transact.circom
  with commit `e79919d` (branch `feat/public-ceremony`) has an input
  leaf-distinctness block (Transact.circom:145-161, `IsEqual(...).out === 0`
  for every pair of leaf indices of one proof). TransactOwned.circom has no
  such block on any branch: grepping it for `IsEqual` returns no match. So
  nothing in the owned circuit stops one proof from publishing the same
  nullifier twice. That is safe only because `nullifier = Poseidon(ownerField,
  leafIndex)` is a pure function of the leaf index: two inputs that reuse one
  leaf index publish the same nullifier value, and the pool's
  nullifier-marking loop (TransactModule.sol:392-398, modeled in
  ArmadaLean.PoolOwned) reverts the whole call the second time that value is
  marked. The circuit cannot see earlier spends on any branch: the contract's
  spent map is the only no-double-spend check. `owned_no_double_spend` in
  ArmadaLean.PoolOwned proves the pool-level guarantee directly; it does not
  assume a circuit field.

  Both circuits compute `npk = Poseidon(X, random)` with the same two-argument
  formula and no on-circuit tag distinguishing which circuit produced `X`
  (confirmed by reading both files: TransactOwned.circom:66-70 and
  Transact.circom:75-78 share the identical call shape). `ownerField` is the
  owning contract's address: `ownerField = uint256(uint160(owner))`, supplied by
  the calling contract, and the on-chain verifier checks it against `msg.sender`
  (TransactOwned.circom:13-14; `ShieldedRagequit.sol:147` is one caller that
  supplies one). The public
  input holds `owner : Address`, a number below `2^160` (`ArmadaLean.Types.Address`),
  and `TransactOwnedPublic.ownerField` is `Term.val owner`. So `ownerField` is never
  a hash term, by constructor disjointness of `Term` (`Address.val_ne_hash`).
  `masterPublicKey` (ArmadaLean.Transact), by contrast, is always a Poseidon
  `Term.hash` term. The separation `user_npk_ne_contract_npk` below rests on that
  constructor difference, not on any tag the circuits themselves carry. An earlier
  version of this model represented `ownerField` as a Keccak hash term and rested
  the separation on the hash-function tag (`Term.poseidon_ne_keccak`). That form let
  a witness name any term as `ownerField`, a user's master public key included, and
  made `Pool.apply_backward_refinement` unprovable.

  DEPARTURE of the current contract, removed by the rewrite (the rewrite takes
  a 20-byte
  `ownerField` and rejects a value at or above 2^160). `_validateOwnedTransaction`
  authorizes with `msg.sender == address(uint160(uint256(ownerField)))`
  (TransactModule.sol:637) — the contract truncates `ownerField` to its low 160
  bits before comparing, so it also accepts a non-canonical `ownerField` with
  high bits set (any field element whose low 160 bits equal the caller's
  address). This model's `Address` admits only the canonical value below `2^160`,
  the rewrite's rule: `ArmadaLean.PoolOwned.owned_owner_binding` models the
  authorization check as plain term equality, `ownerField = caller`
  (`TransactOwned.circom:13`, `ShieldedRagequit.sol:147` establish the canonical,
  untruncated form a genuine caller supplies).
-/
import ArmadaLean.Field
import ArmadaLean.Poseidon
import ArmadaLean.RangeCheck
import ArmadaLean.ValueConservation
import ArmadaLean.Nullifier
import ArmadaLean.Merkle
import ArmadaLean.Transact
import ArmadaLean.Types.Address

namespace ArmadaLean

/-- Private witness of the TransactOwned circuit — mirrors the private
    signals (TransactOwned.circom:43-53). No `publicKey`, `signature` or
    `nullifyingKey`: the owned path carries no EdDSA witness. -/
structure TransactOwnedWitness (N M : Nat) where
  /-- tokenHash, shared by every input/output (:43). -/
  token : Token
  /-- note randomness per input (:46). -/
  randomIn : Fin N → Nat
  /-- note value per input (:47). -/
  valueIn : Fin N → Nat
  /-- Merkle path (sibling, directionBit) per input; each of length 16 and with the
      bits of `leavesIndices i` (:48, enforced by `OwnedConstrained.merkle`). Siblings
      are terms. -/
  pathElements : Fin N → List (Term × Bool)
  /-- Merkle leaf positions (:49). -/
  leavesIndices : Fin N → Nat
  /-- output note public keys (:52). -/
  npkOut : Fin M → Term
  /-- output values (:53). -/
  valueOut : Fin M → Nat

/-- Public inputs of the TransactOwned circuit (TransactOwned.circom:32-36).
    `boundParamsHash` is a term, the same as `TransactPublic.boundParamsHash`. -/
structure TransactOwnedPublic (N M : Nat) where
  merkleRoot : Term
  boundParamsHash : Term
  nullifiers : Fin N → Term
  commitmentsOut : Fin M → Term
  /-- The calling contract's address (TransactOwned.circom:36): a 160-bit `Address`
      (`ArmadaLean.Types.Address`). The circuit takes `ownerField =
      uint256(uint160(owner))` from the calling contract (TransactOwned.circom:13-14).
      The pool checks `ownerField` against the caller
      (modeled by `owned_owner_binding` in ArmadaLean.PoolOwned). -/
  owner : Address

/-- The public input `ownerField` (TransactOwned.circom:36): `uint256(uint160(owner))`
    (TransactOwned.circom:13), the field element of the owner's address. A `Term.val`,
    never a hash term (`ownerField_ne_hash`). -/
def TransactOwnedPublic.ownerField {N M : Nat} (pub : TransactOwnedPublic N M) : Term :=
  Term.val pub.owner

/-- `ownerField` is never a hash term: it is never a note key, a commitment, a nullifier
    or a master public key (`Address.val_ne_hash`). -/
theorem TransactOwnedPublic.ownerField_ne_hash {N M : Nat} (pub : TransactOwnedPublic N M)
    (fn : HashFn) (l : List Term) : pub.ownerField ≠ Term.hash fn l :=
  Address.val_ne_hash pub.owner fn l

/--
The full constraint system of the TransactOwned circuit
(TransactOwned.circom:59-135), as a conjunction. A witness/public pair
satisfying `OwnedConstrained` is exactly a satisfying assignment of the
circuit. (The circuit's two public outputs, `npk[N]` and `transcriptHash`
(:39-40), are deterministic functions of the witness with nothing external to
check them against, so they are not separate fields here: `npk pub.ownerField
(w.randomIn i)` below is literally the output `npk[i]`.)
-/
structure OwnedConstrained {N M : Nat} (w : TransactOwnedWitness N M)
    (pub : TransactOwnedPublic N M) : Prop where
  /-- 1a-1c: `npk = Poseidon(ownerField, random)` (:66-70), `commitment =
      Poseidon(npk, token, value)` (:72-76), and Merkle membership against the
      public root (:78-87): `MerkleTreeProof(16)` with the path's 16 levels (:48, :79,
      :81-83), the direction bits of `leavesIndices i` (:84, `Num2Bits(16)` in
      merkle.circom:28-29) and the root check (:87). The
      bits are tied to the index. -/
  merkle : ∀ i,
    MerkleProof 16
      (commitment (npk pub.ownerField (w.randomIn i)) w.token (w.valueIn i))
      (w.pathElements i) (w.leavesIndices i) pub.merkleRoot
  /-- 1d: nullifier = Poseidon(ownerField, leafIndex) (:89-97). -/
  nullifiers : ∀ i, pub.nullifiers i = nullifier pub.ownerField (w.leavesIndices i)
  /-- 2: output commitments (:100-109). -/
  outputs : ∀ j, pub.commitmentsOut j = commitment (w.npkOut j) w.token (w.valueOut j)
  /-- 3 (inputs): every input value passes Num2Bits(120) (:112-116). -/
  rangeIn : ∀ i, RangeChecked120 (w.valueIn i)
  /-- 3 (outputs): every output value passes Num2Bits(120) (:117-121). -/
  rangeOut : ∀ j, RangeChecked120 (w.valueOut j)
  /-- 3: value conservation — checked *in the field* by the circuit
      (`sumIn === sumOut`, :123-135); upgraded to integer equality by
      `transactOwned_value_conserved`. -/
  balance : fieldEq (listSum (List.ofFn w.valueIn)) (listSum (List.ofFn w.valueOut))

/--
**Value is conserved as an integer equality**, for the owned circuit, exactly
as `transact_value_conserved` for Transact (SECURITY_REVIEW.md Finding 1
fix): because every note value is range-checked below `2^120`
(TransactOwned.circom:114-119) and
there are at most 8 inputs and 4 outputs, both sums stay below the BN254
scalar field prime, so the circuit's mod-`p` check `sumIn === sumOut`
(TransactOwned.circom:135) is an honest integer equality. Rules out an owned spend that mints
value by wraparound. Values are plain `Nat`, so the symbolic `Term` model
does not touch this theorem. -/
theorem transactOwned_value_conserved {N M : Nat} (w : TransactOwnedWitness N M)
    (pub : TransactOwnedPublic N M) (hN : N ≤ 8) (hM : M ≤ 4)
    (h : OwnedConstrained w pub) :
    listSum (List.ofFn w.valueIn) = listSum (List.ofFn w.valueOut) := by
  apply no_wraparound_minting _ _ _ _ _ _ h.balance
  · rw [List.length_ofFn]; exact hN
  · rw [List.length_ofFn]; exact hM
  · intro v hv
    obtain ⟨i, hiv⟩ := List.mem_ofFn.mp hv
    rw [← hiv]
    exact rangeCheck120_sound _ (h.rangeIn i)
  · intro v hv
    obtain ⟨j, hjv⟩ := List.mem_ofFn.mp hv
    rw [← hjv]
    exact rangeCheck120_sound _ (h.rangeOut j)

/--
**A note's commitment determines its owner.** `npk = Poseidon(ownerField,
random)` (:66-70) and `commitment = Poseidon(npk, token, value)` (:72-76), so
by collision resistance (`Term.hash2_inj`, `Term.hash3_inj`, by construction)
the same commitment value cannot arise from two different `ownerField`
terms. This is the Poseidon-injectivity core of owner binding
(`owned_owner_binding` in ArmadaLean.PoolOwned adds the pool's authorization
check on top).
Source: TransactOwned.circom:66-76. -/
theorem commitment_owner_inj {owner₁ owner₂ : Term} {r₁ r₂ value : Nat} {token : Token}
    (h : commitment (npk owner₁ r₁) token value =
         commitment (npk owner₂ r₂) token value) :
    owner₁ = owner₂ := by
  obtain ⟨hnpk, -, -⟩ := Term.hash3_inj h
  exact (Term.hash2_inj hnpk).1

/--
**No user note key equals a contract note key.** A user's `npk` is always
`npk (masterPublicKey pk nk) r` for some spending key `pk` and nullifying key
`nk` (`ArmadaLean.Transact`), and `masterPublicKey pk nk` is always a Poseidon
`Term.hash` term — its definition is literally `Term.hash3 ...`. A contract's `npk`
is always `npk (Term.val owner) r` for the contract's 160-bit address `owner`
(`TransactOwnedPublic.ownerField`) — a `Term.val`, never
a hash term. A `Term.val` and a `Term.hash` never agree, by construction
(`Term.val_ne_hash`), so these two `npk` shapes can never collide, whatever
randomness, spending key or address either side chooses. This is the Dolev-Yao
substitute for an on-circuit domain tag: see the module comment.
Source: TransactOwned.circom:66-70, Transact.circom:75-78. -/
theorem user_npk_ne_contract_npk {pk : Nat × Nat} {nk r₁ : Nat}
    {owner : Address} {r₂ : Nat} :
    npk (masterPublicKey pk nk) r₁ ≠ npk (Term.val owner) r₂ := by
  intro h
  have hmpk : masterPublicKey pk nk = Term.val owner := (Term.hash2_inj h).1
  exact Address.val_ne_hash owner _ _ hmpk.symm

end ArmadaLean
