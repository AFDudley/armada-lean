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
  * Authorization is `msg.sender == ownerField`, checked by the pool
    (modeled in ArmadaLean.PoolOwned), not an EdDSA signature: this circuit
    carries no signature witness and proves no `sig` field.
  * `ownerField` and the per-input `npk` are circuit public inputs/outputs
    (:32-39), so the pool and the owning contract can read them back.

  DEPARTURE (circuit, confirmed by reading the source file): Transact.circom
  has an input leaf-distinctness block (SECURITY_REVIEW.md Finding 2 fix,
  Transact.circom:145-161, `IsEqual(...).out === 0` for every pair of leaf
  indices) that TransactOwned.circom does not repeat — grepping
  TransactOwned.circom for `IsEqual` returns no match. This is safe only
  because `nullifier = Poseidon(ownerField, leafIndex)` is a pure function of
  the leaf index: two inputs that reuse one leaf index are forced to publish
  the same nullifier value, and the pool's own nullifier-marking loop
  (TransactModule.sol:379-386, modeled in ArmadaLean.PoolOwned) reverts the
  whole call the second time that value is marked. `owned_no_double_spend`
  in ArmadaLean.PoolOwned proves the pool-level guarantee directly; it does
  not assume this missing circuit field.

  No domain tag: both circuits compute `npk = Poseidon(X, random)` with the
  same two-argument formula and no tag distinguishing which circuit produced
  `X` (confirmed by reading both files: TransactOwned.circom:66-70 and
  Transact.circom:75-78 share the identical call shape). `ownerField` is an
  address value — a raw `Nat`, embedded as `Term.val` before hashing, exactly
  like any other raw witness number. `masterPublicKey` (ArmadaLean.Transact),
  by contrast, is always a `Term.hash` term: it is itself the output of a
  Poseidon call. The separation `user_npk_ne_contract_npk` below proves rests
  entirely on that shape difference — `Term.val` and `Term.hash` never agree,
  by construction (`ArmadaLean.Poseidon.Term.val_ne_hash`) — not on any tag
  the circuits themselves carry.
-/
import ArmadaLean.Field
import ArmadaLean.Poseidon
import ArmadaLean.RangeCheck
import ArmadaLean.ValueConservation
import ArmadaLean.Nullifier
import ArmadaLean.Merkle
import ArmadaLean.Transact

/-- Private witness of the TransactOwned circuit — mirrors the private
    signals (TransactOwned.circom:43-53). No `publicKey`, `signature` or
    `nullifyingKey`: the owned path carries no EdDSA witness. -/
structure TransactOwnedWitness (N M : Nat) where
  /-- tokenHash, shared by every input/output (:43). -/
  token : Nat
  /-- note randomness per input (:46). -/
  randomIn : Fin N → Nat
  /-- note value per input (:47). -/
  valueIn : Fin N → Nat
  /-- Merkle path (sibling, directionBit) per input; each of length 16
      (:48, enforced by `Constrained.pathLen`). Siblings are terms. -/
  pathElements : Fin N → List (Term × Bool)
  /-- Merkle leaf positions (:49). -/
  leavesIndices : Fin N → Nat
  /-- output note public keys (:52). -/
  npkOut : Fin M → Term
  /-- output values (:53). -/
  valueOut : Fin M → Nat

/-- Public inputs of the TransactOwned circuit (TransactOwned.circom:32-36). -/
structure TransactOwnedPublic (N M : Nat) where
  merkleRoot : Term
  boundParamsHash : Nat
  nullifiers : Fin N → Term
  commitmentsOut : Fin M → Term
  /-- The calling contract's address, Poseidon-field-encoded
      (TransactOwned.circom:36; `ownerField = uint256(uint160(owner))`,
      TransactOwned.circom:13). A raw address value, never a hash output —
      see the module comment's no-domain-tag note. The pool checks this
      against `msg.sender` (modeled by `owned_owner_binding` in
      ArmadaLean.PoolOwned). -/
  ownerField : Nat

/--
The full constraint system of the TransactOwned circuit
(TransactOwned.circom:59-135), as a conjunction. A witness/public pair
satisfying `OwnedConstrained` is exactly a satisfying assignment of the
circuit. (The circuit's two public outputs, `npk[N]` and `transcriptHash`
(:39-40), are deterministic functions of the witness with nothing external to
check them against, so they are not separate fields here: `npk (Term.val
pub.ownerField) (w.randomIn i)` below is literally the output `npk[i]`.)
-/
structure OwnedConstrained {N M : Nat} (w : TransactOwnedWitness N M)
    (pub : TransactOwnedPublic N M) : Prop where
  /-- Every Merkle path has the production depth 16 (:48, :79, :81-83). -/
  pathLen : ∀ i, (w.pathElements i).length = 16
  /-- 1a-1c: `npk = Poseidon(ownerField, random)` (:66-70), `commitment =
      Poseidon(npk, token, value)` (:72-76), and Merkle membership against the
      public root (:78-87). -/
  merkle : ∀ i,
    merkleRoot
      (commitment (npk (Term.val pub.ownerField) (w.randomIn i)) w.token (w.valueIn i))
      (w.pathElements i) = pub.merkleRoot
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
fix): because every note value is range-checked below `2^120` (:112-121) and
there are at most 8 inputs and 4 outputs, both sums stay below the BN254
scalar field prime, so the circuit's mod-`p` check `sumIn === sumOut`
(:133-135) is an honest integer equality. Rules out an owned spend that mints
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
the same commitment value cannot arise from two different `ownerField`s. This
is the Poseidon-injectivity core of owner binding (`owned_owner_binding` in
ArmadaLean.PoolOwned adds the pool's `msg.sender == ownerField` check on top). -/
theorem commitment_owner_inj {owner₁ owner₂ : Nat} {r₁ r₂ token value : Nat}
    (h : commitment (npk (Term.val owner₁) r₁) token value =
         commitment (npk (Term.val owner₂) r₂) token value) :
    owner₁ = owner₂ := by
  obtain ⟨hnpk, -, -⟩ := Term.hash3_inj h
  exact Term.val.inj (Term.hash2_inj hnpk).1

/--
**No user note key equals a contract note key.** A user's `npk` is always
`npk (masterPublicKey pk nk) r` for some spending key `pk` and nullifying key
`nk` (`ArmadaLean.Transact`), and `masterPublicKey pk nk` is always a
`Term.hash` term — a genuine Poseidon output, never a raw value (its
definition is literally `Term.hash3 ...`). A contract's `npk` is always `npk
(Term.val ownerField) r` — and `Term.val ownerField` is always a `Term.val`
term, an address embedded as a raw value, never a hash. `Term.hash` and
`Term.val` never agree (`Term.val_ne_hash`, by construction), so these two
`npk` shapes can never collide, whatever randomness, spending key or owner
field either side chooses. This is the Dolev-Yao substitute for an on-circuit
domain tag: see the module comment. -/
theorem user_npk_ne_contract_npk {pk : Nat × Nat} {nk r₁ : Nat} {ownerField r₂ : Nat} :
    npk (masterPublicKey pk nk) r₁ ≠ npk (Term.val ownerField) r₂ := by
  intro h
  have hmpk : masterPublicKey pk nk = Term.val ownerField := (Term.hash2_inj h).1
  exact Term.val_ne_hash ownerField _ hmpk.symm
