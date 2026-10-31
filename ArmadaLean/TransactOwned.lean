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
  nullifier-marking loop (TransactModule.sol:379-386, modeled in
  ArmadaLean.PoolOwned) reverts the whole call the second time that value is
  marked. The circuit cannot see earlier spends on any branch: the contract's
  spent map is the only no-double-spend check. `owned_no_double_spend` in
  ArmadaLean.PoolOwned proves the pool-level guarantee directly; it does not
  assume a circuit field.

  Both circuits compute `npk = Poseidon(X, random)` with the same two-argument
  formula and no on-circuit tag distinguishing which circuit produced `X`
  (confirmed by reading both files: TransactOwned.circom:66-70 and
  Transact.circom:75-78 share the identical call shape). `ownerField` is the
  owning contract's address: per the operator's ruling, an EVM contract address
  is itself a hash output — the low 160 bits of `keccak256` of its creator and a
  nonce (`CREATE`) or creator, salt and init-code hash (`CREATE2`), canonically a
  `uint256` field element at the circuit boundary (`TransactOwned.circom:13`,
  `ownerField = uint256(uint160(owner))`; `ShieldedRagequit.sol:147` is one
  caller that supplies one). This model represents `ownerField` as a `Term`, a
  Keccak hash (`ArmadaLean.Poseidon.Term.keccak`, `ArmadaLean.PoolOwned`'s module
  comment has the full address-term account), never a raw `Term.val`.
  `masterPublicKey` (ArmadaLean.Transact), by contrast, is always a Poseidon
  `Term.hash` term. The separation `user_npk_ne_contract_npk` below proves rests
  on that function-tag difference — a Poseidon output and a Keccak output never
  agree, by construction (`ArmadaLean.Poseidon.Term.poseidon_ne_keccak`) — not on
  any tag the circuits themselves carry, and not on `Term.val` vs `Term.hash`
  (both shapes are `Term.hash` terms now).

  DEPARTURE (contract, confirmed by reading the source): `_validateOwnedTransaction`
  authorizes with `msg.sender == address(uint160(uint256(ownerField)))`
  (TransactModule.sol:637) — the contract truncates `ownerField` to its low 160
  bits before comparing, so it also accepts a non-canonical `ownerField` with
  high bits set (any field element whose low 160 bits equal the caller's
  address). This symbolic model cannot express "truncate a `Term`" (a `Term` has
  no numeric interpretation to truncate) and does not: `ArmadaLean.PoolOwned
  .owned_owner_binding` models the authorization check as plain term equality,
  `ownerField = caller`, the canonical case (`TransactOwned.circom:13`,
  `ShieldedRagequit.sol:147` establish the canonical, untruncated form a genuine
  caller supplies).
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
  token : Token
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

/-- Public inputs of the TransactOwned circuit (TransactOwned.circom:32-36).
    `boundParamsHash` is a term, the same as `TransactPublic.boundParamsHash`. -/
structure TransactOwnedPublic (N M : Nat) where
  merkleRoot : Term
  boundParamsHash : Term
  nullifiers : Fin N → Term
  commitmentsOut : Fin M → Term
  /-- The calling contract's address (TransactOwned.circom:36; `ownerField =
      uint256(uint160(owner))`, TransactOwned.circom:13) — a Keccak hash term
      (module comment), never a Poseidon output. The pool checks this against
      the caller (modeled by `owned_owner_binding` in ArmadaLean.PoolOwned). -/
  ownerField : Term

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
  /-- Every Merkle path has the production depth 16 (:48, :79, :81-83). -/
  pathLen : ∀ i, (w.pathElements i).length = 16
  /-- 1a-1c: `npk = Poseidon(ownerField, random)` (:66-70), `commitment =
      Poseidon(npk, token, value)` (:72-76), and Merkle membership against the
      public root (:78-87). -/
  merkle : ∀ i,
    merkleRoot
      (commitment (npk pub.ownerField (w.randomIn i)) w.token (w.valueIn i))
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
check on top). -/
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
`Term.hash` term — its definition is literally `Term.hash3 ...`, tagged
`.poseidon`. A contract's `npk` is always `npk (Term.keccak addrInputs) r` for
whatever inputs its address was derived from (module comment) — a genuine
Keccak `Term.hash` term, tagged `.keccak`. A Poseidon output and a Keccak
output never agree, by construction (`Term.poseidon_ne_keccak`), so these two
`npk` shapes can never collide, whatever randomness, spending key or address
inputs either side chooses. This is the Dolev-Yao substitute for an on-circuit
domain tag: see the module comment. -/
theorem user_npk_ne_contract_npk {pk : Nat × Nat} {nk r₁ : Nat}
    {addrInputs : List Term} {r₂ : Nat} :
    npk (masterPublicKey pk nk) r₁ ≠ npk (Term.keccak addrInputs) r₂ := by
  intro h
  have hmpk : masterPublicKey pk nk = Term.keccak addrInputs := (Term.hash2_inj h).1
  exact Term.poseidon_ne_keccak hmpk
