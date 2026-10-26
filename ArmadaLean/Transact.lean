/-
  ArmadaLean.Transact — full constraint model of the Transact circuit.

  Models every constraint group of src/operations/Transact.circom (line cites
  below refer to that file) and proves the three headline security properties:

  * `transact_public_outputs_determined` — the security-critical public outputs
    are uniquely determined by the witness (no under-constrained freedom);
  * `transact_no_double_spend` — the published nullifiers are pairwise distinct
    (SECURITY_REVIEW.md Finding 2 fix);
  * `transact_value_conserved` — input value equals output value as integers
    (SECURITY_REVIEW.md Finding 1 fix; the in-field check at :141-143 cannot be
    exploited by wraparound).

  Commitments, nullifiers, note public keys, master public keys and Merkle
  roots are `Term`s (`ArmadaLean.Poseidon`, the symbolic Dolev-Yao hash model);
  note values, token amounts and range checks stay `Nat`. `msgHashOf`, the
  variable-arity EdDSA message hash, is now defined directly as a `Term.hash` call
  rather than left as an axiom — the generic `Term.hash : HashFn → List Term → Term`
  constructor, tagged `.poseidon`, represents exactly what `Poseidon(2+N+M)` computes,
  so no separate assumption is needed for this one arity.
-/
import ArmadaLean.Field
import ArmadaLean.Poseidon
import ArmadaLean.RangeCheck
import ArmadaLean.ValueConservation
import ArmadaLean.Nullifier
import ArmadaLean.Merkle

/--
CRYPTOGRAPHIC ASSUMPTION: EdDSA signature unforgeability is assumed, not modeled.

`EdDSAVerify pk sig msg` holds iff `sig` is a valid EdDSA-Poseidon signature on
`msg` under public key `pk` (Transact.circom:177-186, circomlib
eddsaposeidon.circom). We only need the *validity* direction here: the circuit
constrains the signature to verify. The message `msg` is a `Term`
(`ArmadaLean.Poseidon`): it is itself a Poseidon output (`msgHashOf` below),
and `EdDSAVerify` is left abstract only on the signature-scheme primitive, not
on the hash that produces its input. -/
axiom EdDSAVerify : (Nat × Nat) → (Nat × Nat × Nat) → Term → Prop

/-- Master public key = Poseidon(spendingPublicKeyX, spendingPublicKeyY,
    nullifyingKey) (Transact.circom:61-66). `pk`/`nk` are raw values (BabyJubJub
    coordinates and a secret nullifying key) the spender chose, embedded as
    `Term.val` before hashing; the result is a genuine Poseidon hash term, never a
    `Term.val` and never a Keccak term — this is what
    `ArmadaLean.TransactOwned.user_npk_ne_contract_npk` rests on. -/
def masterPublicKey (pk : Nat × Nat) (nk : Nat) : Term :=
  Term.hash3 (Term.val pk.1) (Term.val pk.2) (Term.val nk)

/-- Note public key = Poseidon(masterPublicKey, random) (Transact.circom:75-78).
    `mpk` is already a `Term` (a master public key, or — on the owned path,
    `ArmadaLean.TransactOwned` — the owning contract's address term,
    `TransactOwnedPublic.ownerField`, a Keccak hash, `ArmadaLean.PoolOwned`'s module
    comment on address terms); `r` is a raw randomness value, embedded as
    `Term.val`. -/
def npk (mpk : Term) (r : Nat) : Term := Term.hash2 mpk (Term.val r)

/-- `npk` is injective in both arguments: two note public keys built from
    the same Poseidon hash (`Term.hash2_inj`) share the same master key and
    the same random value. What lets a note's own key, once known
    adjudicator-owned (`npk (Term.val self) r`), pin down `r` uniquely —
    so two disclosures of the same commitment can never name a different
    random for it. -/
theorem npk_inj {mpk1 mpk2 : Term} {r1 r2 : Nat} (h : npk mpk1 r1 = npk mpk2 r2) :
    mpk1 = mpk2 ∧ r1 = r2 := by
  unfold npk at h
  obtain ⟨h1, h2⟩ := Term.hash2_inj h
  exact ⟨h1, Term.val.inj h2⟩

/-- Note commitment = Poseidon(npk, token, value)
    (Transact.circom:80-84 for inputs, :105-113 for outputs). `npk` is already
    a `Term`; `token`/`value` are raw numbers (a token ID field element and a
    note value), embedded as `Term.val`. -/
def commitment (npk : Term) (token value : Nat) : Term :=
  Term.hash3 npk (Term.val token) (Term.val value)

/-- Private witness of the Transact circuit — mirrors the private signals
    (Transact.circom:41-55). Arrays indexed by `Fin N` / `Fin M` play the role
    of the circom signal arrays. `pathElements i` is the Merkle path for input
    `i` (the flat `pathElements[N*16]` signal at :50, sliced per note). -/
structure TransactWitness (N M : Nat) where
  /-- tokenHash — all inputs/outputs share this (:42) -/
  token : Nat
  /-- spending public key [x, y] on BabyJubJub (:43) -/
  publicKey : Nat × Nat
  /-- EdDSA signature [R_x, R_y, S] (:44) -/
  signature : Nat × Nat × Nat
  /-- nullifying key (:45) -/
  nullifyingKey : Nat
  /-- note randomness per input (:48) -/
  randomIn : Fin N → Nat
  /-- note value per input (:49) -/
  valueIn : Fin N → Nat
  /-- Merkle path (sibling, directionBit) per input; each of length 16
      (:50, enforced by `Constrained.pathLen`). Siblings are terms (other
      Merkle tree nodes). -/
  pathElements : Fin N → List (Term × Bool)
  /-- Merkle leaf positions (:51) -/
  leavesIndices : Fin N → Nat
  /-- output note public keys (:54) — a term the prover supplies freely, the
      same role `npk` plays for an input note. -/
  npkOut : Fin M → Term
  /-- output values (:55) -/
  valueOut : Fin M → Nat

/-- Public inputs of the Transact circuit (Transact.circom:35-39). `merkleRoot`,
    `nullifiers` and `commitmentsOut` are terms; `boundParamsHash` is a plain
    field element (`keccak256(...) % SNARK_SCALAR_FIELD`,
    `PrivacyPoolStorage._boundParamsHash`) — a different hash family this
    project has never modeled via Poseidon, so it stays a raw `Nat`, exactly
    as the numeric model already treated it. -/
structure TransactPublic (N M : Nat) where
  merkleRoot : Term
  boundParamsHash : Nat
  nullifiers : Fin N → Term
  commitmentsOut : Fin M → Term

/-- The message hash the EdDSA signature covers:
    `Poseidon(merkleRoot, boundParamsHash, ...nullifiers, ...commitmentsOut)`
    (Transact.circom:142-154, `Poseidon(2 + N + M)`). `Term.hash` already
    represents a Poseidon call of any arity, so this is a direct, computable
    transcription of the circuit's own packing — not a separate assumption. -/
def msgHashOf {N M : Nat} (pub : TransactPublic N M) : Term :=
  Term.hash .poseidon (pub.merkleRoot :: Term.val pub.boundParamsHash ::
    (List.ofFn pub.nullifiers ++ List.ofFn pub.commitmentsOut))

/--
The full constraint system of the Transact circuit (Transact.circom:57-186),
as a conjunction (recorded field-wise for easy projection). A witness/public
pair satisfying `Constrained` is exactly a satisfying assignment of the circuit.
-/
structure Constrained {N M : Nat} (w : TransactWitness N M)
    (pub : TransactPublic N M) : Prop where
  /-- Every Merkle path has the production depth 16 (:50, :87, :89-91). -/
  pathLen : ∀ i, (w.pathElements i).length = 16
  /-- 2c: Merkle membership — each input note's commitment (derived from the
      master public key :61-66, npk :75-78, commitment :80-84) opens along its
      path to the public root (:86-95). -/
  merkle : ∀ i,
    merkleRoot
      (commitment (npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i))
        w.token (w.valueIn i))
      (w.pathElements i) = pub.merkleRoot
  /-- 2d: nullifier derivation (:97-101). -/
  nullifiers : ∀ i, pub.nullifiers i = nullifier (Term.val w.nullifyingKey) (w.leavesIndices i)
  /-- 3: output commitments (:105-113). -/
  outputs : ∀ j, pub.commitmentsOut j = commitment (w.npkOut j) w.token (w.valueOut j)
  /-- 4 (inputs): every input value passes Num2Bits(120) (:120-124). -/
  rangeIn : ∀ i, RangeChecked120 (w.valueIn i)
  /-- 4 (outputs): every output value passes Num2Bits(120) (:125-129). -/
  rangeOut : ∀ j, RangeChecked120 (w.valueOut j)
  /-- 4: value conservation — checked *in the field* by the circuit
      (`sumIn === sumOut`, :131-143); upgraded to integer equality by
      `transact_value_conserved`. -/
  balance : fieldEq (listSum (List.ofFn w.valueIn)) (listSum (List.ofFn w.valueOut))
  /-- 4b: input notes are pairwise distinct — the `IsEqual(...).out === 0`
      checks at :145-161 (SECURITY_REVIEW.md Finding 2 fix). -/
  distinct : ∀ i j, i ≠ j → w.leavesIndices i ≠ w.leavesIndices j
  /-- 5–6: EdDSA signature over the message hash verifies (:163-186). -/
  sig : EdDSAVerify w.publicKey w.signature (msgHashOf pub)

/--
**Public outputs are uniquely determined by the witness**: the nullifiers and
output commitments are computed by deterministic hash chains from the witness
(:97-101, :105-113), so two public-input vectors constrained by the same
witness agree on every security-critical output. There is no under-constrained
freedom an attacker could exploit to keep the same witness while altering the
published nullifiers or commitments. -/
theorem transact_public_outputs_determined {N M : Nat} (w : TransactWitness N M)
    (p₁ p₂ : TransactPublic N M) (h₁ : Constrained w p₁) (h₂ : Constrained w p₂) :
    (∀ i, p₁.nullifiers i = p₂.nullifiers i) ∧
    (∀ j, p₁.commitmentsOut j = p₂.commitmentsOut j) := by
  constructor
  · intro i; rw [h₁.nullifiers i, h₂.nullifiers i]
  · intro j; rw [h₁.outputs j, h₂.outputs j]

/--
**No double-spend within a transaction** (SECURITY_REVIEW.md Finding 2 fix):
the pairwise leaf-distinctness constraints (:145-161) plus collision
resistance of `Term.hash2` (by construction, `ArmadaLean.Poseidon`) force the
published nullifiers to be pairwise distinct, so the same note cannot be
consumed twice by one transaction. -/
theorem transact_no_double_spend {N M : Nat} (w : TransactWitness N M)
    (pub : TransactPublic N M) (h : Constrained w pub) :
    ∀ i j, i ≠ j → pub.nullifiers i ≠ pub.nullifiers j := by
  intro i j hij hn
  rw [h.nullifiers i, h.nullifiers j] at hn
  exact h.distinct i j hij (Term.val.inj (Term.hash2_inj hn).2)

/--
**Value is conserved as an integer equality** (SECURITY_REVIEW.md Finding 1
fix): because every note value is range-checked below `2^120` (:120-129) and
there are at most 8 inputs and 4 outputs, both sums stay below the BN254
scalar field prime, so the circuit's mod-`p` check `sumIn === sumOut`
(:141-143) is an honest integer equality — no wraparound minting. Values are
plain `Nat`, never hashed, so the symbolic `Term` model does not touch this
theorem. -/
theorem transact_value_conserved {N M : Nat} (w : TransactWitness N M)
    (pub : TransactPublic N M) (hN : N ≤ 8) (hM : M ≤ 4)
    (h : Constrained w pub) :
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
**A note's commitment determines the master public key that spends it.** `npk =
Poseidon(masterPublicKey, random)` (:75-78) and `commitment = Poseidon(npk, token,
value)` (:80-84), so by collision resistance (`Term.hash2_inj`, `Term.hash3_inj`,
by construction) the same commitment value cannot arise from two different master
public keys. The plain-path analogue of
`ArmadaLean.TransactOwned.commitment_owner_inj`: there, the owner is read
directly off the commitment because `npk = Poseidon(ownerField, random)`; here, the
commitment instead pins down `masterPublicKey = Poseidon(spendingPublicKeyX,
spendingPublicKeyY, nullifyingKey)` (:61-66), one hash layer further from the raw keys.
This is the Poseidon-injectivity core of "a transact spends only notes whose owner key
derives from keys the spender holds" (`ArmadaLean.PoolSafety.transact_spends_only_owned`
adds the circuit's EdDSA check on top, the plain-path counterpart of
`ArmadaLean.PoolOwned.owned_owner_binding`). -/
theorem commitment_mpk_inj {mpk₁ mpk₂ : Term} {r₁ r₂ token value : Nat}
    (h : commitment (npk mpk₁ r₁) token value = commitment (npk mpk₂ r₂) token value) :
    mpk₁ = mpk₂ := by
  obtain ⟨hnpk, -, -⟩ := Term.hash3_inj h
  exact (Term.hash2_inj hnpk).1
