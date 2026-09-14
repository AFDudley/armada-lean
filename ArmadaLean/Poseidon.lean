/-
  ArmadaLean.Poseidon — the Poseidon hash function, axiomatized.

  Poseidon is the hash used everywhere in the circuits
  (circomlib poseidon.circom, instantiated at Transact.circom:63,76,81,98,108,167
  and merkle.circom:40). We do not model its internals; we only assume the
  cryptographic property the security arguments actually rely on:
  collision resistance, phrased as injectivity on the fixed arities used.
-/

/--
CRYPTOGRAPHIC ASSUMPTION (collision resistance / injectivity of the Poseidon
permutation sponge on fixed arities) — assumed, not proven.

The 2-argument Poseidon hash (used for note public keys, nullifiers, and every
Merkle tree level: merkle.circom:40). -/
axiom poseidon2 : Nat → Nat → Nat

/--
CRYPTOGRAPHIC ASSUMPTION (collision resistance / injectivity of the Poseidon
permutation sponge on fixed arities) — assumed, not proven.

Injectivity of `poseidon2`: a collision reveals identical inputs. This is the
contrapositive form used to argue that distinct leaves/nullifiers hash distinctly. -/
axiom poseidon2_inj :
  ∀ {a b c d : Nat}, poseidon2 a b = poseidon2 c d → a = c ∧ b = d

/--
CRYPTOGRAPHIC ASSUMPTION (collision resistance / injectivity of the Poseidon
permutation sponge on fixed arities) — assumed, not proven.

The 3-argument Poseidon hash (used for the master public key and note
commitments: Transact.circom:63,81,108). -/
axiom poseidon3 : Nat → Nat → Nat → Nat

/--
CRYPTOGRAPHIC ASSUMPTION (collision resistance / injectivity of the Poseidon
permutation sponge on fixed arities) — assumed, not proven.

Injectivity of `poseidon3`: a collision reveals identical inputs. -/
axiom poseidon3_inj :
  ∀ {a b c d e f : Nat}, poseidon3 a b c = poseidon3 d e f → a = d ∧ b = e ∧ c = f
