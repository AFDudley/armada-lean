/-
  ArmadaLean.Field — the BN254 scalar field, modeled on plain `Nat`.

  Field elements are plain natural numbers; "equal in the field" means
  `a % p = b % p` (see `fieldEq`). This mirrors how the circom circuits
  (src/operations/Transact.circom, src/lib/merkle.circom in armada-circuits)
  compute over the BN254 scalar field: every `===` constraint is an
  equality modulo `p`.
-/

/-- The BN254 scalar field prime (a.k.a. the alt_bn128 / BabyJubJub scalar field order). -/
def p : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem p_pos : 0 < p := by decide

/-- Equality in the field: two naturals are field-equal iff they agree mod `p`. -/
def fieldEq (a b : Nat) : Prop := a % p = b % p

/-- Below the prime, field equality is plain equality.
    This is the bridge that lets us upgrade in-circuit `===` checks
    (mod `p`) to integer equalities once range checks bound the operands. -/
theorem eq_of_fieldEq_of_lt {a b : Nat} (ha : a < p) (hb : b < p) (h : fieldEq a b) :
    a = b := by
  unfold fieldEq at h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

/-- Closed arithmetic fact: the 120-bit value cap is far below the field prime.
    (Justifies Transact.circom:116-119's comment that Num2Bits(120) range checks
    keep values well inside the field.) -/
theorem two_pow_120_lt_p : 2 ^ 120 < p := by decide

/-- Closed arithmetic fact: eight maximally-sized notes still sum below the field prime.
    (Justifies Transact.circom:117-118: "worst-case sum (8 x 2^120) stays far below
    the BN254 scalar field (~2^254)".) -/
theorem sum_bound_lt_p : 8 * 2 ^ 120 < p := by decide

/-- Closed arithmetic fact: `8 * (2^120 - 1) < p`, the exact worst-case sum bound
    used to prevent wraparound minting (see ValueConservation.no_wraparound_minting). -/
theorem sum_bound_sub_one_lt_p : 8 * (2 ^ 120 - 1) < p := by decide
