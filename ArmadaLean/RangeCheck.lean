/-
  ArmadaLean.RangeCheck — Num2Bits-style range checks.

  Mirrors the `Num2Bits(120)` range checks in Transact.circom:120-129:
  a value is range-checked by exhibiting its 120-bit binary decomposition
  (circomlib bitify.circom constrains `in` to equal Σ bᵢ·2ⁱ with boolean bᵢ).

  We model the bit decomposition directly as a little-endian list of booleans
  valued by `bitsVal`; the soundness theorem says any 120-bit-decomposable
  value is below 2^120. This is the formal content of SECURITY_REVIEW.md
  Finding 1's fix (values constrained to < 2^120).
-/

/-- Little-endian value of a bit list: `bitsVal [b₀, b₁, …] = Σ bᵢ·2ⁱ`.
    Mirrors the `lc` accumulation in circomlib's Num2Bits. -/
def bitsVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsVal bs

/-- An `n`-bit decomposition always denotes a value below `2^n`. -/
theorem bitsVal_lt_two_pow (bs : List Bool) : bitsVal bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsVal]
  | cons b bs ih =>
    simp only [bitsVal, List.length_cons, Nat.pow_succ]
    have hb : b.toNat ≤ 1 := Bool.toNat_le b
    have h2 : 2 * bitsVal bs < 2 * 2 ^ bs.length :=
      Nat.mul_lt_mul_of_pos_left ih (by decide)
    omega

/-- A value passes the in-circuit `Num2Bits(120)` check iff it has a 120-bit
    binary decomposition (Transact.circom:120-129). -/
def RangeChecked120 (v : Nat) : Prop :=
  ∃ bs : List Bool, bs.length = 120 ∧ v = bitsVal bs

/-- A note value that the circuits accept as an input: it passes the input range check
    `Num2Bits(120)` (Transact.circom:120-124, TransactOwned.circom:112-116). The pool
    layer uses this name and never the bit width: a note can be spent only if its
    value is `Spendable`. Audit finding P-6 records the earlier `2 ^ 120` bound in the
    pool state. -/
def Spendable (v : Nat) : Prop := RangeChecked120 v

/-- Soundness of the range check: any value passing `Num2Bits(120)` is below `2^120`.
    This is what keeps the value-conservation sum from wrapping around the field
    (SECURITY_REVIEW.md Finding 1; Transact.circom:116-119). -/
theorem rangeCheck120_sound (v : Nat) (h : RangeChecked120 v) : v < 2 ^ 120 := by
  obtain ⟨bs, hlen, hv⟩ := h
  subst hv
  have := bitsVal_lt_two_pow bs
  rwa [hlen] at this
