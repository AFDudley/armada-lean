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

/-- Soundness of the range check: any value passing `Num2Bits(120)` is below `2^120`.
    This is what keeps the value-conservation sum from wrapping around the field
    (SECURITY_REVIEW.md Finding 1; Transact.circom:116-119). -/
theorem rangeCheck120_sound (v : Nat) (h : RangeChecked120 v) : v < 2 ^ 120 := by
  obtain ⟨bs, hlen, hv⟩ := h
  subst hv
  have := bitsVal_lt_two_pow bs
  rwa [hlen] at this

/-- Little-endian bit extraction: `natToBits n fuel` names `fuel` bits of
    `n`, least-significant first. Always has exactly `fuel` elements,
    regardless of `n`. -/
def natToBits : Nat → Nat → List Bool
  | _, 0 => []
  | n, fuel + 1 => (n % 2 = 1) :: natToBits (n / 2) fuel

theorem natToBits_length (n fuel : Nat) : (natToBits n fuel).length = fuel := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih => show (natToBits (n / 2) k).length + 1 = k + 1; rw [ih]

/-- Base-2 digit decomposition: splitting off the low bit of `n` before
    taking `n`'s mod against `2 * k` matches splitting `n`'s own div/mod
    by `2` first, then taking that quotient's mod against `k`. Pure
    arithmetic, used only to drive `bitsVal_natToBits`'s own induction. -/
theorem mod_two_mul_eq (n k : Nat) (hk : 0 < k) :
    n % (2 * k) = n % 2 + 2 * ((n / 2) % k) := by
  have h1 : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
  have h2 : n / 2 = k * ((n / 2) / k) + (n / 2) % k := (Nat.div_add_mod (n / 2) k).symm
  have h3 : n % 2 < 2 := Nat.mod_lt n (by omega)
  have h4 : (n / 2) % k < k := Nat.mod_lt (n / 2) hk
  have h6 : n % 2 + 2 * ((n / 2) % k) < 2 * k := by omega
  have h5 : n = (2 * k) * ((n / 2) / k) + (n % 2 + 2 * ((n / 2) % k)) := by
    rw [Nat.mul_assoc]; omega
  have key : n % (2 * k) = ((2 * k) * ((n / 2) / k) + (n % 2 + 2 * ((n / 2) % k))) % (2 * k) :=
    congrArg (· % (2 * k)) h5
  rw [key, Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt h6

theorem bitsVal_natToBits (n fuel : Nat) : bitsVal (natToBits n fuel) = n % 2 ^ fuel := by
  induction fuel generalizing n with
  | zero => show (0 : Nat) = n % 1; omega
  | succ k ih =>
    show (decide (n % 2 = 1)).toNat + 2 * bitsVal (natToBits (n / 2) k) = n % 2 ^ (k + 1)
    rw [ih, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
      mod_two_mul_eq n (2 ^ k) (Nat.two_pow_pos k)]
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · rw [h2]; simp only [show (0 = 1) = False from by simp, decide_false, Bool.toNat_false]
    · rw [h2]; simp only [decide_true, Bool.toNat_true]




/-- Completeness of the range check: any value below `2^120` passes
    `Num2Bits(120)` — exhibit its own 120-bit binary decomposition
    directly. Pure arithmetic, independent of the pool model. What lets
    a derived bound (`a ≤ b`, `RangeChecked120 b`) carry over to `a`:
    `rangeCheck120_sound` gives `a < 2 ^ 120` from `a ≤ b < 2 ^ 120`,
    then this reconstructs the witness. -/
theorem rangeCheck120_complete (v : Nat) (h : v < 2 ^ 120) : RangeChecked120 v :=
  ⟨natToBits v 120, natToBits_length v 120, by rw [bitsVal_natToBits]; omega⟩

/-- `RangeChecked120` is monotone: a value no bigger than an
    already-range-checked one is itself range-checked. What
    `unbeatable_pays`'s own strategy needs: a payout or remainder
    bounded by the channel's own held value inherits its range check. -/
theorem rangeCheck120_mono {v w : Nat} (hle : v ≤ w) (h : RangeChecked120 w) :
    RangeChecked120 v :=
  rangeCheck120_complete v (by have := rangeCheck120_sound w h; omega)

