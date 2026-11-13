import Mathlib.Tactic.Says

namespace ArmadaLean

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
  | nil => (simp? [bitsVal] says simp only [bitsVal, List.length_nil, Nat.pow_zero, Nat.lt_add_one])
  | cons b bs ih =>
    simp only [bitsVal, List.length_cons, Nat.pow_succ]
    have hb : b.toNat ≤ 1 := Bool.toNat_le b
    have h2 : 2 * bitsVal bs < 2 * 2 ^ bs.length :=
      Nat.mul_lt_mul_of_pos_left ih (by decide)
    omega

/-- Two bit lists of one length with one value are equal: `bitsVal` is injective on each
    length. `MerkleProof.opens_treeRoot` uses it to match a proof's direction bits with
    the bits of the leaf index. -/
theorem bitsVal_inj {bs bs' : List Bool} (hlen : bs.length = bs'.length)
    (h : bitsVal bs = bitsVal bs') : bs = bs' := by
  induction bs generalizing bs' with
  | nil =>
    cases bs' with
    | nil => rfl
    | cons _ _ => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_one_ne_zero] at hlen
  | cons b bs ih =>
    cases bs' with
    | nil => simp only [List.length_cons, List.length_nil, Nat.add_one_ne_zero] at hlen
    | cons b' bs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bitsVal] at h
      have hb : b = b' := by
        cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;>
          first | rfl | omega
      subst hb
      have : bitsVal bs = bitsVal bs' := by omega
      rw [ih hlen this]

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

/-! ## The converse: a decomposition for any value below `2^n`

`natBits n v` is the `n`-bit little-endian decomposition of `v`, read off by repeated
halving; `natBits_val` shows it denotes `v` whenever `v < 2 ^ n`. `spendable_of_lt` is the
converse of `rangeCheck120_sound`: the pool's `ShieldPre` bounds a value by `2 ^ 120`, and
`Step.shield` needs `Spendable` (`Pool.apply_backward_refinement`, the `shield` case). The
fixtures of `PoolNonVacuity` use it for their concrete values. -/

/-- Little-endian bits of `v`, exactly `n` of them, by repeated halving. -/
def natBits : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, v => (v % 2 == 1) :: natBits n (v / 2)

theorem natBits_length (n v : Nat) : (natBits n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp only [natBits, List.length_cons, ih]

theorem natBits_val (n v : Nat) (hv : v < 2 ^ n) : bitsVal (natBits n v) = v := by
  induction n generalizing v with
  | zero =>
    simp only [Nat.pow_zero] at hv
    have hv0 : v = 0 := by omega
    subst hv0
    rfl
  | succ n ih =>
    have hdm : 2 * (v / 2) + v % 2 = v := Nat.div_add_mod v 2
    have hr : v % 2 < 2 := Nat.mod_lt v (by decide)
    have hq : v / 2 < 2 ^ n := by
      simp only [Nat.pow_succ] at hv
      omega
    have ihq := ih (v / 2) hq
    show ((v % 2 == 1 : Bool)).toNat + 2 * bitsVal (natBits n (v / 2)) = v
    rw [ihq]
    rcases (by omega : v % 2 = 0 ∨ v % 2 = 1) with h0 | h1
    · have hb : (0 == 1 : Bool) = false := by decide
      rw [h0, hb, Bool.toNat_false]; omega
    · have hb : (1 == 1 : Bool) = true := by decide
      rw [h1, hb, Bool.toNat_true]; omega

/-- Every value below `2^120` is `Spendable` (and passes `RangeChecked120`): its own
    `natBits 120` decomposition witnesses it. The converse of `rangeCheck120_sound`. -/
theorem spendable_of_lt {v : Nat} (h : v < 2 ^ 120) : Spendable v :=
  ⟨natBits 120 v, natBits_length 120 v, (natBits_val 120 v h).symm⟩

end ArmadaLean
