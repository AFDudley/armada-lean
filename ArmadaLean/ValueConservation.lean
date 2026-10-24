/-
  ArmadaLean.ValueConservation — no wraparound minting.

  Mirrors Transact.circom:131-143 (`sumIn === sumOut`) together with the
  design comment at Transact.circom:116-119: since every value is range-checked
  below 2^120 and there are at most 8 inputs and 4 outputs, both sums are
  integers below the BN254 scalar field prime, so the circuit's mod-`p`
  equality check is an honest integer equality.

  This is the formalization of the SECURITY_REVIEW.md Finding 1 fix:
  without the range checks, `sumIn === sumOut` could hold mod p with
  `sumOut = sumIn + p` — minting value out of nothing.
-/
import ArmadaLean.Field

/-- Sum of a list of naturals (the circuit's `accIn`/`accOut` accumulators,
    Transact.circom:133-140). -/
def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/-- `listSum` distributes over `++` (ArmadaLean.Pool uses this to split a batch's total
    into the part carried by new notes and the part carried by notes already live). -/
theorem listSum_append (l1 l2 : List Nat) : listSum (l1 ++ l2) = listSum l1 + listSum l2 := by
  induction l1 with
  | nil => simp [listSum]
  | cons x xs ih => simp only [List.cons_append, listSum, ih]; omega

/-- `listSum` is invariant under reordering (ArmadaLean.Pool uses this together with
    `List.Perm.map` to show that removing a sub-multiset of live notes and reinserting
    it changes the total value by exactly the sub-multiset's value, regardless of where
    in the list the removed notes sat). -/
theorem listSum_perm {l1 l2 : List Nat} (h : l1.Perm l2) : listSum l1 = listSum l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [listSum, ih]
  | swap x y l => simp [listSum]; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- A list whose elements are all below `c` sums to at most `length * (c - 1)`. -/
theorem listSum_le_length_mul_sub_one (vs : List Nat) (c : Nat)
    (h : ∀ v ∈ vs, v < c) : listSum vs ≤ vs.length * (c - 1) := by
  induction vs with
  | nil => simp [listSum]
  | cons x xs ih =>
    have hx : x < c := h x (List.mem_cons_self)
    have hxs : ∀ v ∈ xs, v < c := fun v hv => h v (List.mem_cons_of_mem x hv)
    have ihh := ih hxs
    simp only [listSum, List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- The key bound: with at most 8 notes each below `2^120`, the sum is strictly
    below the field prime (Transact.circom:116-119 — "worst-case sum (8 x 2^120)
    stays far below the BN254 scalar field"). -/
theorem listSum_lt_p (vs : List Nat) (hlen : vs.length ≤ 8)
    (h : ∀ v ∈ vs, v < 2 ^ 120) : listSum vs < p := by
  have h1 := listSum_le_length_mul_sub_one vs (2 ^ 120) h
  have h2 : vs.length * (2 ^ 120 - 1) ≤ 8 * (2 ^ 120 - 1) :=
    Nat.mul_le_mul hlen (Nat.le_refl _)
  have h3 : 8 * (2 ^ 120 - 1) < p := sum_bound_sub_one_lt_p
  omega

/--
**No wraparound minting** (SECURITY_REVIEW.md Finding 1 fix, formalized).

If input and output note values are each range-checked below `2^120`
(the `Num2Bits(120)` constraints, Transact.circom:120-129) and there are at
most 8 inputs and 4 outputs, then the circuit's in-field value conservation
check `sumIn === sumOut` (Transact.circom:141-143) is a true integer equality:
no value can be minted by wrapping around the field modulus. -/
theorem no_wraparound_minting (ins outs : List Nat)
    (hN : ins.length ≤ 8) (hM : outs.length ≤ 4)
    (hin : ∀ v ∈ ins, v < 2 ^ 120) (hout : ∀ v ∈ outs, v < 2 ^ 120)
    (hsum : fieldEq (listSum ins) (listSum outs)) :
    listSum ins = listSum outs := by
  apply eq_of_fieldEq_of_lt _ _ hsum
  · exact listSum_lt_p ins hN hin
  · exact listSum_lt_p outs (Nat.le_trans hM (by decide)) hout
