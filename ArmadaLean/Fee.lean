/-
  ArmadaLean.Fee — inclusive shield-fee model of ShieldModule.sol.

  Models `_getFee` (inclusive path) of
  armada-poc/contracts/privacy-pool/modules/ShieldModule.sol:336-354:

      base = amount - (amount * feeBP) / 10000
      fee  = amount - base          -- i.e. fee = (amount * feeBP) / 10000

  with BASIS_POINTS = 10000 and production shieldFee = 50 bps.

  This file is the reference spec for reconciling the contract ↔ SDK ↔ spec
  fee mismatch (audit finding C-3): the theorems below pin down exactly what
  the contract computes (boundedness, exact conservation, monotonicity, and
  the rounding-to-zero threshold below which small shields pay no fee).
-/

/-- `BASIS_POINTS` in ShieldModule.sol. All fee rates are expressed in basis
points (1 bp = 1/10000). -/
def BASIS : Nat := 10000

/-- The inclusive fee charged on a shield of `amount` at rate `feeBP`
(ShieldModule.sol:336-354). Integer floor division, Solidity semantics. -/
def shieldFee (feeBP amount : Nat) : Nat := amount * feeBP / BASIS

/-- The amount credited to the pool after the inclusive fee is taken
(ShieldModule.sol:336-354, `base = amount - fee`). -/
def shieldBase (feeBP amount : Nat) : Nat := amount - shieldFee feeBP amount

/--
The fee never exceeds the shielded amount (for any rate of at most 10000 bps).
Plain English: the contract can never charge more than 100% — `base` in
`_getFee` is always well-defined and the subtraction cannot underflow. -/
theorem fee_bounded (feeBP : Nat) (h : feeBP ≤ BASIS) (amount : Nat) :
    shieldFee feeBP amount ≤ amount := by
  unfold shieldFee BASIS
  rw [Nat.div_le_iff_le_mul_add_pred (show 0 < 10000 by omega)]
  have h2 : amount * feeBP ≤ amount * 10000 := Nat.mul_le_mul_left amount h
  omega

/--
Conservation: `base + fee = amount`. Plain English: the fee split is exact —
nothing is minted or burned by `_getFee`; every wei of the shielded amount
ends up either in the pool (`base`) or with the fee recipient (`fee`).
Together with `fee_bounded`, this validates the `base = amount - fee`
subtraction at ShieldModule.sol:336-354. -/
theorem fee_conservation (feeBP : Nat) (h : feeBP ≤ BASIS) (amount : Nat) :
    shieldBase feeBP amount + shieldFee feeBP amount = amount :=
  Nat.sub_add_cancel (fee_bounded feeBP h amount)

/--
The fee is monotone in the shielded amount. Plain English: shielding more can
never reduce the absolute fee charged — no "shield less, pay more" anomaly
that an integrator (SDK/spec, audit C-3) could trip over. -/
theorem fee_monotone (feeBP : Nat) (_h : feeBP ≤ BASIS) {a b : Nat} (hab : a ≤ b) :
    shieldFee feeBP a ≤ shieldFee feeBP b :=
  Nat.div_le_div_right (Nat.mul_le_mul_right feeBP hab)

/--
Rounding threshold: at the production rate of 50 bps, any shield below 200
base units pays a zero fee. Plain English: floor division in
`(amount * 50) / 10000` rounds sub-200-unit shields down to a 0 fee — the
contract effectively allows fee-free dust shields, which the SDK and spec
must reproduce exactly (audit C-3). -/
theorem fee_zero_below_threshold (amount : Nat) (h : amount < 200) :
    shieldFee 50 amount = 0 := by
  have h2 : amount * 50 ≤ 199 * 50 := Nat.mul_le_mul_right 50 (Nat.le_pred_of_lt h)
  unfold shieldFee BASIS
  exact Nat.div_eq_of_lt (by omega)

/--
Closed form at the production rate: 50 bps of `amount` is exactly
`amount / 200` (50/10000 = 1/200). Plain English: the contract's two-step
`(amount * 50) / 10000` computes the same value as a single division by 200 —
the simplification the SDK/spec may use (audit C-3) is exact, not an
approximation. -/
theorem fee_exact_50bps (amount : Nat) : shieldFee 50 amount = amount / 200 := by
  unfold shieldFee BASIS
  have hdm := Nat.div_add_mod amount 200
  have hmod := Nat.mod_lt amount (show 0 < 200 by omega)
  have hdm2 := Nat.div_add_mod (amount * 50) 10000
  have hmod2 := Nat.mod_lt (amount * 50) (show 0 < 10000 by omega)
  apply Nat.le_antisymm
  · rw [Nat.div_le_iff_le_mul_add_pred (show 0 < 10000 by omega)]
    omega
  · rw [Nat.div_le_iff_le_mul_add_pred (show 0 < 200 by omega)]
    omega
