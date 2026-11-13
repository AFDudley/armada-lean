/-
  ArmadaLean.Fee — the inclusive shield fee, as ratio arithmetic on natural numbers.

  `_getFee` (inclusive path) of
  armada-poc/contracts/privacy-pool/modules/ShieldModule.sol:353-371 computes

      fee  = (amount * rate) / BASIS_POINTS
      base = amount - fee

  with floor division. The contract writes the rate in basis points
  (`BASIS_POINTS = 10000`). That is one encoding of a ratio. This file states the rule
  over a ratio `num / den`. The pool does not fix fees once at deployment: the
  pinned contract's `PrivacyPool.setShieldFee`/`setFeeModule`
  (PrivacyPool.sol:404-410, 478-482) let the owner change the fee rate after
  deployment, and `step_feeRatio_frame` models that the fee admin can change
  `PoolState.feeRatio` (see `docs/departures.md`). The contract's rate is the case
  `den = 10000`.

  The pool applies the fee in the shield step (`ArmadaLean.Step.shield`, with the
  deployment rate `PoolState.feeRatio`): the note gets `shieldBase`, the treasury gets
  `shieldFee` (ShieldModule.sol:324-340 local path, :209-218 cross-chain path). An
  earlier version of this model argued the fee per shield in basis points
  directly, instead of as this ratio.
-/

namespace ArmadaLean

/-- The hard cap on the shield fee, in percent of the gross amount. The contract caps the
    fee at `MAX_SHIELD_FEE_BPS = 1000` basis points, that is 10% (armada-poc `64436c14`,
    PrivacyPool.sol:39, checked by `setShieldFee` at :407). The model uses the
    contract's cap, not an earlier 1% placeholder, so a proof about the fee bound
    matches the deployed contract. This is the one place that sets the cap's value.
    `shieldBase_pos` needs `maxFeePercent < 100`. -/
def maxFeePercent : Nat := 10

/-- A fee rate (the deployment sets it; only the fee admin changes it): the
    fraction `num / den`, with `den > 0`,
    `num ≤ den` (a fee never exceeds the amount) and the hard cap `fee_capped`:
    `num / den ≤ maxFeePercent / 100`, matching the contract's cap above. -/
structure FeeRatio where
  num : Nat
  den : Nat
  den_pos : 0 < den
  num_le_den : num ≤ den
  fee_capped : num * 100 ≤ den * maxFeePercent

/-- The inclusive fee charged on a shield of `amount` (ShieldModule.sol:353-371).
    Floor division, Solidity semantics. -/
def shieldFee (r : FeeRatio) (amount : Nat) : Nat := amount * r.num / r.den

/-- The amount that enters the pool after the inclusive fee
    (ShieldModule.sol:353-371, `base = amount - fee`). -/
def shieldBase (r : FeeRatio) (amount : Nat) : Nat := amount - shieldFee r amount

/-- **The fee never exceeds the shielded amount.** `base` in `_getFee` is well defined
    and the subtraction cannot underflow.
    Source: ShieldModule.sol:353-371. -/
theorem fee_bounded (r : FeeRatio) (amount : Nat) : shieldFee r amount ≤ amount := by
  unfold shieldFee
  rw [Nat.div_le_iff_le_mul_add_pred r.den_pos]
  have h2 : amount * r.num ≤ amount * r.den := Nat.mul_le_mul_left amount r.num_le_den
  rw [Nat.mul_comm amount r.den] at h2
  omega

/-- **Conservation: `base + fee = amount`.** The fee split is exact: every unit of the
    shielded amount goes either to the pool (`base`) or to the fee recipient (`fee`).
    Source: the inclusive branch of `_getFee`, `base = amount - (amount * _feeBP) /
    BASIS_POINTS; fee = amount - base` (ShieldModule.sol:362-366), which both shield
    paths call with `_isInclusive = true` (ShieldModule.sol:211, :326). -/
theorem fee_conservation (r : FeeRatio) (amount : Nat) :
    shieldBase r amount + shieldFee r amount = amount :=
  Nat.sub_add_cancel (fee_bounded r amount)

/-- **The fee is monotone in the shielded amount.** Shielding more never reduces the
    absolute fee.
    Source: ShieldModule.sol:353-371. -/
theorem fee_monotone (r : FeeRatio) {a b : Nat} (hab : a ≤ b) :
    shieldFee r a ≤ shieldFee r b :=
  Nat.div_le_div_right (Nat.mul_le_mul_right r.num hab)

/-- **Rounding threshold.** A shield whose `amount * num` is below `den` pays no fee:
    floor division rounds it down to zero. At the contract's 50 basis points
    (`num = 50`, `den = 10000`) this is every amount below 200.
    Source: ShieldModule.sol:353-371. -/
theorem fee_zero_below_threshold (r : FeeRatio) (amount : Nat) (h : amount * r.num < r.den) :
    shieldFee r amount = 0 :=
  Nat.div_eq_of_lt h

/-- **A shield of a positive gross amount creates a note of positive value.** Because the
    fee is capped below 100% (`FeeRatio.fee_capped`, `maxFeePercent < 100`), the floor of
    `x * num / den` is at most `x * maxFeePercent / 100`, which is below `x` for every
    `x > 0`. No larger minimum `x` is needed: floor division only lowers the fee.
    Source: ShieldModule.sol:353-371. -/
theorem shieldBase_pos (r : FeeRatio) {x : Nat} (hx : 0 < x) : 0 < shieldBase r x := by
  have hcap : maxFeePercent < 100 := by decide
  have hdiv : shieldFee r x * r.den ≤ x * r.num := Nat.div_mul_le_self (x * r.num) r.den
  have h1 : shieldFee r x * r.den * 100 ≤ x * maxFeePercent * r.den := by
    calc shieldFee r x * r.den * 100 ≤ x * r.num * 100 := Nat.mul_le_mul_right 100 hdiv
      _ = x * (r.num * 100) := by rw [Nat.mul_assoc]
      _ ≤ x * (r.den * maxFeePercent) := Nat.mul_le_mul_left x r.fee_capped
      _ = x * maxFeePercent * r.den := by rw [Nat.mul_comm r.den, Nat.mul_assoc]
  have h2 : shieldFee r x * 100 ≤ x * maxFeePercent := by
    rw [Nat.mul_right_comm] at h1
    exact Nat.le_of_mul_le_mul_right h1 r.den_pos
  have h3 : x * maxFeePercent < x * 100 := Nat.mul_lt_mul_of_pos_left hcap hx
  have h4 : shieldFee r x < x := by omega
  unfold shieldBase
  omega

end ArmadaLean
