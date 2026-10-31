/-
  ArmadaLean.Fee — the inclusive shield fee, as ratio arithmetic on natural numbers.

  `_getFee` (inclusive path) of
  armada-poc/contracts/privacy-pool/modules/ShieldModule.sol:353-371 computes

      fee  = (amount * rate) / BASIS_POINTS
      base = amount - fee

  with floor division. The contract writes the rate in basis points
  (`BASIS_POINTS = 10000`). That is one encoding of a ratio. This file states the rule
  over a ratio `num / den` that the deployment fixes once (labbook
  `2026-10-18-contract-owned-notes-and-zk-channel-apps.md`, decision 7: the pool "sets
  verifying keys and fees once at deployment"). The contract's rate is the case
  `den = 10000`.

  The pool applies the fee in the shield step (`ArmadaLean.Pool.Step.shield`, with the
  deployment rate `PoolState.feeRatio`): the note gets `shieldBase`, the treasury gets
  `shieldFee` (ShieldModule.sol:324-340 local path, :209-218 cross-chain path). Audit
  finding P-9 (armada-laconic `labbook/2026-10-26-pool-layout-audit.md`) records the
  earlier per-shield basis-point argument.
-/

/-- The hard cap on the shield fee, in percent of the gross amount. Operator ruling,
    2026-10-27: the shield fee is never 100%; it has a hard cap, probably 1%. This is the
    one place that sets the cap's value. `shieldBase_pos` needs `maxFeePercent < 100`. -/
def maxFeePercent : Nat := 1

/-- A fee rate fixed at deployment: the fraction `num / den`, with `den > 0`,
    `num ≤ den` (a fee never exceeds the amount) and the hard cap `fee_capped`:
    `num / den ≤ maxFeePercent / 100` (operator ruling, 2026-10-27). -/
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
    and the subtraction cannot underflow. -/
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
    absolute fee. -/
theorem fee_monotone (r : FeeRatio) {a b : Nat} (hab : a ≤ b) :
    shieldFee r a ≤ shieldFee r b :=
  Nat.div_le_div_right (Nat.mul_le_mul_right r.num hab)

/-- **Rounding threshold.** A shield whose `amount * num` is below `den` pays no fee:
    floor division rounds it down to zero. At the contract's 50 basis points
    (`num = 50`, `den = 10000`) this is every amount below 200. -/
theorem fee_zero_below_threshold (r : FeeRatio) (amount : Nat) (h : amount * r.num < r.den) :
    shieldFee r amount = 0 :=
  Nat.div_eq_of_lt h

/-- **A shield of a positive gross amount creates a note of positive value.** Because the
    fee is capped below 100% (`FeeRatio.fee_capped`, `maxFeePercent < 100`), the floor of
    `x * num / den` is at most `x * maxFeePercent / 100`, which is below `x` for every
    `x > 0`. No larger minimum `x` is needed: floor division only lowers the fee. -/
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
