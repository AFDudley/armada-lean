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

  The fee leg moves from the caller's wallet to the treasury and never passes through
  the pool (`ArmadaLean.Pool`, module comment). So the pool's books see only `base`,
  and `Step.shield` takes the value that enters the pool. This file is the separate
  specification of how `base` follows from the gross amount. Audit finding P-9
  (armada-laconic `labbook/2026-10-26-pool-layout-audit.md`) records the earlier
  per-shield basis-point argument.
-/

/-- A fee rate fixed at deployment: the fraction `num / den`, with `den > 0` and
    `num ≤ den` (a fee never exceeds the amount). -/
structure FeeRatio where
  num : Nat
  den : Nat
  den_pos : 0 < den
  num_le_den : num ≤ den

/-- The inclusive fee charged on a shield of `amount` (ShieldModule.sol:353-371).
    Floor division, Solidity semantics. -/
def shieldFee (r : FeeRatio) (amount : Nat) : Nat := amount * r.num / r.den

/-- The amount that enters the pool after the inclusive fee
    (ShieldModule.sol:353-371, `base = amount - fee`). -/
def shieldBase (r : FeeRatio) (amount : Nat) : Nat := amount - shieldFee r amount

/-- **The fee never exceeds the shielded amount.** `base` in `_getFee` is well defined
    and the subtraction cannot underflow. -/
theorem fee_bounded (r : FeeRatio) (amount : Nat) : shieldFee r amount ≤ amount := by
  sorry

/-- **Conservation: `base + fee = amount`.** The fee split is exact: every unit of the
    shielded amount goes either to the pool (`base`) or to the fee recipient (`fee`). -/
theorem fee_conservation (r : FeeRatio) (amount : Nat) :
    shieldBase r amount + shieldFee r amount = amount := by
  sorry

/-- **The fee is monotone in the shielded amount.** Shielding more never reduces the
    absolute fee. -/
theorem fee_monotone (r : FeeRatio) {a b : Nat} (hab : a ≤ b) :
    shieldFee r a ≤ shieldFee r b := by
  sorry

/-- **Rounding threshold.** A shield whose `amount * num` is below `den` pays no fee:
    floor division rounds it down to zero. At the contract's 50 basis points
    (`num = 50`, `den = 10000`) this is every amount below 200. -/
theorem fee_zero_below_threshold (r : FeeRatio) (amount : Nat) (h : amount * r.num < r.den) :
    shieldFee r amount = 0 := by
  sorry
