/-
  ArmadaLean.Vault — share-conversion model of ArmadaYieldVault.sol and the
  first-depositor inflation attack (OPEN critical issue #365).

  Models the conversion math of
  armada-poc/contracts/yield/ArmadaYieldVault.sol:492-515 (integer floor
  division, Solidity semantics):

      _convertToShares(assets):  supply == 0 → assets; userClaimable == 0 → assets;
                                 else (assets * supply) / userClaimable
      _convertToAssets(shares):  supply == 0 → shares;
                                 else (shares * userClaimable) / supply

  and the OpenZeppelin-style mitigation (virtual +1 share / +1 asset offset):

      shares = assets * (supply + 1) / (claimable + 1)
      assets = shares * (claimable + 1) / (supply + 1)

  Theorems:
  * `inflation_attack_victim_gets_nothing` / `inflation_attack_profitable` —
    issue #365 is exploitable, not theoretical: for any donation X and victim
    deposit Y < X+1, the victim receives zero shares and the attacker
    withdraws strictly more than deposited.
  * `mitigated_victim_gets_shares_iff` / `mitigated_attack_unprofitable` —
    with the virtual offset the attack is provably unprofitable: the
    mathematical basis for the #365 fix.
  * `c2s_empty_vault` — honesty check documenting where the vulnerability
    enters: the `supply == 0` branch lets the first depositor set the
    exchange rate.
-/

/-- Current, vulnerable `_convertToShares` (ArmadaYieldVault.sol:492-515). -/
def c2s (supply claimable assets : Nat) : Nat :=
  if supply = 0 then assets else if claimable = 0 then assets else assets * supply / claimable

/-- Current, vulnerable `_convertToAssets` (ArmadaYieldVault.sol:492-515). -/
def c2a (supply claimable shares : Nat) : Nat :=
  if supply = 0 then shares else shares * claimable / supply

/-- Mitigated `_convertToShares`: virtual +1 share / +1 asset offset
(OpenZeppelin-style). The `supply == 0` / `claimable == 0` special cases
become dead code — the denominators can never be zero. -/
def c2sV (supply claimable assets : Nat) : Nat := assets * (supply + 1) / (claimable + 1)

/-- Mitigated `_convertToAssets`: virtual +1 share / +1 asset offset. -/
def c2aV (supply claimable shares : Nat) : Nat := shares * (claimable + 1) / (supply + 1)

/-! ### Explicit attack trace (issue #365)

Step 1 — attacker deposits 1 into the empty vault: `attackAttackerShares`.
Step 2 — attacker donates X directly to the vault: claimable = 1 + X, supply = 1.
Step 3 — victim deposits Y: `attackVictimShares X Y`.
Step 4 — attacker redeems everything: `attackAttackerOut X Y`. -/

/-- Attack step 1: shares minted to the attacker for depositing 1 unit into
the empty vault (hits the `supply == 0` branch, so 1 share). -/
def attackAttackerShares : Nat := c2s 0 0 1

/-- Attack step 3: shares minted to a victim depositing Y after the attacker
has donated X (supply = 1, claimable = 1 + X). -/
def attackVictimShares (X Y : Nat) : Nat := c2s 1 (1 + X) Y

/-- Attack step 4: assets the attacker withdraws by redeeming all of their
shares after the victim's deposit (supply = 1, claimable = 1 + X + Y). -/
def attackAttackerOut (X Y : Nat) : Nat := c2a 1 (1 + X + Y) (c2s 0 0 1)

/--
Honesty check for the empty-vault special case: the first deposit mints one
share per asset. This documents exactly where the vulnerability enters — the
`supply == 0` branch at ArmadaYieldVault.sol:492-515 is what lets the first
depositor set the exchange rate (and then distort it via a donation). -/
theorem c2s_empty_vault : c2s 0 0 assets = assets := by simp [c2s]

/--
The victim gets nothing. After the attacker deposits 1 (receiving 1 share)
and donates X, a victim depositing Y < X + 1 receives
`Y * 1 / (1 + X) = 0` shares: their entire deposit accrues to the attacker.

Confirms issue #365 is exploitable, not theoretical. -/
theorem inflation_attack_victim_gets_nothing {X Y : Nat} (_hY : 1 ≤ Y) (hlt : Y < X + 1) :
    c2s 1 (1 + X) Y = 0 := by
  unfold c2s
  rw [if_neg (by omega), if_neg (by omega)]
  exact Nat.div_eq_of_lt (by omega)

/--
The attack is profitable. The attacker deposited 1 and donated X (total cost
1 + X); after a victim deposit of Y ≥ 1 they redeem their 1 share for
`1 * (1 + X + Y) / 1 = 1 + X + Y > 1 + X` — strictly more than deposited,
the difference being the victim's entire deposit.

Confirms issue #365 is exploitable, not theoretical: for any donation X and
victim deposit Y < X+1, the victim receives zero shares
(`inflation_attack_victim_gets_nothing`) and the attacker withdraws strictly
more than deposited. -/
theorem inflation_attack_profitable {X Y : Nat} (_hX : 1 ≤ X) (hY : 1 ≤ Y) (_hlt : Y < X + 1) :
    c2a 1 (1 + X + Y) (c2s 0 0 1) > 1 + X := by
  have hs : c2s 0 0 1 = 1 := c2s_empty_vault
  rw [hs]
  unfold c2a
  rw [if_neg (by omega), Nat.one_mul, Nat.div_one]
  omega

/--
With the virtual offset, the victim receives zero shares **iff**
`Y * (a + 1) < a + X + 1`, where `a` is the attacker's initial deposit and X
the donation. Plain English: for the attack to work at all, the attacker must
now donate more than (approximately) the victim's deposit times (a + 1) —
the required donation scales with the victim's deposit, unlike the current
code where any X ≥ Y suffices. -/
theorem mitigated_victim_gets_shares_iff {a X Y : Nat} :
    c2sV a (a + X) Y = 0 ↔ Y * (a + 1) < a + X + 1 := by
  unfold c2sV
  rw [Nat.div_eq_zero_iff]
  constructor
  · intro h
    cases h with
    | inl h => omega
    | inr h => exact h
  · intro h
    exact Or.inr h

/--
With a virtual offset of 1 share / 1 asset, the first-depositor inflation
attack is provably unprofitable: even in the worst case where the victim gets
0 shares, the attacker (who deposited `a ≥ 1` and donated X) withdraws no
more than `a + X` — they cannot recover more than they put in. This is the
mathematical basis for the #365 fix. -/
theorem mitigated_attack_unprofitable {a X Y : Nat} (ha : 1 ≤ a)
    (hzero : c2sV a (a + X) Y = 0) :
    c2aV a (a + X + Y) a ≤ a + X := by
  -- From hzero: Y * (a + 1) < a + X + 1, hence Y * (a + 1) ≤ a + X.
  have hYb : Y * (a + 1) ≤ a + X := by
    have h := mitigated_victim_gets_shares_iff.mp hzero
    omega
  -- Therefore a * Y ≤ (a + 1) * Y = Y * (a + 1) ≤ a + X.
  have hmul : a * Y ≤ a + X := by
    have h1 : a * Y ≤ (a + 1) * Y := Nat.mul_le_mul_right Y (Nat.le_succ a)
    rw [Nat.mul_comm (a + 1) Y] at h1
    exact Nat.le_trans h1 hYb
  unfold c2aV
  rw [Nat.div_le_iff_le_mul_add_pred (show 0 < a + 1 by omega)]
  -- Goal: a * (a + X + Y + 1) ≤ (a + 1) * (a + X) + (a + 1 - 1).
  -- Expand both sides; the nonlinear atoms a*a, a*X cancel, leaving a*Y ≤ a+X.
  have e1 : a * (a + X + Y + 1) = a * a + a * X + a * Y + a := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have e2 : (a + 1) * (a + X) + (a + 1 - 1) = a * a + a * X + (a + X) + a := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega
  rw [e1, e2]
  omega
