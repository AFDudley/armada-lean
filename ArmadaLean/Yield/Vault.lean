/-
  ArmadaLean.Yield.Vault — share-conversion model of the FIXED ArmadaYieldVault.sol.

  **Pinned version.** `armada-poc` `origin/main` commit `64436c14`, file
  `contracts/yield/ArmadaYieldVault.sol`, git blob `8859da5c`. That file state
  includes two merged PRs:
  * PR #631 (commit `04753139`), "stop the first-depositor share-inflation
    attack on ArmadaYieldVault" (issue #365): locks `LOCKED_SHARES = 1e6`
    shares to the dead address `LOCKED_SHARES_HOLDER` on the first deposit.
  * PR #632 (commit `6e38fddd`), "remove the vault's per-holder cost-basis
    bookkeeping": does not change the conversion math or the lock this file
    models.
  `armada-poc`'s own `integrated` branch still has the PRE-fix vault (blob
  `721b38e5`); never cite that branch's file.

  Models the conversion math, unchanged by PR #631's fix, at
  `ArmadaYieldVault.sol:491-514` (integer floor division, Solidity
  semantics):

      _convertToShares(assets):  supply == 0 → assets; userClaimable == 0 → assets;
                                 else (assets * supply) / userClaimable
      _convertToAssets(shares):  supply == 0 → shares;
                                 else (shares * userClaimable) / supply

  and the fix itself, the first-deposit lock in `deposit`
  (`ArmadaYieldVault.sol:285-290`): on the first deposit (`totalSupply() == 0`)
  the contract requires `shares > LOCKED_SHARES`, mints `LOCKED_SHARES` to
  the dead address `LOCKED_SHARES_HOLDER`, and gives the receiver the rest.

  **Known pending change.** The operator plans to move the contract to a
  version that does not round the conversion and instead returns the change,
  which conserves value exactly. That version does not exist yet and this
  file does not model it. `c2s` and `c2a` below are the ONLY two definitions
  of the share/asset conversion in this file; every theorem uses them, never
  its own copy of the arithmetic. So the later switch is a change to `c2s`
  and `c2a` alone. The theorems below are split into two sections precisely
  for that cutover: "independent of the rounding rule" (true of both the
  current floor-division contract and the future give-change one, since they
  never read `c2s`/`c2a` past the `supply = 0` case) and "depend on the
  rounding rule" (state a floor-division bound; a give-change version would
  need new statements, proved differently, not a patch to these ones).

  Theorems, proving the fixed contract's own NatSpec claims
  (`ArmadaYieldVault.sol:74-85`):
  * `locked_shares_set_at_first_deposit` / `locked_shares_supply_invariant` —
    total supply never drops below `LOCKED_SHARES` after the first deposit
    (the base case and the inductive step of that invariant).
  * `round_trip_loss_le` / `donation_loss_bound` — a depositor's rounding
    loss from a donation `X` is at most `X / LOCKED_SHARES + 2` — the exact
    integer bound the floor division gives, not the NatSpec's `~` estimate.
  * `donation_attack_unprofitable` — the donation attack cannot profit: an
    attacker who donates `X` and holds `s` shares out of total supply `S`
    recovers at most `X + s` whenever `s < S`. Since `LOCKED_SHARES` is
    permanently held by the dead address, the attacker can never hold the
    full supply after the fix (`s ≤ S - LOCKED_SHARES`), so this condition
    always holds post-fix — the attacker can approach breakeven but never
    exceed it, for any `X` or any victim deposit.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ArmadaLean

/-- `LOCKED_SHARES` (`ArmadaYieldVault.sol:81`): shares the first deposit
locks forever to the dead address `LOCKED_SHARES_HOLDER`
(`ArmadaYieldVault.sol:85`), the defense against the first-depositor
share-inflation attack (#365, PR #631). -/
def LOCKED_SHARES : Nat := 1000000

/-- `_convertToShares` (`ArmadaYieldVault.sol:491-501`). The one definition
of the share side of the conversion: every theorem below reads it from here,
never its own copy. A future switch to a give-change, non-rounding version
is a change to this definition alone. -/
def c2s (supply claimable assets : Nat) : Nat :=
  if supply = 0 then assets else if claimable = 0 then assets else assets * supply / claimable

/-- `_convertToAssets` (`ArmadaYieldVault.sol:503-514`). The one definition
of the asset side of the conversion; see `c2s`. -/
def c2a (supply claimable shares : Nat) : Nat :=
  if supply = 0 then shares else shares * claimable / supply

/-! ### Theorems independent of the rounding rule

Each of these reads `c2s`/`c2a` only through the `supply = 0` branch (a
direct pass-through, no division) or not at all. A future give-change
`c2s`/`c2a` keeps that branch, so these statements and proofs do not change
when the conversion rule changes. -/

/--
Honesty check for the empty-vault special case (`ArmadaYieldVault.sol:
491-494`): the first deposit's pre-lock share count is one-for-one with the
deposited assets. This is the input `deposit` (`ArmadaYieldVault.sol:282,
285-289`) feeds into the `LOCKED_SHARES` lock. -/
theorem c2s_empty_vault {assets : Nat} : c2s 0 0 assets = assets := by simp [c2s]

/-- Shares the first deposit would mint before the lock
(`ArmadaYieldVault.sol:282`: `shares = _convertToShares(assets)` on an empty
vault hits the `supply == 0` branch, so 1 asset buys 1 share). -/
def firstDepositShares (assets : Nat) : Nat := c2s 0 0 assets

/-- Shares the receiver of the first deposit is minted, after the
`LOCKED_SHARES` lock (`ArmadaYieldVault.sol:287-289`: `shares -=
LOCKED_SHARES`, guarded by `require(shares > LOCKED_SHARES)`). -/
def firstDepositReceiverShares (assets : Nat) : Nat := firstDepositShares assets - LOCKED_SHARES

/-- Total supply right after the first deposit: the locked holder's
`LOCKED_SHARES` plus the receiver's shares (`ArmadaYieldVault.sol:288-289,
302`: `_mint(LOCKED_SHARES_HOLDER, LOCKED_SHARES)` then `_mint(receiver,
shares)`). -/
def firstDepositSupply (assets : Nat) : Nat := LOCKED_SHARES + firstDepositReceiverShares assets

/--
**Claim (a), base case.** After a valid first deposit (`require(shares >
LOCKED_SHARES)`, `ArmadaYieldVault.sol:287`), total supply equals the
deposited assets one-for-one, and so it exceeds `LOCKED_SHARES`
(`ArmadaYieldVault.sol:74-81, 285-290`: the NatSpec claim that total supply
never drops below `LOCKED_SHARES` starts here). -/
theorem locked_shares_set_at_first_deposit {assets : Nat} (h : assets > LOCKED_SHARES) :
    firstDepositSupply assets = assets ∧ firstDepositSupply assets > LOCKED_SHARES := by
  unfold firstDepositSupply firstDepositReceiverShares firstDepositShares
  rw [c2s_empty_vault]
  omega

/--
**Claim (a), inductive step.** `LOCKED_SHARES_HOLDER` is a dead address
nobody holds a key for (`ArmadaYieldVault.sol:83-85`), so its `LOCKED_SHARES`
balance is never the one a later `redeem`/transfer burns: every burn is
bounded by the non-locked ("extra") balance outstanding. Combined with the
base case above, this is the full induction behind the NatSpec claim that
total supply never drops below `LOCKED_SHARES` (`ArmadaYieldVault.sol:
74-81`). -/
theorem locked_shares_supply_invariant {extra burn : Nat} (hburn : burn ≤ extra) :
    LOCKED_SHARES + extra - burn ≥ LOCKED_SHARES := by omega

/-! ### Theorems that depend on the rounding rule

Each of these states a bound that comes from floor division, through
`c2s`/`c2a`'s general (`supply ≠ 0`) branch. A future give-change conversion
needs new statements here, proved against the new `c2s`/`c2a`; these are not
reusable as lemmas of the new rule. -/

/--
**Round-trip rounding-loss bound**, for any supply `S > 0` and claimable
`C > 0` (`ArmadaYieldVault.sol:491-514`: `_convertToShares`/
`_convertToAssets`, the same floor division on both legs): depositing `Y` and
immediately redeeming the resulting shares back returns at most `Y`, and the
loss is at most `C / S + 1` — the exact bound two floor divisions give, not
an approximation. -/
theorem round_trip_loss_le (S C Y : Nat) (hS : 0 < S) (hC : 0 < C) :
    let shares := Y * S / C
    let redemption := shares * C / S
    redemption ≤ Y ∧ Y - redemption ≤ C / S + 1 := by
  intro shares redemption
  have h1 : C * shares + Y * S % C = Y * S := Nat.div_add_mod (Y * S) C
  have h2 : S * redemption + shares * C % S = shares * C := Nat.div_add_mod (shares * C) S
  have hr1 : Y * S % C < C := Nat.mod_lt _ hC
  have hr2 : shares * C % S < S := Nat.mod_lt _ hS
  have hmul : S * redemption ≤ S * Y := by
    have e1 : C * shares = shares * C := Nat.mul_comm C shares
    have e2 : Y * S = S * Y := Nat.mul_comm Y S
    omega
  have hle : redemption ≤ Y := Nat.le_of_mul_le_mul_left hmul hS
  refine ⟨hle, ?_⟩
  have hceq : S * (C / S) + C % S = C := Nat.div_add_mod C S
  have hr3 : C % S < S := Nat.mod_lt _ hS
  have hdiffS : S * (Y - redemption) + 1 ≤ C + S := by
    have e1 : C * shares = shares * C := Nat.mul_comm C shares
    have e2 : Y * S = S * Y := Nat.mul_comm Y S
    have : S * (Y - redemption) = S * Y - S * redemption := by rw [Nat.mul_sub]
    omega
  nlinarith [hdiffS, hceq, hr3]

/--
**Claim (b).** A depositor's rounding loss from a donation `X`
(`ArmadaYieldVault.sol:74-81` NatSpec: "a depositor loses at most ~donation /
LOCKED_SHARES"): if supply `S ≥ LOCKED_SHARES` prices 1:1 against claimable
(`claimable = S`, as it does right after the lock-respecting first deposit)
and a donation `X` then inflates claimable to `S + X`, a deposit of `Y`
right after loses at most `X / LOCKED_SHARES + 2` on round-trip. The
NatSpec's `~` hides this `+ 2`; it is not a weaker bound, it is the exact one
`round_trip_loss_le`'s floor division gives, monotone in `S ≥ LOCKED_SHARES`
(`Nat.div_le_div_left`). -/
theorem donation_loss_bound (S X Y : Nat) (hS : LOCKED_SHARES ≤ S) :
    let shares := c2s S (S + X) Y
    let redemption := c2a S (S + X) shares
    Y - redemption ≤ X / LOCKED_SHARES + 2 := by
  have hSpos : 0 < S := by unfold LOCKED_SHARES at hS; omega
  have hLpos : 0 < LOCKED_SHARES := by unfold LOCKED_SHARES; omega
  have hCpos : 0 < S + X := by omega
  have hgen := round_trip_loss_le S (S + X) Y hSpos hCpos
  simp only [c2s, c2a, if_neg (by omega : ¬ S = 0), if_neg (by omega : ¬ S + X = 0)]
  obtain ⟨_, hbound⟩ := hgen
  have hdiv : (S + X) / S = X / S + 1 := by
    rw [Nat.add_comm S X, Nat.add_div_right X hSpos]
  have hmono : X / S ≤ X / LOCKED_SHARES := Nat.div_le_div_left hS hLpos
  omega

/--
**Claim (c).** The donation attack cannot profit: for any supply `S > 0`, a
holder of `s < S` shares who donates `X` (inflating claimable from `S` to
`S + X`) and then lets a victim deposit `Y` before redeeming all `s` shares
recovers at most `X + s` — never more than the donation plus the shares'
starting value (`ArmadaYieldVault.sol:74-81, 491-514`). The exact condition
is `s < S`, not holding the whole supply: `LOCKED_SHARES_HOLDER`
(`ArmadaYieldVault.sol:83-85`) permanently keeps `LOCKED_SHARES` of `S` out
of every attacker's reach, so `s < S` always holds after the fix
(`donation_attack_unprofitable_post_fix` below) — the attacker can approach
breakeven but never exceed it. -/
theorem donation_attack_unprofitable
    (S X Y s : Nat) (hS : 0 < S) (hs : s < S) :
    let v := c2s S (S + X) Y
    c2a (S + v) (S + X + Y) s ≤ X + s := by
  have hSXne : ¬ S + X = 0 := by omega
  have hSne : ¬ S = 0 := by omega
  simp only [c2s, if_neg hSne, if_neg hSXne]
  set v := Y * S / (S + X) with hvdef
  have hSX : 0 < S + X := by omega
  have hb : 0 < S + v := Nat.lt_of_lt_of_le hS (Nat.le_add_right S v)
  have hSvne : ¬ S + v = 0 := by omega
  simp only [c2a, if_neg hSvne]
  rw [Nat.div_le_iff_le_mul_add_pred hb]
  have hr : Y * S % (S + X) < S + X := Nat.mod_lt _ hSX
  have heq : (S + X) * v + Y * S % (S + X) = Y * S := Nat.div_add_mod (Y * S) (S + X)
  set r := Y * S % (S + X) with hrdef
  have hSY : S * Y = (S + X) * v + r := by rw [Nat.mul_comm S Y]; exact heq.symm
  have hgoalS : S * (s * (S + X + Y)) + S ≤ S * ((S + v) * (X + s) + (S + v)) := by
    clear_value v r
    clear heq hb hvdef
    obtain ⟨e, rfl⟩ : ∃ e, S = s + e + 1 := ⟨S - s - 1, by omega⟩
    have hr' : r ≤ s + e + X := by omega
    have hSYs : s * ((s + e + 1) * Y) = s * ((s + e + 1 + X) * v + r) := by rw [hSY]
    have hsr : s * r ≤ s * (s + e + X) := Nat.mul_le_mul_left s hr'
    nlinarith [hSYs, hsr, mul_nonneg (mul_nonneg (Nat.zero_le X) (Nat.zero_le e)) (Nat.zero_le v),
               mul_nonneg (Nat.zero_le e) (Nat.zero_le v), mul_nonneg (Nat.zero_le s) (Nat.zero_le v),
               Nat.zero_le v, sq_nonneg e, mul_nonneg (Nat.zero_le X) (Nat.zero_le e)]
  have heq2 : S * (s * (S + X + Y) + 1) = S * (s * (S + X + Y)) + S := by ring
  have hfin := Nat.le_of_mul_le_mul_left (heq2 ▸ hgoalS) hS
  clear hSXne hSne hvdef hSX hb hSvne hr heq hrdef hSY hgoalS heq2
  omega

/--
`donation_attack_unprofitable`, specialized to the fixed contract's own
invariant: supply `S ≥ LOCKED_SHARES` and an attacker whose shares `s`
satisfy `s ≤ S - LOCKED_SHARES` (`ArmadaYieldVault.sol:74-85` — the dead
holder's `LOCKED_SHARES` is never the attacker's, so this is every reachable
state after the fix). `S` and `S + X` stand for the supply and claimable assets
before and after the donation: this states the attack from a 1:1 share price
(`claimable = supply`, no pending protocol fee owed), the state `c2s`/`c2a` take as
their starting `claimable` argument; it does not model `pendingProtocolFee()`
(`ArmadaYieldVault.sol`). Under that start, the donation attack cannot profit, for any
donation `X` and any victim deposit `Y`. -/
theorem donation_attack_unprofitable_post_fix
    (S X Y s : Nat) (hS : LOCKED_SHARES ≤ S) (hs : s ≤ S - LOCKED_SHARES) :
    let v := c2s S (S + X) Y
    c2a (S + v) (S + X + Y) s ≤ X + s := by
  have hSpos : 0 < S := by unfold LOCKED_SHARES at hS; omega
  have hLpos : 0 < LOCKED_SHARES := by unfold LOCKED_SHARES; omega
  exact donation_attack_unprofitable S X Y s hSpos (by omega)

end ArmadaLean
