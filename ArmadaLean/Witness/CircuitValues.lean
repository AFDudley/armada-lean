/-
  Shared example values for the circuit-model witnesses of
  `ArmadaLean/BoundParams.lean`, `Fee.lean`, `RangeCheck.lean` and
  `TransactOwned.lean` (`docs/spec-module-design.md` §5). One term, one
  token, one fee ratio and one 120-bit decomposition of `0`, so each witness
  file builds its concrete instance from the same values.
-/
import ArmadaLean.BoundParams
import ArmadaLean.Fee
import ArmadaLean.Token
import ArmadaLean.RangeCheck

namespace ArmadaLean.Witness.CircuitValues

/-- A term with no internal structure: every witness that needs one `Term`
    and reads nothing off it uses this one. -/
def t0 : Term := Term.val 0

/-- A token over `t0`. -/
def token0 : Token := ⟨t0⟩

/-- Bound parameters with no unshield and no adapt contract. -/
def bp0 : BoundParams := ⟨0, none, none, t0⟩

/-- A fee ratio of `0/1`: `den_pos`, `num_le_den` and `fee_capped` all hold by
    `decide` (`fee_capped` reads `0 * 100 ≤ 1 * maxFeePercent`). -/
def feeRatio0 : FeeRatio := ⟨0, 1, by decide, by decide, by decide⟩

/-- A 120-bit decomposition of `0`: every bit `false`. -/
def bits0 : List Bool := List.replicate 120 false

theorem bitsVal_replicate_false (n : Nat) : bitsVal (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bitsVal, ih]

/-- `0` passes the `Num2Bits(120)` range check, witnessed by `bits0`. -/
theorem bits0_range : RangeChecked120 0 :=
  ⟨bits0, by simp [bits0], (bitsVal_replicate_false 120).symm⟩

end ArmadaLean.Witness.CircuitValues
