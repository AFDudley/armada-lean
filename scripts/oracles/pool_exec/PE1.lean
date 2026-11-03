/-
  Probe for rule PE1 (contract state), `docs/pool-executable.md`. It elaborates only when
  PE1 holds. Run it from the repo root, after `lake build`:

    python3 scripts/oracles/lean_probe.py scripts/oracles/pool_exec/PE1.lean

  The interface it fixes:
  * `Pool.ContractState`: a structure with exactly six fields, in this order:
    `trees : List TreeState`, `spent : Nat → NullifierSet`, `held : Token → Nat`,
    `preimageOf : PreimageRegistry`, `treasuryFees : Token → Nat`, `feeRatio : FeeRatio`.
  * `PoolState.contract : PoolState → Pool.ContractState`, which keeps those six fields
    of the state and drops `live`, `published` and `payouts`.
-/
import ArmadaLean

-- An unknown name in a binder must be an error, not a new variable.
set_option autoImplicit false

/-- The six fields, in this order and with these types, and no other field: an anonymous
    constructor with six arguments elaborates only for a six-field structure, and each
    projection gives back its own argument. -/
example (trees : List TreeState) (spent : Nat → NullifierSet) (held : Token → Nat)
    (preimageOf : PreimageRegistry) (treasuryFees : Token → Nat) (feeRatio : FeeRatio) :
    let c : Pool.ContractState := ⟨trees, spent, held, preimageOf, treasuryFees, feeRatio⟩
    c.trees = trees ∧ c.spent = spent ∧ c.held = held ∧ c.preimageOf = preimageOf ∧
      c.treasuryFees = treasuryFees ∧ c.feeRatio = feeRatio :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The type of `PoolState.contract`. -/
example : PoolState → Pool.ContractState := PoolState.contract

/-- The field equations of `PoolState.contract`, by `rfl`: the contract state of `s` is the
    six contract fields of `s`. No other field of `s` reaches it, so `live`, `published` and
    `payouts` are dropped. -/
example (s : PoolState) :
    s.contract = ⟨s.trees, s.spent, s.held, s.preimageOf, s.treasuryFees, s.feeRatio⟩ :=
  rfl

/-- `Pool.Step` in `docs/pool-executable.md` is the root-level `Step` of
    `ArmadaLean/Pool.lean`. -/
example : PoolState → PoolState → Prop := Step

/-! ### Axioms

`lean_probe.py` reports each `#print axioms` line. The check after them fails the probe
when a main declaration depends on an axiom other than Lean's three core axioms and the
model's three declared primitives (PE6: no new axiom; `sorryAx` is not allowed). -/

#print axioms PoolState.contract

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound,
    ``EdDSAVerify, ``VerifyAccepts, ``VerifyOwnedAccepts]
  for d in [``PoolState.contract] do
    for a in (← collectAxioms d) do
      unless allowed.contains a do
        throwError m!"{d} depends on the axiom {a}, which is not allowed"
