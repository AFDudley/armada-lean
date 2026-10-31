/-
  Refined channel types. `docs/lean/typed-library.md` §4, row `Channel.lean`.
  Each type replaces a loose `Prop` hypothesis that more than one Nitro
  statement repeated (`docs/lean/typed-library.md` rule 1).
-/
import ArmadaLean.Nitro.Constructions

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-! ## `TimedChannel`: a challenge duration that covers two round delays -/

/-- The fact `TimedChannel` wraps: `c`'s challenge duration covers two
    network delays of `ε`. Operator ruling 2026-10-31: `2 * ε` is
    sufficient for the Liveness proofs; the factor 2 comes from the round
    model, `docs/nitro-repair-2026-10-27.md:38-42`. `docs/lean/typed-library.md`
    §4, row `Channel.lean`. -/
def FixedPart.IsTimed (c : FixedPart) (ε : Time) : Prop := 2 * ε ≤ c.challengeDuration

instance (c : FixedPart) (ε : Time) : Decidable (c.IsTimed ε) :=
  inferInstanceAs (Decidable (2 * ε ≤ c.challengeDuration))

/-- A channel whose challenge duration covers two round delays of `ε`
    (`FixedPart.IsTimed`). `docs/lean/typed-library.md` §4, row
    `Channel.lean`. -/
def TimedChannel (ε : Time) : Type := {c : FixedPart // c.IsTimed ε}

namespace TimedChannel

variable {ε : Time}

/-- Coercion to the carrier (`writing-lean.md` §3, rule 2 of
    `typed-library.md`). -/
instance : CoeOut (TimedChannel ε) FixedPart := ⟨Subtype.val⟩

@[simp] theorem dur_le (c : TimedChannel ε) : 2 * ε ≤ (c : FixedPart).challengeDuration := c.property

/-- Decidable smart constructor (`typed-library.md` rule 2): `none` when
    `c`'s challenge duration is too short for `ε`. -/
def ofFixedPart? (c : FixedPart) (ε : Time) : Option (TimedChannel ε) :=
  if h : c.IsTimed ε then some ⟨c, h⟩ else none

@[simp] theorem ofFixedPart?_eq_some_iff {c : FixedPart} {ε : Time} {t : TimedChannel ε} :
    ofFixedPart? c ε = some t ↔ (t : FixedPart) = c := by
  unfold ofFixedPart?
  split
  · constructor
    · intro h; cases h; rfl
    · intro h; cases t with
      | mk tc htc => cases h; rfl
  · constructor
    · intro h; cases h
    · intro h; subst h; rename_i hcon; exact absurd t.property hcon

end TimedChannel

/-! ## `LedgerChannel`: the ledger encoding `IsLedgerChannel` already decides -/

/-
  `c.kind = .ledger` and `IsLedgerChannel apps c` (`c.kind = .ledger ∧
  apps c.appDef = consensusRules`, `Constructions.lean`) are NOT equivalent
  on a reachable state. Checked (`.scratch/ledger_disagreement_check.lean`,
  `lake env lean` clean): let `apps1 := fun _ => noRules` where `noRules :
  Rules Nat` never supports anything, and let `c0 : FixedPart := ⟨[], 0,
  ⟨0⟩, 2, .ledger⟩`. One `deposit` reaches a state `s1` where `c0` holds a
  real balance (`s1.balances.get c0.address = 1`) and `Reachable apps1 s1`
  holds. At `s1`, `c0.kind = .ledger` holds, but `IsLedgerChannel apps1 c0`
  does not: `apps1` never maps `c0.appDef` to `consensusRules`. This
  disagreement is reported, not resolved by this file: `deposit`,
  `transfer` and `reclaim` (`Adjudicator.lean`) take no `apps` argument and
  decide "ledger" from `kind` alone, a strictly lower-level, `apps`-free
  notion than `IsLedgerChannel`. No statement moved to `LedgerChannel`
  (`ledger_partial_withdrawal`, the one Liveness.lean use of
  `IsLedgerChannel`) reads the `kind`-only notion; the `Adjudicator.lean`
  operations and their Safety.lean theorems keep reading `kind` directly,
  unchanged by this file.
-/

/-- One encoding of "ledger channel": `kind` and `appDef` must agree
    (`IsLedgerChannel`, `Constructions.lean`, operator ruling 2026-10-27,
    SATP §1 SATP:79-84). `docs/lean/typed-library.md` §4, row `Channel.lean`.
    See the note above: this is a different, stronger fact than the
    `kind`-only notion `Adjudicator.lean`'s `deposit`/`transfer`/`reclaim`
    decide; it is the one `ledger_partial_withdrawal` needs. -/
structure LedgerChannel (apps : Apps E) where
  channel : FixedPart
  isLedger : IsLedgerChannel apps channel

namespace LedgerChannel

variable {apps : Apps E}

/-- Coercion to the carrier (`writing-lean.md` §3, rule 2 of
    `typed-library.md`). -/
instance : CoeOut (LedgerChannel apps) FixedPart := ⟨LedgerChannel.channel⟩

@[simp] theorem kind_eq (c : LedgerChannel apps) : (c : FixedPart).kind = .ledger := c.isLedger.1

@[simp] theorem appDef_eq (c : LedgerChannel apps) :
    apps (c : FixedPart).appDef = consensusRules := c.isLedger.2

-- No decidable smart constructor: `IsLedgerChannel`'s second conjunct,
-- `apps c.appDef = consensusRules`, is an equation on `Rules E`, a type
-- with no `DecidableEq` instance (`Rules.supports` is an arbitrary
-- function; `typed-library.md` rule 2 makes the constructor conditional
-- on decidability).

end LedgerChannel

end ArmadaLean.Nitro
