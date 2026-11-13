/-
  ArmadaLean.Types.Address — a 160-bit EVM address, as a refined type.

  `TransactOwnedPublic.ownerField` is a 160-bit address.
  The circuit takes `ownerField = uint256(uint160(owner))` from the calling contract
  (TransactOwned.circom:13-14). The on-chain verifier checks `ownerField` against
  `msg.sender`. So the value is the number of an address, below `2^160`, embedded as
  `Term.val`. It is never a hash term (`Term.val_ne_hash`, `ArmadaLean.Poseidon`).

  API: the coercion to the
  carrier `Nat`, the bound (`Address.lt`), the decidable smart constructor
  (`Address.ofNat?`) and decidable equality.
-/
import ArmadaLean.Poseidon

namespace ArmadaLean

/-- A 160-bit EVM address: a number below `2^160` (`uint160`). -/
def Address : Type := {a : Nat // a < 2 ^ 160}

namespace Address

/-- Coercion to the carrier (`typed-library.md` §3 rule 2). -/
instance : CoeOut Address Nat := ⟨Subtype.val⟩

instance : DecidableEq Address := inferInstanceAs (DecidableEq {a : Nat // a < 2 ^ 160})

@[simp] theorem lt (a : Address) : (a : Nat) < 2 ^ 160 := a.property

@[ext] theorem ext {a b : Address} (h : (a : Nat) = b) : a = b := Subtype.ext h

/-- Decidable smart constructor (`typed-library.md` rule 2): `none` when `a` does not
    fit in 160 bits. -/
def ofNat? (a : Nat) : Option Address := if h : a < 2 ^ 160 then some ⟨a, h⟩ else none

@[simp] theorem ofNat?_eq_some_iff {a : Nat} {x : Address} :
    ofNat? a = some x ↔ (x : Nat) = a := by
  unfold ofNat?
  split
  · constructor
    · intro h; cases h; rfl
    · intro h; cases x with
      | mk v hv => cases h; rfl
  · constructor
    · intro h; cases h
    · intro h; subst h; rename_i hcon; exact absurd x.property hcon

/-- The field element of an address is never a hash term (`Term.val_ne_hash`). The fact
    `TransactOwned.user_npk_ne_contract_npk` rests on. -/
theorem val_ne_hash (a : Address) (fn : HashFn) (l : List Term) :
    Term.val a ≠ Term.hash fn l :=
  Term.val_ne_hash a fn l

end Address

end ArmadaLean
