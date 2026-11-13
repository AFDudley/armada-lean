/-
  ArmadaLean.BoundParams — the bound parameters of a transaction, as symbolic data.

  `BoundParams` (PoolTypes.sol:105-113) is the part of a transaction that the proof
  binds through the public input `boundParamsHash`. The contract computes that input
  as `keccak256(abi.encode(core)) % SNARK_SCALAR_FIELD` (`hashBoundParams`,
  VerifierModule.sol:71-73). This module keeps the hash symbolic: `hashBoundParams`
  is a Keccak `Term` of the parameters (`ArmadaLean.Poseidon`), so two different
  parameter records never give the same hash (`hashBoundParams_inj`). The ABI
  encoding and the `% p` reduction belong to the current contract. The rewrite
  does not keep the `% p` reduction: it encodes the hash as the low 248 bits
  of the Keccak output. This model represents neither. An earlier version of
  this model used a plain `boundParamsHash : Nat` field instead of this
  symbolic encoding.

  The record holds the fields that the pool reads:
  * `treeNumber`: the tree that every input's Merkle proof and nullifier names
    (`_validateTransaction`, TransactModule.sol:315; `_accumulateAndNullify`,
    TransactModule.sol:394).
  * `unshield`: an optional payout of an amount to a recipient address (finding P-7,
    see `Unshield`).
  * `adaptContract`: an optional contract that alone may submit the transaction
    (`_validateTransaction`, TransactModule.sol:301-307). "No adapt contract" is
    `none`, not the zero address (finding P-4).
  * `adaptParams`: data that the adapt contract reads. Armada puts a channel's
    deposit data here. The pool does not read it.

  `minGasPrice`, `chainID` and `commitmentCiphertext` are bound by the same hash in the
  contract. The model has one chain, no gas and no ciphertexts, so it omits them.
-/
import ArmadaLean.Poseidon
import Mathlib.Tactic.Says

namespace ArmadaLean

/-- An unshield: the pool pays `value` of the transaction's token to `recipient`, an
    address term. The 2021 Railgun whitepaper lists "Withdrawal amount" and "An
    address to withdraw from" as public inputs, and the contract "transfers tokens from
    itself to the specified user wallet address in the public inputs, if a withdrawal
    amount is specified" (S-RG, "RAILGUN Core System & Protocol"). One transaction has
    at most one such pair, so the bound parameters hold an `Option Unshield`. The
    contract carries the pair as the last output commitment, with the address packed
    into `npk` (TransactModule.sol:357-360, PoolTypes.sol:74). That packing is an
    encoding; `ArmadaLean.Pool.UnshieldRefines` states it at the circuit boundary. -/
structure Unshield where
  recipient : Term
  value : Nat
  deriving DecidableEq

/-- The bound parameters that the pool reads (module comment). -/
structure BoundParams where
  treeNumber : Nat
  unshield : Option Unshield
  adaptContract : Option Term
  adaptParams : Term
  deriving DecidableEq

/-- The term of an optional term: a Keccak term over the empty list or the one-element
    list. Used only to build the argument list of `hashBoundParams`. No theorem reads
    the shape; `hashBoundParams_inj` is the property that matters. -/
def optionTerm : Option Term → Term
  | none => Term.keccak []
  | some t => Term.keccak [t]

/-- The term of an optional unshield, the same construction as `optionTerm`. -/
def unshieldTerm : Option Unshield → Term
  | none => Term.keccak []
  | some u => Term.keccak [u.recipient, Term.val u.value]

/-- `hashBoundParams` (VerifierModule.sol:71-73), symbolic: the Keccak term of the
    bound parameters. -/
def hashBoundParams (bp : BoundParams) : Term :=
  Term.keccak [Term.val bp.treeNumber, unshieldTerm bp.unshield,
    optionTerm bp.adaptContract, bp.adaptParams]

theorem optionTerm_inj {a b : Option Term} (h : optionTerm a = optionTerm b) : a = b := by
  cases a <;> cases b <;> simp_all [optionTerm, Term.keccak]

theorem unshieldTerm_inj {a b : Option Unshield} (h : unshieldTerm a = unshieldTerm b) :
    a = b := by
  cases a with
  | none => cases b <;> simp_all [unshieldTerm, Term.keccak]
  | some u =>
    cases b with
    | none => (simp_all? [unshieldTerm, Term.keccak] says simp_all only [unshieldTerm, Term.keccak, Term.hash.injEq, reduceCtorEq, and_false])
    | some v =>
      cases u; cases v
      (simp_all? [unshieldTerm, Term.keccak] says simp_all only [unshieldTerm, Term.keccak, Term.hash.injEq, List.cons.injEq, Term.val.injEq, and_true, true_and])

/-- **Two different bound-parameter records never give the same hash.** By
    construction of the symbolic hash (`Term.hash.inj`), not by assumption.
    Source: VerifierModule.sol:71-73. -/
theorem hashBoundParams_inj {bp₁ bp₂ : BoundParams}
    (h : hashBoundParams bp₁ = hashBoundParams bp₂) : bp₁ = bp₂ := by
  unfold hashBoundParams Term.keccak at h
  simp only [Term.hash.injEq, List.cons.injEq, Term.val.injEq, and_true, true_and] at h
  obtain ⟨htn, hu, ha, hp⟩ := h
  cases bp₁; cases bp₂
  simp only [BoundParams.mk.injEq]
  exact ⟨htn, unshieldTerm_inj hu, optionTerm_inj ha, hp⟩

/-- `_validateTransaction`'s adapt check (TransactModule.sol:301-307): a transaction
    that names an adapt contract executes only when that contract is the caller. -/
def AdaptAllows (bp : BoundParams) (caller : Term) : Prop :=
  ∀ a, bp.adaptContract = some a → caller = a

/-- The amount that an optional unshield takes out of the pool: its value, or nothing
    when there is no unshield. -/
def withdrawn : Option Unshield → Nat
  | none => 0
  | some u => u.value

/-- `AdaptAllows` as a computable check: no constraint when there is no adapt contract,
    else the caller must be the named one. The contract performs exactly this check
    (`_validateTransaction`, TransactModule.sol:301-307). -/
def AdaptAllowsB (bp : BoundParams) (caller : Term) : Bool :=
  match bp.adaptContract with
  | none => true
  | some a => decide (caller = a)

theorem AdaptAllows_iff (bp : BoundParams) (caller : Term) :
    AdaptAllows bp caller ↔ AdaptAllowsB bp caller = true := by
  unfold AdaptAllows AdaptAllowsB
  cases bp.adaptContract with
  | none => simp
  | some a => simp [eq_comm]

/-- `AdaptAllows` is decidable: `Pool.apply` (docs/pool-executable.md, rule PE3) needs this
    to compute `TransactPre`/`TransactOwnedPre`. -/
instance instDecidableAdaptAllows (bp : BoundParams) (caller : Term) :
    Decidable (AdaptAllows bp caller) :=
  decidable_of_iff _ (AdaptAllows_iff bp caller).symm

end ArmadaLean
