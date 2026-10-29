/-
  ArmadaLean.PoolMachine — the pool as a `Machine` (`ArmadaLean.Machine`),
  and the pool's reachable-state obligation restated against it. Operator
  ruling 2026-10-29 ("Generic state: `Machine` and `System`"):
  `docs/process.md:130` requires a step to start "built by real steps from
  genesis"; the four can-happen theorems of `PoolSafety.lean:639-794`
  instead start from an arbitrary `s : PoolState`. This file restates them
  from a `Pool.machine`-reachable `s`, without deleting the originals.
-/
import ArmadaLean.Machine
import ArmadaLean.PoolSafety

/-- The pool as a `Machine`: an initial state is `genesis r` for some fee
    rate `r` (`genesis`, `Pool.lean:968`, one genesis state per fee rate,
    not a single state); a step is `Step` (`Pool.lean:1037`). -/
def Pool.machine : Machine PoolState where
  init := fun s => ∃ r, s = genesis r
  step := Step

/-- `Pool.machine`'s `Machine.Reachable` is exactly `Pool.lean`'s own
    `Reachable` (`Pool.lean:1146`): both are some `genesis r`, closed under
    `Step`. -/
theorem Pool.machine_reachable_iff {s : PoolState} : Pool.machine.Reachable s ↔ Reachable s := by
  constructor
  · rintro ⟨s₀, ⟨r, rfl⟩, hsteps⟩
    induction hsteps with
    | refl => exact Reachable.genesis r
    | tail _ hstep ih => exact Reachable.step ih hstep
  · intro hr
    induction hr with
    | genesis r => exact ⟨genesis r, ⟨r, rfl⟩, Relation.ReflTransGen.refl⟩
    | step _ hstep ih =>
      obtain ⟨s₀, hinit, hsteps⟩ := ih
      exact ⟨s₀, hinit, hsteps.tail hstep⟩

/-- **Can happen, from a reachable state: a shield succeeds.** Restates
    `shield_can_happen` (`PoolSafety.lean:639`) with the `Pool.machine`
    premise `docs/process.md:130` asks for; the existing proof already
    closes it, since `hr` is not needed and `Pool.machine.step` unfolds to
    `Step`. -/
theorem shield_can_happen_reachable {s : PoolState} (_hr : Pool.machine.Reachable s)
    (token : Token) (x : Nat) (npk : Term) (hValue : 0 < x)
    (hSpendable : Spendable (shieldBase s.feeRatio x)) :
    ∃ s', Pool.machine.step s s' :=
  shield_can_happen token x npk hValue hSpendable

/-- **Can happen, from a reachable state: a transact succeeds.** Restates
    `transact_can_happen` (`PoolSafety.lean:653`); the existing proof
    already closes it. -/
theorem transact_can_happen_reachable {s : PoolState} (_hr : Pool.machine.Reachable s)
    (hComplete : TransactProofCompleteness) (hSig : HonestSignature) {N M : Nat}
    (caller : Term) (bp : BoundParams) (hAdapt : AdaptAllows bp caller)
    (hNoUnshield : bp.unshield = none) (publicKey : Nat × Nat) (nullifyingKey : Nat)
    (token : Token) (root : Term) (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4) (hRoot : root ∈ s.rootsAt' bp.treeNumber)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i)) (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent bp.treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Pool.machine.step s s' :=
  transact_can_happen hComplete hSig caller bp hAdapt hNoUnshield publicKey nullifyingKey token
    root randomIn valueIn leavesIndices pathElements npkOut valueOut hN hM hRoot hPathLen hMerkle
    hRangeIn hRangeOut hBalance hDistinctLeaves hFresh hLive

/-- **Can happen, from a reachable state: an unshield succeeds and pays its
    recipient.** Restates `unshield_can_happen` (`PoolSafety.lean:720`);
    the existing proof already closes it. -/
theorem unshield_can_happen_reachable {s : PoolState} (_hr : Pool.machine.Reachable s)
    (hComplete : TransactProofCompleteness) (hSig : HonestSignature) {N : Nat} (caller : Term)
    (bp : BoundParams) (hAdapt : AdaptAllows bp caller) (recipient : Term) (value : Nat)
    (hU : bp.unshield = some ⟨recipient, value⟩) (publicKey : Nat × Nat) (nullifyingKey : Nat)
    (token : Token) (root : Term) (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (hN : N ≤ 8)
    (hRoot : root ∈ s.rootsAt' bp.treeNumber) (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot
        (commitment (npk (masterPublicKey publicKey nullifyingKey) (randomIn i)) token
          (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i)) (hRangeOut : RangeChecked120 value)
    (hBalance : listSum (List.ofFn valueIn) = value)
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier (Term.val nullifyingKey) (leavesIndices i) ∉ s.spent bp.treeNumber)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk (masterPublicKey publicKey nullifyingKey) (randomIn i), token, valueIn i⟩ :
              CommitmentPreimage)))
        = some rest) :
    ∃ s', Pool.machine.step s s' ∧ s'.payouts = s.payouts ++ [⟨token, recipient, value⟩] :=
  unshield_can_happen hComplete hSig caller bp hAdapt recipient value hU publicKey nullifyingKey
    token root randomIn valueIn leavesIndices pathElements hN hRoot hPathLen hMerkle hRangeIn
    hRangeOut hBalance hDistinctLeaves hFresh hLive

/-- **Can happen, from a reachable state: an owned transact succeeds.**
    Restates `owned_transact_can_happen` (`PoolSafety.lean:794`); the
    existing proof already closes it. -/
theorem owned_transact_can_happen_reachable {s : PoolState} (_hr : Pool.machine.Reachable s)
    (hComplete : OwnedProofCompleteness) {N M : Nat} (ownerField : Term) (token : Token)
    (bp : BoundParams) (hNoUnshield : bp.unshield = none) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool)) (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hN : N ≤ 8) (hM : M ≤ 4) (hRoot : root ∈ s.rootsAt' bp.treeNumber)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot (commitment (npk ownerField (randomIn i)) token (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i)) (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (hFresh : ∀ i, nullifier ownerField (leavesIndices i) ∉ s.spent bp.treeNumber)
    (caller : Term) (hCaller : caller = ownerField) (hAdapt : AdaptAllows bp caller)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hLive : removeAll (s.live token)
        (List.ofFn fun i =>
          ((bp.treeNumber, leavesIndices i),
            (⟨npk ownerField (randomIn i), token, valueIn i⟩ : CommitmentPreimage)))
        = some rest) :
    ∃ s', Pool.machine.step s s' :=
  owned_transact_can_happen hComplete ownerField token bp hNoUnshield root randomIn valueIn
    leavesIndices pathElements npkOut valueOut hN hM hRoot hPathLen hMerkle hRangeIn hRangeOut
    hBalance hDistinctLeaves hFresh caller hCaller hAdapt hLive
