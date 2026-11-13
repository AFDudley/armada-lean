/-
  Failure tests for the type-doctrine linters (`ArmadaLean/Lint/TypeDoctrine.lean`:
  `layerHits`, `analyzeDecl`). Each `#eval` throws, and so fails the build of this module,
  when its result differs from the expected one.
  `scripts/gate_extra.py` builds this module before it runs
  `scripts/type_lint.lean`, so a failed test fails `lint_ok`.

  The declarations below are not in the linters' scope (`inScope` excludes
  `ArmadaLean.Lint`). Each `layerHits` test passes its layer's base operations to
  `layerHits` explicitly.
-/
import ArmadaLean
import ArmadaLean.Lint.TypeDoctrine
import Mathlib.Data.List.Dedup

open Lean Meta ArmadaLean.Lint.TypeDoctrine

namespace ArmadaLean.Lint.TypeDoctrineTest

/-- Skips a layer: a statement about reachable states whose proof splits on
    `Step`. Naming `Reachable` does not make `Step.casesOn` a statement
    constant. -/
theorem poolSkip {s : PoolState} (h : Reachable s) : s.feeRatio = s.feeRatio := by
  cases h with
  | genesis r _ _ => rfl
  | step _ hstep => cases hstep <;> rfl

/-- Names `markSpent` only through the statement of `markSpent_succeeds`,
    in the motive of the `obtain`. -/
theorem poolMotiveOnly {spent : NullifierSet} {ns : List ArmadaLean.Term}
    (hpw : ns.Pairwise (· ≠ ·)) (hfresh : ∀ n ∈ ns, n ∉ spent) : ns.length = ns.length := by
  obtain ⟨_, _⟩ := markSpent_succeeds hpw hfresh
  rfl

/-- Names the tree-insertion operations only through the type of
    `Step.shield`, which the statement names. -/
theorem poolConstructorOnly {s : PoolState} (token : Token) (x : Nat) (npk : ArmadaLean.Term)
    (hValue : 0 < x) (hSpendable : Spendable (shieldBase s.feeRatio x)) : ∃ s', Step s s' :=
  ⟨_, Step.shield token x npk hValue hSpendable⟩

/-- Throws unless `layerHits` on `n` against `ops` is `expected`. -/
def expectHits (n : Name) (ops : Array Name) (expected : Array Name) : MetaM Unit := do
  let hits ← layerHits (← getEnv) n ops
  unless hits == expected do
    throwError "layerHits {n}: expected {expected}, got {hits}"

#eval expectHits ``poolSkip poolBaseOps #[`ArmadaLean.Step.casesOn]
#eval expectHits ``poolMotiveOnly poolBaseOps #[]
#eval expectHits ``poolConstructorOnly poolBaseOps #[]

/-- Premises the premise-shape linters skip (a Pool structure, a base
    call result, a transition relation) and one they keep (`Reachable s`,
    a condition on one input that `ReachableState` types). -/
theorem premiseCases {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M}
    {spent spent' : NullifierSet} {ns : List ArmadaLean.Term} {s s' : PoolState}
    (_hc : Constrained w pub) (_hm : markSpent spent ns = some spent') (_hs : Step s s')
    (_hr : Reachable s) : s = s := rfl

/-- One alias (`tn` defined from `trees`) and one condition on one input
    (`o = o.dedup`), which is not an alias. -/
theorem aliasCases (o : List Nat) (trees : List TreeState) (tn k : Nat)
    (_ho : o = o.dedup) (_ht : tn = insertTree trees k) : o = o := rfl

/-- Throws unless `analyzeDecl` on `n` keeps exactly the conjuncts
    `kept` (pretty-printed) and reports exactly the alias binders
    `aliases`. -/
def expectConjuncts (n : Name) (kept : Array String) (aliases : Array Name) : MetaM Unit := do
  let d ← analyzeDecl (← getEnv) n
  let gotKept := d.conjuncts.map (·.pretty)
  let gotAliases := d.conjuncts.filterMap fun c => c.aliasInfo.map (·.1)
  unless gotKept == kept && gotAliases == aliases do
    throwError "analyzeDecl {n}: expected {kept} / {aliases}, got {gotKept} / {gotAliases}"

#eval expectConjuncts ``premiseCases #["Reachable s"] #[]
#eval expectConjuncts ``aliasCases #["o = o.dedup", "tn = insertTree trees k"] #[`tn]

end ArmadaLean.Lint.TypeDoctrineTest
