/-
  `decisionScope`: a command linter, report-only. `docs/lean/type-doctrine.md`
  §3's `decisionScope` row (`armada-laconic` branch `draft/type-doctrine`,
  commit `9e297a7`). Modelled on Mathlib's flexible linter
  (`Mathlib/Tactic/Linter/FlexibleLinter.lean`): a `Lean.Linter.Linter`
  that walks the command's `InfoTree` after elaboration, not the Batteries
  `@[env_linter]` pattern `ArmadaLean/Lint/TypeDoctrine.lean` uses (that
  pattern inspects a declaration's TYPE; this linter needs the TACTIC
  STATE inside a proof, which only the `InfoTree` carries).

  `linter.decisionScope` is `false` by default (report-only): logs a
  warning (`Linter.logLint`) for an `omega` call whose consumed-hypothesis
  count exceeds `linter.decisionScope.maxOmegaHyps`, a `decide` call whose
  goal has a free variable or whose `Expr.sizeWithoutSharing` exceeds
  `linter.decisionScope.maxDecideSize`, or any `decide +kernel` /
  `native_decide`.

  `linter.decisionScope.dump` is a second, separate option: when `true`,
  it also prints ONE line per `omega`/`decide` node it sees, with the raw
  numbers, regardless of any threshold — used only to MEASURE the trunk
  and set the two thresholds above (TypeLinters' report). It is `false`
  in this committed file.
-/
import Lean.Elab.Command
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Decide
import Lean.Server.InfoUtils
import Lean.Linter.Basic

open Lean Elab Command Meta Linter

namespace ArmadaLean.Lint.DecisionScope

/-- Report an `omega` call whose consumed-hypothesis count exceeds
    `linter.decisionScope.maxOmegaHyps`, a `decide` call whose goal has a
    free variable or exceeds `linter.decisionScope.maxDecideSize`, or any
    `decide +kernel` / `native_decide`. `false` by default: report-only,
    `type-doctrine.md` §3. -/
register_option linter.decisionScope : Bool := {
  defValue := false
  descr := "report an omega/decide call whose input may be too large (type-doctrine.md §3)"
}

/-- Print every `omega`/`decide` node's raw numbers, not only the ones
    over a threshold. Used to measure the corpus and set
    `maxOmegaHyps`/`maxDecideSize` below; `false` in this committed
    tree. -/
register_option linter.decisionScope.dump : Bool := {
  defValue := false
  descr := "dump every omega/decide call's raw numbers (measurement only)"
}

/-- An `omega` call whose consumed-hypothesis count exceeds this is
    reported. `13`: the trunk's (`integrated`@`522e16d`) own measured
    MAXIMUM consumed-hypothesis count, over all 209 `omega` calls in the
    tree (TypeLinters' report, `armada-laconic` `draft/type-doctrine`
    §3). `draft/refined-types`'s own max is also `13`, so both trees
    report zero `repeatedPremise`-style day-one noise; `>13` only fires
    on a call that is already worse than anything either tree has
    today. The trunk's own 3 SLOWEST `omega` calls (`-Dprofiler=true`,
    `Nitro/Lemmas.lean`, `ArmadaLean.Nitro.Allocation.cover_pay`,
    287 ms/260 ms/47.5 ms) consume only 9-11 hypotheses, below this
    bound: the count bounds the INPUT size, not the observed time
    (Pearson r ≈ 0.13 between consumed-count and tactic time, 137 paired
    calls across `Nitro/Lemmas.lean`, `Nitro/Liveness.lean`,
    `PoolSafety.lean`); `type-doctrine.md` §3 itself says time is
    measured by the profiler, not gated by this linter. -/
register_option linter.decisionScope.maxOmegaHyps : Nat := {
  defValue := 13
  descr := "report an omega call that consumes more than this many hypotheses"
}

/-- A `decide` call whose goal `Expr.sizeWithoutSharing` exceeds this is
    reported. `300`: just above the trunk's own measured maximum decide
    goal size, `293` (`ArmadaLean.Nitro.NonVacuity._example`,
    `NonVacuity.lean:1336`), over all 271 `decide` calls in the tree.
    `draft/refined-types` introduces one `unfold
    Route.LedgerAfterRound2; decide` whose goal
    (`NonVacuity.lean:2661`) is size `21601` — 74 times the trunk's own
    worst case — plus two further calls over `300` (`335`, `331`,
    both `NonVacuity.lean`); this bound reports exactly those three,
    zero on the trunk. -/
register_option linter.decisionScope.maxDecideSize : Nat := {
  defValue := 300
  descr := "report a decide call whose goal exceeds this Expr.sizeWithoutSharing"
}

/-! ## Mirroring `omega`'s own fact recognizer

`omegaTactic` (`Lean.Elab.Tactic.Omega.Frontend`, `omegaTactic`/`omega`,
lines 672-696) calls `getLocalHyps` — EVERY non-implementation-detail
local declaration (`Lean.LocalContext.getLocalHyps`,
`LocalContext.lean:672-676`), data and `Prop` binders alike — and feeds
each one to `MetaProblem.addFact` (`Frontend.lean:425-508`). A
declaration `omega` does not recognize still costs a `whnfR` and a
pattern match; it just contributes no linear-arithmetic fact
(`addFact`'s fallthrough `_ => pure (p, 0)`). The functions below mirror
`addFact`'s dispatch (and, through its `Not` case, `pushNot`'s dispatch,
`Frontend.lean:372-420`) as a pure recognizer, not a proof-producing
one: `omegaConsumes ty` is `true` exactly when `addFact` would have
added at least one linear-arithmetic fact from a hypothesis of type
`ty`. -/

/-- `Nat`/`Int` always count; `Fin n` counts only where `addFact`'s own
    match lists a `Fin n` case (every comparison and `Eq`, but not `Ne`
    or `Dvd.dvd`, `Frontend.lean:441-486`; `pushNot`'s `LT.lt`/`LE.le`/
    `Eq` cases also list `Fin n`, but its `Dvd.dvd` case does not,
    `Frontend.lean:384-404`). -/
def omegaAtomic (α : Expr) (allowFin : Bool) : MetaM Bool := do
  match_expr α with
  | Nat => return true
  | Int => return true
  | Fin _ => return allowFin
  | _ => return false

mutual

/-- Mirrors `pushNot` (`Frontend.lean:372-420`): given `P` (already
    `whnfR`'d by the caller is NOT assumed; this function does its own
    `whnfR`, matching `pushNot`'s own first line), is `¬ P` a fact
    `addFact`'s `Not` case turns into a recognized one? -/
partial def omegaPushNotConsumes (P : Expr) : MetaM Bool := do
  let p ← whnfR P
  match p with
  | .forallE _ x y _ =>
    return p.isArrow && (← isProp x) && (← isProp y)
  | .app _ _ =>
    match_expr p with
    | LT.lt α _ _ _ => omegaAtomic α true
    | LE.le α _ _ _ => omegaAtomic α true
    | Eq α _ _ => omegaAtomic α true
    | Dvd.dvd α _ _ _ => omegaAtomic α false
    | Prod.Lex _ _ _ _ _ _ => return true
    -- double negation (`Decidable.of_not_not`): re-dispatch through the
    -- general `addFact`-style recognizer, as `addFact`'s own `Not` case
    -- does by calling `addFact` on the transformed hypothesis.
    | Not Q => omegaConsumes Q
    -- `¬(P ∧ Q)` becomes `P ∨ Q`'s negation pair
    -- (`Decidable.or_not_not_of_not_and`): an `Or`, consumed whenever
    -- `addFact`'s own `Or` case is (`cfg.splitDisjunctions`, default
    -- `true`, `Frontend.lean:502-506`).
    | And _ _ => return true
    -- `¬(P ∨ Q)` becomes `¬P ∧ ¬Q` (`and_not_not_of_not_or`): consumed
    -- if either conjunct is, matching `addFact`'s `And` case recursing
    -- into both sides.
    | Or P Q => return (← omegaPushNotConsumes P) || (← omegaPushNotConsumes Q)
    -- `¬(P ↔ Q)` becomes an `And` of two `Or`s
    -- (`Decidable.and_not_or_not_and_of_not_iff`): consumed via the same
    -- `Or`-under-`splitDisjunctions` path as the `And` case above.
    | Iff _ _ => return true
    | _ => return false
  | _ => return false

/-- Mirrors `MetaProblem.addFact`'s top-level dispatch
    (`Frontend.lean:425-508`): is a hypothesis of type `ty` one `omega`
    turns into at least one linear-arithmetic fact? `Exists`/`Subtype`
    open their body via `Expr.bindingBody!` (a loose `bvar` remains,
    which `match_expr`'s structural match on the HEAD application does
    not need resolved — this recognizer never prints or infers a type
    from the opened body, only pattern-matches its shape). -/
partial def omegaConsumes (ty : Expr) : MetaM Bool := do
  let t ← whnfR ty
  match t with
  | .forallE _ x y _ =>
    return t.isArrow && (← isProp x) && (← isProp y)
  | .app _ _ =>
    match_expr t with
    | Eq α _ _ => omegaAtomic α true
    | LE.le α _ _ _ => omegaAtomic α true
    | LT.lt α _ _ _ => omegaAtomic α true
    | GT.gt α _ _ _ => omegaAtomic α true
    | GE.ge α _ _ _ => omegaAtomic α true
    | Ne α _ _ => omegaAtomic α false
    | Dvd.dvd α _ _ _ => omegaAtomic α false
    | Not P => omegaPushNotConsumes P
    | Prod.Lex _ _ _ _ _ _ => return true
    | And P Q => return (← omegaConsumes P) || (← omegaConsumes Q)
    | Exists _ P => omegaConsumes P.bindingBody!
    | Subtype _ P => omegaConsumes P.bindingBody!
    | Iff P Q => return (← omegaConsumes P) || (← omegaConsumes Q)
    -- `cfg.splitDisjunctions` defaults to `true` (no ArmadaLean call
    -- passes `omega (config := ...)`, checked by `grep -n 'omega ('`).
    | Or _ _ => return true
    | _ => return false
  | _ => return false

end

/-- The consumed-hypothesis count `omega` would face on this goal, out of
    its total non-implementation-detail local declarations
    (`getLocalHyps`'s own filter). -/
def countOmegaContext (lctx : LocalContext) : MetaM (Nat × Nat) := do
  let mut consumed := 0
  let mut total := 0
  for d in lctx do
    if !d.isImplementationDetail then
      total := total + 1
      if ← omegaConsumes d.type then
        consumed := consumed + 1
  return (consumed, total)

/-- `decide`'s goal: does it have a free variable (so the `Decidable`
    instance cannot reduce to `isTrue`/`isFalse` and the call is stuck or
    falls through to `Decidable.decide`'s `rfl`-via-elaborator path
    anyway), and its `Expr.sizeWithoutSharing`. -/
def analyzeDecideGoal (ty : Expr) : MetaM (Bool × Nat) := do
  let g ← instantiateMVars ty
  return (g.hasFVar, g.sizeWithoutSharing)

/-- `true` when `stx` (a `decide`/`native_decide` tactic node)'s optional
    config argument mentions `kernel` — `decide +kernel` or
    `decide (config := \{ kernel := true })`. A textual check on the
    config syntax's reprint: `Lean.Elab.Tactic.Decide.elabDecideConfig`
    is a macro-based config elaborator (`declare_config_elab`,
    `Decide.lean:184`), not reusable outside tactic elaboration, to
    recover the `Bool` it resolves to without re-running elaboration.
    [INFERENCE] a config written through a named abbreviation bound
    elsewhere would be missed; none exists in this corpus (checked:
    `grep -n 'decide' ArmadaLean -r` shows only bare `decide` and
    `decide +kernel`, never a named config). -/
def mentionsKernelConfig (stx : Syntax) : Bool :=
  let s := stx.reprint.getD ""
  (s.splitOn "kernel").length > 1

/-- The declaration a tactic node belongs to, from its `ContextInfo`. -/
def declOf (ci : ContextInfo) : Name :=
  ci.parentDecl?.getD .anonymous

def handleOmega (ci : ContextInfo) (ti : TacticInfo) (fm : FileMap)
    (dumpOn reportOn : Bool) (maxHyps : Nat) : CommandElabM Unit := do
  let some mv := ti.goalsBefore.head? | return
  let some mdecl := ti.mctxBefore.decls.find? mv | return
  let (consumed, total) ← ci.runMetaM mdecl.lctx do
    Meta.withMCtx ti.mctxBefore do
      countOmegaContext mdecl.lctx
  let line := (fm.toPosition (ti.stx.getPos?.getD 0)).line
  let decl := declOf ci
  if dumpOn then
    logInfo m!"DECISIONSCOPE_OMEGA \{\"decl\":\"{decl}\",\"line\":{line},\"consumed\":{consumed},\"total\":{total}}"
  if reportOn && consumed > maxHyps then
    Linter.logLint linter.decisionScope ti.stx
      m!"omega call in {decl} (line {line}) consumes {consumed} hypotheses (> {maxHyps})"

def handleDecide (ci : ContextInfo) (ti : TacticInfo) (fm : FileMap)
    (dumpOn reportOn : Bool) (maxSize : Nat) (isNative : Bool) : CommandElabM Unit := do
  let some mv := ti.goalsBefore.head? | return
  let some mdecl := ti.mctxBefore.decls.find? mv | return
  let (hasFVar, size) ← ci.runMetaM mdecl.lctx do
    Meta.withMCtx ti.mctxBefore do
      analyzeDecideGoal mdecl.type
  let line := (fm.toPosition (ti.stx.getPos?.getD 0)).line
  let decl := declOf ci
  let kernelCfg := mentionsKernelConfig ti.stx
  if dumpOn then
    logInfo m!"DECISIONSCOPE_DECIDE \{\"decl\":\"{decl}\",\"line\":{line},\"native\":{isNative},\"kernel\":{kernelCfg},\"hasFVar\":{hasFVar},\"size\":{size}}"
  if reportOn then
    if isNative then
      Linter.logLint linter.decisionScope ti.stx
        m!"native_decide in {decl} (line {line}): forbidden, adds Lean.ofReduceBool"
    else if kernelCfg then
      Linter.logLint linter.decisionScope ti.stx
        m!"decide +kernel in {decl} (line {line}): flagged for review"
    else if hasFVar then
      Linter.logLint linter.decisionScope ti.stx
        m!"decide call in {decl} (line {line}): goal has a free variable, cannot reduce to a literal"
    else if size > maxSize then
      Linter.logLint linter.decisionScope ti.stx
        m!"decide call in {decl} (line {line}): goal size {size} (> {maxSize})"

/-- The main implementation: walk every `TacticInfo` node of the
    command's `InfoTree`s, dispatching `omega`/`decide`/`native_decide`
    nodes to the handlers above. Modelled on
    `Mathlib.Linter.Flexible.flexibleLinter`'s own top-level structure
    (`FlexibleLinter.lean:462-467`: `withSetOptionIn`, bail out early if
    neither option is set or the command already has errors, then fold
    over `← getInfoTrees`). -/
def decisionScopeLinter : Linter where
  name := `decisionScope
  run := withSetOptionIn fun _stx => do
    let dumpOn := linter.decisionScope.dump.get (← getOptions)
    let reportOn := getLinterValue linter.decisionScope (← getLinterOptions)
    unless dumpOn || reportOn do return
    if (← MonadState.get).messages.hasErrors then return
    let maxHyps := linter.decisionScope.maxOmegaHyps.get (← getOptions)
    let maxSize := linter.decisionScope.maxDecideSize.get (← getOptions)
    let fm ← getFileMap
    let trees ← getInfoTrees
    for tree in trees do
      tree.foldInfoM (init := ()) fun ci info () => do
        match info with
        | .ofTacticInfo ti =>
          let k := ti.stx.getKind
          if k == ``Lean.Parser.Tactic.omega then
            handleOmega ci ti fm dumpOn reportOn maxHyps
          else if k == ``Lean.Parser.Tactic.decide then
            handleDecide ci ti fm dumpOn reportOn maxSize false
          else if k == ``Lean.Parser.Tactic.nativeDecide then
            handleDecide ci ti fm dumpOn reportOn maxSize true
          else
            pure ()
        | _ => pure ()

initialize addLinter decisionScopeLinter

end ArmadaLean.Lint.DecisionScope
