/-
  Type-doctrine linters, report-only. `docs/lean/type-doctrine.md` §3-4a
  (`armada-laconic` branch `draft/type-doctrine`, commit f1d0089). None of
  these linters is in the default lint set (`@[env_linter disabled]`),
  and this module is not imported by `ArmadaLean.lean`, so `lake build`
  never elaborates it. `scripts/type_lint.lean` imports it directly, to
  build it: `lake build ArmadaLean.Lint.TypeDoctrine`.

  Scope (§1, §4 decision 1): every `def`/`theorem` declared in a module
  whose own path starts with `ArmadaLean`, selected by MODULE, not
  namespace. Every armada-lean declaration is under the root namespace
  `ArmadaLean` (draft/root-namespace, 2026-11-06); the module test stays
  because it needs no rule about names. A module under
  `ArmadaLean.Spec` or `ArmadaLean.Witness` is out of scope: the spec
  module (`docs/spec-module-design.md`) generates these from a cited
  theorem's own header, so a finding on one is a finding on that header,
  already reported once, under its own module. A declaration whose last
  name component is `nonvacuity` or starts with `nonvacuity_` is also out
  of scope: the spec module promotes a non-vacuity `example` to a theorem
  of that name (`docs/spec-module-design.md` §5, `convert_spec.py`'s own
  `nm = f"{short}.nonvacuity" + …`), so it reports the fact the `example`
  already stated, now under a name instead of anonymous.
-/
import Lean.Meta.Basic
import Lean.DocString
import Lean.Util.FoldConsts
import Lean.Structure
import Lean.Meta.Match.MatcherInfo
import Batteries.Tactic.Lint.Basic

open Lean Meta Batteries.Tactic.Lint

namespace ArmadaLean.Lint.TypeDoctrine

/-! ## Declaration selection, by module -/

/-- The module a constant was declared in. `none` for a constant of the
    file currently being elaborated (never the case for an imported
    `ArmadaLean` declaration, which is always from an already-built
    module by the time this runs). -/
def declModule (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun idx => env.header.moduleNames[idx.toNat]!

/-- The spec module's own generated-witness naming
    (`docs/spec-module-design.md` §5): a name whose last component is
    `nonvacuity`, or starts with `nonvacuity_` (a disambiguating suffix,
    `convert_spec.py`'s `nm`). -/
def isGeneratedWitnessExample : Name → Bool
  | .str _ s => s == "nonvacuity" || "nonvacuity_".isPrefixOf s
  | _ => false

/-- A declaration is in scope when its own module path starts with
    `ArmadaLean`, outside this linter module itself and outside the spec
    module's own generated declarations (`ArmadaLean.Spec`,
    `ArmadaLean.Witness`, a promoted non-vacuity example: the module
    comment above). -/
def inScope (env : Environment) (n : Name) : Bool :=
  match declModule env n with
  | some m => (`ArmadaLean).isPrefixOf m && !(`ArmadaLean.Lint).isPrefixOf m
      && !(`ArmadaLean.Spec).isPrefixOf m && !(`ArmadaLean.Witness).isPrefixOf m
      && !isGeneratedWitnessExample n
  | none => false

/-- Nitro declarations live in a module under `ArmadaLean.Nitro`; every
    other in-scope module is the Pool. -/
def isNitroModule (env : Environment) (n : Name) : Bool :=
  match declModule env n with
  | some m => (`ArmadaLean.Nitro).isPrefixOf m
  | none => false

/-- Every name the environment knows, imported and local (the pattern
    `Batteries.Tactic.Lint.Frontend.getAllDecls` uses, inlined here as a
    pure function of `Environment` so it needs no `CoreM`). -/
def allDeclNames (env : Environment) : Array Name :=
  let cur := env.constants.map₂.foldl (init := #[]) fun r k _ => r.push k
  env.constants.map₁.fold (init := cur) fun r k _ => r.push k

/-- The `def`/`theorem` declarations in scope, excluding auto-generated
    and private names, and excluding structure projection functions
    (`Lean.Environment.isProjectionFn`). A projection is not itself a
    premise-bearing declaration: its hypotheses are the structure's own
    fields, generated once per field by the structure command, not a
    condition an author repeated across declarations (rule 1 is about
    repeated AUTHORED conditions). Without this exclusion, a structure
    with two or more fields shows up as a `repeatedPremise` group of its
    own projections (measured: two such groups on `draft/round-combinator`
    `8611a8f`, `Bounds.unforgeableDeliver`/`StepInvariant.deliver` and
    `StepInvariant.land`/`CondStepInvariant.condMono`). `isAutoDecl` does
    not catch a projection (`Batteries.Tactic.Lint.Misc`'s own linters
    check `isProjectionFn` separately, for the same reason). -/
def scopedDeclNames (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for n in allDeclNames env do
    if !inScope env n then continue
    if env.isAutoDecl n then continue
    if env.isProjectionFn n then continue
    match env.find? n with
    | some (.defnInfo _) | some (.thmInfo _) => out := out.push n
    | _ => continue
  return out

/-- The `theorem` declarations in scope (`layerDiscipline`'s own scope,
    `type-doctrine.md` §4a: "theorems scanned", not every declaration —
    unlike `repeatedPremise`/`looseHypothesis`, which `scopedDeclNames`
    serves and which decision 1 extends to helpers). -/
def scopedTheoremNames (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for n in allDeclNames env do
    if !inScope env n then continue
    if env.isAutoDecl n then continue
    if let some (.thmInfo _) := env.find? n then out := out.push n
  return out

/-! ## Expr-level helpers -/

/-- Split `e` at every top-level `∧`. -/
partial def splitAnd (e : Expr) : Array Expr :=
  match e.and? with
  | some (p, q) => splitAnd p ++ splitAnd q
  | none => #[e]

/-- Free variables of `e`, in order of first occurrence (a preorder walk),
    each listed once. -/
partial def collectOrderedFVars (e : Expr) (acc : Array FVarId := #[]) : Array FVarId :=
  match e with
  | .fvar fvarId => if acc.contains fvarId then acc else acc.push fvarId
  | .app f a => collectOrderedFVars a (collectOrderedFVars f acc)
  | .lam _ t b _ => collectOrderedFVars b (collectOrderedFVars t acc)
  | .forallE _ t b _ => collectOrderedFVars b (collectOrderedFVars t acc)
  | .letE _ t v b _ => collectOrderedFVars b (collectOrderedFVars v (collectOrderedFVars t acc))
  | .mdata _ e => collectOrderedFVars e acc
  | .proj _ _ e => collectOrderedFVars e acc
  | _ => acc

/-- `e`'s carrier, when `e` is `ReachableState.state e'`: the coercion a
    converted theorem's header uses for its `ReachableState` binder
    (`docs/spec-module-design.md` decision 2). A premise's shape must not
    change just because its state binder moved from a bare parameter to a
    `ReachableState` one — the reachable type's own carrier projection is
    not part of the shape. Matches `ReachableState.state` by `Name`, not by
    an import of `ArmadaLean.Types.Reachable` (which would drag in
    `Lean.Linter`, ambiguous here with `Batteries.Tactic.Lint.Linter`).
    Scoped to `ReachableState.state` itself, not every `Subtype` carrier
    (`Subtype.val`/`.1`): a refined type such as `TimedChannel` also
    coerces through `Subtype.val`, and its own carrier projection IS part
    of its premises' shape (`docs/lean/typed-library.md` §3 rule 2 gives
    every refined type the same coercion; only the reachable type's is
    exempted here). -/
def stateCarrier? (e : Expr) : Option Expr :=
  match e with
  | .app (.app (.app (.const n _) _) _) e => if n == `ArmadaLean.ReachableState.state then some e else none
  | _ => none

/-- `e` with every `ReachableState.state e'` subterm replaced by
    `stripStateCarrier e'`, applied everywhere in `e`, not only at `e`'s
    own head. Must run BEFORE `collectOrderedFVars`/`abstract`: a raw
    `ReachableState.state net` carries extra implicit arguments (the
    reachability witness), and `collectOrderedFVars` walks into them, so
    two premises that print identically (`HoldsVirtualSetup net …` versus
    `HoldsVirtualSetup (ReachableState.state net) …`) collected different
    numbers of leading free variables and so got different `bvar` indices
    after `abstract` (observed: `B8 B7` against `B5 B4`, same printed
    conjunct, different `repeatedPremise` keys). Stripping first means
    `collectOrderedFVars` sees only `net` itself in both forms. -/
partial def stripStateCarrier (e : Expr) : Expr :=
  match stateCarrier? e with
  | some inner => stripStateCarrier inner
  | none =>
    match e with
    | .app f a => .app (stripStateCarrier f) (stripStateCarrier a)
    | .lam n t b bi => .lam n (stripStateCarrier t) (stripStateCarrier b) bi
    | .forallE n t b bi => .forallE n (stripStateCarrier t) (stripStateCarrier b) bi
    | .letE n t v b nd => .letE n (stripStateCarrier t) (stripStateCarrier v) (stripStateCarrier b) nd
    | .mdata m e => .mdata m (stripStateCarrier e)
    | .proj n i e => .proj n i (stripStateCarrier e)
    | _ => e

/-- A structural key for `e`, stable under consistent renaming of bound
    variables (`bvar` indices only; no fvar should remain once `e` has
    been abstracted by `collectOrderedFVars`). Assumes `e` has already
    gone through `stripStateCarrier` (`normalizedKey` below): there is no
    `ReachableState.state` case left to match here. -/
partial def exprKey (e : Expr) : String :=
  match e with
  | .bvar i => s!"B{i}"
  | .fvar fvarId => s!"F{fvarId.name}"
  | .mvar _ => "M"
  | .sort _ => "S"
  | .const n _ => s!"C{n}"
  | .app f a => s!"({exprKey f} {exprKey a})"
  | .lam _ t b _ => s!"(λ{exprKey t}.{exprKey b})"
  | .forallE _ t b _ => s!"(∀{exprKey t}.{exprKey b})"
  | .letE _ t v b _ => s!"(let{exprKey t}:={exprKey v}.{exprKey b})"
  | .lit (.natVal n) => s!"#{n}"
  | .lit (.strVal s) => s!"#{s}"
  | .mdata _ e => exprKey e
  | .proj n i e => s!"π{n}.{i}{exprKey e}"

/-- `e`'s normalized shape key: strip the `ReachableState` carrier
    (`stripStateCarrier`), then abstract every free variable the result
    mentions, in order of first occurrence, so binder names (and their
    order in the enclosing declaration) do not matter either. The strip
    runs first so the free-variable count `abstract` indexes against is
    the same in both of a premise's binder forms (see
    `stripStateCarrier`'s doc comment). -/
def normalizedKey (e : Expr) : String :=
  let e := stripStateCarrier e
  let ordered := collectOrderedFVars e
  exprKey (e.abstract (ordered.map Expr.fvar))

/-- Every `(binderType, field)` pair `e` mentions as a direct projection
    or predicate applied to one of `e`'s free variables, for example
    `(FixedPart, challengeDuration)` in `c.challengeDuration`. Only a
    direct application `T.field v` counts; a chain through a computed
    subterm does not. -/
partial def fieldRefsM (e : Expr) : MetaM (Array (Name × Name)) := do
  match e with
  | .app fn arg =>
    let mut rest := (← fieldRefsM fn) ++ (← fieldRefsM arg)
    if let .const c _ := fn then
      if let .fvar fvarId := arg then
        let ty ← fvarId.getType
        if let some tyHead := ty.getAppFn.constName? then
          if c.getPrefix == tyHead then
            rest := rest.push (tyHead, c)
    return rest
  | .lam _ t b _ => return (← fieldRefsM t) ++ (← fieldRefsM b)
  | .forallE _ t b _ => return (← fieldRefsM t) ++ (← fieldRefsM b)
  | .letE _ t v b _ => return (← fieldRefsM t) ++ (← fieldRefsM v) ++ (← fieldRefsM b)
  | .mdata _ e => fieldRefsM e
  | .proj _ _ e => fieldRefsM e
  | _ => return #[]

/-! ## Per-declaration analysis -/

/-- One top-level-`∧` conjunct of one hypothesis, normalized. -/
structure ConjunctInfo where
  /-- The hypothesis binder's own name. -/
  hypName : Name
  /-- Index of this conjunct within that hypothesis (0 for an
      un-split hypothesis). -/
  idx : Nat
  /-- `repeatedPremise`/`premiseVariant` grouping key. -/
  key : String
  /-- Pretty-printed conjunct, with the declaration's own variable names. -/
  pretty : String
  /-- `(binderType, field)` pairs this conjunct mentions. -/
  fieldRefs : Array (Name × Name)
  /-- User names of the free binders this conjunct mentions, in order of
      first occurrence. -/
  freeVars : Array Name
  /-- `some fieldVar` when this conjunct's only free variable, apart from
      type parameters and instances, is the one data binder `fieldVar`
      (rule 2's single-input case). -/
  singleDataVar : Option Name
  /-- `some (binderName, rhsPretty)` when this conjunct is
      `binderName = rhsPretty` (or the symmetric form), `binderName` one
      of the declaration's own binders and the other side an
      application (rule 3's alias case). -/
  aliasInfo : Option (Name × String)
  deriving Inhabited

/-- Everything `repeatedPremise`, `premiseVariant`, `looseHypothesis` and
    `aliasHypothesis` need about one in-scope declaration. -/
structure DeclInfo where
  name : Name
  isNitro : Bool
  conjuncts : Array ConjunctInfo
  deriving Inhabited

/-- Check whether `e` is `x = f …` (or `f … = x`) with `x` one of
    `binders` and `f …` free of `x`. An equation whose other side
    mentions `x` (`o = o.dedup`) does not define `x` from another
    argument: it is a condition on `x` alone (rule 2), not an alias
    (rule 3). -/
def aliasCandidate (binders : Array FVarId) (e : Expr) : MetaM (Option (Name × String)) := do
  let some (_, lhs, rhs) := e.eq? | return none
  let side (x y : Expr) : MetaM (Option (Name × String)) := do
    let .fvar fv := x | return none
    if binders.contains fv && y.isApp && !y.containsFVar fv then
      return some (← fv.getUserName, toString (← ppExpr y))
    else
      return none
  match ← side lhs rhs with
  | some r => return some r
  | none => side rhs lhs

/-- Nitro's base operations (`type-doctrine.md` §4a). -/
def nitroBaseOps : Array Name := #[
  `ArmadaLean.Nitro.Adjudicator.apply,
  `ArmadaLean.Nitro.NetworkState.applyAdv,
  `ArmadaLean.Nitro.Adjudicator.transfer,
  `ArmadaLean.Nitro.Adjudicator.challenge,
  `ArmadaLean.Nitro.Adjudicator.checkpoint,
  `ArmadaLean.Nitro.Adjudicator.conclude,
  `ArmadaLean.Nitro.Adjudicator.reclaim]

/-- The Pool's base operations (`type-doctrine.md` §4a): tree insertion,
    nullifier marking, preimage records, and case analysis on `Step`. -/
def poolBaseOps : Array Name := #[
  `ArmadaLean.removeAll, `ArmadaLean.markSpent, `ArmadaLean.applyRecords,
  `ArmadaLean.recordPreimages, `ArmadaLean.insertLeaves, `ArmadaLean.insertTree,
  `ArmadaLean.insertStart, `ArmadaLean.withTreePositionsFrom, `ArmadaLean.Step.casesOn]

/-- `n` is declared in a module under `ArmadaLean`. The test is the
    module, not the name (the module comment above). -/
def isArmadaConst (env : Environment) (n : Name) : Bool :=
  (declModule env n).any (`ArmadaLean).isPrefixOf

/-- `e`'s head is already the typed result rule 1 asks for, so `e` is
    not itself a premise rule 1 can act on. Unfolds the head constant's
    `def` chain (bounded by the chain itself; every chain observed ends
    at a structure, `Subtype`, or a non-`def` constant) and stops at the
    first `ArmadaLean` structure or `Subtype` head found. The structure
    match is scoped to `ArmadaLean`: `And`, `Exists` and `Iff` are also
    Lean `structure`s (one constructor each), and an `ArmadaLean` `def`
    normally unfolds through one of them (`∧`, `∃`) before reaching its
    own content; matching ANY structure there would misclassify every
    conjunction-shaped `Prop`, not only the domain types rule 1 makes.
    `Subtype` itself is core (not `ArmadaLean`-prefixed) and still
    counts: it is the refined-type carrier every `TimedChannel`-style
    type coerces through (`typed-library.md` §3 rule 2). -/
partial def unfoldsToTypedCarrier (env : Environment) (e : Expr) : MetaM Bool := do
  let .const n _ := e.getAppFn | return false
  if n == ``Subtype then return true
  if isArmadaConst env n && isStructure env n then return true
  let some (.defnInfo _) := env.find? n | return false
  let some e' ← Meta.unfoldDefinition? e | return false
  unfoldsToTypedCarrier env (← Meta.whnfR e')

/-- `e` is the result of one base-operation call: an equation with a
    base operation of `nitroBaseOps` or `poolBaseOps` at the head of one
    side, and not a bare variable on the other side (`s.apply apps caller
    op = some s'`, `markSpent spent ns = some spent'`). `tn = insertTree
    trees k` is an alias of `tn` (rule 3), not a call result. -/
def isBaseOpResult (e : Expr) : Bool :=
  match e.eq? with
  | some (_, lhs, rhs) =>
    let call (x y : Expr) :=
      !y.isFVar && x.getAppFn.constName?.any (nitroBaseOps ++ poolBaseOps).contains
    call lhs rhs || call rhs lhs
  | none => false

/-- `n` is an `ArmadaLean` transition relation: an inductive type or a
    structure field whose type ends in `S → S → Prop`, two arguments of
    one type (`Step s s'`, `Threat.RoundSeq apps T t pending net net'`,
    `ReachableFrom s s'`, `Machine.step`). -/
def isTransitionRelation (env : Environment) (n : Name) : MetaM Bool := do
  if !isArmadaConst env n then return false
  if !(env.find? n matches some (.inductInfo _)) && !env.isProjectionFn n then return false
  forallTelescope (← getConstInfo n).type fun xs body => do
    if !body.isProp || xs.size < 2 then return false
    return (← inferType xs[xs.size - 2]!) == (← inferType xs[xs.size - 1]!)

/-- `e`, a hypothesis conjunct, is excluded from every premise-shape
    linter (`repeatedPremise`, `premiseVariant`, `looseHypothesis`,
    `aliasHypothesis`) for one of four reasons:
    - **`e`'s head is a local variable** (`Inv net`, `Cond n op`): the
      head is the declaration's OWN parameter, not a named declaration
      rule 1 could replace. Rule 1 converts a condition on a value into
      a type; it cannot act on the abstraction's own predicate
      parameter, which has no fixed meaning to give a type to.
    - **`e`'s head names an `ArmadaLean` structure, or an `ArmadaLean`
      `def` that unfolds to a structure or a `Subtype`**
      (`unfoldsToTypedCarrier`): `e` already IS the typed value rule 1
      asks for (`SatpEnds r alice bob P`, with `SatpEnds` a structure
      made to satisfy rule 1 on some earlier repeated condition).
      Counting it as a NEW `repeatedPremise` group would flag the
      intended result of the rule as a fresh violation of the rule. A
      head outside `ArmadaLean` (a Mathlib/core predicate) is not a type
      this doctrine governs. `ArmadaLean` is the declaring module
      (`isArmadaConst`), so the Pool's `Constrained w pub` counts.
    - **`e` is the result of one base-operation call**
      (`isBaseOpResult`). A per-call lemma takes the call's result as
      its premise: that layer sits directly above the base operations
      (`type-doctrine.md` §4a rule 1, `writing-lean.md` §6), and the
      typed operation equations keep this premise
      (`docs/process.md` R.2). The premise relates a call's inputs to
      its result. It is not a fact about one input that a type can
      carry.
    - **`e`'s head is a transition relation** (`isTransitionRelation`).
      A lemma about a step or a run takes it as its premise
      (`writing-lean.md` §5, `inv_step … (h : Step s s')`). The relation
      is the subject of the lemma, and it is already an inductive type. -/
def premiseExcluded (env : Environment) (e : Expr) : MetaM Bool := do
  if isBaseOpResult e then return true
  match e.getAppFn with
  | .fvar _ => return true
  | .const n _ =>
    if !isArmadaConst env n then return false
    if ← isTransitionRelation env n then return true
    unfoldsToTypedCarrier env e
  | _ => return false

/-- Analyze one in-scope declaration: its data/hypothesis binders, and
    every normalized hypothesis conjunct. `none` only when `n`'s type is
    not a `∀`-telescope of ordinary binders (none observed in scope).
    A type parameter (`E : Type`) or an instance binder is not an input:
    `s.IsDAG` with `s : Adjudicator E` mentions `E` and `DecidableEq E`,
    and still constrains the one input `s` (rule 2). -/
def analyzeDecl (env : Environment) (n : Name) : MetaM DeclInfo := do
  let info ← getConstInfo n
  forallTelescope info.type fun args _ => do
    let mut dataB : Array FVarId := #[]
    let mut hypB : Array FVarId := #[]
    let mut typeB : Array FVarId := #[]
    for a in args do
      let ldecl ← a.fvarId!.getDecl
      if ldecl.binderInfo.isInstImplicit || ldecl.type.isSort then
        typeB := typeB.push a.fvarId!
      else if ← Meta.isProp ldecl.type then
        hypB := hypB.push a.fvarId!
      else
        dataB := dataB.push a.fvarId!
    let allBinders := dataB ++ hypB
    let mut conjuncts : Array ConjunctInfo := #[]
    for h in hypB do
      let ldecl ← h.getDecl
      let parts := splitAnd ldecl.type
      for i in [0:parts.size] do
        let e := parts[i]!
        if ← premiseExcluded env e then continue
        let key := normalizedKey e
        let pretty := toString (← ppExpr e)
        let refs ← fieldRefsM e
        let ordered := collectOrderedFVars e
        let freeVars ← ordered.mapM (·.getUserName)
        let inputs := ordered.filter (!typeB.contains ·)
        let singleDataVar ←
          if inputs.size == 1 && dataB.contains inputs[0]! then
            some <$> inputs[0]!.getUserName
          else
            pure none
        let aliasInfo ← aliasCandidate allBinders e
        conjuncts := conjuncts.push
          { hypName := ldecl.userName, idx := i, key, pretty, fieldRefs := refs, freeVars,
            singleDataVar, aliasInfo }
    return { name := n, isNitro := isNitroModule env n, conjuncts }

/-! ## Cross-declaration grouping (pure, over precomputed `DeclInfo`) -/

/-- Group `rows` by `keyOf`, in the order a total order on
    `(keyOf, tiebreakOf)` gives: a sort, then adjacent rows sharing a key —
    never `HashMap` iteration order. `HashMap`'s order depends on Lean's
    per-process hash seed; `repeatedFindings`'s own group count read 258
    on one run and 259 on another, same code, same tree
    (`docs/spec-module-design.md` §10). `keyOf`/`tiebreakOf` together must
    total-order `rows`: two rows with the same `keyOf` but an unordered
    `tiebreakOf` leave `qsort` free to place either first, which only
    matters where a caller reads "the first row of a group" as a
    representative (`variantFindings` below). -/
def groupByKey {α} [Inhabited α] (rows : Array α) (keyOf : α → String) (tiebreakOf : α → String) :
    Array (String × Array α) :=
  let sorted := rows.qsort fun a b =>
    keyOf a < keyOf b || (keyOf a == keyOf b && tiebreakOf a < tiebreakOf b)
  Id.run do
    let mut out := #[]
    let mut i := 0
    while i < sorted.size do
      let k := keyOf sorted[i]!
      let mut j := i
      let mut g := #[]
      while j < sorted.size && keyOf sorted[j]! == k do
        g := g.push sorted[j]!
        j := j + 1
      out := out.push (k, g)
      i := j
    return out

/-- `repeatedPremise`: every normalized shape that at least two distinct
    declarations use, with one `(decl, prettyConjunct)` pair per use, the
    uses in declaration-name order. -/
def repeatedFindings (decls : Array DeclInfo) : Array (String × Array (Name × String)) := Id.run do
  let mut rows : Array (String × Name × String) := #[]
  for d in decls do
    for c in d.conjuncts do
      rows := rows.push (c.key, d.name, c.pretty)
  let mut out := #[]
  for (key, g) in groupByKey rows (·.1) (fun r => toString r.2.1) do
    let names : Std.HashSet Name := g.foldl (init := {}) fun s r => s.insert r.2.1
    if names.size ≥ 2 then
      out := out.push (key, g.map fun r => r.2)
  return out

/-- `premiseVariant`: every `(binderType, field)` that two or more
    distinct normalized shapes constrain. Each inner entry is one shape
    (its pretty text and the declarations that use it, in declaration-name
    order); the `pretty` text is the alphabetically first declaration's,
    deterministically (the group's own order, `groupByKey`). -/
def variantFindings (decls : Array DeclInfo) :
    Array ((Name × Name) × Array (String × String × Array Name)) := Id.run do
  let mut rows : Array ((Name × Name) × String × String × Name) := #[]
  for d in decls do
    for c in d.conjuncts do
      for ref in c.fieldRefs do
        rows := rows.push (ref, c.key, c.pretty, d.name)
  let mut out := #[]
  for (_, refRows) in groupByKey rows (fun r => s!"{r.1.1}.{r.1.2}")
      (fun r => s!"{r.2.1}#{r.2.2.2}") do
    let ref := refRows[0]!.1
    let byKey := groupByKey refRows (·.2.1) (fun r => toString r.2.2.2)
    if byKey.size ≥ 2 then
      let inner := byKey.map fun (key, krows) =>
        (key, krows[0]!.2.2.1, krows.map fun r => r.2.2.2)
      out := out.push (ref, inner)
  return out

/-- `looseHypothesis`: every conjunct whose only free variable is one
    data binder, restricted to declarations whose shape `repeatedPremise`
    also reports (the single-use exception: a single-use, single-input
    precondition is a proof argument, not a loose hypothesis). -/
def looseFindings (decls : Array DeclInfo) : Array (Name × Name × String) := Id.run do
  let repeatedKeys : Std.HashSet String :=
    (repeatedFindings decls).foldl (init := {}) fun s (k, _) => s.insert k
  let mut out := #[]
  for d in decls do
    for c in d.conjuncts do
      if repeatedKeys.contains c.key then
        if let some fieldVar := c.singleDataVar then
          out := out.push (d.name, fieldVar, c.pretty)
  return out

/-- `aliasHypothesis`: every conjunct of the form `x = f …` with `x` a
    binder of the same declaration. -/
def aliasFindings (decls : Array DeclInfo) : Array (Name × Name × String) := Id.run do
  let mut out := #[]
  for d in decls do
    for c in d.conjuncts do
      if let some (nm, rhs) := c.aliasInfo then
        out := out.push (d.name, nm, rhs)
  return out

/-! ## `layerDiscipline` (§4a) -/

/-- `true` when `s` names `marker` immediately followed by a digit
    (ignoring one optional space), anywhere in `s`. A hand-rolled
    substring scan: the doc comments here are ASCII, so no regex engine
    is needed. -/
def hasMarkerDigit (s marker : String) : Bool :=
  match s.splitOn marker with
  | [] | [_] => false
  | _ :: rest =>
    rest.any fun part =>
      -- Skip at most one leading space, then check the next character.
      let chars := part.toList
      let chars := match chars with
        | ' ' :: more => more
        | _ => chars
      match chars with
      | c :: _ => c.isDigit
      | [] => false

/-- A Nitro spec-level theorem's doc comment cites a paper passage. -/
def nitroCitation (doc : String) : Bool :=
  hasMarkerDigit doc "Nitro:" || hasMarkerDigit doc "SATP:" || hasMarkerDigit doc "ForceMove:"

/-- A Pool spec-level theorem's doc comment cites a contract/circuit line
    or a dated design decision. -/
def poolCitation (doc : String) : Bool :=
  hasMarkerDigit doc ".sol:" || hasMarkerDigit doc ".circom:" ||
    (doc.splitOn "design decision").length > 1

/-- The reflexivity and congruence constants (`Eq.refl a : a = a`,
    `congrArg f h : f a₁ = f a₂`, the motive of every `rw` step). Lean
    fills their explicit data arguments in from the goal. -/
def goalCopyConsts : Array Name :=
  #[``Eq.refl, ``HEq.refl, ``Iff.refl, ``eq_self, ``iff_self, ``congrArg, ``congrFun, ``congr]

/-- For each argument position of the constant `c`, `true` when
    `valueConstants` does not enter an argument at that position:
    - an implicit or instance-implicit argument (`Eq.mpr`'s `α β`, a
      `casesOn`/`rec` motive, `id`'s type in a `show` ascription);
    - for a matcher, also its motive (`Lean.Meta.MatcherInfo.numParams`),
      an explicit argument; its discriminants and alternatives count;
    - for a `goalCopyConsts` constant, an explicit data argument that its
      result type names: a copy of a term of the goal.
    The last rule is not general. An explicit argument that the result
    type names can be the author's choice: `Option.eq_none_or_eq_some
    (s.apply …)` is a case split on `apply`, as `cases h : s.apply …` is. -/
def skippedArgs (c : Name) : StateT (Std.HashMap Name (Array Bool)) MetaM (Array Bool) := do
  if let some s := (← get)[c]? then return s
  let motive := (← getMatcherInfo? c).map (·.numParams)
  let goalCopy := goalCopyConsts.contains c
  let s ← forallTelescope (← getConstInfo c).type fun xs body => do
    let mut out := #[]
    for h : i in [0:xs.size] do
      let d ← xs[i].fvarId!.getDecl
      out := out.push <| ← do
        if !d.binderInfo.isExplicit then pure true
        else if let some m := motive then pure (i == m)
        else if goalCopy then pure (body.containsFVar d.fvarId && !(← isProp d.type))
        else pure false
    return out
  modify (·.insert c s)
  return s

/-- The constants `e` names in a VALUE position: the positions the proof's
    author chose, as opposed to the positions Lean fills in from a type.
    The walk does not enter the binder type of a `fun`, `∀` or `let`, an
    argument `skippedArgs` excludes, nor an implicit argument of a local
    hypothesis (`ih` of an induction: `ih (sg := (sg.transfer a b).getD
    sg) h'` names `transfer` only because unification filled `sg` in). A
    constant that enters the proof only through one of these is named by
    a type: a constructor's field type (destructuring `Nitro.Step.mk` gives
    `h : s.apply … = some s'`), a lemma's instantiated statement (`obtain
    ⟨spent', h⟩ := markSpent_succeeds …`), or a rewrite motive. Every other
    position counts, including a case-split discriminant (`cases h :
    s.apply apps caller op`) and an explicit witness. -/
partial def valueConstants (e : Expr) (acc : NameSet) :
    StateT (Std.HashMap Name (Array Bool)) MetaM NameSet := do
  match e with
  | .const n _ => return acc.insert n
  | .app .. =>
    let args := e.getAppArgs
    let mut acc := acc
    let mut skip := #[]
    match e.getAppFn with
    | .const n _ =>
      acc := acc.insert n
      skip ← skippedArgs n
    | .fvar fv => skip := implicitKinds (← instantiateMVars (← fv.getType)) #[]
    | f => acc ← valueConstants f acc
    for h : i in [0:args.size] do
      if skip[i]?.getD false then continue
      acc ← valueConstants args[i] acc
    return acc
  | .lam n t b bi => withLocalDecl n bi t fun x => valueConstants (b.instantiate1 x) acc
  | .letE n t v b _ => do
    let acc ← valueConstants v acc
    withLetDecl n t v fun x => valueConstants (b.instantiate1 x) acc
  | .mdata _ b => valueConstants b acc
  | .proj _ _ b => valueConstants b acc
  | _ => return acc
where
  /-- For each leading `∀` binder of `t`, `true` when it is not explicit. -/
  implicitKinds (t : Expr) (out : Array Bool) : Array Bool :=
    match t with
    | .forallE _ _ b bi => implicitKinds b (out.push !bi.isExplicit)
    | _ => out

/-- `c` is an unfolding auxiliary of `op`: an equation lemma (`op.eq_<n>`,
    `op.eq_def`), a matcher compiled from `op`'s body or one of its lemmas
    (`op.match_<n>`, `op.match_<n>.splitter`, `op.match_<n>.eq_<k>`), or
    `op`'s functional induction principle (`op.induct`). A proof term that
    names one of these unfolded `op` (`type-doctrine.md` §4a: "its proof
    term names the operation's equation or match lemmas"), wherever the
    name sits in the term. -/
def isUnfoldAux (op c : Name) : Bool :=
  c != op && op.isPrefixOf c &&
    match (c.replacePrefix op .anonymous).components.head? with
    | some (.str _ s) => "eq_".isPrefixOf s || "match_".isPrefixOf s || s == "induct"
    | _ => false

/-- The constants a declaration's statement names, directly or through an
    `ArmadaLean` inductive type it names: that type's constructor field
    types, its `casesOn` and its `rec`. A statement about `Step s s'` is a
    step lemma; `Step`'s constructors are defined by the base operations, so
    a proof about one step names them (the Pool's `insertLeaves` in the post
    state of `Step.shield`, Nitro's `apply` in the field of `Step.mk`). One
    level only: `Reachable` names `Step` through its `step` constructor,
    and that does not make `Step.casesOn` a constant of a statement about
    `Reachable`. -/
def statementConstants (env : Environment) (type : Expr) : MetaM NameSet := do
  let direct := type.getUsedConstants
  let mut out : NameSet := direct.foldl (init := {}) NameSet.insert
  for c in direct do
    let some m := declModule env c | continue
    if !(`ArmadaLean).isPrefixOf m then continue
    let some (.inductInfo ii) := env.find? c | continue
    out := (out.insert (c ++ `casesOn)).insert (c ++ `rec)
    for k in ii.ctors do
      for d in (← getConstInfo k).type.getUsedConstants do
        out := out.insert d
  return out

/-- The base operations of `baseOps` that the proof of `n` names directly
    or unfolds, and that `n`'s statement does not name
    (`statementConstants`). A base operation counts when its own name is in
    a value position of the proof term (`valueConstants`), or when any
    unfolding auxiliary of it occurs anywhere in the proof term
    (`isUnfoldAux`). A base operation the statement names is not a layer
    violation: an equation about `s.apply …` embeds `apply` in every proof
    of it, whatever the technique (checked across 11 proofs written in
    different styles), and such a theorem is the per-call lemma itself.

    Measured on `integrated` `0b933ad9`: the earlier check, which counted
    every constant of the proof term, reported 15 theorems. This measure
    reports 5. The other 10 named a base operation only through a type.

    Not detected: an unfolding by definitional equality alone (`dsimp only
    [op]`, `show`, `rfl`, or `simp only [op]` with an `rfl` equation lemma,
    which `simp` applies with no proof step). Such an unfolding leaves no
    constant in the proof term. Sealing the base operations
    (`type-doctrine.md` §4a rule 4) makes it fail to elaborate. -/
def layerHits (env : Environment) (n : Name) (baseOps : Array Name) : MetaM (Array Name) := do
  let info ← getConstInfo n
  let some val := info.value? (allowOpaque := true) | return #[]
  let named ← statementConstants env info.type
  let used := val.getUsedConstants
  let direct ← (valueConstants val {}).run' {}
  return baseOps.filter fun op => !named.contains op &&
    (direct.contains op || used.any (isUnfoldAux op))

/-- `layerDiscipline`: every spec-level declaration (its doc comment cites
    a source) with a `layerHits` finding against its own layer's base
    operations. -/
def layerFindings (env : Environment) (names : Array Name) : MetaM (Array (Name × Bool × Array Name)) := do
  let mut out := #[]
  for n in names do
    let some doc ← findDocString? env n | continue
    let isNitro := isNitroModule env n
    let cited := if isNitro then nitroCitation doc else poolCitation doc
    if !cited then continue
    let hit ← layerHits env n (if isNitro then nitroBaseOps else poolBaseOps)
    if !hit.isEmpty then
      out := out.push (n, isNitro, hit)
  return out

/-! ## A cached global pass, shared by `scripts/type_lint.lean` and the
    per-declaration `@[env_linter]` wrappers below. -/

/-- All five linters' findings, computed once per process. -/
structure GlobalData where
  decls : Array DeclInfo
  repeated : Array (String × Array (Name × String))
  variant : Array ((Name × Name) × Array (String × String × Array Name))
  loose : Array (Name × Name × String)
  alias : Array (Name × Name × String)
  layer : Array (Name × Bool × Array Name)

/-- Run every declaration-level pass, then every cross-declaration pass. -/
def computeGlobalData : MetaM GlobalData := do
  let env ← getEnv
  let names := scopedDeclNames env
  let mut decls : Array DeclInfo := #[]
  for n in names do
    decls := decls.push (← analyzeDecl env n)
  return {
    decls
    repeated := repeatedFindings decls
    variant := variantFindings decls
    loose := looseFindings decls
    alias := aliasFindings decls
    layer := ← layerFindings env (scopedTheoremNames env)
  }

initialize globalDataRef : IO.Ref (Option GlobalData) ← IO.mkRef none

/-- `computeGlobalData`, memoized for the life of the process. -/
def getGlobalData : MetaM GlobalData := do
  match ← globalDataRef.get with
  | some d => return d
  | none =>
    let d ← computeGlobalData
    globalDataRef.set (some d)
    return d

/-! ## `@[env_linter]` wrappers (report-only: `disabled`, so `#lint`
    never runs them by default; `scripts/type_lint.lean` reports the
    full corpus directly from `GlobalData`, below). -/

@[env_linter disabled] def repeatedPremise : Linter where
  noErrorsFound := "No repeated hypothesis shapes."
  errorsFound := "REPEATED HYPOTHESIS SHAPES (type-doctrine.md §3, rule 1, report-only)."
  test declName := do
    let data ← getGlobalData
    let hits := data.repeated.filter fun (_, uses) => uses.any (·.1 == declName)
    if hits.isEmpty then return none
    let msgs := hits.map fun (key, uses) =>
      let others := (uses.map Prod.fst).filter (· != declName) |>.toList.eraseDups
      m!"shape {key} also in {others}"
    return some (MessageData.joinSep msgs.toList "\n")

@[env_linter disabled] def premiseVariant : Linter where
  noErrorsFound := "No field constrained by two different shapes."
  errorsFound := "A FIELD IS CONSTRAINED BY TWO DIFFERENT SHAPES (type-doctrine.md §3, rule 1, report-only)."
  test declName := do
    let data ← getGlobalData
    let hits := data.variant.filter fun (_, shapes) =>
      shapes.any fun (_, _, names) => names.contains declName
    if hits.isEmpty then return none
    let msgs := hits.map fun ((ty, field), shapes) =>
      m!"{ty}.{field}: {shapes.size} variants: {shapes.toList.map (·.2.1)}"
    return some (MessageData.joinSep msgs.toList "\n")

@[env_linter disabled] def looseHypothesis : Linter where
  noErrorsFound := "No single-input, repeated-shape hypothesis."
  errorsFound := "SINGLE-INPUT, REPEATED-SHAPE HYPOTHESIS (type-doctrine.md §3, rule 2, report-only)."
  test declName := do
    let data ← getGlobalData
    let hits := data.loose.filter (·.1 == declName)
    if hits.isEmpty then return none
    let msgs := hits.map fun (_, fieldVar, pretty) => m!"{fieldVar}: {pretty}"
    return some (MessageData.joinSep msgs.toList "\n")

@[env_linter disabled] def aliasHypothesis : Linter where
  noErrorsFound := "No hypothesis restates a binder as an equation."
  errorsFound := "A HYPOTHESIS RESTATES A BINDER AS AN EQUATION (type-doctrine.md §3, rule 3, report-only)."
  test declName := do
    let data ← getGlobalData
    let hits := data.alias.filter (·.1 == declName)
    if hits.isEmpty then return none
    let msgs := hits.map fun (_, binderName, rhs) => m!"{binderName} = {rhs}"
    return some (MessageData.joinSep msgs.toList "\n")

@[env_linter disabled] def layerDiscipline : Linter where
  noErrorsFound := "No spec-level declaration's proof term names a base operation."
  errorsFound := "A SPEC-LEVEL DECLARATION'S PROOF TERM NAMES A BASE OPERATION (type-doctrine.md §4a, report-only)."
  test declName := do
    let data ← getGlobalData
    let some (_, _, hit) := data.layer.find? (·.1 == declName) | return none
    return some m!"names base operation(s) {hit.toList}"

end ArmadaLean.Lint.TypeDoctrine
