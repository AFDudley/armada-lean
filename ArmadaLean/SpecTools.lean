/-
  ArmadaLean.SpecTools — the Lean half of the spec check. Design record:
  `docs/spec-module-design.md`. Operator decisions 2026-10-31: spec membership
  is an algorithm, reachability is a type, and the check stores no list.

  This file declares no model and no statement. It gives five tools:

  - `obtain_reach ⟨s, h⟩ := s` (tactic) and `obtain_reach% ⟨s, h⟩ := s; t`
    (term): the access repair that `scripts/convert_spec.py` inserts into a proof
    body when it changes a state binder `(s : S) (h : R s)` into one reachable-state
    binder `(s : {s : S // R s})`. They restore `s` and `h` with their old types.
  - `spec_premise% D`: the premise of the spec definition `D`. It is
    `∃ x₁ … xₙ, True` over every binder of `D`: its parameters and the `∀`
    binders of its statement.
  - `spec_witness e`: proves `spec_premise% D` from `e`, a non-vacuity example in
    its own form (`verification.md` §5a). It unifies the hypotheses of the
    premise with the facts that `e` gives.
  - `#check_spec_bindings`: fails the build when a spec definition of this module
    and its theorem do not have definitionally equal types.
  - `SpecTools.reachPredicates`, `SpecTools.stateHeads`: the reachability
    predicates and the machine state types, computed from the environment.
-/
import Lean

open Lean Elab Meta Tactic Term Command

namespace ArmadaLean.SpecTools

/-! ## Names -/

/-- `N.Spec.x` is the spec definition of the theorem `N.x`: the component `Spec`
    comes immediately before the last component. -/
def specTarget? : Name → Option Name
  | .str (.str p "Spec") s => some (.str p s)
  | _ => none

/-- The spec definition name of the theorem `N.x`: `N.Spec.x`. -/
def specNameOf : Name → Option Name
  | .str p s => some (.str (.str p "Spec") s)
  | _ => none

/-- The witness name of the spec definition `D`: `D.witness`. -/
def witnessNameOf (d : Name) : Name := .str d "witness"

/-! ## Subtype projections of an anonymous constructor -/

/-- Replace each projection of an anonymous constructor `⟨x, h⟩` of a subtype by
    `x` or `h`. A projection is `Subtype.val`, `Subtype.property`, or a reducible
    accessor that unfolds to one of them (`ReachableState.state`). The result is
    definitionally equal to the input. -/
def cleanSubtypeMk (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun t => do
    let t' := t.consumeMData
    unless t'.isApp do return .continue
    let a := t'.appArg!.consumeMData
    unless a.isAppOfArity ``Subtype.mk 4 do return .continue
    unless t'.getAppFn.isConst do return .continue
    let x := a.getArg! 2
    let h := a.getArg! 3
    let r ← whnfR t'
    if r == x || r == h then return .done r
    return .continue)

/-- Apply `cleanSubtypeMk` to the target and to every local hypothesis of `g`. -/
def cleanGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let t ← instantiateMVars (← g.getType)
  let t' ← cleanSubtypeMk t
  if t' != t then g ← g.replaceTargetDefEq t'
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    let ty' ← cleanSubtypeMk ty
    if ty' != ty then g ← g.replaceLocalDeclDefEq ld.fvarId ty'
  return g

/-! ## Access repair -/

/-- Strip leading `∀` binders without opening them. -/
partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | e => e


/-- The theorems that state `M.Reachable s ↔ R … s` (or the reverse) for a
    machine `M` and a predicate `R` of the model. -/
def reachIffs : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    unless ci matches .thmInfo _ do continue
    -- a constant of an `ArmadaLean` module, or of the current file
    if let some i := env.getModuleIdxFor? n then
      unless (`ArmadaLean).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    let b := stripForall ci.type
    if b.isAppOfArity ``Iff 2 then
      if (b.getArg! 0).isAppOf `ArmadaLean.Machine.Reachable || (b.getArg! 1).isAppOf `ArmadaLean.Machine.Reachable then
        out := out.push n
  return out

/-- `isDefEq` at `instances` transparency: a match up to instances and reducible
    definitions, which stays fast on the large terms of the model. -/
def isDefEqI (a b : Expr) : MetaM Bool := withTransparency .instances <| isDefEq a b

/-- A proof of `T` from `h : M.Reachable s`: `h` itself when the types agree, else
    `(iff).mp h` or `(iff).mpr h` for an iff of `iffs` (`reachIffs`). -/
def castReachWith (iffs : Array Name) (h T : Expr) : MetaM Expr := do
  let hT ← inferType h
  if ← isDefEqI hT T then return h
  for n in iffs do
    for (src, dst, dir) in [(0, 1, ``Iff.mp), (1, 0, ``Iff.mpr)] do
      let r ← commitWhenSome? do
        let c ← mkConstWithFreshMVarLevels n
        let (args, _, b) ← forallMetaTelescope (← inferType c)
        unless ← isDefEqI (b.getArg! src) hT do return none
        unless ← isDefEqI (b.getArg! dst) T do return none
        return some (← mkAppM dir #[mkAppN c args, h])
      if let some pf := r then return ← instantiateMVars pf
  throwError "obtain_reach: no proved iff turns{indentExpr hT}\ninto{indentExpr T}"

/-- `castReachWith` over all proved reachability iffs (`reachIffs`). -/
def castReach (h T : Expr) : MetaM Expr := do
  castReachWith (← reachIffs) h T

/-- `reach_cast% h` proves the expected type from `h : M.Reachable s` (`castReach`). -/
elab "reach_cast% " h:term : term <= T => do
  castReach (← elabTerm h none) T

/-- `obtain_reach ⟨s, h⟩ := s` splits the reachable-state binder `s` into the
    state `s` and its reachability proof `h`. It then writes every `↑⟨s, h⟩` in
    the goal and the context as `s`. The context is the one the proof had
    before the conversion. `obtain_reach ⟨s, h : T⟩ := s` also turns `h` into
    the native predicate `T` through a proved iff (`castReach`). -/
syntax (name := obtainReach) "obtain_reach " "⟨" ident ", " ident (" : " term)? "⟩" " := " term :
  tactic

elab_rules : tactic
  | `(tactic| obtain_reach ⟨$x, $h⟩ := $e) => do
    evalTactic (← `(tactic| obtain ⟨$x:ident, $h:ident⟩ := $e))
    replaceMainGoal [← cleanGoal (← getMainGoal)]
  | `(tactic| obtain_reach ⟨$x, $h : $T⟩ := $e) => do
    evalTactic (← `(tactic| obtain ⟨$x:ident, hraw⟩ := $e))
    replaceMainGoal [← cleanGoal (← getMainGoal)]
    evalTactic (← `(tactic| have $h:ident : $T := reach_cast% hraw))
    evalTactic (← `(tactic| clear hraw))

/-- The term form of `obtain_reach`, for a proof body that is a term. -/
syntax "obtain_reach% " "⟨" ident ", " ident (" : " term)? "⟩" " := " term "; " term : term

macro_rules
  | `(obtain_reach% ⟨$x, $h⟩ := $e; $t) =>
    `(by obtain_reach ⟨$x, $h⟩ := $e; exact $t)
  | `(obtain_reach% ⟨$x, $h : $T⟩ := $e; $t) =>
    `(by obtain_reach ⟨$x, $h : $T⟩ := $e; exact $t)

/-! ## Premise of a spec definition -/

/-- The claim of a spec statement: `∀ hypotheses, Claim conclusion`. It marks where
    the hypotheses end, so `spec_premise%` does not take the binders of the
    conclusion (`∀ p ∈ c.participants, …`) as hypotheses. It is the identity. -/
@[reducible] def Claim (p : Prop) : Prop := p

/-- `∃ x₁ … xₙ, b` over the free variables `xs`. -/
def mkExistsChain (xs : Array Expr) (b : Expr) : MetaM Expr :=
  xs.foldrM (init := b) fun x acc => do
    let lam ← mkLambdaFVars #[x] acc
    mkAppM ``Exists #[lam]

/-- Run `k` on the binders of the spec definition `d` (its parameters, then the
    `∀` binders of its value up to `Claim`) and on the conclusion. -/
def withSpecTelescope {α} (d : Name) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let ci ← getConstInfoDefn d
  unless ci.levelParams.isEmpty do
    throwError "spec definition {d} has universe parameters; the spec check supports none"
  lambdaTelescope ci.value fun ps body =>
    forallTelescope body fun xs concl => k (ps ++ xs) concl

/-- The premise of the spec definition `d`: `∃` over all its binders, body `True`. -/
def premiseOf (d : Name) : MetaM Expr :=
  withSpecTelescope d fun xs _ => mkExistsChain xs (mkConst ``True)

/-- `d` needs a non-vacuity witness when one of its binders is a proposition (a
    hypothesis). A theorem with no hypotheses beyond its binders' types needs
    none (`verification.md` §5a). -/
def needsWitness (d : Name) : MetaM Bool :=
  withSpecTelescope d fun xs _ => xs.anyM fun x => do isProp (← inferType x)

/-- `spec_premise% D` elaborates to the premise of the spec definition `D`. -/
elab "spec_premise% " id:ident : term => do
  let d ← realizeGlobalConstNoOverloadWithInfo id
  premiseOf d

/-! ## Non-vacuity witness from an example -/

/-- Build the proof of `∃ x₁ … xₙ, True`. A value binder becomes a fresh
    metavariable. A reachable-state binder `{y // p y}` becomes `⟨?y, ?hy⟩`. A
    proposition binder becomes an obligation. Returns the proof, the value
    metavariables and the obligations. -/
partial def openPremise (t : Expr) : MetaM (Expr × Array MVarId × Array MVarId) := do
  let t ← cleanSubtypeMk (← instantiateMVars t).cleanupAnnotations.headBeta
  let t := t.cleanupAnnotations
  if t.isConstOf ``True then return (mkConst ``True.intro, #[], #[])
  unless t.isAppOfArity ``Exists 2 do throwError "spec_witness: not a premise: {t}"
  let α := t.getArg! 0
  let body := t.getArg! 1
  let (v, vals, obls) ← do
    if ← isProp α then
      let o ← mkFreshExprMVar α
      pure (o, #[], #[o.mvarId!])
    else
      let α' ← whnf α
      if α'.isAppOfArity ``Subtype 2 then
        let y ← mkFreshExprMVar (α'.getArg! 0)
        let hy ← mkFreshExprMVar ((α'.getArg! 1).beta #[y])
        let v := mkApp4 (mkConst ``Subtype.mk [← getLevel (α'.getArg! 0)])
          (α'.getArg! 0) (α'.getArg! 1) y hy
        pure (v, #[y.mvarId!], #[hy.mvarId!])
      else
        let x ← mkFreshExprMVar α
        pure (x, #[x.mvarId!], #[])
  let (rest, vals', obls') ← openPremise (body.beta #[v])
  -- `rest` proves the cleaned body, which is definitionally equal to `body v`; the
  -- kernel checks the whole term when the witness is added.
  let pf := mkApp4 (mkConst ``Exists.intro [← getLevel α]) α body v rest
  return (pf, vals ++ vals', obls ++ obls')

/-- Close the obligations `obls`, in order, with local hypotheses. Backtracks over
    the choice of hypothesis and keeps the choice that leaves the fewest
    obligations open. Returns the obligations that no hypothesis closes. -/
partial def matchObligations (iffs : Array Name) (hyps : Array Expr) (obls : List MVarId) :
    MetaM (List MVarId) := do
  match obls with
  | [] => return []
  | o :: rest =>
    if ← o.isAssigned then return ← matchObligations iffs hyps rest
    let oty ← instantiateMVars (← o.getType)
    let start ← saveState
    let mut best : Option (List MVarId × Meta.SavedState) := none
    for h in hyps do
      start.restore
      -- the fact itself, or a native reachability fact through a proved iff
      let pf? ← if ← isDefEqI (← inferType h) oty then
          pure (some h)
        else if oty.isAppOf `ArmadaLean.Machine.Reachable then
          try some <$> castReachWith iffs h oty catch _ => pure none
        else pure none
      let some pf := pf? | continue
      o.assign pf
      let left ← try matchObligations iffs hyps rest catch _ => continue
      if left.isEmpty then return []
      if best.all (left.length < ·.1.length) then best := some (left, ← saveState)
    -- No hypothesis closes `o`: keep it open for the closing tactics.
    start.restore
    let left := o :: (← matchObligations iffs hyps rest)
    if let some (bl, bs) := best then
      if bl.length ≤ left.length then
        bs.restore
        return bl
    return left

/-- Close a remaining obligation by a decision procedure. -/
def closeByTactic (o : MVarId) : TacticM Unit := do
  let ty ← instantiateMVars (← o.getType)
  if ty.hasExprMVar then throwError "spec_witness: open obligation {ty} still has holes"
  let gs ← try
      Tactic.run o do evalTactic (← `(tactic| first | rfl | decide | trivial | simp))
    catch _ => throwError "spec_witness: no fact of the example proves{indentExpr ty}"
  unless gs.isEmpty do throwError "spec_witness: cannot close{indentExpr ty}"

/-- Give an unassigned value metavariable a value: an instance, a local of its
    type, or a constant of `cands` (the shared values of the example's namespace). -/
def closeValue (cands : Array Name) (v : MVarId) : MetaM Unit := do
  if ← v.isAssigned then return
  let ty ← instantiateMVars (← v.getType)
  if (← isClass? ty).isSome then
    v.assign (← synthInstance ty); return
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let s ← saveState
    if ← isDefEq ld.type ty then v.assign ld.toExpr; return
    s.restore
  for c in cands do
    let s ← saveState
    let e ← mkConstWithFreshMVarLevels c
    if ← withTransparency .instances <| isDefEq (← inferType e) ty then v.assign e; return
    s.restore
  -- No hypothesis constrains this binder: any value serves. A type parameter
  -- becomes `Nat` (the destination type of `NonVacuity.lean`); another binder
  -- takes `default` or a `Classical.choice` of a `Nonempty` instance.
  if ty.isType then v.assign (mkConst ``Nat); return
  if let .some inst ← trySynthInstance (← mkAppM ``Inhabited #[ty]) then
    v.assign (← mkAppOptM ``Inhabited.default #[ty, inst]); return
  if let .some inst ← trySynthInstance (← mkAppM ``Nonempty #[ty]) then
    v.assign (← mkAppOptM ``Classical.choice #[ty, inst]); return
  throwError "spec_witness: no value for a binder of type {ty}"

/-- Split every `∃` and `∧` fact of the context into its parts, and keep the
    whole fact too: a hypothesis of the premise can be a conjunction or an
    existential itself. `done` holds the facts already split. -/
partial def splitFacts (g : MVarId) (done : FVarIdSet) : MetaM MVarId := g.withContext do
  for ld in (← getLCtx) do
    if ld.isImplementationDetail || done.contains ld.fvarId then continue
    let ty ← whnfR ld.type
    if ty.isAppOfArity ``And 2 then
      let (l, g) ← (← g.assert `hspecl (ty.getArg! 0) (← mkAppM ``And.left #[ld.toExpr])).intro1P
      let (r, g) ← (← g.assert `hspecr (ty.getArg! 1) (← mkAppM ``And.right #[ld.toExpr])).intro1P
      let _ := (l, r)
      return ← splitFacts g (done.insert ld.fvarId)
    if ty.isAppOfArity ``Exists 2 then
      let (keep, g) ← (← g.assert `hspeck ld.type ld.toExpr).intro1P
      let gs ← g.cases ld.fvarId
      let some sub := gs[0]? | throwError "spec_witness: cannot split {ld.type}"
      return ← splitFacts sub.mvarId (done.insert keep)
  return g

/-- The embedded property of a non-Prop local `e` whose type is a refined type
    in the `Subtype` form (`TimedChannel ε`, …): `none`
    when `e`'s type does not unfold to `Subtype`. The example's own context
    carries such a local whole (`splitFacts` destructs only `Exists`/`And`),
    so its property is not otherwise a usable fact; this exposes it as one,
    matching the obligation that `openPremise` creates for the same shape in
    the premise (`spec_premise%`'s `Subtype` branch). -/
def subtypeProjections (e : Expr) : MetaM (Option Expr) := do
  let ty ← whnf (← inferType e)
  unless ty.isAppOfArity ``Subtype 2 do return none
  try some <$> mkAppM ``Subtype.property #[e] catch _ => return none


/-- `spec_witness e` proves a goal `spec_premise% D` from the example proof `e`.
    It splits every `∃` and `∧` of `e` into local facts. It then closes each
    hypothesis of the premise with one of these facts (unification fixes the
    binder values), and closes the rest with `rfl`, `decide`, `trivial` or `simp`. -/
elab "spec_witness " e:ident : tactic => do
  -- The shared values of the example's namespace (`NonVacuity.apps0`, `c1`, …),
  -- in name order: values for binders that no hypothesis constrains.
  let exName ← realizeGlobalConstNoOverloadWithInfo e
  let ns := exName.getPrefix.getPrefix
  let env ← getEnv
  let mut cands : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless ci matches .defnInfo _ do continue
    unless n.getPrefix == ns && !n.isInternal do continue
    unless ci.levelParams.isEmpty do continue
    if ci.type.isForall then continue
    cands := cands.push n
  cands := cands.qsort (·.toString < ·.toString)
  evalTactic (← `(tactic| have hspecw := $e))
  let g ← splitFacts (← getMainGoal) {}
  g.withContext do
    let (pf, vals, obls) ← openPremise (← g.getType)
    let hyps ← (← getLCtx).foldlM (init := #[]) fun acc ld => do
      if ld.isImplementationDetail then return acc
      if ← isProp ld.type then return acc.push ld.toExpr
      else if let some pf ← subtypeProjections ld.toExpr then return acc.push pf
      else return acc
    let left ← matchObligations (← reachIffs) hyps obls.toList
    for v in vals do closeValue cands v
    for o in left do
      if !(← o.isAssigned) then closeByTactic o
    let pf ← instantiateMVars pf
    if pf.hasExprMVar then throwError "spec_witness: the proof still has holes: {pf}"
    g.assign pf
    replaceMainGoal []

/-! ## Statement protection -/

/-- The spec definition `d` as one closed proposition: its parameters become `∀`
    binders in front of its value. -/
def specType (d : Name) : MetaM Expr := do
  let ci ← getConstInfoDefn d
  lambdaTelescope ci.value fun ps body => mkForallFVars ps body

/-- `none` when the theorem of the spec definition `d` exists and its type is
    definitionally equal to `d`; otherwise the reason. -/
def bindingError? (d : Name) : MetaM (Option String) := do
  let some t := specTarget? d | return some s!"{d} is not a spec definition name"
  let some tci := (← getEnv).find? t | return some s!"no theorem {t} for spec definition {d}"
  unless tci matches .thmInfo _ do return some s!"{t} is not a theorem"
  unless tci.levelParams.isEmpty do return some s!"{t} has universe parameters"
  if ← isDefEq (← specType d) tci.type then return none
  return some s!"the type of {t} is not definitionally equal to {d}"

/-- Fail when a spec definition of this module and its theorem differ. -/
elab "#check_spec_bindings" : command => liftTermElabM do
  let env ← getEnv
  for (d, ci) in env.constants.map₂.toList do
    unless ci matches .defnInfo _ do continue
    if (specTarget? d).isNone then continue
    if let some err ← bindingError? d then throwError err

/-! ## Machines and reachability -/

/-- The state type head of every `Machine` definition in the environment
    (`ArmadaLean/Machines.lean` scans the same set). -/
def stateHeads : MetaM NameSet := do
  let env ← getEnv
  let mut out : NameSet := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless ci matches .defnInfo _ do continue
    unless (stripForall ci.type).isAppOfArity `ArmadaLean.Machine 1 do continue
    let h ← forallTelescope ci.type fun _ b => pure (b.getArg! 0).getAppFn
    if let some c := h.constName? then out := out.insert c
  return out

/-- The reachability predicates: `Machine.Reachable`, and the predicate `R` of
    every proved iff `M.Reachable s ↔ R … s` (`reachIffs`). The converter
    turns a hypothesis with such a predicate into a `ReachableState` binder. -/
def reachPredicates : MetaM NameSet := do
  let mut out : NameSet := ({} : NameSet).insert `ArmadaLean.Machine.Reachable
  for n in ← reachIffs do
    let b := stripForall (← getConstInfo n).type
    for side in [b.getArg! 0, b.getArg! 1] do
      if let some c := side.getAppFn.constName? then out := out.insert c
  return out

end ArmadaLean.SpecTools
