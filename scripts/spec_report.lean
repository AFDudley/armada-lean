/-
  The computed report of the spec check (`docs/spec-module-design.md`).
  Run: `lake env lean scripts/spec_report.lean`. Prints ONE JSON object on
  stdout. `scripts/spec_check.py` and `scripts/convert_spec.py` read it.

  The report reads the checked environment, not source text. It stores no
  list: every fact below is computed on each run.

  - `theorems`: every `theorem` constant of an `ArmadaLean` module, outside
    `ArmadaLean.Spec` and `ArmadaLean.Witness`: its doc string, its axioms
    (`collectAxioms`, the data of `#print axioms`), its binders, and its spec
    definition `N.Spec.x` with the binding, state and witness facts.
  - `spec_defs`, `witnesses`: every spec definition and every witness in the
    environment, so the check finds one with no theorem.
  - `state_heads`, `reach_preds`: `SpecTools.stateHeads`,
    `SpecTools.reachPredicates`.
-/
import ArmadaLean
import ArmadaLean.SpecTools

open Lean Elab Meta
open ArmadaLean.SpecTools

/-- The module of a constant, or `none` for a constant of the current file. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- `true` for a module of the spec layer, whose constants are not theorems
    of the model. -/
def isSpecLayer (m : Name) : Bool :=
  (`ArmadaLean.Spec).isPrefixOf m || (`ArmadaLean.Witness).isPrefixOf m

/-- The head constant of a type, if any. -/
def headConst? (e : Expr) : Option Name := e.consumeMData.getAppFn.constName?

/-- `true` when `ty` unfolds to `{x : S // M.Reachable x}` with `S` a machine
    state type: `ReachableState M` (`ArmadaLean/Types/Reachable.lean`). -/
def isReachSubtype (heads : NameSet) (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  unless ty.isAppOfArity ``Subtype 2 do return false
  let some s := headConst? (ty.getArg! 0) | return false
  unless heads.contains s do return false
  let p := ty.getArg! 1
  let body := match p with
    | .lam _ _ b _ => b
    | e => e
  return headConst? body == some `ArmadaLean.Machine.Reachable

/-- The binder facts of a telescope. -/
def binderFacts (heads preds : NameSet) (xs : Array Expr) : MetaM (Array Json) := do
  let mut out := #[]
  for i in [:xs.size] do
    let x := xs[i]!
    let ty ← instantiateMVars (← inferType x)
    let prop ← isProp ty
    let state := (headConst? ty).any heads.contains
    let sub ← isReachSubtype heads ty
    let mut reachOf : Option Nat := none
    if prop then
      if let some r := headConst? ty then
        if preds.contains r && ty.consumeMData.getAppNumArgs > 0 then
          let a := ty.consumeMData.appArg!
          if let some j := xs.findIdx? (· == a) then
            if j < i then reachOf := some j
    out := out.push <| Json.mkObj [
      ("name", toJson (← x.fvarId!.getUserName).toString),
      ("prop", toJson prop), ("state", toJson state), ("reach_sub", toJson sub),
      ("head", toJson ((headConst? ty).map toString)),
      ("type", toJson (toString (← withOptions (·.setBool `pp.notation false) (ppExpr ty)))),
      ("reach_of", toJson reachOf)]
  return out

/-- The `ArmadaLean` axioms that every value of the binder types `tys` must supply.
    The walk follows a definition's type and value and a structure's field types,
    because every field must hold. It does not follow an inductive's constructors:
    one constructor suffices (a reachable pool state needs no transact step). -/
def requiredAxioms (tys : List Expr) : MetaM (List Name) := do
  let env ← getEnv
  let inModel (c : Name) : Bool := (moduleOf? env c).any (`ArmadaLean).isPrefixOf
  let mut todo : List Name := tys.foldl (fun acc t => t.getUsedConstants.toList ++ acc) []
  let mut seen : NameSet := {}
  let mut out : List Name := []
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c || !inModel c then continue
    seen := seen.insert c
    match env.find? c with
    | some (.axiomInfo _) => out := c :: out
    | some (.defnInfo v) =>
      todo := v.type.getUsedConstants.toList ++ v.value.getUsedConstants.toList ++ todo
    | some (.inductInfo v) =>
      if isStructure env c then
        for k in v.ctors do
          if let some kci := env.find? k then todo := kci.type.getUsedConstants.toList ++ todo
    | _ => pure ()
  return out

/-- The facts of a spec definition `d`. -/
def specFacts (heads : NameSet) (d : Name) : MetaM Json := do
  let env ← getEnv
  let doc := (← findDocString? env d).getD ""
  let err ← bindingError? d
  let (raw, reach) ← withSpecTelescope d fun xs _ => do
    let raw ← xs.anyM fun x => do
      return (headConst? (← instantiateMVars (← inferType x))).any heads.contains
    let reach ← xs.anyM fun x => do isReachSubtype heads (← inferType x)
    return (raw, reach)
  let needs ← needsWitness d
  -- The axioms that a value of every premise binder must supply. A witness whose
  -- premise needs a declared primitive (an axiom that is not a proposition, such as
  -- `EdDSAVerify`) has no concrete proof (`docs/spec-module-design.md` §5).
  let premiseAxioms ← withSpecTelescope d fun xs _ => do
    let tys ← xs.toList.mapM fun x => do instantiateMVars (← inferType x)
    return (← requiredAxioms tys).map toString
  let w := witnessNameOf d
  let witness ← match env.find? w with
    | none => pure Json.null
    | some wci => do
      let ok ← isDefEq wci.type (← premiseOf d)
      let axs ← collectAxioms w
      pure <| Json.mkObj [("name", toJson w.toString), ("type_ok", toJson ok),
        ("axioms", toJson (axs.map toString)),
        ("module", toJson ((moduleOf? env w).map toString))]
  return Json.mkObj [("name", toJson d.toString), ("doc", toJson doc),
    ("module", toJson ((moduleOf? env d).map toString)),
    ("binding_error", toJson err), ("raw_state", toJson raw), ("reach_state", toJson reach),
    ("needs_witness", toJson needs), ("premise_axioms", toJson premiseAxioms), ("witness", witness)]

#eval show MetaM Unit from do
  let env ← getEnv
  let heads ← stateHeads
  let preds ← reachPredicates
  let mut theorems := #[]
  let mut specDefs := #[]
  let mut witnesses := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    let some m := moduleOf? env n | continue
    unless (`ArmadaLean).isPrefixOf m do continue
    if isSpecLayer m then
      if ci matches .defnInfo _ && (specTarget? n).isSome then
        specDefs := specDefs.push (toJson n.toString)
      if ci matches .thmInfo _ then
        if let .str d "witness" := n then
          if (specTarget? d).isSome then witnesses := witnesses.push (toJson n.toString)
      continue
    unless ci matches .thmInfo _ do continue
    let some rng ← findDeclarationRanges? n | continue
    let doc := (← findDocString? env n).getD ""
    let axs ← collectAxioms n
    let binders ← forallTelescope ci.type fun xs _ => binderFacts heads preds xs
    let spec ← match specNameOf n with
      | some d => if (env.find? d).isSome then specFacts heads d else pure Json.null
      | none => pure Json.null
    theorems := theorems.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson m.toString),
      ("line", toJson rng.selectionRange.pos.line), ("doc", toJson doc),
      ("axioms", toJson (axs.map toString)), ("binders", Json.arr binders), ("spec", spec)]
  let mut machines := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless ci matches .defnInfo _ do continue
    unless (stripForall ci.type).isAppOfArity `ArmadaLean.Machine 1 do continue
    machines := machines.push <| Json.mkObj [("name", toJson n.toString),
      ("module", toJson ((moduleOf? env n).map toString))]
  let mut iffs := #[]
  for n in ← reachIffs do
    let b := stripForall (← getConstInfo n).type
    let side (e : Expr) := toJson ((e.getAppFn.constName?).map toString)
    iffs := iffs.push <| Json.mkObj [("name", toJson n.toString),
      ("lhs", side (b.getArg! 0)), ("rhs", side (b.getArg! 1))]
  IO.println <| Json.compress <| Json.mkObj [
    ("machines", Json.arr machines), ("reach_iffs", Json.arr iffs),
    ("state_heads", toJson (heads.toList.map toString)),
    ("reach_preds", toJson (preds.toList.map toString)),
    ("theorems", Json.arr theorems), ("spec_defs", Json.arr specDefs),
    ("witnesses", Json.arr witnesses)]
