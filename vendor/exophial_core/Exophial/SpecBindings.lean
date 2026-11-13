/-
Pure environment-inspection core shared by `Exophial.CheckSpecBindings`
(the `#check_spec_bindings` command) and `Exophial.spec_report` (the
`#spec_report` command). docs/merge_plan.md Stage ML names the convention
this module decides against: a module `N`'s specification lives in its
`Spec` sub-namespace as `def N.Spec.x : Prop`, and the binding theorem that
discharges it is named `N.x`. A theorem whose own statement is not
definitionally equal to the `Spec` entry it is paired with is the exact
defect `#check_spec_bindings` exists to catch (docs/merge_plan.md Stage ML
"Measured").
-/
import Lean

open Lean Lean.Meta

namespace Exophial

/-- One `N.Spec.x : Prop` declaration found in the environment, together with
the name of the binding theorem it names (`N.x`), whether that theorem
exists, and -- if it does -- whether its statement is definitionally equal
to the `Spec` entry. -/
structure SpecBinding where
  /-- The `N.Spec.x` declaration name. -/
  specName : Name
  /-- The paired binding declaration name, `N.x`. -/
  bindingName : Name
  /-- Whether `bindingName` exists in the environment. -/
  bindingExists : Bool
  /-- Whether `bindingName`'s type is definitionally equal to `specName`,
  when `bindingExists` is true. `none` when `bindingExists` is false. -/
  defEq : Option Bool
  deriving Repr

/-- If `n` has the shape `<prefix>.<seg>.<last>`, the paired name
`<prefix>.<last>`. `none` for every other name, including a bare
`<seg>.x` with no prefix (there is no module to bind to) and a `<seg>`
segment that is not immediately followed by the declaration's final
component. -/
def segCounterpart (seg : String) : Name → Option Name
  | .str (.str pre s) last => if s == seg && pre != .anonymous then some (.str pre last) else none
  | _ => none

/-- If `n` has the shape `<prefix>.Spec.<last>`, the paired binding name
`<prefix>.<last>`. See `segCounterpart`. -/
def specCounterpart : Name → Option Name := segCounterpart "Spec"

/-- If `n` has the shape `<prefix>.Witness.<last>`, the paired statement
name `<prefix>.<last>`. See `segCounterpart`. -/
def witnessCounterpart : Name → Option Name := segCounterpart "Witness"

/-- If `n` has the shape `<prefix>.<fromSeg>.<last>`, the sibling name
`<prefix>.<toSeg>.<last>` -- the same declaration path with one namespace
segment swapped. Used to go from a `Spec` entry to its `Witness` sibling
(`Exophial.spec_report`), the opposite direction from `segCounterpart`
(which strips the segment rather than swapping it). -/
def siblingName (fromSeg toSeg : String) : Name → Option Name
  | .str (.str pre s) last =>
    if s == fromSeg && pre != .anonymous then some (.str (.str pre toSeg) last) else none
  | _ => none

/-- Every declaration local to the CURRENT module (not from an imported
one: `env.getModuleIdxFor?` is `none` only for a declaration this module
itself has added, since every imported constant has a module index) whose
name matches the `N.Spec.x` shape. Scoping to the current module, rather
than the whole transitively-imported environment, is load-bearing: Lean's
own standard library ships an UNRELATED `Std.Do.Spec` /
`Std.Internal.Do.Spec` namespace (monadic do-notation verification specs)
that collides with this package's `N.Spec.x` binding-pair convention, and
scanning past the current module turns an unrelated stdlib naming choice
into a spurious `#check_spec_bindings` failure -- measured directly while
authoring this module: the whole-environment scan found `Std.Do.Spec.*`
and `Std.Internal.Do.Spec.*` entries and reported one of them mismatched,
in a file where the two declarations this package's own test actually
wrote were both clean. -/
def specDeclNames (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (n, info) in env.constants.toList do
    if !info.isUnsafe && (env.getModuleIdxFor? n).isNone && (specCounterpart n).isSome then
      out := out.push n
  return out

/-- Resolve every `SpecBinding` for the declarations `specDeclNames` finds,
running the `isDefEq` check in `MetaM` for each one that has a paired
binding declaration. -/
def collectSpecBindings : MetaM (Array SpecBinding) := do
  let env ← getEnv
  let mut out := #[]
  for specName in specDeclNames env do
    let some bindingName := specCounterpart specName | pure ()
    let bindingExists := (env.find? bindingName).isSome
    let defEq ←
      if bindingExists then
        let specInfo ← getConstInfo specName
        let bindingInfo ← getConstInfo bindingName
        let bindingType := bindingInfo.type
        -- The binding's own stated type, compared against a direct
        -- reference to the Spec constant: `isDefEq` unfolds through the
        -- Spec def's own reducibility, so a binding theorem whose type
        -- textually restates (rather than references) the Spec entry is
        -- still caught precisely when the restatement is NOT
        -- propositionally identical after unfolding.
        let specRef := mkConst specName (specInfo.levelParams.map mkLevelParam)
        pure (some (← isDefEq bindingType specRef))
      else
        pure none
    out := out.push { specName, bindingName, bindingExists, defEq }
  return out

/-- A `SpecBinding` is clean when its binding theorem exists and its type is
definitionally equal to the `Spec` entry. -/
def SpecBinding.isClean (b : SpecBinding) : Bool :=
  b.bindingExists && b.defEq == some true

end Exophial
