/-
The `spec_premise%` term elaborator (docs/merge_plan.md Stage ML).

`spec_premise% N.Spec.x` elaborates to the global declaration `N.Spec.x`
itself, after checking that `N.Spec.x` is a `Prop` -- the shape every
specification premise this package's binding convention names must have
(`Exophial.SpecBindings`). It exists so a binding theorem's statement reads
`theorem N.x : spec_premise% N.Spec.x := ...` -- a use site that fails loud
at elaboration time if `N.Spec.x` is not resolvable or is not itself a
proposition, rather than a plain `N.Spec.x` reference that would silently
accept a non-`Prop` declaration of the same name.
-/
import Lean

open Lean Lean.Elab Lean.Elab.Term Lean.Meta

namespace Exophial

/-- Resolve `id` as a global constant with no ambiguity, require its type to
be `Prop`, and elaborate to a reference to that constant. -/
elab "spec_premise%" id:ident : term => do
  let name ← resolveGlobalConstNoOverload id
  let e := Lean.mkConst name
  unless ← isProp e do
    throwErrorAt id m!"spec_premise%: '{name}' is not a Prop -- \
      spec_premise% binds a specification premise, which must be declared \
      `: Prop` (docs/merge_plan.md Stage ML)"
  return e

end Exophial
