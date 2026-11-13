/-
The `#check_spec_bindings` command (docs/merge_plan.md Stage ML).

Run inside a module whose declarations include some `N.Spec.x : Prop`
entries, `#check_spec_bindings` fails the elaboration of the command itself
-- and therefore fails `lake build` -- when a binding theorem `N.x` exists
but its statement is not definitionally equal to `N.Spec.x`. A `Spec` entry
with no binding theorem yet is reported, not failed: an open proof
obligation is the normal state of a `sorry`-queue item (docs/merge_plan.md
Stage ML, "The `sorry` list is the queue").
-/
import Exophial.SpecBindings

open Lean Lean.Elab Lean.Elab.Command Lean.Meta

namespace Exophial

/-- Run `collectSpecBindings` in the command elaborator's own environment,
report every binding found, and throw when any binding theorem's statement
diverges from its `Spec` entry. -/
elab "#check_spec_bindings" : command => liftTermElabM do
  let bindings ← collectSpecBindings
  let mismatches := bindings.filter fun b => b.bindingExists && b.defEq != some true
  let open_ := bindings.filter fun b => !b.bindingExists
  let clean := bindings.filter SpecBinding.isClean
  logInfo m!"check_spec_bindings: {bindings.size} Spec entr{if bindings.size == 1 then "y" else "ies"}, \
    {clean.size} bound, {open_.size} open, {mismatches.size} mismatched"
  for b in open_ do
    logInfo m!"check_spec_bindings: open -- {b.specName} has no binding theorem {b.bindingName}"
  unless mismatches.isEmpty do
    let lines := mismatches.map fun b =>
      m!"{b.bindingName} does not match {b.specName}"
    throwError m!"check_spec_bindings: {mismatches.size} mismatched binding(s):\n{MessageData.joinSep lines.toList "\n"}"

end Exophial
