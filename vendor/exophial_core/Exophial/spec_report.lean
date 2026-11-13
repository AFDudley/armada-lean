/-
The `#spec_report` command (docs/merge_plan.md Stage ML "Where each part
belongs"): the procedure that today lives as `spec_report.lean` in each
consuming repository's own tree (armada-lean, evm-proof-toolchain,
lean-mend), replaced by one copy this package ships. The report's four
parts, run over every `N.Spec.x : Prop` declaration `Exophial.SpecBindings`
finds:

* **binding check** -- `Exophial.collectSpecBindings` (shared with
  `#check_spec_bindings`).
* **axiom report** -- the axioms each bound theorem's proof actually
  depends on (`Lean.collectAxioms`), the same information `#print axioms`
  reports for one declaration, gathered here for every bound spec entry at
  once.
* **sorry list** -- every bound spec entry whose proof depends on
  `sorryAx`: an open proof obligation. docs/merge_plan.md Stage ML, "The
  `sorry` list is the queue": each name on this list is one proof pebble.
* **witness check** -- for every `N.Spec.x` that has a paired
  `N.Witness.x` declaration, confirms the witness exists and type-checks
  against the environment (its mere presence as a well-typed declaration
  *is* the check: an ill-typed witness never elaborates in the first
  place, so reaching this command at all is the positive witness check;
  this command additionally confirms that the Spec entry has a witness to
  check, which a build with the witness module omitted would not).
-/
import Exophial.SpecBindings

open Lean Lean.Elab Lean.Elab.Command Lean.Meta

namespace Exophial

/-- The axioms a declaration's proof depends on, via the same traversal
`#print axioms` uses (`Lean.collectAxioms`). -/
def axiomsOf (name : Name) : MetaM (Array Name) :=
  Lean.collectAxioms name

/-- `true` when `name`'s axiom set includes `sorryAx`: an open proof
obligation rather than a completed one. -/
def usesSorry (axioms : Array Name) : Bool :=
  axioms.any fun a => a == ``sorryAx

/-- One row of the spec report: a `SpecBinding` together with its axiom
report, whether it depends on `sorryAx`, and whether a `Witness` module
pairs with it. -/
structure SpecReportRow where
  binding : SpecBinding
  axioms : Array Name
  sorried : Bool
  hasWitness : Bool
  deriving Repr

/-- Run the full report over the current environment: binding check, axiom
report, sorry detection and witness check, for every `N.Spec.x`
declaration found. -/
def runSpecReport : MetaM (Array SpecReportRow) := do
  let env ← getEnv
  let bindings ← collectSpecBindings
  let mut out := #[]
  for b in bindings do
    let axioms ← if b.bindingExists then axiomsOf b.bindingName else pure #[]
    let sorried := usesSorry axioms
    let hasWitness :=
      match siblingName "Spec" "Witness" b.specName with
      | some witnessName => (env.find? witnessName).isSome
      | none => false
    out := out.push { binding := b, axioms, sorried, hasWitness }
  return out

/-- Print the report as `logInfo` lines: one summary line, then one line per
`Spec` entry naming its binding status, its axioms, whether it is sorried,
and whether it has a witness. `#check_spec_bindings`'s own mismatch check
still runs (and still fails the build on a mismatch) via `collectSpecBindings`
inside `runSpecReport`; this command additionally reports, it does not
relax that check. -/
elab "#spec_report" : command => liftTermElabM do
  let rows ← runSpecReport
  let sorryList := rows.filter (·.sorried) |>.map (·.binding.specName)
  let mismatched := rows.filter fun r => r.binding.bindingExists && r.binding.defEq != some true
  logInfo m!"spec_report: {rows.size} Spec entr{if rows.size == 1 then "y" else "ies"}, \
    {sorryList.size} sorried, {mismatched.size} mismatched"
  for r in rows do
    let status :=
      if !r.binding.bindingExists then "open"
      else if r.sorried then "sorried"
      else if r.binding.defEq != some true then "mismatched"
      else "proved"
    logInfo m!"spec_report: {r.binding.specName} -- {status}, \
      witness={r.hasWitness}, axioms={r.axioms.toList}"
  unless mismatched.isEmpty do
    throwError m!"spec_report: {mismatched.size} mismatched binding(s)"

end Exophial
