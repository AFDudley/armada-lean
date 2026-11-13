/-
  ArmadaLean.Machines — the machine registry, scanned, not hand-maintained.
  Reachability is decided at typing time, and the spec check must see every declared
  `Machine` (`ArmadaLean/Machine.lean`), not a hand-typed list of state types.

  A hand-written `def machines : List (Σ S : Type, Machine S) := [...]` would need one entry added
  by hand every time a worker declares a new `Machine`. Lean checks that each entry TYPE-CHECKS,
  but it cannot check that the list is COMPLETE: nothing stops a worker from declaring
  `def Foo.machine : Machine FooState where ...` without adding a matching line, and the gate would
  silently keep gating only the OLD state types. A linter over file text has the same gap, because
  it reads source, not the type checker's own verdict on what a `Machine` IS.

  This file closes that gap by reading the CHECKED ENVIRONMENT directly, after every file this
  project's root module `ArmadaLean` imports has been elaborated: the `#eval` below walks every
  `def` Lean has type-checked and reports the ones whose statement, read as a `∀ binders, Machine S`
  telescope, ends in `Machine S` for some `S`. A `Machine` declared ANYWHERE under `ArmadaLean` is
  found by this scan with no separate registration step, because the scan does not consult source
  text or a maintained list — it consults `Lean.Environment`, the same data `lake build` itself
  used to accept the file. `lakefile.lean` lists `ArmadaLean.Machines` as a second build root
  (alongside `ArmadaLean`) so `lake build` always runs this scan and prints the registry. The
  spec check computes the same set of state types with `ArmadaLean.SpecTools.stateHeads`
  (`scripts/spec_report.lean`, `docs/spec-module-design.md` §4).

  Lists `ArmadaLean.Pool.machine`, `ArmadaLean.Nitro.chain`, `ArmadaLean.Nitro.signedChain`,
  `ArmadaLean.Nitro.participant`, `ArmadaLean.Nitro.network` as of this writing
  (`ArmadaLean/PoolMachine.lean`, `ArmadaLean/Nitro/Reachable.lean`).
  `Nitro.signedChain` (added 2026-10-31) is the chain whose steps use only a given list of
  signatures; its reachable states are `ReachableSigned` (`Nitro.signedChain_reachable_iff`), so a
  statement over them takes the type `ReachableState (Nitro.signedChain apps signed)`. Every
  armada-lean declaration is under the root namespace `ArmadaLean` (draft/root-namespace,
  2026-11-06). The scan does not filter by name prefix: it inspects every `def` in the checked
  environment, and the one marker that matters is `ArmadaLean.Machine`
  (`ArmadaLean/Machine.lean`).
-/
import ArmadaLean

open Lean Elab Meta

namespace ArmadaLean

open ArmadaLean.Nitro

/-- Strip a `Expr`'s leading `∀` binders without opening them (no `MetaM`
    needed): the cheap, non-meta half of the scan, run once per candidate
    `def` before the expensive `forallTelescope` + pretty-print is tried only
    on the few that pass. -/
partial def Machines.stripForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => stripForall b
  | _ => e

-- Every `def` in the checked environment whose statement, with its leading
-- `∀` binders stripped, is an application `Machine S` (`ArmadaLean.Machine`,
-- arity 1): printed as `MACHINE <name> : <S>`, one line per machine, sorted
-- by name for a stable diff, for a reader of the build log. A doc comment (`/-- -/`) cannot attach to `#eval`, so this is a plain
-- comment.
#eval show MetaM Unit from do
  let env ← getEnv
  let mut candidates : Array Name := #[]
  for (name, info) in env.constants.toList do
    if !name.isInternal then
      match info with
      | .defnInfo _ =>
        if (Machines.stripForall info.type).isAppOfArity ``Machine 1 then
          candidates := candidates.push name
      | _ => pure ()
  for name in candidates.qsort (fun a b => a.toString < b.toString) do
    let some info := env.find? name | pure ()
    let stateType ← forallTelescope info.type fun _ body => do
      let fmt ← ppExpr (body.getArg! 0)
      return fmt.pretty
    IO.println s!"MACHINE {name} : {stateType}"

end ArmadaLean
