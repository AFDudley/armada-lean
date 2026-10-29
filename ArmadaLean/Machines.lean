/-
  ArmadaLean.Machines — the machine registry, scanned, not hand-maintained.
  Operator rulings 2026-10-29 (`armada-laconic/labbook/2026-10-29-nitro-reachability-ruling.md`,
  `armada-laconic/labbook/2026-10-29-machine-types-for-approval.md`, `docs/lean/writing-lean.md`
  §11): reachability is decided at typing time, and `scripts/check.sh`'s reachability gate must
  see every declared `Machine` (`ArmadaLean/Machine.lean`), not a hand-typed list of state types.

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
  (alongside `ArmadaLean`) so `lake build` always runs this scan, and `scripts/reach.py` runs
  `lake env lean ArmadaLean/Machines.lean` to capture its `MACHINE` lines and build its set of
  system state types from them (`scripts/reach.py`'s own doc comment).

  Lists `Pool.machine`, `Nitro.chain`, `Nitro.participant`, `Nitro.network` as of this writing
  (`ArmadaLean/PoolMachine.lean`, `ArmadaLean/Nitro/Reachable.lean`); all four are declared at the
  root, not inside a namespace (see `Nitro.participant`'s own doc comment for why), so the scan
  does not filter by name prefix — it inspects every `def` in the checked environment, including
  ones outside the `ArmadaLean` namespace, and relies on `Machine` itself (unqualified, declared
  once in `ArmadaLean/Machine.lean`) being the one marker that matters.
-/
import ArmadaLean

open Lean Elab Meta
open ArmadaLean.Nitro

/-- Strip a `Expr`'s leading `∀` binders without opening them (no `MetaM`
    needed): the cheap, non-meta half of the scan, run once per candidate
    `def` before the expensive `forallTelescope` + pretty-print is tried only
    on the few that pass. -/
partial def ArmadaLean.Machines.stripForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => stripForall b
  | _ => e

-- Every `def` in the checked environment whose statement, with its leading
-- `∀` binders stripped, is an application `Machine S` (`ArmadaLean.Machine`,
-- arity 1): printed as `MACHINE <name> : <S>`, one line per machine, sorted
-- by name for a stable diff. `scripts/reach.py` parses exactly this output
-- (`^MACHINE \S+ : (.+)$`); nothing else in this file's output matters to
-- it. A doc comment (`/-- -/`) cannot attach to `#eval`, so this is a plain
-- comment.
#eval show MetaM Unit from do
  let env ← getEnv
  let mut candidates : Array Name := #[]
  for (name, info) in env.constants.toList do
    if !name.isInternal then
      match info with
      | .defnInfo _ =>
        if (ArmadaLean.Machines.stripForall info.type).isAppOfArity ``Machine 1 then
          candidates := candidates.push name
      | _ => pure ()
  for name in candidates.qsort (fun a b => a.toString < b.toString) do
    let some info := env.find? name | pure ()
    let stateType ← forallTelescope info.type fun _ body => do
      let fmt ← ppExpr (body.getArg! 0)
      return fmt.pretty
    IO.println s!"MACHINE {name} : {stateType}"
