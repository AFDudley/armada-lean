/-
The root module of the `exophial` Lean package (docs/merge_plan.md Stage ML).

A consumer imports this one module to get all three pieces Stage ML's
"Where each part belongs" table assigns to exophial:

* `Exophial.CheckSpecBindings` — the `#check_spec_bindings` command.
* `Exophial.SpecPremise` — the `spec_premise%` term elaborator.
* `Exophial.spec_report` — the `#spec_report` command (build, binding check,
  axiom report, sorry list, witness check), replacing the hand-copied
  `spec_report.lean` each consumer repository carried in its own tree.
-/
import Exophial.CheckSpecBindings
import Exophial.SpecPremise
import Exophial.spec_report
