# The repair pass: rules for bringing the model to zero type-doctrine findings

This file states the rules that every repair of the model follows. Sections 1 and 2 are operator rulings. Sections 3 and 4 copy, verbatim, the type doctrine and the repair pass of the project's process document (armada-laconic `docs/lean/type-doctrine.md` §2 and `docs/process.md`, "The repair pass", at armada-laconic `f9e9199e`). A gate is one check that runs; a decision that a person or an agent makes is a judgment, not a gate (`glossary.md`).

## 1. The type-doctrine check requires zero findings (operator ruling, 2026-11-14)

The type-doctrine check of `scripts/check.sh` (`lint_ok`) fails if any type-doctrine linter reports any finding. It does not compare the number of findings with a stored number: a branch with one finding fails, even when the number did not rise.

## 2. A fix is a refined type (operator ruling, 2026-11-15)

A fix is correct by construction: a refined type that carries the data together with its fact, so that a value without the fact cannot exist. A one-field `Prop` structure that only removes a finding is not a fix.

## 3. The type doctrine (armada-laconic `docs/lean/type-doctrine.md` §2)

1. **An invariant that two or more statements need is a type.** It is defined once, in `ArmadaLean/Types/`, as a
   `structure` (composed with `extends`) or, for a local unnamed restriction, a `Subtype`.
2. **A spec theorem's hypotheses are relational or source-stated.** A hypothesis that constrains one input alone
   is a refined type of that input, unless the theorem's own source states that condition for that theorem.
3. **One source of truth per input.** A statement never takes a value together with an equation that defines it
   from another argument (`v` with `hvn : v = n.views`).
4. **A step returns the refined type.** The invariant is proved once, where the value is made, not again in each
   theorem that uses it.
5. **Every refined type has its API:** a coercion to its carrier, a decidable smart constructor where the
   predicate is decidable, and `@[simp]` projection lemmas (`writing-lean.md` §3).

## 4. The repair pass (armada-laconic `docs/process.md`)

## The repair pass. Bring existing code to the strata

The strata above describe building forward. Rule 4.4 assumes each repeated pattern is refactored when it appears.
When a model is already proved but was not built that way, the repair pass brings it to the strata. Operator ruling,
2026-11-01. The Nitro model is the first case: its 115 spec theorems state about seven ideas (one equation per
operation, one safety invariant, one liveness principle, the Turbo value algorithm, the ledger constructions, the
virtual-channel protocol, and proof helpers).

A tool does the repair pass, not a person or an agent. The tool is lean-temper (`AFDudley/lean-temper`, design record
`docs/design.md`), a compiler from a Lean project that builds to the same project in the form of the strata. Operator
ruling, 2026-11-20. lean-temper replaced the codemods that agents ran from 2026-11-01 to 2026-11-19.

**R.1 Measure the gap before changing anything.** The audit (`docs/lean/audit-2026-10-31.md`) and the type-doctrine
linters (`docs/lean/type-doctrine.md` §3) give the work lists: each `repeatedPremise` group is one missing refined
type, and each `layerDiscipline` hit is one proof that unfolds a base operation. Before a pass is built, a Lean script
makes its inventory from the linter's work list (operator ruling, 2026-11-19).

**R.2 Rewrite to the strata's forms.** The targets are one equation per operation (2.2), one invariant with one step
lemma (2.1), and refined types instead of hypotheses (1.2, 3.1). An operation equation takes the dependent-`if` form,
so the effect receives the precondition as a value: `apply (.transfer a b) s = if h : s.Finalized a then some
(transferEffect ⟨a, h⟩ b s) else none`. The model keeps failing calls, because the adversary may submit any call;
go-nitro reverts them. Each lean-temper pass replaces a form with an equivalent form, and Lean checks each change
before the tool keeps it. lean-temper has passes for aliases, refined types and premise variants (`design.md` §5). It
has no pass for the layer rule (`layerDiscipline`) yet.

**R.3 Prove each changed specification statement equivalent to the statement it replaces.** Lean proves `New ↔ Old`.
A new statement proved equivalent to an approved statement changes shape, not meaning. The same applies to each
definition that a specification statement reaches. A helper theorem needs no equivalence proof.

**R.4 Rewrite each proof in place.** The tool changes the proof of the theorem that callers already use. It adds no
helper that restates an existing theorem's premises, and no adapter: no function, `subst` or transport that restores
an old context (`design.md` §5.2).

**R.5 Delete the replaced statements and their helpers.** No alias and no deprecated copy stays.

**Done.** A run is done in the weak form or in the strong form of lean-temper `design.md` §9.1. In both forms, the
whole model builds, each pass's linter reports no finding in its scope, and no adapter remains. The weak form
changes only theorems, and no specification statement or definition. The strong form is one run on the whole model
with one verdict, and it changes specification statements and definitions only with the proofs of R.3.

The net line change of the model code (`ArmadaLean/` outside `ArmadaLean/Lint/`) is a measurement, not a condition.
armada-lean `scripts/check.sh --json --base REF` reports it as `model_net_lines`. A run that adds lines is examined
for a missing deletion (R.5) or an adapter (R.4).

Lessons from the manual passes on the Nitro adjudicator (armada-lean `7057602b`, `cb84006a`, `draft/r4-rest`,
2026-11-01, and the pass of 2026-11-02). They are the reasons for the rules of the tool:

- **A new helper that restates an existing theorem's premises raises the counts.** It raised `repeatedPremise`,
  `looseHypothesis` and `aliasHypothesis` above the baseline, and armada-lean's lint check (`scripts/check.sh`,
  `lint_ok`) refused it. Hence R.4.
- **Do not write `s.apply …` in a `show` or `have` when the theorem's own statement does not name `apply`.** The
  ascription puts `Adjudicator.apply` into the proof term, and `layerDiscipline` flags it. State the derived equation in
  the operation's own form (`have heq : s.challenge … = if h : … then … else none := apply_challenge_equation …`) and
  rely on definitional equality with `s.apply apps caller (.challenge …)`.
- **A base operation that the statement itself names is not a layer violation.** An equation about `apply` puts
  `apply` into every proof term, whatever the technique. The linter subtracts the statement's constants from the proof's
  (armada-lean `88356264`). Before this fix, 26 of 35 Nitro `layerDiscipline` hits were this case.
- **Check that an acceptance clause can be met before it goes to a worker.** The first R.4 pebble required "no
  `layerDiscipline` finding" while the linter had the defect above. The worker spent about 290k tokens before it proved
  the clause impossible.
- **A work item whose acceptance is a lint count gets gamed.** The manual merges made `Safety.lean` larger
  (`reclaim_decompose` beside `reclaim_some`, which kept 68 uses), and a codemod worker copied a step's post-state
  into a new `def` so that the base operations left the proof. Hence a tool with no person in the loop, R.4 and R.5.
- **Measure the linter before the code.** 10 of 15 `layerDiscipline` hits counted names that entered a proof only
  through a type (a constructor field type, a `casesOn`, a rewrite motive), and `looseHypothesis` counted type
  parameters as inputs, which hid 106 findings (armada-lean `draft/cm-opus`, failure tests in
  `ArmadaLean/Lint/TypeDoctrineTest.lean`). A commit that corrects a measure may raise a count; it is its own commit
  and states the defect and the counts.
- **A spec theorem is finished when its proof and its witness are closed.** `sorry_count` counts proofs only. A
  witness proved by `sorry` stays in `witness_open`, and `scripts/check.sh --json NAME` reports both
  `theorem_in_sorry` and `theorem_witness_open` for one theorem.

**Gate GRa (the repair pass; execution of the lean-temper run; input: armada-lean at a pinned commit).** The run is done
in the weak or the strong form.

**Gate GRb (the repair pass; execution of `lake build`; input: the run's result).** armada-lean builds.

**Gate GRc (the repair pass; execution of `scripts/check.sh`; input: the run's result).** No type-doctrine count rises
above `scripts/gate-baseline.json` (`lint_ok`).
