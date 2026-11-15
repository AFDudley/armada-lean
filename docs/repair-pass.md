# The repair pass: rules for bringing the model to zero type-doctrine findings

This file states the rules that every repair of the model follows. Sections 1 and 2 are operator rulings. Sections 3 and 4 copy, verbatim, the type doctrine and the repair pass of the project's process document (armada-laconic `docs/lean/type-doctrine.md` §2 and `docs/process.md`, "The repair pass", at armada-laconic `a4551d1`).

## 1. The gate requires zero findings (operator ruling, 2026-11-14)

The gate fails if any type-doctrine linter reports any finding. It does not compare the number of findings with a stored number: a branch with one finding fails, even when the number did not rise.

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

**R.1 Measure the gap before changing anything.** The audit (`docs/lean/audit-2026-10-31.md`) and the type-doctrine
linters (`docs/lean/type-doctrine.md` §3) give the work lists: each `repeatedPremise` group is one missing refined
type, and each `layerDiscipline` hit is one proof that unfolds a base operation.

**R.2 Build the target layer next to the old one. Add, never replace, in this step.** The targets are the strata's
own forms: one equation per operation (2.2), one invariant with one step lemma (2.1), refined types instead of
hypotheses (1.2, 3.1). An operation equation takes the dependent-`if` form, so the effect receives the precondition as
a value: `apply (.transfer a b) s = if h : s.Finalized a then some (transferEffect ⟨a, h⟩ b s) else none`. The model
keeps failing calls, because the adversary may submit any call; go-nitro reverts them.

**R.3 Prove each new statement equivalent to the statements it replaces.** Lean proves `New ↔ Old₁ ∧ … ∧ Oldₖ` from
the existing proofs. A new statement proved equivalent to approved statements changes shape, not meaning.

**R.4 Move the proofs with codemods.** A codemod applies one rewrite rule across the code and keeps each edit only if
Lean accepts it. Two rules, each driven by a linter work list: replace a repeated premise by its refined type
(`repeatedPremise`), and replace an unfolded base operation by its equation (`layerDiscipline`).

Lessons from the first R.4 pass on the Nitro adjudicator (armada-lean `7057602b`, `cb84006a`, `draft/r4-rest`,
2026-11-01):

- **Rewrite the existing proof in place.** A new helper that restates an existing theorem's premises raises
  `repeatedPremise`, `looseHypothesis` and `aliasHypothesis` above the gate baseline, and the gate refuses it. Change the
  proof of the theorem that callers already use; keep its statement.
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

Lessons from the second pass (armada-lean, 2026-11-02):

- **A work item whose acceptance is a lint count gets gamed.** The R.4 merges made `Safety.lean` larger
  (`reclaim_decompose` beside `reclaim_some`, which kept 68 uses), and a codemod worker copied a step's post-state
  into a new `def` so that the base operations left the proof. Every repair item now also requires: the net line
  change of the model code (`ArmadaLean/` outside `Lint/`) is at most 0, no definition restates an existing one, and
  the work deletes what it replaces.
- **Measure the linter before the code.** 10 of 15 `layerDiscipline` hits counted names that entered a proof only
  through a type (a constructor field type, a `casesOn`, a rewrite motive), and `looseHypothesis` counted type
  parameters as inputs, which hid 106 findings (armada-lean `draft/cm-opus`, failure tests in
  `ArmadaLean/Lint/TypeDoctrineTest.lean`). A commit that corrects a measure may raise a count; it is its own commit
  and states the defect and the counts.
- **A brief names the replacement, not only the target.** The local model completed 1 of 3 layer items: the one whose
  replacement lemma was easy to find. The two others looped for three hours. A codemod brief states the base
  operation that the lint flags and the existing lemma that replaces it, or says that none exists; an item with no
  replacement lemma is design work for a stronger model, not a codemod.
- **A spec theorem is finished when its proof and its witness are closed.** `sorry_count` counts proofs only. A
  witness proved by `sorry` stays in `witness_open`, and `scripts/check.sh --json NAME` reports both
  `theorem_in_sorry` and `theorem_witness_open` for one theorem.

**R.5 Delete the replaced statements and their helpers.** No alias and no deprecated copy stays.

**R.6 Order for the Nitro model:** the typed operation equations; then the premise-to-type codemod; then the
layer-rule codemod; then the general liveness theorem (Nitro §4.4: an online participant can finalize the latest state
it holds), proved once with the window argument, with the funding point, the concluded state and the Nitro-24 claims as
corollaries. Status 2026-11-02: the exit strategy (`TakeOut.exitStrategy`, `exit_finalizes`) forces finalization from
every state where `p` holds a support at least as new as the chain's record, and the two Nitro-24 claims are its
corollaries, with enabled outcomes measured against that strategy (operator ruling 2026-11-02; armada-lean
`docs/nitro-repair-2026-10-27.md` §7.4).

**GATE.** Every step merges on its own. No type-doctrine linter count rises (`scripts/check.sh`, `lint_ok`), except in
a commit that only corrects a linter's measure. The net line change of the model code is at most 0. Every deleted
statement has an equivalence proof to a statement that remains.
