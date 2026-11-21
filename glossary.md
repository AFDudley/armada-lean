# Glossary

One word means one concept. The model, the scripts and the documents of armada-lean use these words and no
synonyms. A new term enters here before it enters a document or the code (armada-laconic `docs/process.md`, Judgment
J0). The terms of the Armada protocol and of the verification chain are in armada-laconic `glossary.md`. Each row
cites its source.

## Statements

- **Spec theorem** (n) — a `theorem` whose own doc comment cites a source in a form that armada-laconic
  `docs/lean/writing-lean.md` §11 names: a paper passage, a contract or circuit line, a dated operator ruling, or a
  repository property id (`docs/spec-module-design.md` §2; `scripts/spec_lib.py`).
- **Helper** (n) — every `theorem` that is not a spec theorem (`docs/spec-module-design.md` §2).
- **Spec definition** (n) — the definition `N.Spec.x : Prop` in `ArmadaLean/Spec/<module>.lean` that states the spec
  theorem `N.x`, as `∀ binders, conclusion` (`docs/spec-module-design.md` §3).
- **Statement binding** (n) — the check `#check_spec_bindings` (`ArmadaLean/SpecTools.lean`), which fails the build
  when the type of a spec theorem is not its spec definition (`docs/spec-module-design.md` §1, §3).
- **Reachable state** (n) — a value of `ReachableState M`: a state of the machine `M` that real steps reach from its
  initial state (`ArmadaLean/Types/Reachable.lean`; `docs/spec-module-design.md` §4).
- **Primitive** (n) — an uninterpreted function that an `axiom` only declares, with no property: `EdDSAVerify`,
  `VerifyAccepts`, `VerifyOwnedAccepts` (`docs/spec-module-design.md` §5; armada-laconic `docs/process.md` 2.4).

## Witnesses

- **Witness** (n) — the theorem `D.witness : spec_premise% D` for a spec definition `D` that has a hypothesis. It
  proves that a value satisfies every hypothesis of `D`, so `D` is not true by an empty premise
  (`docs/spec-module-design.md` §5).
- **Open witness** (n) — a witness whose proof uses `sorry`. `scripts/check.sh --json` lists it in `witness_open`
  (`docs/spec-module-design.md` §5).
- **Blocked witness** (n) — an open witness whose premise reaches a primitive. No concrete value proves a hypothesis
  about a primitive, so the witness waits on the primitive, not on work (`witness_blocked`, `scripts/spec_check.py`).
- **Approved open proof** (n) — a spec theorem with a `sorry` that `scripts/approved-open.tsv` names, with the date of
  the operator's approval (`docs/spec-module-design.md` §7; armada-laconic `docs/process.md` 8.3).

## Type-doctrine findings

The linters are in `ArmadaLean/Lint/`. armada-laconic `docs/lean/type-doctrine.md` §3 states the rules they measure.

- **Finding** (n) — one report of a linter: one instance of one pattern.
- **repeatedPremise** (n) — a normalized hypothesis shape that two or more declarations use. Each group is one missing
  refined type (`ArmadaLean/Lint/TypeDoctrine.lean`, `repeatedFindings`).
- **premiseVariant** (n) — one field of one type that two or more different hypothesis shapes constrain
  (`variantFindings`).
- **looseHypothesis** (n) — a hypothesis whose only free variable is one data binder, in a declaration whose shape
  `repeatedPremise` also reports (`looseFindings`).
- **aliasHypothesis** (n) — a hypothesis `x = f …` where `x` is a binder of the same declaration (`aliasFindings`).
  lean-temper calls the binder and its equation an alias (lean-temper `glossary.md`, "Alias").
- **layerDiscipline** (n) — a spec-level declaration whose proof uses a base operation of its own layer that its
  statement does not name (`layerFindings`; armada-laconic `docs/process.md`, the lessons of the manual passes).
- **decisionScope** (n) — an `omega` call that consumes more hypotheses than a limit, a `decide` call on a goal with a
  free variable or above a size limit, or any `decide +kernel` or `native_decide` (`ArmadaLean/Lint/DecisionScope.lean`).
- **Lint baseline** (n) — the committed counts of the findings, in `scripts/gate-baseline.json`. `lint_ok` is true when
  no count on the working tree is higher than the baseline (`scripts/gate_extra.py`). This comparison is a ratchet:
  an equal or a lower count passes.
- **Model code** (n) — the files under `ArmadaLean/` outside `ArmadaLean/Lint/`. `scripts/check.sh --json --base REF`
  reports its net line change from `REF` as `model_net_lines` (`scripts/refactor_measure.py`).

## Checks

- **Gate** (n) — one check that runs, with an id, a kind (static, mutation or execution), the stratum it grades and
  the inputs it reads. A decision that a person or an agent makes is a judgment, not a gate. The full run of a
  repository's checks has no name: `.exophial/config.yaml` `gate.command` is the command that runs them, not a gate.
  Not a verb (armada-laconic `glossary.md`, "Gate").
- **Judgment** (n) — a decision that a person or an agent makes and that no machine checks again (armada-laconic
  `glossary.md`, "Judgment").
