# The spec module: a check that stores no list, with one named exception

Status: branch `draft/spec-module-2`, 2026-10-31. Operator decisions of 2026-10-31.
Review ship-armada/armada-lean#1 finding 3 (2026-11-12) added the one exception: §6
and §7 below.

This document replaces the ratchet check: `scripts/check.sh`, `scripts/sigs-baseline.tsv`,
the sorry baseline count, `scripts/reach-exempt.tsv`, `scripts/sigs.py`, `scripts/reach.py`
and `scripts/sorry_report.py`. The new check is `lake build` plus one computed report, plus
`scripts/approved-open.tsv` (§7). Every other set the check reports is computed, not stored.

## 1. Parts

| Part | File | Job |
|---|---|---|
| Membership rule | `scripts/spec_lib.py` (`citations`) | Decide which `theorem` is a spec theorem |
| Statement record | `ArmadaLean/Spec/<module>.lean` | One `def … Spec.x : Prop` per spec theorem |
| Statement binding | `#check_spec_bindings` (`ArmadaLean/SpecTools.lean`) | Fail the build when a theorem's type is not its `Spec` definition |
| Reachable states | `ArmadaLean/Types/Reachable.lean` | `ReachableState M` and its API |
| Witnesses | `ArmadaLean/Witness/<module>.lean` | One witness per spec entry with a hypothesis |
| Report | `scripts/spec_report.lean` | Axioms, bindings, state facts and witnesses, computed from the environment |
| Check | `scripts/spec_check.py` | Run the build and the report; print the result and the JSON object |
| Conversion | `scripts/convert_spec.py` | Convert any branch to this form; re-runnable |

## 2. Spec membership is an algorithm (decision 1)

A `theorem` is a spec theorem when its own doc comment cites a source in a form that
`armada-laconic/docs/lean/writing-lean.md` §11 names. Every other `theorem` is a helper.
The forms (`scripts/spec_lib.py`):

- a paper passage: `SATP:213-215`, `Nitro:162`, `ForceMove §3`, `SATP §2.1`;
- a contract or circuit line: `MultiAssetHolder.sol:402-415`, `Transact.circom:61`
  (white space before the line number is accepted, `TransactModule.sol\n:550-578`);
- a dated design-review citation: `review 2026-10-27`, `Review, 2026-10-29`;
- a repo property id that names one passage through `docs/nitro-theorems.md` or
  `docs/pool-symbolic-changes.md`: `Nitro-26`, `SATP-15`, `ForceMove-D11`, `docs-0080-03`,
  `P-5`, `S-RG`.

A bare line number with no file name (`(:120-129)` in `Transact.lean`) is not a citation.
The check reads the doc string from the Lean environment (`findDocString?`), not from the
source text. So a namespace, an attribute or an `omit … in` line cannot hide a doc comment.

Theorems that `docs/how-to-verify.md` §4 names, but whose own doc comment cites no source in
these forms, are helpers by this rule. Examples: `transact_value_conserved`,
`transact_no_double_spend`, `fee_conservation`. To make one of them a spec theorem, add a §11
citation to its
doc comment and run `scripts/convert_spec.py`. That is a statement decision for the operator.

**Out of scope (decision 4, removed 2026-11-01).** The check once read the marker "Out of
scope (reviewed YYYY-MM-DD)" in a spec theorem's doc comment, kept its open proof out of
`sorry`, and reported it in `out_of_scope`/`out_of_scope_open`. The three theorems that carried
the marker (`ledger_offload_funds_subchannel`, `subchannel_open_value_preserving`,
`subchannel_close_value_preserving`) are block comments now, not live declarations, so the
marker has no reader. The mechanism, the `is_out_of_scope` rule and the two JSON fields are
removed.

## 3. Statement protection by type

Each spec theorem `N.x` has one definition `N.Spec.x : Prop` in
`ArmadaLean/Spec/<module>.lean`. The definition is the statement: the binders and the
conclusion of the theorem header, in the source layout, written as `∀ binders, conclusion`.
The doc comment of the theorem is copied to the definition.

Every armada-lean declaration is under the root namespace `ArmadaLean` (branch
`draft/root-namespace`, 2026-11-06). So `N` starts with `ArmadaLean`: the theorem
`ArmadaLean.Pool.x` has the definition `ArmadaLean.Pool.Spec.x`, and a theorem directly in
`ArmadaLean` has `ArmadaLean.Spec.x`. A spec module wraps its definitions in the same
`namespace` blocks as its source file. A witness module names each witness with its full
name at the top level of the file: `theorem ArmadaLean.Pool.Spec.x.witness`.

The last command of each spec module is `#check_spec_bindings`. For each `Spec` definition
of the module, it checks that the theorem `N.x` exists and that its type is definitionally
equal to `N.Spec.x` (with the section variables of both as leading `∀` binders). On a
difference, `lake build` fails. So a change to an approved statement is a change under
`ArmadaLean/Spec/`. A theorem header can change only in a way that Lean accepts as the same
statement.

The theorem keeps its own binders in its header, because its proof body refers to them by
name. `theorem foo : Spec.foo := …` would change every proof body. The binding check is the
"equivalent form that Lean checks definitionally".

**Proposed gate rule (not wired).** A proof branch may not change a file under
`ArmadaLean/Spec/`. The gate computes `git diff --name-only BASE...HEAD -- ArmadaLean/Spec/`
and fails when it is not empty, unless the branch is a statement branch that the operator
approved. This is a path rule. It needs no list of names.

## 4. Reachability is a type (decision 2)

`ArmadaLean/Types/Reachable.lean` defines the reachable states of a machine:

```lean
def ReachableState {S : Type} (M : Machine S) : Type := {s : S // M.Reachable s}
```

with its API (`armada-laconic/docs/lean/typed-library.md` §3 rule 2): the coercion and the
projection `ReachableState.state`, the evidence `ReachableState.reachable`, the constructor
`ReachableState.mk'`, `@[ext]`, `ReachableState.step`, and `@[simp]` lemmas for each
projection. The module imports only `ArmadaLean.Machine`. The Nitro forms are abbreviations in
`ArmadaLean/Nitro/Reachable.lean`, directly after their machines:
`Nitro.ReachableParticipant apps T` and `Nitro.ReachableNetwork apps Ts`.

The machines are the ones that `ArmadaLean/Machines.lean` scans: `Pool.machine`,
`Nitro.chain`, `Nitro.signedChain`, `Nitro.participant`, `Nitro.network`.
`Nitro.signedChain apps signed` is new on this branch: its reachable states are
`ReachableSigned apps signed` (`Nitro.signedChain_reachable_iff`). `Nitro.chain` and
`Nitro.chain_reachable_iff` moved above `Reachable.balances_virtual_zero` with their text
unchanged.

**The conversion.** A spec theorem with a state binder `(s : S)` and a hypothesis
`(h : R … s)` gets one binder `(s : ReachableState M)` at the place of the state binder. `R`
is `Machine.Reachable` or a predicate with a proved iff to it (`Nitro.chain_reachable_iff`,
`Nitro.signedChain_reachable_iff`, `Pool.machine_reachable_iff`). The rest of the header
writes the state as `s.state`. The meaning of the statement does not change.

**Access repair.** A proof body that is not `sorry` gets one generated first line:

```lean
obtain_reach ⟨s, h⟩ := s                      -- when R is Machine.Reachable
obtain_reach ⟨s, h : Reachable apps s⟩ := s   -- when R is a native predicate
```

`obtain_reach` splits the binder and writes every `(⟨s, h⟩ : ReachableState M).state` of the
goal and the context as `s`. The proof then sees the context it had before the conversion.
For the native form it turns `h` back into `R … s` through the proved iff. A term body gets
`obtain_reach% ⟨s, h⟩ := s;` in front of it. The rest of each body stays byte-identical.

**Call sites.** The script adds, after each converted theorem `foo`, a helper
`foo.of_reachable`: the original header (state and hypothesis), proved by `foo` with
`ReachableState.mk'`. A use of `foo` in another proof becomes a use of `foo.of_reachable`. Its
arguments and the goals it produces do not change. The helper cites no source, so it is not a
spec theorem.

**Every state.** A spec entry with a binder of a machine state type and no `ReachableState`
binder says "Every state: REASON" in the doc comment of its spec definition. The conversion
takes the reason from `scripts/reach-exempt.tsv` at cutover. A proved theorem with no row gets
a generated reason that says so. An open theorem with no row stops the conversion: it needs a
design decision. After cutover the reason lives only in the spec definition.

## 5. Non-vacuity by construction

`spec_premise% D` elaborates to the premise of the spec definition `D`: `∃ x₁ … xₙ, True`
over all binders of `D` (its parameters, then the `∀` binders of its statement). A
`ReachableState` binder is in the premise as a value, so the witness proves that a reachable
state satisfies the other hypotheses.

A spec entry needs a witness when one binder of its statement is a proposition (a
hypothesis). The witness is the theorem `D.witness : spec_premise% D`. The report computes the
premise and checks the witness type, so the check fails on a missing or wrong witness. A
witness whose proof uses `sorry` is open required work; the report lists it in
`witness_open`.

The conversion writes the witnesses. For a spec entry that has a tagged example in
`ArmadaLean/Nitro/NonVacuity.lean` (`/-- \`name\`. -/`), the example becomes
`theorem name.nonvacuity` (header only), and the witness is
`by spec_witness NonVacuity.name.nonvacuity`. `spec_witness` splits the example's `∃` and `∧`
into facts, matches each hypothesis of the premise with a fact (a native reachability fact
through a proved iff), gives the binders that no hypothesis constrains a value of the
example's namespace, and closes the rest with `rfl`, `decide`, `trivial` or `simp`. The kernel
checks the result. Every other witness starts open. A re-run keeps an existing witness.

No witness uses an axiom that asserts a property. A hypothesis about an uninterpreted
primitive (`VerifyAccepts`, `VerifyOwnedAccepts`, `EdDSAVerify`) has no concrete proof, so its
witness stays open; the report names it.

## 6. Axioms

`axioms_ok` reads the axioms of every spec theorem and every witness from `collectAxioms` (the
data of `#print axioms`). An axiom passes only when `scripts/spec_check.py`'s
`ALLOWED_AXIOMS` names it: Lean's three core axioms (`propext`, `Classical.choice`,
`Quot.sound`) or the model's three declared primitives (`ArmadaLean.EdDSAVerify`,
`ArmadaLean.VerifyAccepts`, `ArmadaLean.VerifyOwnedAccepts`), or it is `sorryAx` (an open
proof, gated by §7, not here). Every other axiom fails, whatever its type.

Before this allowlist, an axiom passed when its type was not a proposition
(`writing-lean.md` §11: a declared primitive "never asserts a property", so its type is
never a `Prop`). Review ship-armada/armada-lean#1, finding 3: a declared `axiom x : Empty`
has that same shape (`Empty : Type`, not a `Prop`), so it passed too, and a false axiom
proves anything. `ALLOWED_AXIOMS` is an exact name list instead: checked against the built
environment on 2026-11-12, no spec theorem's or witness's axioms ever name a seventh.

## 7. Open proofs, except one committed approval list

`sorry` is the set of spec theorems whose axioms include `sorryAx`; this set is still
computed, not stored. `sorry_ok` is true only when every name in `sorry` is also a row of
`scripts/approved-open.tsv`: `FULLNAME<TAB>APPROVED<TAB>REASON`, one row per spec theorem
the operator approved to stay open with `sorry`, with the date of that approval
(`docs/process.md` rule 8.3). `--json` reports the file's content as `approved_open`.

Before this gate, a `sorry` spec theorem passed unconditionally (review
ship-armada/armada-lean#1, finding 3). A live comparison against the branch's merge base
("this branch opens no new spec proof") was proposed instead, but the gate's
commit-boundary container builds the judged tree as a single orphan commit with no other
ref and no inherited history, the same constraint `scripts/gate_extra.py`'s own committed
baseline documents for its lint and `decisionScope` counts. A committed file travels with
the judged tree; a query against history older than that one commit cannot run inside it.
`scripts/approved-open.tsv` is the one committed list in the check.

## 8. The JSON object

`python3 scripts/spec_check.py --json [THEOREM_NAME]` prints one JSON object. The fields
that the open pebble specs read keep their names:

| Field | Old meaning (`check.sh`) | New meaning |
|---|---|---|
| `build_ok` | `lake build` exits 0 | The same. The build now also runs `#check_spec_bindings`. |
| `sorry` | theorems with a literal `sorry` in their body | spec theorems whose axioms include `sorryAx` |
| `sorry_count` | length of `sorry` | the same |
| `theorem_under_test` | the argument, echoed | the same |
| `theorem_in_sorry` | the argument (or a name that ends in `.ARG`) is in `sorry` | the same |
| `axioms_ok` | every theorem's axioms are in a fixed name set | every spec theorem's and witness's axioms pass §6 (the exact `ALLOWED_AXIOMS` list) |
| `signatures_ok` | no statement text changed against `sigs-baseline.tsv` | every spec theorem has its `Spec` definition, its type is definitionally equal to it, and every `Spec` definition has its spec theorem |
| `nonvacuity_ok` | `NonVacuity.lean` has no `sorry` | every spec entry with a hypothesis has a witness of its premise, with axioms that pass §6 |
| `reach_ok` | baseline theorems over a state name `Reachable*` or have a TSV row | every spec entry over a state type has a `ReachableState` binder or an "Every state:" line |
| `sorry_ok` | (new) | every name in `sorry` is a row of `scripts/approved-open.tsv` (§7) |

New fields: `spec_count`, `helper_count`, `witness_open`, `theorem_witness_open`, `every_state`,
`vacuous_defs`, `failures`, `runtime_seconds`, `sorry_ok`, `approved_open`.
`theorem_witness_open` answers, for the theorem
named on the command line, whether its witness is in `witness_open`. It is one boolean because
the acceptance-oracle grammar compares scalars only and has no list membership.
`approved_open` reports `scripts/approved-open.tsv`'s content, keyed by theorem name
(§7).
`witness_blocked` maps each open witness whose premise needs a declared primitive (an axiom
that is not a proposition: `EdDSAVerify`, `VerifyAccepts`, `VerifyOwnedAccepts`) to those
primitives; such a witness is not in `witness_open`, and `theorem_witness_blocked` answers for
a named theorem. The primitives a premise needs are found from its binder types: the walk
follows definitions and structure fields (every field must hold) and does not follow the
constructors of an inductive (one constructor suffices, so a reachable pool state needs no
transact step). Measured at `13cd2e50`: 11 blocked witnesses, 0 open outside Nitro.

A pebble that reads `theorem_in_sorry` reads the same answer for a spec theorem. A helper is
not in `sorry` any more: an open helper shows in `sorry` through the spec theorems that use it.

## 9. The conversion script and the rolling cutover (decision 3)

`python3 scripts/convert_spec.py` runs on any branch whose tree builds. It changes theorem
headers, the generated access lines, each call site's own arguments, the `example` headers of
`NonVacuity.lean`, the spec and witness modules, and the root imports. It prints every
converted theorem and every call site. A second run changes nothing.

Order of the cutover commits on `draft/spec-module-2`:

1. The infrastructure (types, tools, report, scripts). The old check passes on it.
2. The conversion: the output of `scripts/convert_spec.py`, unedited.
3. The removal of the old check and its stored lists.

A worker branch from before the cutover:

1. Merge commit 1 (a normal merge).
2. Run `python3 scripts/convert_spec.py` and commit the result.
3. `git merge -s ours <commit 2>`: the branch already holds the conversion of its own tree.
   The script is deterministic, so the parts that the branch did not change are equal to
   commit 2.
4. Merge commit 3 and later commits (normal merges).
5. Run `python3 scripts/convert_spec.py` again: it must change nothing.

## 10. Measurements (2026-10-31, warm build, this host, rerun on `integrated` `5e5ce55`)

| | Old check (`integrated` `5e5ce55`) | New check (`draft/spec-module-4`) |
|---|---:|---:|
| `scripts/check.sh --json`, wall time | 12.7 s | 16.1 s |
| Open spec proofs (`sorry` ∪ `out_of_scope_open`) | 12 | 12, the same names |
| Spec theorems | — (no rule) | 177 |
| Converted to `ReachableState` | — | 55 (43 with an access line, 12 with a `sorry` body) |
| Call sites rewritten in place | — | 18 |
| "Every state" entries | 86 TSV rows | 56 (14 with a generated reason) |
| Witnesses | 149 entries need one: 81 proved by `spec_witness`, 68 open |

**The `scripts/check.sh --json` wall-time row above is stale.** It
measures only `lake build` plus `spec_report.lean`, at commit `5e5ce55`.
Commit `c0af16a2` (2026-11-01), a child of `5e5ce55`, added the
`gate_extra.check_lint`, `check_decision_scope`, and
`check_counterexamples` checks that `scripts/check.sh --json` now runs on
every call. Commit `88d4ab9a` on branch `perf/counterexamples-pool`
(2026-11-03) pools the `check_counterexamples` file loop in a
`ThreadPoolExecutor`. Measured on a worktree at that branch:
`scripts/check.sh --json`, warm build, 3 runs, wall time 53.9-57.4 s.

**No compatibility helper (decision 3 restated).** The first cutover
(`draft/spec-module-2`/`-3`) gave each converted theorem `foo` a
`foo.of_reachable` theorem — the pre-conversion header, proved by `foo` — and
renamed every call of `foo` to it, so a caller's own two arguments (a state
and its reachability hypothesis) stayed untouched. That is a shim; the
project's cutover rule is a clean one. `convert_spec.py` now rewrites each of
the 18 call sites' own arguments into the one `ReachableState` value the
converted header takes, `⟨state, proof⟩` (`⟨_, proof⟩` when the state binder
was implicit, so the call never named it), and generates no helper.
`git grep -c 'of_reachable' ArmadaLean` is 0.

One call site needed a one-line repair of its OWN proof, not the script:
`nTwoCh_finalizable_latest_snd` (`ArmadaLean/Nitro/NonVacuity.lean`) calls
`latest_state_finalizable` with a non-trivial state expression, then later
`rw`s six goals through lemmas that mention that same expression. Once the
call builds the state and its reachability proof as one dependent pair, `rw`
cannot form a motive for a term a sibling field's type also depends on
(Lean's own diagnostic: "motive is not type correct"). `simp only` can,
through its own congruence reasoning, once the lemma's own implicit state
arguments are given explicitly (`@nTwoCh_views_p0/q0 n0 st1 st2 …`): `simp`'s
argument elaboration does not pin them from the goal first, the way `rw`'s
does.

**`scripts/type_lint.lean` (report-only, `docs/lean/type-doctrine.md` §3-4a).**
`ArmadaLean/Lint/TypeDoctrine.lean`'s `inScope` excludes two cases, by rule:
a module under `ArmadaLean.Spec` or `ArmadaLean.Witness` (the spec module's
own generated statements and witnesses), and a declaration whose last name
component is `nonvacuity` or `nonvacuity_N` (an `example` the conversion
promotes to a named theorem, `scripts/spec_lib.py` §5). A third case lives
in `exprKey` itself, not `inScope`: `stateCarrier?` reduces a
`ReachableState.state e` premise subterm to `e` before keying, so a
premise's shape does not change just because its state binder moved from a
bare parameter to a `ReachableState` one (decision 2). Scoped to
`ReachableState.state` alone, not every `Subtype` carrier (`Subtype.val`,
`.1`): a refined type such as `TimedChannel` also coerces through
`Subtype.val`, and that projection IS part of its own premises' shape.

`repeatedFindings` and `variantFindings` grouped by `Std.HashMap`, whose
iteration order depends on Lean's per-process hash seed: the same
unchanged commit read `repeatedPremise_groups` 258 on one run, 259 on
another. `groupByKey` replaces both: sort the rows by `(key, tiebreak)`, a
total order over the row data, then group adjacent rows. `premiseVariant`'s
representative `pretty` text is now the alphabetically first declaration's,
by the same order, not whichever declaration the `HashMap` iteration
reached first.

Measured with this same linter file on both ends, five runs in each of two
fresh worktrees (ten runs per row): every run of a row reads the same
number.

| | Base (`integrated` `5e5ce55`) | Tip (`draft/spec-module-4`) |
|---|---:|---:|
| `decls_scanned` | 1593 (10/10 runs) | 1593 (10/10 runs) |
| `nitro_decls` | 1185 (10/10 runs) | 1185 (10/10 runs) |
| `pool_decls` | 408 (10/10 runs) | 408 (10/10 runs) |
| `repeatedPremise_groups` | 258 (10/10 runs) | 257 (10/10 runs) |
| `premiseVariant_groups` | 11 (10/10 runs) | 10 (10/10 runs) |
| `looseHypothesis_findings` | 139 (10/10 runs) | 123 (10/10 runs) |
| `aliasHypothesis_findings` | 62 (10/10 runs) | 62 (10/10 runs) |
| `layerDiscipline_nitro_spec_total`/`_hits` | 96 / 35 | 96 / 35 |
| `layerDiscipline_pool_spec_total`/`_hits` | 45 / 12 | 45 / 12 |

Every field is equal or lower on the tip.
