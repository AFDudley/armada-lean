# The spec module: a check that stores no list

Status: branch `draft/spec-module-2`, 2026-10-31. Operator decisions of 2026-10-31.

This document replaces the ratchet check: `scripts/check.sh`, `scripts/sigs-baseline.tsv`,
the sorry baseline count, `scripts/reach-exempt.tsv`, `scripts/sigs.py`, `scripts/reach.py`
and `scripts/sorry_report.py`. The new check is `lake build` plus one computed report. The
check stores no list of names, counts or signatures.

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
- an operator ruling with its date: `operator ruling 2026-10-27`, `Operator ruling, 2026-10-29`;
- a repo property id that names one passage through `docs/nitro-theorems.md` or
  `docs/pool-symbolic-changes.md`: `Nitro-26`, `SATP-15`, `ForceMove-D11`, `docs-0080-03`,
  `P-5`, `S-RG`.

A bare line number with no file name (`(:120-129)` in `Transact.lean`) is not a citation.
The check reads the doc string from the Lean environment (`findDocString?`), not from the
source text. So a namespace, an attribute or an `omit … in` line cannot hide a doc comment.

Theorems that `docs/how-to-verify.md` §4 names, but whose own doc comment cites no source in
these forms, are helpers by this rule. Examples: `transact_value_conserved`,
`transact_no_double_spend`, `fee_conservation`, `inflation_attack_profitable`,
`mitigated_attack_unprofitable`. To make one of them a spec theorem, add a §11 citation to its
doc comment and run `scripts/convert_spec.py`. That is a statement decision for the operator.

**Out of scope (decision 4).** A spec theorem whose doc comment contains "Out of scope
(operator ruling YYYY-MM-DD)" stays in the tree and keeps its spec definition. The report
lists it in `out_of_scope`. Its open proof is in `out_of_scope_open`, not in `sorry`. Its
open witness is not in `witness_open`.

## 3. Statement protection by type

Each spec theorem `N.x` has one definition `N.Spec.x : Prop` in
`ArmadaLean/Spec/<module>.lean`. The definition is the statement: the binders and the
conclusion of the theorem header, in the source layout, written as `∀ binders, conclusion`.
The doc comment of the theorem is copied to the definition.

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
ruling. After cutover the reason lives only in the spec definition.

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
data of `#print axioms`). An axiom passes when it is a Lean core axiom (module `Init`:
`propext`, `Classical.choice`, `Quot.sound`), when it is `sorryAx` (an open proof), or when its
type is not a proposition: a declared primitive such as `EdDSAVerify : … → Prop`
(`writing-lean.md` §11: an axiom "never asserts a property"). An axiom whose type is a
proposition fails. The rule needs no list of axiom names.

## 7. Open proofs are computed

`sorry` is the set of spec theorems whose axioms include `sorryAx`. Nothing stores it. A gate
decision that compares ("this branch opens no new spec proof", "this branch closes
`theorem_under_test`") computes the same set twice: on the branch, and on the merge base
`git merge-base BASE HEAD` in a scratch worktree. The branch passes when
`sorry(HEAD) ⊆ sorry(merge base)`. The same rule applies to `witness_open`.

## 8. The JSON object

`python3 scripts/spec_check.py --json [THEOREM_NAME]` prints one JSON object. The fields
that the open pebble specs read keep their names:

| Field | Old meaning (`check.sh`) | New meaning |
|---|---|---|
| `build_ok` | `lake build` exits 0 | The same. The build now also runs `#check_spec_bindings`. |
| `sorry` | theorems with a literal `sorry` in their body | spec theorems whose axioms include `sorryAx`, without the out-of-scope ones |
| `sorry_count` | length of `sorry` | the same |
| `theorem_under_test` | the argument, echoed | the same |
| `theorem_in_sorry` | the argument (or a name that ends in `.ARG`) is in `sorry` | the same |
| `axioms_ok` | every theorem's axioms are in a fixed name set | every spec theorem's and witness's axioms pass §6 |
| `signatures_ok` | no statement text changed against `sigs-baseline.tsv` | every spec theorem has its `Spec` definition, its type is definitionally equal to it, and every `Spec` definition has its spec theorem |
| `nonvacuity_ok` | `NonVacuity.lean` has no `sorry` | every spec entry with a hypothesis has a witness of its premise, with axioms that pass §6 |
| `reach_ok` | baseline theorems over a state name `Reachable*` or have a TSV row | every spec entry over a state type has a `ReachableState` binder or an "Every state:" line |

New fields: `spec_count`, `helper_count`, `out_of_scope`, `out_of_scope_open`,
`witness_open`, `every_state`, `vacuous_defs`, `failures`, `runtime_seconds`.

A pebble that reads `theorem_in_sorry` reads the same answer for a spec theorem. A helper is
not in `sorry` any more: an open helper shows in `sorry` through the spec theorems that use it.

## 9. The conversion script and the rolling cutover (decision 3)

`python3 scripts/convert_spec.py` runs on any branch whose tree builds. It changes theorem
headers, the generated access lines, the call-site names, the `example` headers of
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

## 10. Runtime

Measured on this branch with a warm build: see the cutover commit message.
