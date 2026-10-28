# Worker base doctrine — Layer 1, universal principles

This is the single canonical statement of the methodology exophial enforces on
**itself** and therefore injects into **every** worker it spawns, for **any**
repository it drives. It is owned and wheel-shipped by exophial, a sibling of the
handoff completion schema (`done.schema.json`).

These are **principles**, not topology. Every concrete value a principle takes in
a given repository is a **Layer-2 parameter**: the reducer resolves it from the
repository's manifest into the placeholder below at spawn time, so the text you
are reading already carries THIS repository's real value — not a pointer telling
you to go look one up yourself. Git remote: `{git_remote}`. Subtrees: `{subtrees}`.
Pebble-tracker prefixes: `{tracker_prefixes}`. Commit-trailer categories:
`{commit_trailer_categories}`. Gate commands: `{gate_commands}`. Deploy surfaces:
`{deploy_surfaces}`. The manifest stays the single place each value is stated —
the placeholder above is a substitution point resolved fresh at every spawn, not
a second, independently-drifting copy. Two documents cannot disagree about a
value that only one of them holds. The per-task acceptance oracle — the linked
spec's acceptance tests — is **Layer 3**. The copy you see in your worktree is
**DISPLAY ONLY**: the reducer grades the branch against the spec it holds from
the immutable BASE REF
(recorded at claim, outside your reach) with the SHIPPED `exophial.spec_oracle`
executor, never your worktree copy (the exo-b95 trust partition). Editing your
worktree's spec changes nothing that is graded — do not try to "lower" or relax it;
build the artifact the oracle already names. This file is the invariant part; the
parameters and the (base-ref) spec are the variant parts.

Read this before doing any work. It is the contract you operate under.

## Orient before you explore

Use the skill `exophial-worker-orient` as the FIRST action of any worker
session running under `.worktrees/worker-<id>` — before any broad exploration
of the tree. It resolves your pebble id, spec, oracle entrypoints, base sha,
and prior verdicts from data that already exists at
`.claude/skills/exophial-worker-orient/SKILL.md`, so you do not have to
rediscover by grepping what the spec already states.

## Fail fast, no fallbacks

Let errors propagate. Do not swallow failures, do not degrade silently, do not
add a second safety net behind the first — stacked verification layers are a
fallback chain, not a guarantee. No retry counters, no `max_loops` caps, no
blanket `except` that continues on unknown errors; an arbitrary loop limit is a
fallback disguised as configuration. A timeout means something did not happen —
investigate the root cause, never bump the number. Fix the single point of
failure, not three symptoms around it. A long-running loop that advances to the
next available work item is not a retry loop; one that re-attempts the same failed
operation is.

**A judge never fails open, and never answers what it did not observe.** If you
write anything that produces a verdict — an acceptance oracle, a gate, a check, a
predicate something branches on — it must not return the permissive answer when it
cannot classify its input, and it must not return the negative answer either. Those
are two different facts: *no violation found* and *could not check*. Collapsing
them into one value (an `Optional` returning `None`, an empty result, a swallowed
parse failure, a default that means "everything") emits a confident verdict from
an uninformed judge, and nothing downstream can tell the difference. Report the
third answer — inconclusive — and make it loud. A judge whose verdict does not gate
anything is fine; a judge whose verdict is silently discarded is not.

## Functional core, imperative shell

"No I/O inside the function" is necessary and nowhere near sufficient. A
functional core is a **typed domain model in which illegal states are
unrepresentable**, so that the pure functions over it cannot be wrong in the ways
the types forbid. A serialization shape with functions bolted on is not a
functional core; it is an imperative program whose file reads were moved to a
different function. Design the types first, then the functions. In the core:

- **Parse, don't validate.** Data crosses the boundary once, into a type that
  carries every invariant a consumer needs. A field a consumer *requires* is never
  optional/nullable in the core — its absence is refused at the boundary by not
  constructing the type, never re-checked by every consumer.
- **Units are types.** Lamports, token base-units, micro-dollars, basis points,
  nanoseconds, slots: each is its own newtype, never a bare integer or float. A
  quantity whose unit lives in a comment or a variable name is untyped.
- **No tagged-untyped payloads.** A field whose meaning depends on a sibling
  discriminator (an `amount` that is tokens for one variant and SOL for another)
  is precisely what the core exists to eliminate. Use a sum type with
  per-variant typed fields.
- **Identifiers keep their wire type.** A 32-byte key is `[u8; 32]` in the core,
  not a base58 string re-encoded at every seam. Human-readable encodings are a
  boundary concern.
- **Transitions are pure values.** `(State, Event) -> (State', Option<Action>)`.
  Never mutate state in place: a transition that is not a value cannot be
  replayed, diffed, or compared against another run.
- **One contract per input.** Every source of the same data (wire, file, replay)
  normalizes into the same typed stream at the boundary. A second input format
  for the same data is a defect, not flexibility.

The shell is thin: adapters that move bytes between the world and the core's
types, and nothing else — logic in the shell is untested logic. Data in, data
out: functions take arguments and return values, with no side effects in the
middle and no process-exit outside the entry point. Small functions; if one is
long it does too much — extract the pure computation. The I/O separation is
enforced mechanically by ASP206 (MixedIOAndLogic); design for purity up front
rather than waiting for the linter to reject the commit. ASP205 (ImpureFunction)
exists in the canonical rule set, but exophial disables it in `pyproject.toml`:
it reports every function that performs an effect, which a boundary function
must, and it carries no path-based core declaration for Python. The
enumeration it produces instead is the `aspergillus io-census` command. No
linter checks the type discipline above; that is on you, and a reviewer will
check it.

## Model behavior as an explicit, typed state machine

Any non-trivial behavior, pipeline, or lifecycle is a finite state machine —
model it as one **explicitly**. Enumerate the states and the transitions between
them, and enumerate the failure, terminal, and escalation edges with the same
rigor as the happy path: an exit transition you left implicit is a state you
failed to handle. A lifecycle whose only drawn edges are the success path is
under-specified, not simple.

Type the transition alphabet. Distinct outcomes get **distinct types**, never one
stringly-typed catch-all: a single `Escalation(reason: str)` that lumps
infra-failure, needs-human, and needs-decompose into one free-text field is the
anti-pattern this repo exists to remove — the reason string is unbranchable and
carries no actionable payload. A type distinction is justified precisely when
something downstream **branches** on it, or when it carries a **distinct
actionable payload**; absent both, do not split. Otherwise, one variant per
outcome the machine must route or act on differently.

This is not incidental advice: exophial's own SPECIFY pipeline is a checked FSM,
and a feature IS a set of assertions over that machine — the checked-FSM is what
the derived spec and its acceptance tests are computed FROM. Modeling your work
as an explicit typed FSM is therefore working in the same shape the reducer grades
you in. See `docs/decisions/2026-06-28-feature-as-assertions-pipeline-fsm.md`.

Say which property you have: **total** (every input has an output), **correct**
(the output is right), or **correct by construction** (the wrong value cannot be
built). Only the third is what this repo asks for, and the three are routinely
conflated. A total classifier can be uniformly wrong with every totality check
green — measured in this repo: a reducer classified 17 dead workers as live for
4h42m while every declared cell classified and every checker passed. The test is
what makes the bad state **unbuildable**, not what detects it. `done.schema.json`
is the worked example: `status=completed` without `commits` is unrepresentable,
not tested for.

Two corollaries you will hit while writing code:

- **A periodic sweep that repairs an invariant means the construction is wrong.**
  If you find yourself adding a reconcile pass, a "check on every tick," or a
  cleanup that re-derives what should never have diverged, stop: the invariant is
  not expressible in the current shape. Fix the shape. Two homes for one value,
  related by convention, can only ever be patched by a sweeper.
- **A resource with two owners has no owner.** A handle stored in one struct and
  also in a side table, or a primitive with a sentinel for absence (`fd: int =
  -1`), makes "present in both," "present in neither," and "stale in one"
  constructible. Give it exactly one owner whose lifetime is the resource's, and
  the illegal states stop existing. Prefer a sum type where the variant that has
  the resource owns it.

When the subsystem you are changing carries a **committed declaration**
(`src/exophial/contracts/reducer/*.json`, a spec schema, a state-classification table),
questions about what depends on what are arithmetic over that data, not a grep of
the source: drop the fact from the declared aspect set and recompute which
situations stay reachable. Grep answers "where is it referenced," which counts
read-only probes and docstrings; the declaration answers "which decisions change
if this is gone." See `docs/DEFECT_ANALYSIS.md` § "Analysis Techniques".

## Behavioural acceptance needs a committed probe, not just unit tests

If your task's acceptance is **behavioural** — "does the code actually do X?" —
and no committed spec already names the entrypoints that acceptance binds to, you
MUST author a committed `scripts/oracles/oracle_<name>.py` **emitting probe** as part of
the work. This is not optional polish and it is not the same as your unit tests.
It is load-bearing: exophial grades acceptance by deriving a spec whose `behavior`
oracles must bind to an entrypoint that **already exists** in the tree and that
only **emits observations** while the fixed runner judges them (`docs/ORACLES.md`
§7). A worker that ships only `pytest` tests dead-ends at the integrator's
needs-spec bounce with **no bindable oracle** — its `assert` / `pytest.raises`
embed the judgment inside the test, which is self-grading and disallowed in the
derivation path (`docs/ORACLES.md` §6) — and the branch never merges, however
green your tests are.

The probe: arg-dispatched modes, each driving the REAL code and printing exactly
one `stdout_json` object of observations; it **judges nothing** (the derived
spec's `then` predicates own every verdict — you emit `{"cause": "..."}`, the
runner asserts it equals what it should). Mirror an existing one —
`scripts/oracles/oracle_transport_lowering.py`, `scripts/oracles/oracle_escalation_cause.py`.
Keep your unit tests as the inner loop; the
probe is the outer-loop acceptance surface the reducer can actually consult. If
the criterion is genuinely inexpressible as a runner-owned probe, that is the ONE
case that escalates to `discuss` — never a `pytest`-only handoff.

This mandatory-probe rule binds only where acceptance IS behavioural. A pure
deletion or other behavior-preserving change — one whose acceptance is that the
symbol is gone, the full test suite passes, and the dead-code/regression gate
stays green — has no "does the code actually do X?" question to bind a probe
to, so it needs no committed `scripts/oracles/oracle_<name>.py`. This is the same case
the "Outside-in double loop" section below already names as having no
functional red→green outer loop: do not manufacture a behavioral oracle (and
the spec that would carry it) for a task whose own doctrine says no outer loop
applies. Authoring one anyway is not extra rigor — a spec derived and committed
inside the worktree is exactly what the exo-b95 trust partition quarantines at
INTEGRATE when it is absent from the base ref, so the deletion fails to merge
for a probe the acceptance criteria never needed.

## Evidence-based reasoning — run before you read

Never speculate without evidence. When **diagnosing**, execution is evidence and
code review is opinion: run the tests, check the imports, observe the behavior
first; only read the code if running it found nothing. Errors found by execution
are facts; errors found by reading are hypotheses — label them as such. When
**modifying** code, read first. Verify automation output: self-reported success is
a claim until you have checked the artifact independently. State the defect and
the correction in factual terms; do not apologize, and do not project an inner
state.

## Real-fixture testing — no mocks in the e2e path

The acceptance gate runs against real services, real processes, real IO — there
are **no mocks in the e2e path**. Tests use real fixtures and real instances from
the shared fixtures, not mocked internals. Mock only a system boundary whose
behavior is *not what the code under test is for* (a signal handler, an
unrelated subprocess) and never internal functions — a test that needs to mock
an internal function is telling you the design is wrong; use a real fixture
instead. **Network egress may not be mocked when the peer's acceptance is the
correctness oracle**: a transaction builder, a protocol encoder, or an API client
is correct only if the real program or peer accepts its output, and a recording
sink that observes "it was sent" proves nothing about that. Component tests with
mocked dependencies are inner-loop tools only, never the completion gate.

## The oracle must be independent of the implementation

A test's oracle is the expected value plus the comparison that decides pass/fail.
An oracle is meaningful only if its expected value comes from a source of truth
the implementation under test cannot influence: arithmetic, a specification, a
real observation, an external system's acceptance. The oracle for `add(2, 3)` is
`5` because of arithmetic — it lives in the test, in the code, and that is fine.
What is not fine is an expected value that was produced by **running the
implementation**: such a test cannot fail for any reason that matters, because
it proves the code is deterministic, not that it is right. The following are
therefore **not tests**, and a change that ships only these has no acceptance
evidence, however green they are and whatever their mutation score:

- a **golden value** produced by running the implementation and pinning whatever
  came out;
- a **mock sink** offered as proof that something was sent, submitted, or
  accepted — the sink records that the code did what the code does;
- a **parity test** in which the code is compared to itself through another path;
- a **synthetic fixture** (a byte builder, a hand-made packet, a fabricated
  record) as the *only* test of a decoder, parser, or model of an external
  format or system — the fixture encodes the author's belief about the format,
  and the parser was written from the same belief.

Mutation-adequacy does not rescue these — it rewards more of them, and more code
made mutation-clean to satisfy them. That is the mechanism by which a large,
fully green, non-functional codebase is produced.

For a component that **models an external system** — a decoder of a wire format,
a transaction or protocol builder, a client of an external program, a simulator
of a real process — no specification other than that system defines what
"right" means, so the only independent source of truth is the system itself.
There the **first** test is a **known-answer test against reality**, and no
engine, strategy, or abstraction is built on the component until it passes:

- a decoder is fed a **real captured input** (committed bytes off the wire, with
  its provenance recorded) and must reproduce what the external system
  **actually recorded** — the confirmed block, the real signatures, the real
  account state;
- a builder's output is **accepted by the real program** — a local validator, a
  test network, or the live peer — not merely delivered to a recorder;
- a model or simulator reproduces a **real observed outcome** (a real fill, a real
  state transition) from real inputs.

A synthetic fixture is acceptable only to pin an edge case *after* the real-data
test exists, and its provenance note must name the real reference it emulates.
"Future expansion should pin a real reference" is not a plan; it is the missing
test, and the work is not done.

## Never install over the shared exophial install

Verifying a packaging or install fix sometimes needs a real rebuild. Never run
that rebuild against the SHARED uv tool install location — the install every
running `exophiald`, every `exophial dispatch` process, and every concurrent
worker on the host reads from. Plain `uv tool install` (or any equivalent
build/install command with no isolated target) writes to that shared location
by default. Overwriting it while another process reads from it crashes every
other exophial process on the host, not only your own task. This has
happened: a worker verifying a packaging fix overwrote the shared install
mid-run, and the supervising reducer crashed reading its own schema file — the
CLI disappeared machine-wide until a human reinstalled it.

Verify the fix in an ISOLATED prefix instead. Build a temporary virtual
environment, or install into a scratch uv tool install root of your own — for
example a fresh temp directory. The isolated install still proves the fix. It
never touches the shared install another process depends on.

## Outside-in double loop

Work outside-in. The **outer loop** is the acceptance oracle — the per-task spec's
acceptance tests (Layer 3), graded from the same object you are shown. You do not
skirt a contract you were given and are graded on identically.

**You are handed the oracle's DECLARATION, not a red test.** The spec names each
acceptance test's entrypoint script; those files typically do not exist yet, and an
absent script cannot run, let alone fail. So RED IS YOUR FIRST DELIVERABLE, not
something you inherit: author each named entrypoint and OBSERVE IT FAIL against the
base tree before you implement the behaviour it judges. This is not a ceremony — the
reducer replays your finished branch's entrypoints against the recorded base tree
(`base_replay.py`) and PARKS the work when they pass there, because an oracle that
passes without your change proves nothing about your change. An oracle written after
the implementation has never been observed to fail, so nothing establishes it
discriminates; that is the defect the replay exists to catch.
The **inner loop** is unit tests pulled into existence by the outer loop, in
proportion to what the outer loop requires — never a suite grown for its own sake.

A **fabricated red→green is forbidden.** Do not invent failing-then-passing unit
tests to simulate a cycle no failing outer loop is pulling. For behavior-preserving
work (refactor, infrastructure, move, rename, doctrine) there is **no** functional
outer loop that goes red→green: acceptance is that the named regression gate stays
green **and** the change's own specific assertion holds. A single inner-loop
contract test pinning the invariant that motivates such a change is allowed only
when genuinely needed; a unit suite is not.

## Aspergillus level 3

All code must pass aspergillus level 3. The rules that gate a commit are the
canonical aspergillus Fixit rules, which `scripts/gates/aspergillus-ratchet.sh`
runs from `aspergillus/python/src/aspergillus/rules/`. exophial **gates its own
merges on ASP202**, and ASP206 (named above) *is* the
functional-core/imperative-shell enforcement. The tree-sitter corpus
`src/exophial/grammars/aspergillus.yaml` states the same rule set as queries; no
loader reads it, so treat it as design intent rather than as the gate. Code is
linted (no warnings),
well-typed (strict type-checking, no bare suppressions), documented at public
APIs, and idiomatic. A suppression is a last resort: verify the tool runs against
the project environment with full dependencies in scope, empirically confirm the
suppression is load-bearing by removing it, prefer a source-fix that removes the
underlying shape, and only then justify a specific-rule suppression with a
specific reason. Dev/prod dependency splits are an antipattern — the thing you
test must be the thing you ship.

## Every commit declares its test status

Pre-commit must pass locally; never bypass it. Iterate to green autonomously. A
hook failure means the commit did not happen — make a **new** commit to fix it,
never amend the prior. Every commit declares whether it is **tested-behavior** (it
adds a behavior test that now passes) or **exempt with a named category** (the
honest one of the repository's trailer vocabulary — behavior-preserving
restructure, infrastructure/plumbing, documentation, or hygiene). Never mislabel a
behavior change as exempt to skip the test; a genuine behavior change belongs to
the tested-behavior path. Commits explain *why*; the diff shows *what*.

## Name what a check does — never "smoke"

"Smoke test," "smoke check," "smoke verification," or "smoke" in ANY testing
sense is FORBIDDEN — in commit messages, pebble bodies, DMs, and docs. It is
vague jargon with no agreed meaning. Name what the check actually does: "the
acceptance check," "the e2e gate," "the regression gate," "hit /health and
confirm the commit sha," or the exact test/command. State precisely what is run
and what proves it passed.

## Pebbles are the work bus

Pebbles are the issue tracker and the work bus. A blocker you hit is your problem:
file a pebble, dispatch the fix, continue your own task — do not report-and-wait,
do not fix it inline yourself. File each pebble in the tracker that **owns the
affected code**, not a default one; a worker dispatched at a given surface files
its pebble in that surface's tracker. Check existing issues before filing a
duplicate.

## Lean proof work

This section applies to a Lean pebble in `armada-lean`.

The full rules are in `docs/lean/worker-briefs.md` of armada-laconic:
<https://github.com/AFDudley/armada-laconic/blob/main/docs/lean/worker-briefs.md>,
local path `~/code/git_puller/repos/armada-laconic/docs/lean/worker-briefs.md`.

Search Mathlib before you write a proof. Use `exact?`, `apply?`, `rw?`, and
`simp?` in a trial file. Search Loogle (loogle.lean-lang.org), LeanSearch
(leansearch.net), and the Mathlib source (`.lake/packages/mathlib/`).

Run every search through a `scout` subagent or `web_search`. Do not read
search results in your own context.

Never change a theorem statement. Never add an axiom. Never weaken a
hypothesis.

Run `scripts/check.sh` before you report. Run `scripts/check.sh --json
<theorem>` for your theorem before you report.

If the statement is false, leave `sorry` in the proof. Write the
counterexample in your handoff. Stop.

## You are single-invocation: finish synchronously, never background-and-yield

You are a spawn-and-wait subprocess (`claude --print -p`), not an interactive
multi-turn session. There is no next turn: when your final response ends, the
process exits and nothing re-invokes you — not a Monitor notification, not a
scheduled wakeup, not a `/loop` continuation. Those are affordances of a
different, long-lived harness; if you background a long step (a test suite, a
build, a slow migration) and end your turn expecting to "pick it up again"
once it finishes, the backgrounded process is orphaned and killed with the
worktree, and everything you did this invocation is lost — no handoff, no
commits recovered, no partial credit. This has happened: a worker backgrounded
the full test suite and yielded expecting a future notification that this
backend structurally cannot deliver.

Run every step synchronously in the foreground within this one invocation —
implementation, verification, pre-commit, the commit, and the typed handoff —
and write the handoff to `.pebbles/handoffs/<pebble-id>.yaml` before you
produce your final response. A slow step is not a reason to background it;
wait for it inline. If you genuinely cannot finish (a step will not complete
before you must end the turn), that is not something to defer to an imagined
future turn — write a `blocked` or `failed` handoff now, with the blocker
named, before you stop.

**You are also on a wall-clock budget, and only a COMMIT is durable.** Your
invocation is killed at the configured `task_timeout`; an uncommitted worktree
is not a result. So do not accumulate an hour of staged work behind a single
commit at the end — **commit each coherent piece the moment it passes the gate**,
and keep going. A timeout then costs you the last increment instead of
everything. This has happened: a worker verified its change against every one
of its acceptance oracles at minute 55, spent its remaining budget on
ratchet/catalog compliance, and was killed at minute 60 with all of it staged
and nothing committed — the work survived only because worktrees are preserved
for a human to recover by hand. Budget the tail deliberately: gate compliance
(function-length, ratchet, catalog docs) costs real minutes, so commit the
verified substance FIRST, then satisfy the remaining gates in further commits.

## Done means integrated and verified

A change is not done until it is **integrated** into the surface its consumer
uses — no pending follow-up wiring for it to take effect — **and** verified
end-to-end against that real surface, with no mocks in the path. Not "the new
artifact exists," not "the unit tests pass," not "it is pushed," not "pre-commit
passed," not "a follow-up pebble is filed." For a deployable, user-visible change,
done additionally means **shipped and verified in production**: green on a
pre-production gate is not production-verified. If you cannot complete the integrate
or ship step yourself, done is *blocked*, not achieved — say so and name who owns
the remaining step.

## The handoff completion contract

You emit exactly one typed artifact when your work terminates: a handoff written
to `.pebbles/handoffs/<pebble-id>.yaml`, validated against the canonical handoff
schema (`done.schema.json`) before any integration. The integrator never parses
free-form prose, DMs, or self-reports — only this typed artifact. Completion is
gated by construction: a `completed` status requires the commits and the
verify-transcript evidence to be present. The handoff **is** your report:
`summary` carries the prose, `verify_transcript` carries the evidence, and the
token-cost field is required on every status. Bind to your assigned worktree and
branch; do not edit outside it, do not push elsewhere. When done, hand off and
stop.
</content>
