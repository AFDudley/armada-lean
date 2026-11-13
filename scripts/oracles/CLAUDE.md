# scripts/oracles/

Committed acceptance oracles. A pebble spec runs them; a worker does not write
them. The rule for an oracle is that it is the property's own decision
procedure. For a Lean rule, that is Lean elaborating a statement.

- `lean_probe.py PROBE.lean` — runs `lake env lean PROBE.lean` from the repo
  root and prints one JSON object: `elaborates` (Lean exited 0), `error_count`,
  `errors` (the first line of each error) and `axioms` (one
  `{"decl", "axioms"}` entry per `#print axioms` line, in probe order). The
  exit code is Lean's. It decides nothing. It reads the built `.olean` files,
  so run `lake build` (or `scripts/check.sh`) first.
- `pool_exec/PE1.lean` … `PE5.lean` — the probes of rules PE1-PE5 of
  `docs/pool-executable.md`. Each probe elaborates only when its rule holds,
  and its header comment states the interface it fixes (names, field order,
  argument types). Each probe also fails when a main declaration depends on an
  axiom outside `propext`, `Classical.choice`, `Quot.sound` and the declared
  primitives `EdDSAVerify`, `VerifyAccepts` and `VerifyOwnedAccepts` (PE6).
  A probe holds no `sorry`, `admit`, `native_decide` or `#exit`. Each probe
  has `open ArmadaLean` after its import: every armada-lean declaration is
  under the root namespace `ArmadaLean`, so the interface names in a probe's
  header (`Pool.ContractState`, `Step`) are relative to `ArmadaLean`.

A change to a probe changes the acceptance standard of every spec that runs it.
