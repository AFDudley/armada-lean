# The pool as an executable operation

Status: design, 2026-11-03. Owner: the armada-laconic session in pane w3:p5, by operator order of 2026-11-03.

The rules below are the rules that the pool-execution pebbles cite. Each rule is one sentence, so that a filing can
quote it exactly.

## Why

The translator from this specification to Stele reads executable functions (armada-laconic `engineering/build-plan.md`
S5, "Lean model → Stele is a programmatic translation"). The Nitro adjudicator already has that form
(`Adjudicator.apply`, `ArmadaLean/Nitro/Adjudicator.lean`). The pool does not: `Pool.Step` (`ArmadaLean/Pool.lean`) is
an inductive relation. Step L2 of armada-laconic `labbook/2026-10-28-liveness-refinement-design.md` asks for "an
executable operation form (`PoolState → Call → Option PoolState`), with `VerifyAccepts` as a primitive".

`Pool.Step` cannot become that function by a rewrite:

- Each `Step.transact` takes the private witness `w` and the hypothesis `Constrained w pub`. A contract never sees `w`.
- `PoolState` has ghost fields: `live` (the preimage and position of every unspent note), `published` and `payouts`.
  A contract stores commitments, nullifiers, custody, fees and the preimage registry.
- The new notes of a transact come from the witness (`UnshieldRefines w …`). A contract sees only the output
  commitments.

So the executable form works on the state that a contract can store, and a refinement theorem ties it to `Pool.Step`.
`Pool.Step` and every approved pool statement stay as they are.

## Rules

**Rule PE1 (contract state).** `Pool.ContractState` holds only what the pool contract stores: the Merkle trees, the
nullifier set of each tree, the custody of each token, the preimage registry, the treasury fees of each token and the
fee rate, and `PoolState.contract` maps a model state to it by dropping `live`, `published` and `payouts`.

**Rule PE2 (calls).** `Pool.Call` holds only what a caller sends: for a shield, the token, the gross amount and the
note key; for a transact, the caller, the public inputs, the bound parameters, the proof, the token of the unshield if
there is one, the disclosed records and the published openings; for an owned transact, the same with no unshield.

**Rule PE3 (executable operation).** `Pool.apply verify : Pool.ContractState → Pool.Call → Option Pool.ContractState`
is a computable function that reads only its call and its state, takes the proof check as the parameter `verify`, and
states each call as `if h : Pre then some (Effect ⟨_, h⟩) else none`.

**Rule PE4 (forward refinement).** For every reachable `s` and every `Pool.Step s s'`, some call `c` gives
`Pool.apply verify s.contract c = some s'.contract`, under the hypothesis that `verify` accepts every proof for public
inputs that a witness satisfies.

**Rule PE5 (backward refinement).** For every reachable `s`, if `Pool.apply verify s.contract c = some t`, then some
`s'` with `Pool.Step s s'` has `s'.contract = t`, under the hypothesis that every public input that `verify` accepts
has a witness that satisfies the circuit.

**Rule PE6 (no statement change).** The pool-execution work changes no approved statement, adds no axiom, and raises no
type-doctrine linter count above `scripts/gate-baseline.json`.

## Notes for the work

- The two hypotheses of PE4 and PE5 are the completeness and soundness of the trusted zero-knowledge verifier
  (armada-laconic `labbook/2026-10-28-verification-chain-rulings.md`, ruling 1). `TransactProofCompleteness`
  (`ArmadaLean/PoolSafety.lean`) and `OwnedProofCompleteness` (`ArmadaLean/PoolOwned.lean`) already state completeness
  over `VerifyAccepts`. The soundness direction is the hypothesis that every `Step.transact` takes today
  (`Constrained w pub`).
- `Step.transact` checks that the spent positions are live (`hRemove`). A contract checks nullifier freshness and the
  Merkle root instead. So PE5 holds only on reachable states, through the existing pool lemmas such as
  `live_note_unspent` and `live_leaf_matches`.
- The contract reads the unshield note's token from calldata and checks it against the last output commitment
  (`UnshieldRefines`). That is why PE2 names the token of the unshield.
- Order: PE1 and PE2, then PE3, then PE4, then PE5. Each later rule uses the definitions of the earlier ones.
- The vault (ship-armada/armada-poc#651) gets the same form later, by the same pattern.
