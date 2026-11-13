# The pool as an executable operation

Status: design, 2026-11-03.

The rules below are the rules that the pool-execution pebbles cite. Each rule is one sentence, so that a filing can
quote it exactly.

## Why

The translator from this specification to Stele reads executable functions (armada-laconic `engineering/build-plan.md`
S5, "Lean model → Stele is a programmatic translation"). The Nitro adjudicator already has that form
(`Adjudicator.apply`, `ArmadaLean/Nitro/Adjudicator.lean`). The pool does not: `Pool.Step` (`ArmadaLean/Pool.lean`) is
an inductive relation. The design asks for "an
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
nullifier set of each tree, the custody of each token, the preimage registry, the treasury fees of each token, the
fee rate, the fee-admin address and the treasury address, and `PoolState.contract` maps a model state to it by
dropping `live`, `published` and `payouts`.

**Rule PE2 (calls).** `Pool.Call` holds only what a caller sends: for a shield, the token, the gross amount and the
note key; for a transact, the caller, the public inputs, the bound parameters, the proof, the token of the unshield if
there is one, the disclosed records and the published openings; for an owned transact, the same with no unshield; for
the fee-admin setter `setFeeRatio`, the caller and the new fee rate.

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
type-doctrine linter count above `scripts/gate-baseline.json`. The one exception is the fee-admin setter of design
decision 2026-11-06 (see the notes).

**Rule PE7 (run refinement).** For every list of calls that `Pool.apply verify` accepts in order from
`(genesis r feeAdmin treasury).contract`, the last contract state is `s.contract` for some reachable `s`, under the
hypothesis of PE5.

## Notes for the work

- The two hypotheses of PE4 and PE5 are the completeness and soundness of the trusted zero-knowledge verifier.
  `TransactProofCompleteness`
  (`ArmadaLean/PoolSafety.lean`) and `OwnedProofCompleteness` (`ArmadaLean/PoolOwned.lean`) already state completeness
  over `VerifyAccepts`. The soundness direction is the hypothesis that every `Step.transact` takes today
  (`Constrained w pub`).
- `Step.transact` checks that the spent positions are live (`hRemove`). A contract checks nullifier freshness and the
  Merkle root instead. So PE5 holds only on reachable states. The proof (2026-11-08) uses two reachable-state
  invariants in `ArmadaLean/PoolSafety.lean`: `RootsOfPrefixes` (every root in a tree's history is the root of a
  prefix of its leaves) and `LeafLiveOrSpent` (every leaf is live, or its note's own nullifier is spent). With
  `MerkleProof.opens_treeRoot` (`ArmadaLean/Merkle.lean`), each input of an accepted proof is a live note
  (`transact_inputs_live`, `transactOwned_inputs_live`). The contract's records give the registry of a sublist of the
  witness's records (`transact_records_registry`, `transactOwned_records_registry`, `applyRecords_eq_of_keys`).
- The contract reads the unshield note's token from calldata and checks it against the last output commitment
  (`UnshieldRefines`). That is why PE2 names the token of the unshield.
- Order: PE1 and PE2, then PE3, then PE4, then PE5, then PE7. Each later rule uses the definitions of the earlier
  ones.
- PE7 is PE5 by induction over the calls. The pool safety theorems (`core_invariant`,
  `live_note_unspent`, `pool_no_double_spend`) are statements about `Pool.Step` runs. PE7 makes them statements about
  every run of the contract. Review of ship-armada/armada-lean#1 found that no theorem stated this transfer.
- The vault (ship-armada/armada-poc#651) gets the same form later, by the same pattern.
- One named address, the fee admin, can change the fee rate. `Pool.Step` has the
  constructor `setFeeRatio`. Its caller must equal `feeAdmin`, an address that the deployment fixes. Its effect changes
  only `feeRatio`. `Pool.apply` accepts the call `setFeeRatio caller r` only when `caller = s.feeAdmin`
  (`SetFeeRatioPre`, `setFeeRatioEffect`, `Pool.apply_setFeeRatio_equation`).
- The fee-admin theorems: (a) `step_setFeeRatio_frame` and `Pool.apply_setFeeRatio_frame`; (b)
  `Pool.apply_setFeeRatio_not_admin`; (c) `step_feeRatio_frame`; (d) `setFeeRatio_can_happen`. `step_feeAdmin` and
  `step_treasury` show that no step changes the two addresses. The model `Step` keeps no caller identity in its
  states, so (b) has its content at the contract level.
- `treasury` is an address only. No step reads it or writes it. The model does not model treasury behaviour.
  Governance and other permissioned features are out of scope.
