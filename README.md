# armada-lean

Formal verification (Lean 4) of the core security properties of the **Armada
shielded pool** — the `Transact` ZK circuit, its Merkle membership verifier,
the `PrivacyPool` contract's bookkeeping (notes, nullifiers, roots, token
custody), the yield-vault share math, and the shield fee formula.

**Status:** pre-audit assurance artifact. Companion to
`armada-circuits/docs/SECURITY_REVIEW.md` and the shielded-pool launch track
(armada-poc #381).

## Build & verify

**→ Step-by-step independent verification guide: [docs/how-to-verify.md](docs/how-to-verify.md)**
(no Lean experience needed; ~5 min)

Short version — requires an [elan](https://elan.lean-lang.org)-managed Lean
toolchain (the exact version is pinned in `lean-toolchain`; elan installs it
automatically):

```bash
lake build                        # checks every proof
grep -rn "sorry\|admit" ArmadaLean/   # → no output: no unfinished proofs
```

No dependencies (no mathlib) — a fresh clone builds in seconds.

## What is proven, and where it maps to the code

### Circuit (`armada-circuits`, `Transact.circom` / `merkle.circom`)

| Lean theorem | Module | Property | Circuit code | Security review |
|---|---|---|---|---|
| `rangeCheck120_sound` | `RangeCheck` | `Num2Bits(120)` bounds values `< 2^120` | `Transact.circom:120-129` | Finding 1 (prereq) |
| `no_wraparound_minting` | `ValueConservation` | field equality of sums ⇒ integer equality (≤8 in, ≤4 out, all `< 2^120`) | `Transact.circom:131-143` | **Finding 1 fix** |
| `distinct_leaves_distinct_nullifiers` | `Nullifier` | distinct leaf indices ⇒ distinct nullifiers | `Transact.circom:97-101, 145-161` | **Finding 2 fix** |
| `merkleRoot_inj_leaf` | `Merkle` | a membership proof binds exactly one leaf to the root | `merkle.circom:39-54` | Item 9 |
| `transact_public_outputs_determined` | `Transact` | nullifiers/commitmentsOut uniquely determined by the witness | full model | under-constraint check |
| `transact_no_double_spend` | `Transact` | any valid witness has pairwise-distinct nullifiers | full model | Finding 2, end-to-end |
| `transact_value_conserved` | `Transact` | any valid witness conserves value over the integers | full model | Finding 1, end-to-end |

### Contract-owned notes (`armada-circuits` `TransactOwned.circom`, `armada-poc` `TransactModule.transactOwned`)

| Lean theorem | Module | Property | Circuit or contract code | Source |
|---|---|---|---|---|
| `transactOwned_value_conserved` | `TransactOwned` | any valid owned witness conserves value over the integers | `TransactOwned.circom:111-135` | Finding 1, owned path |
| `commitment_owner_inj` | `TransactOwned` | a note's commitment determines its owner (`ownerField`) | `TransactOwned.circom:66-76` | owner-binding core |
| `user_npk_ne_contract_npk` | `TransactOwned` | no user note key equals a contract note key | `TransactOwned.circom:66-70`, `Transact.circom:75-78` | Dolev-Yao domain separation |
| `owned_owner_binding` | `PoolOwned` | no one except the owning contract can spend its note | `TransactModule.sol:636-639` | labbook decision 2 |
| `owned_no_double_spend` | `PoolOwned` | an accepted call's nullifiers are pairwise distinct and were not already spent | `TransactModule.sol:379-386` | Finding 2, pool-level |
| `preimageOf_consistent` | `PoolOwned` | every recorded preimage hashes to the commitment it is recorded for | `TransactModule.sol:550-604` | labbook §3a (registry defect) |
| `owned_spend_can_happen` | `PoolOwned` | the real owner's spend, with an accepted proof, clears every modeled pool gate | `TransactModule.sol:488-519,609-647` | proof completeness |

### Pool contract (`armada-poc` `PrivacyPool.sol`, `ShieldModule.sol`, `TransactModule.sol`, `MerkleModule.sol`)

| Lean theorem | Module | Property | Contract code | Source |
|---|---|---|---|---|
| `core_invariant` | `PoolSafety` | for every reachable state and each token, the tokens the pool holds equal the total value of its unspent notes | full model | the pool's core invariant |
| `pool_no_double_spend` | `PoolSafety` | no nullifier is ever accepted twice, across the pool's whole history | `TransactModule.sol:379-386` | S-RG, "RAILGUN Core System & Protocol" |
| `transact_spends_only_owned` | `PoolSafety` | a transact spends only notes whose owner key derives from keys the spender holds | `Transact.circom:142-150` | plain-path owner binding |
| `transactOwned_spends_only_owned` | `PoolSafety` | an owned transact spends only notes owned by the calling contract | `TransactModule.sol:636-639` | lifts `PoolOwned.owned_owner_binding` |
| `transact_cannot_be_blocked` | `PoolSafety` | no step any caller can take, the owner included, makes an otherwise-valid transact fail | `TransactModule.sol:460-475`, `PrivacyPool.sol:466-470` | DEPARTURE, see module comment |
| `transactOwned_cannot_be_blocked` | `PoolSafety` | no step any caller can take, the owner included, makes an otherwise-valid owned transact fail | `TransactModule.sol:460-475,491-492` | DEPARTURE, see module comment |
| `spend_live_exact` | `PoolSafety` | a spend removes exactly the `(treeNumber, position)` pairs it names and adds exactly its new notes, tagged with the tree and positions they land at | `Step.transact`/`Step.transactOwned` | S-RG, "How Does RAILGUN Work?" |
| `transact_unshield_exact` | `PoolSafety` | an unshield sends out exactly the value of the notes it spends minus what stays in new notes | `TransactModule.sol:401-424` | value conservation |
| `shield_creates_exactly` | `PoolSafety` | a shield creates exactly one note of the shielded amount minus the fee, at the `(treeNumber, position)` it reports; no second note; no capacity hypothesis — a full tree rolls over instead | `ShieldModule.sol:277-341`, `MerkleModule.sol:62-70` | DEPARTURE, see module comment |
| `transact_root_was_produced` | `PoolSafety` | a transact names only a root the pool itself produced for that tree, or that tree's genesis root | `TransactModule.sol:538` | S-RG, "RAILGUN Core System & Protocol" |
| `pool_preimageOf_consistent` | `PoolSafety` | every entry the pool has ever written to `preimageOf` hashes to the commitment it is recorded under | `TransactModule.sol:590-604`, `ShieldModule.sol:71,136` | lifts `PoolOwned.preimageOf_consistent` |
| `transactOwned_records_all` | `PoolSafety` | after an owned transact, `preimageOf` returns the recorded preimage for each of its outputs | `TransactModule.sol:630-634` | full disclosure, `requireAll = true` |
| `shield_can_happen` | `PoolSafety` | a shield of a positive amount, while not paused, succeeds | `ShieldModule.sol:45-90` | shield can happen |
| `transact_can_happen` | `PoolSafety` | a private transfer by a real key holder, with an accepted proof, succeeds | `TransactModule.sol:43-96` | transact can happen |
| `unshield_can_happen` | `PoolSafety` | an unshield by a real key holder, with an accepted proof, succeeds | `TransactModule.sol:43-96` | unshield can happen |
| `owned_transact_can_happen` | `PoolSafety` | an owned transact by the real owner, with an accepted proof, succeeds | `TransactModule.sol:488-519` | owned transact can happen |
| `leaf_has_merkle_witness` | `PoolSafety` | every leaf the pool has ever inserted into any tree has a real Merkle path to a root the pool produced for that tree | `MerkleModule.sol:54-121` | tree is computed, not chosen |
| `owned_spend_witness_exists` | `PoolSafety` | a live owned note with a recorded preimage has a constructible `OwnedConstrained` spend witness, built entirely from public data, against any tree's leaf list | `TransactOwned.circom:66-87` | spend-construction |
| `live_values_lt_2pow120` | `PoolSafety` | every note the pool records as live has a value below `2 ^ 120`, pool-wide | `PoolTypes.sol:79-83` | `CommitmentPreimage.value : uint120` |
| `leaf_stable` | `PoolSafety` | a leaf, once inserted at a `(treeNumber, position)`, never changes in any later reachable state | `Step`'s own construction | insertion only ever appends |
| `live_note_unspent` | `PoolSafety` | a live note's nullifier is not in `spent`, in every reachable state, under any nullifying key | `TransactModule.sol:379-386` | adjudicator payout freshness |
| `live_leaf_matches` | `PoolSafety` | a live entry's position names the leaf that holds its commitment, in every reachable state | `Step`'s own construction | adjudicator payout witness |
| `live_positions_distinct_nullifiers` | `PoolSafety` | two different live leaf positions never share a nullifier, for a fixed spender key | `Transact.circom:97-101`, `TransactOwned.circom:89-97` | position identity is sound |
| `pool_ownedRandomOf_consistent` | `PoolSafety` | every entry the pool has ever written to `ownedRandomOf` genuinely reconstructs the matching note's `npk` | `PoolOwned.OwnedDisclosure` module comment | DEPARTURE, approved design |

### Adjudicator (`ArmadaLean/Adjudicator/`, the specification of the armada-nitro adjudicator rewrite)

The 40 theorems below are the adjudicator's statements. Every other theorem in
`Adjudicator/Safety.lean` and `Adjudicator/Lemmas.lean` is a helper lemma. A
statement's text changes only with the operator's approval.

Sources: S1 ForceMove (2018), S2 Nitro (2019), S3 SATP (2022), S4 the
docs.statechannels.org protocol tutorial, by page number. The files are in
armada-nitro `docs/references/nitro/sources/`. Each theorem's doc comment
quotes the exact passages. "Armada rule" is a rule of the Armada design: the
adjudicator's money is notes it owns in the pool, it is an ordinary pool user,
and the only fee is the shield-in fee. "armada-nitro code" marks a statement
whose only source is the armada-nitro contract or its R1 mutation tests, not
S1–S4.

Origin and approval: `v1` is the statement set the operator approved on
2026-10-24 (tag `adjudicator-statements-v1`). `A-xx` came from the
2026-10-25 read of S1–S4. The operator approved A-01 to A-14 on 2026-10-25
("A01-A14 should be added"; "if the analysis says they're statements in the
docs they should be statements in our system"). `B4` replaced `v1`'s
`bulk_paths_never_succeed`, by the operator's ruling of 2026-10-25 to follow
the docs. `none` has no recorded approval.

| Lean theorem | Property | Source | Origin |
|---|---|---|---|
| `finalized_outcome_was_concluded_or_challenged` | a finalized channel's state and outcome come from a conclusion proof or an expired challenge, never from a caller's assertion | S2 §3.2 | `v1` |
| `transfer_pays_only_the_finalized_outcome` | `transfer` pays only the destinations the finalized outcome names, and each selected entry exactly its affordable amount | S2 §5.1; S1; S3; S4 0060 | `v1`, strengthened by A-01 |
| `transfer_order_independent_for_simple_allocations` | paying two simple entries in either order pays each the same amount and leaves the same held value | S2; S1 | A-02 |
| `turn_number_record_monotone` | the turn-number record of a live channel never decreases; only `conclude` resets it, in the step that finalizes | S1; S3; S4 0010, 0020, 0040, 0070 | A-03 |
| `finalization_permanent` | a finalized channel stays finalized with the same state hash and deadline; only `transfer` and `reclaim` rewrite its outcome | S2; S1; S3; S4 0040 | A-04 |
| `challenge_requires_authorized_challenger` | a successful challenge names a participant who signed it | S4 0070; S1 | A-05 |
| `deposit_external_destination_fails` | a deposit to an external address fails | S4 0060 | A-06 |
| `deposit_wrong_expected_held_fails` | a deposit whose `expectedHeld` differs from the channel's held value fails | S4 0060 | A-07 |
| `deposit_effect` | a deposit adds exactly its amount to one channel and asset, and changes no other held value or channel status | S2 §3.1 | A-08 |
| `transfer_never_pays_guarantee` | `transfer` never pays a guarantee allocation | S4 0030 | A-10 |
| `reclaim_value_neutral` | `reclaim` moves a finalized guarantee's amount between outcome entries only; the pool and the holdings do not change | S2; S3; S4 0080 | A-11 |
| `value_leaves_only_via_transfer_of_finalized_channel` | a channel's held value goes down only by a `transfer` or bulk payout of that channel after it is finalized | S2; S1; S3; S4 0080 | A-13 |
| `cumulative_payout_never_exceeds_allocation` | across `transfer` calls, an entry's remaining amount plus its total paid equals its original allocation | S2; S1 | A-14 |
| `holdings_point_to_live_notes` | every holding names a live note in the pool | Armada rule | `v1` |
| `value_exists_only_as_notes` | the adjudicator holds no raw balance; a held value is always a live note's value | Armada rule | `v1` |
| `unbeatable_pays` | once all participants sign a final state, no sequence of other callers' steps stops the honest participant's conclude-then-transfer from paying them a spendable note | S2 §4.3, §4.4; Armada rule | `v1` |
| `unbeatable_pays_after_timeout` | the same guarantee after an unanswered challenge times out | S1 §1.2; S2 §4.4 | `v1` |
| `notedValue_conserved` | no single call creates or destroys pool value | Armada rule | `v1` |
| `notedValue_conserved_reachable` | in every reachable state, the pool's noted value per token equals its value at deployment | Armada rule | `v1` |
| `checkpoint_can_happen` | a checkpoint can clear a challenge back to Open | S4 0040, 0070; S1 | A-09 |
| `deposit_can_happen` | a deposit can happen | S2 §3.1; Armada rule | `v1` |
| `guarantee_reallocation_order_dependent` | a `reclaim` can change a later transfer's payout, so A-02 holds only for simple allocations | S2 | A-12 |
| `topup_can_happen` | a second deposit into a funded channel merges with its holding and raises the held value by exactly its amount | armada-nitro code (`ArmadaNitroAdjudicator.sol:60-72`) | `v1` |
| `challenge_can_happen` | a challenge can happen | armada-nitro code (`ForceMove.sol:39-81`) | `v1` |
| `challenge_timeout_can_happen` | an unanswered challenge finalizes when its deadline passes | S4 0040 | `v1` |
| `conclude_can_happen` | a conclude can finalize a channel at once | S4 0070 | `v1` |
| `payout_can_happen` | a funded, concluded channel can pay its whole held value to a destination | none cited | `v1` |
| `reclaim_can_happen` | a guarantee can be reclaimed | S3 §2.4 | `v1` |
| `payout_takes_no_fee` | `transfer` pays out exactly what it debits | S2 §5.1; Armada rule | `v1` |
| `conclude_moves_no_value` | `conclude` changes no pool note and no holding | Armada rule | `v1` |
| `bulk_transfer_all_assets_effect` | `bulkTransferAllAssets` transfers every asset of the outcome in full | S4 0080 | B4 |
| `bulk_conclude_and_transfer_all_assets_effect` | `bulkConcludeAndTransferAllAssets` concludes, then transfers every asset in full | S4 0080 | B4 |
| `bulk_conclude_and_transfer_can_happen` | a bulk conclude-and-transfer can happen | S4 0080 | B4 |
| `transfer_after_transfer_can_happen` | after one `transfer` leaves a remainder, a later `transfer` on the same channel can still pay | S2 §5.1, §5.2 | none |
| `holdings_never_zero_valued` | the adjudicator never records a zero-value note as a holding | Armada rule (`TransactOwned.circom:117-120`) | `v1` |
| `heldValue_zero_iff_no_collateral` | a held value is zero exactly when the channel has no holding | armada-nitro code (R1 mutant) | `v1` |
| `configuredAssets_invariant` | the configured asset set never changes after deployment | armada-nitro code (R1 mutant) | `v1` |
| `zero_payout_mints_nothing` | an allocation paid zero mints no note | armada-nitro code (R1 mutant); S2 §3.1, §5.1 | `v1` |
| `full_payout_leaves_no_remainder` | a full payout leaves no holding | armada-nitro code (R1 mutant); S2 §3.1, §5.1 | `v1` |
| `nullify_iff_commitment_was_some` | a `transfer` nullifies the old holding exactly when one existed | armada-nitro code (R1 mutant) | `v1` |

The axiom audit for these 40 statements is `docs/axioms-adjudicator.txt`.

### Yield vault (`armada-poc/contracts/yield/ArmadaYieldVault.sol`, issue #365)

| Lean theorem | Module | Property | Contract code |
|---|---|---|---|
| `inflation_attack_profitable` | `Vault` | first-depositor inflation attack is profitable on the current share math (`_convertToShares`/`_convertToAssets`, `ArmadaYieldVault.sol:492-515`) | confirms **#365** |
| `mitigated_attack_unprofitable` | `Vault` | with virtual shares/assets offset the attack costs more than it returns | proves the fix |

### Shield fee (`armada-poc/contracts/privacy-pool/modules/ShieldModule.sol`, audit C-3)

| Lean theorem | Module | Property | Contract code |
|---|---|---|---|
| `fee_conservation` | `Fee` | `base + fee = amount` | `_getFee`, `ShieldModule.sol:336-354` |
| `fee_bounded` | `Fee` | `fee ≤ amount` | same |
| `fee_monotone` | `Fee` | larger amount ⇒ no smaller fee | same |
| `fee_zero_below_threshold` | `Fee` | amounts `< 200` pay zero fee at 50 bps | same |

## Trust base & scope

Poseidon and Keccak are both modeled symbolically (Dolev-Yao style,
`ArmadaLean.Poseidon.Term`): a hash output is an inductive term, never a raw
number, tagged with the hash function that produced it
(`ArmadaLean.Poseidon.HashFn`), so collision resistance, domain separation and
cross-function separation (a Keccak output — a contract address — can never
equal a Poseidon output — a note key, a commitment, a nullifier) hold by
construction (the type's own constructors), not as an axiom on a concrete
numeric function — no `poseidon2`/`poseidon3`/`keccak`/injectivity axiom
exists in this project. EdDSA stays an abstract unforgeable signature scheme —
an **explicit axiom** (`EdDSAVerify`), visible per-theorem via `#print axioms`
(see `docs/axioms-*.txt`).
What is and isn't covered, in plain English: **[docs/what-the-proofs-mean.md](docs/what-the-proofs-mean.md)**.

Out of scope: Groth16, the circom compiler, Poseidon's concrete parameters,
the trusted-setup ceremony, and all contract/relayer/SDK code beyond the
modeled formulas. This project complements (does not replace) static analysis
(Ecne/circomspect/Picus) and an external circuit audit.

## Layout

```
ArmadaLean/
  Field.lean              BN254 scalar-field modulus + mod lemmas
  Poseidon.lean           symbolic (Dolev-Yao) Term model of Poseidon + Keccak
  RangeCheck.lean         Num2Bits(120) semantics
  ValueConservation.lean  no-wraparound minting theorem
  Nullifier.lean          double-spend impossibility
  Merkle.lean             Merkle proof leaf-binding + the incremental tree (root, path)
  Transact.lean           full constraint model of Transact.circom
  TransactOwned.lean      constraint model of TransactOwned.circom
  PoolOwned.lean          pool's owned path (TransactModule.transactOwned) and preimage storage
  Pool.lean               pool state (live notes, nullifiers, roots, custody) and operations
  PoolSafety.lean         pool contract's safety theorems, over Pool.lean
  Vault.lean              #365 attack + mitigation proofs
  Fee.lean                shield-fee reference spec
  Adjudicator/            the adjudicator model (the rewrite's specification)
    State.lean            on-chain state and `genesis`
    Channel.lean          channel identity, state, signatures
    Outcome.lean          outcomes, allocations, guarantees, `afford`
    Notes.lean            the adjudicator's money as pool notes
    Operations.lean       every call the adjudicator accepts (`Step`)
    Assumptions.lean      named signature and liveness assumptions
    Reachability.lean     reachable states from deployment
    Safety.lean           the statements (listed above) and their proofs
    Lemmas.lean           helper lemmas for Safety.lean
docs/
  what-the-proofs-mean.md one-page explainer
  how-to-verify.md      step-by-step independent verification guide
  axioms-circuit.txt    #print axioms audit output (circuit theorems)
  axioms-contracts.txt    #print axioms audit output (vault/fee theorems)
  axioms-adjudicator.txt  #print axioms audit output (adjudicator statements)
```
