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
| `spend_live_exact` | `PoolSafety` | a spend removes exactly the leaf positions it names and adds exactly its new notes | `Step.transact`/`Step.transactOwned` | S-RG, "How Does RAILGUN Work?" |
| `transact_unshield_exact` | `PoolSafety` | an unshield sends out exactly the value of the notes it spends minus what stays in new notes | `TransactModule.sol:401-424` | value conservation |
| `shield_creates_exactly` | `PoolSafety` | a shield creates exactly one note of the shielded amount minus the fee; no second note | `ShieldModule.sol:277-341` | DEPARTURE, see module comment |
| `transact_root_was_produced` | `PoolSafety` | a transact names only a root the pool itself produced, or the genesis root | `TransactModule.sol:538` | S-RG, "RAILGUN Core System & Protocol" |
| `pool_preimageOf_consistent` | `PoolSafety` | every entry the pool has ever written to `preimageOf` hashes to the commitment it is recorded under | `TransactModule.sol:590-604`, `ShieldModule.sol:71,136` | lifts `PoolOwned.preimageOf_consistent` |
| `transactOwned_records_all` | `PoolSafety` | after an owned transact, `preimageOf` returns the recorded preimage for each of its outputs | `TransactModule.sol:630-634` | full disclosure, `requireAll = true` |
| `shield_can_happen` | `PoolSafety` | a shield of a positive amount, while not paused, succeeds | `ShieldModule.sol:45-90` | shield can happen |
| `transact_can_happen` | `PoolSafety` | a private transfer by a real key holder, with an accepted proof, succeeds | `TransactModule.sol:43-96` | transact can happen |
| `unshield_can_happen` | `PoolSafety` | an unshield by a real key holder, with an accepted proof, succeeds | `TransactModule.sol:43-96` | unshield can happen |
| `owned_transact_can_happen` | `PoolSafety` | an owned transact by the real owner, with an accepted proof, succeeds | `TransactModule.sol:488-519` | owned transact can happen |
| `leaf_has_merkle_witness` | `PoolSafety` | every leaf the pool has ever inserted has a real Merkle path to a root the pool produced | `MerkleModule.sol:54-121` | tree is computed, not chosen |
| `owned_spend_witness_exists` | `PoolSafety` | a live owned note with a recorded preimage has a constructible `OwnedConstrained` spend witness, built entirely from public data | `TransactOwned.circom:66-87` | spend-construction |
| `live_positions_distinct_nullifiers` | `PoolSafety` | two different live leaf positions never share a nullifier, for a fixed spender key | `Transact.circom:97-101`, `TransactOwned.circom:89-97` | position identity is sound |
| `pool_ownedRandomOf_consistent` | `PoolSafety` | every entry the pool has ever written to `ownedRandomOf` genuinely reconstructs the matching note's `npk` | `PoolOwned.OwnedDisclosure` module comment | DEPARTURE, approved design |

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

Poseidon is modeled symbolically (Dolev-Yao style, `ArmadaLean.Poseidon.Term`):
a hash output is an inductive term, never a raw number, so collision
resistance and domain separation hold by construction (the type's own
constructors), not as an axiom on a concrete numeric function — no
`poseidon2`/`poseidon3`/injectivity axiom exists in this project. EdDSA stays
an abstract unforgeable signature scheme — an **explicit axiom**
(`EdDSAVerify`), visible per-theorem via `#print axioms` (see
`docs/axioms-*.txt`).
What is and isn't covered, in plain English: **[docs/what-the-proofs-mean.md](docs/what-the-proofs-mean.md)**.

Out of scope: Groth16, the circom compiler, Poseidon's concrete parameters,
the trusted-setup ceremony, and all contract/relayer/SDK code beyond the
modeled formulas. This project complements (does not replace) static analysis
(Ecne/circomspect/Picus) and an external circuit audit.

## Layout

```
ArmadaLean/
  Field.lean              BN254 scalar-field modulus + mod lemmas
  Poseidon.lean           symbolic (Dolev-Yao) Term model of Poseidon
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
docs/
  what-the-proofs-mean.md one-page explainer
  how-to-verify.md      step-by-step independent verification guide
  axioms-circuit.txt    #print axioms audit output (circuit theorems)
  axioms-contracts.txt    #print axioms audit output (vault/fee theorems)
```
