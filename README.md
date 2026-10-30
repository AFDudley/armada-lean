# armada-lean

Formal verification (Lean 4) of the core security properties of the **Armada
shielded pool** — the `Transact` ZK circuit, its Merkle membership verifier,
the `PrivacyPool` contract's bookkeeping (notes, nullifiers, roots, token
custody), the yield-vault share math, the shield fee formula — and of the
**Nitro state-channel adjudicator** (ledger and virtual channels).

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
lake exe cache get                 # downloads the prebuilt Mathlib
lake build                         # checks every proof
scripts/check.sh                   # lists each open proof as a `SORRY <name>` line
```

**The pool model** (`ArmadaLean/*.lean`) has no contract layout or encoding
(findings P-1 to P-11 of armada-laconic `labbook/2026-10-26-pool-layout-audit.md`).
Every theorem type is approved, tag `pool-symbolic-approved-2026-10-28`
(armada-laconic `labbook/2026-10-28-pool-symbolic-types-approval.md`). Every pool
theorem is proved (2026-10-29). `docs/pool-symbolic-changes.md` lists every
change and every changed type.

**The Nitro model** (`ArmadaLean/Nitro/`) covers ledger and virtual channels.
Every theorem type is approved, tag `nitro-proofs-approved-2026-10-28`, with the
later rulings in `docs/nitro-repair-2026-10-27.md` and armada-laconic
`labbook/2026-10-29-machine-types-for-approval.md`. `Safety.lean`'s 63 theorems
are proved. Of `Liveness.lean`'s 34 theorems, 16 are proved; `scripts/check.sh`
lists the open ones. `docs/nitro-repair-2026-10-27.md` §3 gives the status of each.
`docs/nitro-theorems.md` maps every theorem to its source.

Both models came from the branches `pool-symbolic` and `nitro-proofs`, now
merged into this trunk. The branches no longer exist; their content survives
as the tags `archive/pool-symbolic` and `archive/nitro-proofs`.

Dependency: Mathlib `v4.33.1` (operator ruling 2026-10-27: use Mathlib where it makes sense). Run
`lake exe cache get` before the first `lake build`.

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
| `owned_spend_can_happen` | `PoolOwned` | the real owner's spend, with an accepted proof, clears every modeled pool gate (type changed: P-1, P-2, P-4; proved) | `TransactModule.sol:488-519,609-647` | proof completeness |
| `hashBoundParams_inj` | `BoundParams` | two different bound-parameter records never give the same `boundParamsHash` (symbolic Keccak) | `PrivacyPoolStorage.sol:46-57` | P-2 |

### Pool contract (`armada-poc` `PrivacyPool.sol`, `ShieldModule.sol`, `TransactModule.sol`, `MerkleModule.sol`)

| Lean theorem | Module | Property | Contract code | Source |
|---|---|---|---|---|
| `core_invariant` | `PoolSafety` | for every reachable state and each token, the tokens the pool holds equal the total value of its unspent notes | full model | the pool's core invariant |
| `pool_no_double_spend` | `PoolSafety` | no nullifier is ever accepted twice, across the pool's whole history | `TransactModule.sol:379-386` | S-RG, "RAILGUN Core System & Protocol" |
| `transact_spends_only_owned` | `PoolSafety` | a transact spends only notes whose owner key derives from keys the spender holds | `Transact.circom:142-150` | plain-path owner binding |
| `transactOwned_spends_only_owned` | `PoolSafety` | an owned transact spends only notes owned by the calling contract | `TransactModule.sol:636-639` | lifts `PoolOwned.owned_owner_binding` |
| `spend_not_blocked` | `PoolSafety` | for every reachable state, no step by any caller disables a pending spend unless the step spends one of the same notes (new; proved) | `TransactModule.sol:373-399,538` | channel design, theorem 1 |
| `transact_not_blocked` | `PoolSafety` | `spend_not_blocked` for a pending `transact` (new; proved) | same | channel design, theorem 1 |
| `transactOwned_not_blocked` | `PoolSafety` | `spend_not_blocked` for a pending `transactOwned` (new; proved) | same | channel design, theorem 1 |
| `spend_bound_to_adapt` | `PoolSafety` | a transaction bound to `(adaptContract, adaptParams)` executes only by that contract, only with those bound parameters (new; proved) | `TransactModule.sol:530-532`, `PrivacyPoolStorage.sol:46-57` | channel design, theorem 2 |
| `owned_merge_can_happen` | `PoolSafety` | an owner can merge `N ≤ 8` live notes into one note of their exact sum, value conserved (new; proved) | `TransactModule.sol:488-519` | channel design, theorem 3 |
| `spend_live_exact` | `PoolSafety` | a spend removes exactly the `(treeNumber, position)` pairs it names and adds exactly its new notes, tagged with the tree and positions they land at | `Step.transact`/`Step.transactOwned` | S-RG, "How Does RAILGUN Work?" |
| `transact_unshield_exact` | `PoolSafety` | an unshield pays exactly the bound recipient exactly the spent value minus the new notes' value, and custody falls by that amount (type changed: P-7; proved) | `TransactModule.sol:401-424` | S-RG, "RAILGUN Core System & Protocol" |
| `shield_creates_exactly` | `PoolSafety` | a shield of the gross amount `x` creates exactly one note of `shieldBase r x`, at a position that held no leaf before, pays `shieldFee r x` to the treasury, and the two add up to `x`; no second note; no capacity hypothesis (type changed: P-3, P-6, P-9, P-11; proved) | `ShieldModule.sol:45-90,244,324-340,353-371`, `MerkleModule.sol:62-70` | operator ruling on P-9, 2026-10-27 |
| `transact_root_was_produced` | `PoolSafety` | a transact names only a root the pool itself produced for that tree, or that tree's genesis root | `TransactModule.sol:538` | S-RG, "RAILGUN Core System & Protocol" |
| `pool_preimageOf_consistent` | `PoolSafety` | every entry the pool has ever written to `preimageOf` hashes to the commitment it is recorded under | `TransactModule.sol:590-604`, `ShieldModule.sol:71,136` | lifts `PoolOwned.preimageOf_consistent` |
| `transactOwned_records_all` | `PoolSafety` | after an owned transact, `preimageOf` returns the recorded preimage for each of its outputs (type changed: P-4; proved) | `TransactModule.sol:630-634` | full disclosure, `requireAll = true` |
| `shield_can_happen` | `PoolSafety` | a shield of a positive gross amount whose note value `shieldBase r x` is spendable succeeds (type changed: P-3, P-6, P-9; proved) | `ShieldModule.sol:45-90,244` | shield can happen |
| `transact_spend_can_happen` | `PoolSafety` | a key holder's spend, with an accepted proof, satisfies the circuit and clears the nullifier check | `Transact.circom:57-186` | proof completeness |
| `transact_can_happen` | `PoolSafety` | a private transfer by a real key holder, with an accepted proof, succeeds (type changed: P-1, P-2; proved) | `TransactModule.sol:43-96` | transact can happen |
| `unshield_can_happen` | `PoolSafety` | an unshield by a real key holder succeeds and pays its recipient (type changed: P-1, P-2, P-7; proved) | `TransactModule.sol:43-96` | unshield can happen |
| `owned_transact_can_happen` | `PoolSafety` | an owned transact by the real owner, with an accepted proof, succeeds (type changed: P-1, P-2, P-4; proved) | `TransactModule.sol:488-519` | owned transact can happen |
| `leaf_has_merkle_witness` | `PoolSafety` | every leaf in any tree has a real Merkle path to a root the pool produced for that tree (type changed: P-8; proved) | `MerkleModule.sol:54-121` | tree is computed, not chosen |
| `leaf_stable` | `PoolSafety` | a leaf, once inserted at a `(treeNumber, position)`, stays in range and keeps its value in every later reachable state (`Option` lookup, type changed: P-8; proved) | `MerkleModule.sol:12,54-121` | append-only incremental Merkle tree; S-RG, "batch incremental Merkle trees" |
| `owned_spend_witness_exists` | `PoolSafety` | an owned note with a recorded preimage and a published opening has a constructible `OwnedConstrained` spend witness, built from public data (type changed: P-1, P-2, P-8, P-10; proved) | `TransactOwned.circom:66-87` | spend construction |
| `live_values_spendable` | `PoolSafety` | every live note passes the circuit's input range check (`Spendable`) (type changed: P-6; was `live_values_lt_2pow120`; proved) | `PoolTypes.sol:82` | lemma of `owned_merge_can_happen` (P-5) |
| `live_note_unspent` | `PoolSafety` | a live note's nullifier is not in `spent`, in every reachable state, under any nullifying key | `TransactModule.sol:379-386` | lemma of `owned_merge_can_happen`, `spend_not_blocked` (P-5) |
| `live_leaf_matches` | `PoolSafety` | a live entry's position holds the leaf of its commitment (`Option` lookup) (type changed: P-1, P-8; proved) | `Step`'s own construction | lemma of `owned_merge_can_happen` (P-5) |
| `live_positions_distinct_nullifiers` | `PoolSafety` | two different live leaf positions never share a nullifier, for a fixed spender key | `Transact.circom:97-101`, `TransactOwned.circom:89-97` | position identity is sound |

**Removed** (details in `docs/pool-symbolic-changes.md`):
`transact_cannot_be_blocked`, `transactOwned_cannot_be_blocked` (P-3: they covered only
the admin step; `spend_not_blocked` replaces them); `live_values_lt_2pow120` (P-6: renamed
`live_values_spendable`, bound moved to the circuit layer); `pool_ownedRandomOf_consistent`
(P-10: no `ownedRandomOf` map); `fee_exact_50bps` (P-9: no basis-point constant).

### Yield vault (`armada-poc/contracts/yield/ArmadaYieldVault.sol`, issue #365)

| Lean theorem | Module | Property | Contract code |
|---|---|---|---|
| `inflation_attack_profitable` | `Vault` | first-depositor inflation attack is profitable on the current share math (`_convertToShares`/`_convertToAssets`, `ArmadaYieldVault.sol:492-515`) | confirms **#365** |
| `mitigated_attack_unprofitable` | `Vault` | with virtual shares/assets offset the attack costs more than it returns | proves the fix |

### Shield fee (`armada-poc/contracts/privacy-pool/modules/ShieldModule.sol`, audit C-3)

The fee is a ratio `num / den` fixed at deployment (`PoolState.feeRatio`), with floor
division (P-9). The contract's basis-point rate is the case `den = 10000`. The shield
step applies it to the gross amount (operator ruling, 2026-10-27).

| Lean theorem | Module | Property | Contract code |
|---|---|---|---|
| `fee_conservation` | `Fee` | `base + fee = amount` (type changed: P-9; proved) | `_getFee`, `ShieldModule.sol:353-371` |
| `fee_bounded` | `Fee` | `fee ≤ amount` (type changed: P-9; proved) | same |
| `fee_monotone` | `Fee` | larger amount ⇒ no smaller fee (type changed: P-9; proved) | same |
| `fee_zero_below_threshold` | `Fee` | `amount * num < den` pays zero fee (amounts `< 200` at 50/10000) (type changed: P-9; proved) | same |
| `shieldBase_pos` | `Fee` | a shield of a positive gross amount creates a note of positive value, under the fee cap `maxFeePercent` (new; proved) | `_getFee`, `ShieldModule.sol:353-371`; operator ruling 2026-10-27 (fee cap) |

### State channels (`ArmadaLean/Nitro/`, go-nitro and the SATP/Nitro/ForceMove papers)

The adjudicator model covers ledger and virtual channels: deposit, transfer,
reclaim, challenge, checkpoint and conclude. `Safety.lean` proves 63 on-chain
safety and conservation theorems. `Liveness.lean` states 34 theorems on
unbeatable strategies and the Turbo Value Algorithm; 16 are proved, and
`docs/nitro-repair-2026-10-27.md` §3 gives the status of the others.
`docs/nitro-theorems.md` maps every theorem to its source paper and to go-nitro.
`docs/nitro-repair-2026-10-27.md` records the approved changes to the statements.

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
(see `docs/axioms-*.txt`). The Groth16 verifiers are the uninterpreted predicates
`VerifyAccepts` and `VerifyOwnedAccepts`, also declared with `axiom`; only the
can-happen theorems mention them. The empty leaf `ZERO_VALUE` is the opaque constant
`emptyLeaf`, not an axiom.
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
  Token.lean              a token as a symbolic address (P-1)
  BoundParams.lean        bound parameters and their symbolic hash (P-2, P-7)
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
  Nitro/
    Address.lean          coins, time, participants, fixed part, destinations, balances
    Outcome.lean          items, allocations, priority payout, afford, outcomes
    Channel.lean           states, signed states, ForceMove and consensus rules
    Adjudicator.lean       adjudicator state, deposit/transfer/reclaim/challenge/checkpoint/conclude
    Strategy.lean           network states, moves, threat model, unbeatable strategies
    Value.lean              outcome network, DAG, Turbo Value Algorithm
    Constructions.lean      ledger channels with sub-channels
    SATP.lean               vouchers, virtual channel rules, routes
    Lemmas.lean             reading lemmas and the coins-held invariant
    Safety.lean             63 proved on-chain safety theorems
    Liveness.lean           34 liveness theorems (16 proved)
    NonVacuity.lean         one proved witness per theorem with hypotheses
docs/
  what-the-proofs-mean.md one-page explainer
  how-to-verify.md      step-by-step independent verification guide
  axioms-circuit.txt    #print axioms audit output (circuit theorems)
  axioms-contracts.txt    #print axioms audit output (vault/fee theorems)
  pool-symbolic-changes.md  the P-1..P-11 changes, the new theorems, the changed types
  nitro-theorems.md       the Nitro/SATP/ForceMove theorem-to-source map
  nitro-repair-2026-10-27.md  the approved corrections to the Safety statements
```
