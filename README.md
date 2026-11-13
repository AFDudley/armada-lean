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
(findings P-1 to P-11 of the pool-layout audit). Every pool theorem is
proved. `docs/pool-symbolic-changes.md` lists every change and every changed
type. Contract paths the model does not model — a changeable verification
key, an owner-adjustable fee, CCTP, and batched shields/transacts — are
**[docs/departures.md](docs/departures.md)**.

Dependency: Mathlib `v4.35.0`. Run
`lake exe cache get` before the first `lake build`.

## What is proven, and where it maps to the code

### Circuit (`armada-circuits`, `Transact.circom` / `merkle.circom`)

| Lean theorem | Module | Property | Circuit code | Security review |
|---|---|---|---|---|
| `rangeCheck120_sound` | `RangeCheck` | `Num2Bits(120)` bounds values `< 2^120` | `Transact.circom:120-129` | Finding 1 (prereq) |
| `no_wraparound_minting` | `ValueConservation` | field equality of sums ⇒ integer equality (≤8 in, ≤4 out, all `< 2^120`) | `Transact.circom:131-143` | **Finding 1 fix** |
| `distinct_leaves_distinct_nullifiers` | `Nullifier` | distinct leaf indices ⇒ distinct nullifiers | `Transact.circom:97-101, 145-161` (commit `e79919d`, `feat/public-ceremony`) | Finding 2 |
| `merkleRoot_inj_leaf` | `Merkle` | a membership proof binds exactly one leaf to the root | `merkle.circom:39-54` | Item 9 |
| `transact_public_outputs_determined` | `Transact` | nullifiers/commitmentsOut uniquely determined by the witness | full model | under-constraint check |
| `transact_inputs_distinct_nullifiers` | `Transact` | the nullifiers one proof publishes are pairwise distinct; the circuit cannot see earlier spends (no double-spend is the contract's `pool_no_double_spend`) | full model | Finding 2, one proof only |
| `transact_value_conserved` | `Transact` | any valid witness conserves value over the integers | full model | Finding 1, end-to-end |

### Contract-owned notes (`armada-circuits` `TransactOwned.circom`, `armada-poc` `TransactModule.transactOwned`)

Both the owned-path contract change and the owned circuit are open pull
requests, not yet merged into `main`: ship-armada/armada-poc#653 ("Add the
contract-owned spend path (transactOwned, verifyOwned)", head commit
`ac99ca1c44eb80cbd258bec1064fe078416cc36e`) and
ship-armada/armada-circuits#7 ("Add the owned Transact circuit
(TransactOwned)", head commit `6d405abf97dd0eb73fb5a55f0064d701427e6498`).
This table cites those two PR branches directly: a `TransactModule.sol:N`
citation with `N` past the pin's 498 lines, or any `TransactOwned.circom`
citation, names PR #653 or PR #7, not `main`.

| Lean theorem | Module | Property | Circuit or contract code | Source |
|---|---|---|---|---|
| `transactOwned_value_conserved` | `TransactOwned` | any valid owned witness conserves value over the integers | `TransactOwned.circom:111-135` | Finding 1, owned path |
| `commitment_owner_inj` | `TransactOwned` | a note's commitment determines its owner (`ownerField`) | `TransactOwned.circom:66-76` | owner-binding core |
| `user_npk_ne_contract_npk` | `TransactOwned` | no user note key equals a contract note key | `TransactOwned.circom:66-70`, `Transact.circom:75-78` | Dolev-Yao domain separation |
| `owned_owner_binding` | `PoolOwned` | no one except the owning contract can spend its note | `TransactModule.sol:636-639` | owner-check design (`ownerField == msg.sender`) |
| `owned_no_double_spend` | `PoolOwned` | an accepted call's nullifiers are pairwise distinct and were not already spent | `TransactModule.sol:385-411` (on the pin; the owned path reuses this mechanism in the fork design) | Finding 2, pool-level |
| `preimageOf_consistent` | `PoolOwned` | every recorded preimage hashes to the commitment it is recorded for | `TransactModule.sol:550-604` | preimage-registry integrity |
| `owned_spend_can_happen` | `PoolOwned` | the real owner's spend, with an accepted proof, clears every modeled pool gate (type changed: P-1, P-2, P-4; proved) | `TransactModule.sol:488-519,609-647` | proof completeness |
| `hashBoundParams_inj` | `BoundParams` | two different bound-parameter records never give the same `boundParamsHash` (symbolic Keccak) | `VerifierModule.sol:71-73` | P-2 |

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
| `shield_creates_exactly` | `PoolSafety` | a shield of the gross amount `x` creates exactly one note of `shieldBase r x`, at a position that held no leaf before, pays `shieldFee r x` to the treasury, and the two add up to `x`; no second note; no capacity hypothesis (type changed: P-3, P-6, P-9, P-11; proved) | `ShieldModule.sol:45-90,244,324-340,353-371`, `MerkleModule.sol:62-70` | pool-layout audit, finding P-9 |
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

### Yield vault (`armada-poc/contracts/yield/ArmadaYieldVault.sol`, FIXED)

The model follows the fixed contract: `armada-poc` `origin/main` `64436c14`
(blob `8859da5c`), PR #631 (`04753139`, the `LOCKED_SHARES` lock) and PR #632
(`6e38fddd`, cost-basis removal, no change to the conversion math).

| Lean theorem | Module | Property | Contract code |
|---|---|---|---|
| `locked_shares_set_at_first_deposit` | `Yield.Vault` | after a valid first deposit, total supply equals the deposited assets and exceeds `LOCKED_SHARES` | `ArmadaYieldVault.sol:74-81, 285-290` |
| `locked_shares_supply_invariant` | `Yield.Vault` | a burn bounded by the non-locked balance keeps total supply at or above `LOCKED_SHARES` | `ArmadaYieldVault.sol:74-81, 83-85` |
| `round_trip_loss_le` | `Yield.Vault` | a deposit-then-redeem round trip loses at most `C / S + 1`, the exact floor-division bound | `ArmadaYieldVault.sol:491-514` |
| `donation_loss_bound` | `Yield.Vault` | a depositor's rounding loss from a donation `X` is at most `X / LOCKED_SHARES + 2`, sharper than the NatSpec's `~` estimate | `ArmadaYieldVault.sol:74-81, 491-514` |
| `donation_attack_unprofitable` | `Yield.Vault` | a donation attacker holding `s < S` shares out of supply `S` recovers at most `X + s` | `ArmadaYieldVault.sol:74-81, 491-514` |
| `donation_attack_unprofitable_post_fix` | `Yield.Vault` | `donation_attack_unprofitable`, specialized to the fixed contract's own invariant `s ≤ S - LOCKED_SHARES`; starting from a 1:1 share price (`claimable = supply`, no pending protocol fee), the donation attack cannot profit | `ArmadaYieldVault.sol:74-85` |

### Shield fee (`armada-poc/contracts/privacy-pool/modules/ShieldModule.sol`, audit C-3)

The fee is a ratio `num / den` (`PoolState.feeRatio`), with floor division (P-9). The
deployment sets it. Only the fee admin `PoolState.feeAdmin`, an address that the
deployment fixes, can change it with the step `Step.setFeeRatio`
(`step_feeRatio_frame`, `Pool.apply_setFeeRatio_not_admin`). The contract's
basis-point rate is the case `den = 10000`. The shield step applies it to the gross
amount.

| Lean theorem | Module | Property | Contract code |
|---|---|---|---|
| `fee_conservation` | `Fee` | `base + fee = amount` (type changed: P-9; proved) | `_getFee`, `ShieldModule.sol:353-371` |
| `fee_bounded` | `Fee` | `fee ≤ amount` (type changed: P-9; proved) | same |
| `fee_monotone` | `Fee` | larger amount ⇒ no smaller fee (type changed: P-9; proved) | same |
| `fee_zero_below_threshold` | `Fee` | `amount * num < den` pays zero fee (amounts `< 200` at 50/10000) (type changed: P-9; proved) | same |
| `shieldBase_pos` | `Fee` | a shield of a positive gross amount creates a note of positive value, under the fee cap `maxFeePercent` (new; proved) | `_getFee`, `ShieldModule.sol:353-371` (fee cap) |

### State channels (`ArmadaLean/Nitro/`, go-nitro and the SATP/Nitro/ForceMove papers)

See **[docs/nitro-theorems.md](docs/nitro-theorems.md)** for the full
theorem-to-source map, and **[docs/nitro-scope.md](docs/nitro-scope.md)** for
the three points a reader must check before relying on any Nitro theorem as a
claim about go-nitro. `Safety.lean` proves 63 on-chain safety and
conservation theorems. `Liveness.lean` states 34 theorems on unbeatable
strategies and the Turbo Value Algorithm; `docs/nitro-repair-2026-10-27.md`
§3 gives each one's current proof status.

## Trust base & scope

Poseidon and Keccak are both modeled symbolically (Dolev-Yao style,
`ArmadaLean.Term`, `ArmadaLean/Poseidon.lean`): a hash output is an inductive term, never a raw
number, tagged with the hash function that produced it (`ArmadaLean.HashFn`). The
symbolic model is itself the cryptographic assumption: inside it, Poseidon and Keccak
collision freedom, their domain separation from each other (including cross-function
separation — a Keccak output, a contract address, can never equal a Poseidon output, a
note key, a commitment, or a nullifier), and preimage resistance all hold by
construction (the type's own constructors), with no further hypothesis. `#print axioms`
on a theorem that uses this fact lists no `poseidon2`/`poseidon3`/`keccak`/injectivity
axiom, because the assumption lives in the choice of model, not in a per-theorem axiom.
The refinement from this specification to concrete code names these same three
properties as explicit hypotheses on the real hash functions
(`docs/verification-chain.md`). EdDSA stays an abstract unforgeable signature scheme —
an **explicit axiom** (`EdDSAVerify`), visible per-theorem via `#print axioms`
(see `docs/axioms-*.txt`). The Groth16 verifiers are the uninterpreted predicates
`VerifyAccepts` and `VerifyOwnedAccepts`, also declared with `axiom`; only the
can-happen theorems mention them. The empty leaf `ZERO_VALUE` is the opaque constant
`emptyLeaf`, not an axiom.
What is and isn't covered, in plain English: **[docs/what-the-proofs-mean.md](docs/what-the-proofs-mean.md)**.

Out of scope: Groth16, the circom compiler, Poseidon's concrete parameters,
the trusted-setup ceremony, the go-nitro Solidity contracts themselves (this
project models their behavior; it does not verify their bytecode), and all
contract/relayer/SDK code beyond the modeled formulas. This project
complements (does not replace) static analysis (Ecne/circomspect/Picus) and
an external circuit audit.

## Layout

```
ArmadaLean/
  Field.lean              BN254 scalar-field modulus + mod lemmas
  Poseidon.lean           symbolic (Dolev-Yao) Term model of Poseidon + Keccak
  Token.lean              a token as a symbolic address (P-1)
  BoundParams.lean        bound parameters and their symbolic hash (P-2, P-7)
  RangeCheck.lean         Num2Bits(120) semantics
  ValueConservation.lean  no-wraparound minting theorem
  Nullifier.lean          nullifier derivation + injectivity (not itself a double-spend proof)
  Merkle.lean             Merkle proof leaf-binding + the incremental tree (root, path)
  Transact.lean           full constraint model of Transact.circom
  TransactOwned.lean      constraint model of TransactOwned.circom
  PoolOwned.lean          pool's owned path (TransactModule.transactOwned) and preimage storage
  Pool.lean               pool state (live notes, nullifiers, roots, custody) and operations
  PoolSafety.lean         pool contract's safety theorems, over Pool.lean
  Yield/
    Vault.lean             #365 fix (LOCKED_SHARES lock) conversion model + proofs
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
    Liveness.lean           34 liveness theorems (status in docs/nitro-repair-2026-10-27.md §3)
    NonVacuity.lean         one proved witness per theorem with hypotheses
docs/
  what-the-proofs-mean.md one-page explainer
  how-to-verify.md      step-by-step independent verification guide
  axioms-circuit.txt    #print axioms audit output (circuit theorems)
  axioms-contracts.txt    #print axioms audit output (vault/fee theorems)
  pool-symbolic-changes.md  the P-1..P-11 changes, the new theorems, the changed types
  departures.md          contract paths the pool model does not model, and why
  nitro-scope.md         what the Nitro theorems cover, and what they do not
  nitro-theorems.md       the Nitro/SATP/ForceMove theorem-to-source map
  nitro-repair-2026-10-27.md  the review-driven corrections to the Safety statements
```
