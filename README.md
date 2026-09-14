# armada-lean

Formal verification (Lean 4) of the core security properties of the **Armada
shielded pool** — the `Transact` ZK circuit, its Merkle membership verifier,
the yield-vault share math, and the shield fee formula.

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

Poseidon is modeled as an abstract injective (collision-resistant) hash and
EdDSA as an abstract unforgeable signature scheme — these are **explicit
axioms**, visible per-theorem via `#print axioms` (see `docs/axioms-*.txt`).
What is and isn't covered, in plain English: **[docs/what-the-proofs-mean.md](docs/what-the-proofs-mean.md)**.

Out of scope: Groth16, the circom compiler, Poseidon's concrete parameters,
the trusted-setup ceremony, and all contract/relayer/SDK code beyond the
modeled formulas. This project complements (does not replace) static analysis
(Ecne/circomspect/Picus) and an external circuit audit.

## Layout

```
ArmadaLean/
  Field.lean              BN254 scalar-field modulus + mod lemmas
  Poseidon.lean           abstract Poseidon + stated cryptographic assumptions
  RangeCheck.lean         Num2Bits(120) semantics
  ValueConservation.lean  no-wraparound minting theorem
  Nullifier.lean          double-spend impossibility
  Merkle.lean             Merkle proof leaf-binding
  Transact.lean           full constraint model of Transact.circom
  Vault.lean              #365 attack + mitigation proofs
  Fee.lean                shield-fee reference spec
docs/
  what-the-proofs-mean.md one-page explainer
  how-to-verify.md      step-by-step independent verification guide
  axioms-circuit.txt    #print axioms audit output (circuit theorems)
  axioms-contracts.txt    #print axioms audit output (vault/fee theorems)
```
