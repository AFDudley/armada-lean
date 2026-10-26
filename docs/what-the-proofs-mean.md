# What the Armada Lean proofs mean — one page

## What is this?

`armada-lean` is a [Lean 4](https://lean-lang.org) project. Lean is an interactive
theorem prover: code in this repo is not executed — it is *checked*. Every
`theorem` in the repo comes with a proof that Lean's small, heavily-scrutinized
kernel re-verifies step by step. If `lake build` succeeds, the proofs are
correct with the same certainty as a mathematical proof reviewed line-by-line
by an infallible (if pedantic) referee.

## What was verified

We translated the security-critical *logic* of the Armada shielded pool into
Lean and proved the properties that the internal security review
(`armada-circuits/docs/SECURITY_REVIEW.md`) argued for informally:

| Theorem | Plain-English meaning |
|---|---|
| `rangeCheck120_sound` | The circuit's 120-bit range check really does bound every note value below 2¹²⁰. |
| `no_wraparound_minting` | Because all values are < 2¹²⁰ and a transaction has ≤ 8 inputs / ≤ 4 outputs, "sum of inputs equals sum of outputs" holds as ordinary integers — not just modulo the field prime. **Value cannot be created by wrapping around the field modulus.** (Formalizes the fix for Finding 1.) |
| `distinct_leaves_distinct_nullifiers` | The circuit's pairwise-distinctness check on leaf positions guarantees all nullifiers in a proof are distinct (Poseidon is modeled symbolically, so collision resistance holds by construction — see below). **The same note can never be spent twice in one proof.** (Formalizes the fix for Finding 2.) |
| `merkleRoot_inj_leaf` | A Merkle membership proof binds exactly *one* leaf to the tree root — a proof for one commitment cannot be repurposed for another. |
| `transact_public_outputs_determined` | Given the private witness, the public outputs (nullifiers, output commitments) are fully determined — no hidden degrees of freedom in the security-critical signals. |
| `transact_no_double_spend` / `transact_value_conserved` | The two properties above, proven end-to-end against the full constraint model of `Transact.circom`. |
| `inflation_attack_profitable` | On the *current* yield vault share math, the first-depositor inflation attack (issue #365) is provably profitable — the vulnerability is real, not theoretical. |
| `mitigated_attack_unprofitable` | With the standard virtual-shares fix, the same attack is provably *un*profitable — the fix is mathematically sufficient. |
| `fee_*` | The shield fee, a ratio fixed at deployment with floor division, conserves value (`net + fee = gross`), is bounded by the amount, and is monotone — a reference spec for the contract↔SDK↔spec mismatch (audit C-3). On branch `pool-symbolic` these proofs are `sorry` until the operator approves the new types (`docs/pool-symbolic-changes.md`). |

## The trust base — what you are trusting when you trust these proofs

1. **Lean's kernel** (~a few thousand lines, widely audited) — not our code.
2. **Fidelity of the model** — we re-expressed `Transact.circom`, the Merkle
   verifier, the vault share math, and the fee formula as Lean definitions,
   constraint for constraint, with line-references in the source. A mismatch
   between our Lean model and the real Circom/Solidity would not be caught by
   Lean. This is why the model is deliberately small and auditable (~a page
   per component), and why this complements rather than replaces Ecne/Picus
   and an external circuit audit.
3. **Explicit cryptographic assumptions.** Poseidon and Keccak are both modeled
   symbolically (Dolev-Yao style): a hash output is a term built by an inductive
   type (`ArmadaLean.Poseidon.Term`), tagged with which hash function produced
   it, never a raw number, so collision resistance, domain separation and
   cross-function separation (a Keccak output — a contract address — can never
   equal a Poseidon output) hold *by construction* — no Poseidon or Keccak axiom
   exists in this project. EdDSA signature unforgeability is still assumed
   (`EdDSAVerify` axiom). These are standard assumptions — every security
   argument about the system makes them, we just make them *visible*. Run
   `#print axioms <theorem>` to see exactly which assumptions any theorem
   depends on; they are also listed in `docs/axioms-*.txt`.

## What is NOT covered

- The Groth16 proof system itself, the circom compiler, and snarkjs.
- The concrete security of Poseidon parameters (assumed, as above).
- The trusted-setup ceremony (toxic-waste hygiene is operational, not mathematical).
- All Solidity contract logic beyond the modeled fee/vault formulas, the relayer,
  the SDK, and liveness/DoS concerns.
- The two contract-side **verification bypasses** (`testingMode`,
  `VERIFICATION_BYPASS`) — these must be *removed*; no proof can help while
  proof-checking can be switched off.

## Reproduce

```bash
git clone https://github.com/ship-armada/armada-lean && cd armada-lean
lake build        # needs an elan-managed Lean toolchain (see lean-toolchain)
grep -rn sorry ArmadaLean/   # → only the theorems listed in docs/pool-symbolic-changes.md
```

Full walkthrough, including how to audit the assumptions with `#print axioms`
and how to check the model against the real Circom/Solidity:
**[docs/how-to-verify.md](how-to-verify.md)**.
