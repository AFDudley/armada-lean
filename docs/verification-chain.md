# From this specification to deployed bytecode

This repository is the specification of the Armada adjudicator and pool. It is
symbolic (Dolev–Yao): hashes are terms, addresses are terms, and the attacker is
modelled. It is the only layer that reasons about an attacker. The decision
record covers the verification chain end to end, Lean through deployed bytecode.

## The chain

| Step | From | To | How | Proof |
|---|---|---|---|---|
| 1 | this Lean specification | a Stele specification (EquiVM) | programmatic translation of the executable operations | a refinement proof, emitted with the translation |
| 2 | Stele | Solidity | transliteration (Stele is close to Solidity) | none needed: step 4 checks the result |
| 3 | Solidity | bytecode | solc | none needed: step 4 checks the result |
| 4 | bytecode | Stele | EquiVM on EVMLean's EVM semantics | a refinement proof, written by an agent |

All of it is Lean on one toolchain, `leanprover/lean4:v4.35.0`.

## What the specification leaves out, and why

The specification omits the concrete forms because they are already known:

- Keccak over `abi.encode` for channel ids and state hashes (go-nitro
  `NitroUtils.sol`);
- Poseidon for note commitments, note keys and nullifiers (the pool's circuits);
- 20-byte addresses, `uint256` amounts, `uint120` note values;
- the Solidity ABI and storage-layout rules.

Step 1 maps each symbolic term to its concrete value through a typed decoder
per ABI position: a word that the run computed as a hash decodes to that hash
term, and any other word decodes to `val` in its range. The symbolic model
(`ArmadaLean.Term`, `ArmadaLean/Poseidon.lean`) is itself the specification's
cryptographic assumption: inside it, Poseidon and Keccak collision freedom,
their domain separation, and preimage resistance hold by construction, with no
further hypothesis. Concrete code has no such construction, so the step-1
theorem names the same three properties as explicit hypotheses on the real
functions: collision freedom of Keccak-256, of its 160-bit truncation, and
between Poseidon and Keccak outputs (no Poseidon output that a run uses equals
a Keccak output that it uses), and preimage resistance of each hash. Poseidon
stays trusted. The current Solidity is not
authoritative: the rewrite chooses encodings that need no other assumption.

## What this asks of the specification

The translation in step 1 reads the operations' definitions. So the operations
are small executable functions over a typed state, built by composing existing
definitions, and each changes only its own fields. Proofs meet the size and
complexity criteria of `armada-laconic/docs/lean/verification.md` §6a.

## Alternatives considered

- Verity: rejected; it adds a young compiler to the trusted base and gives
  nothing that step 4 does not.
- A Bend2 specification: no shorter route. Bend2 can still be an
  implementation language: EquiVM checks bytecode from any source.

## Design decisions of 2026-10-28

Findings on this chain, decided during the specification's review.

- **The zero-knowledge verifier stays a trusted primitive at step 4.** Step 4
  does not refine the Groth16 verifier. The specification keeps
  `VerifyAccepts`, `VerifyOwnedAccepts` and `EdDSAVerify` as the trusted
  primitives.
- **Poseidon stays a trusted primitive.** This is the project's design decision.
- **The new pool comes from the armada-poc pool.** The new pool removes
  features from the armada-poc pool.
- **An EquiVM certificate is a one-way inclusion.** Every bytecode run matches
  some Stele run, or it runs out of gas. No theorem states the converse
  relation. The certificate preserves safety theorems. It does not preserve
  "can happen" theorems or liveness theorems. The design for these two
  classes of theorem reflects design review findings. The operator answered
  O1 and O4-O7 on 2026-10-28, and the coordinator corrected O2 and O3 the same
  day. The design, and the owner of the EquiVM and EVMLean work, are decided
  in a later refinement-risks review §7 (Q2.1, Q2.2).
