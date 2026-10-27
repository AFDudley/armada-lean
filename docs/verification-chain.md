# From this specification to deployed bytecode

This repository is the specification of the Armada adjudicator and pool. It is
symbolic (Dolev–Yao): hashes are terms, addresses are terms, and the attacker is
modelled. It is the only layer that reasons about an attacker. The decision
record is in `AFDudley.github.com/armada-laconic`, `engineering/build-plan.md`,
section "Verification chain" (operator rulings 2026-10-25 and 2026-10-27).

## The chain

| Step | From | To | How | Proof |
|---|---|---|---|---|
| 1 | this Lean specification | a Stele specification (EquiVM) | programmatic translation of the executable operations | a refinement proof, emitted with the translation |
| 2 | Stele | Solidity | transliteration (Stele is close to Solidity) | none needed: step 4 checks the result |
| 3 | Solidity | bytecode | solc | none needed: step 4 checks the result |
| 4 | bytecode | Stele | EquiVM on EVMLean's EVM semantics | a refinement proof, written by an agent |

All of it is Lean on one toolchain, `leanprover/lean4:v4.33.1`.

## What the specification leaves out, and why

The specification omits the concrete forms because they are already known:

- Keccak over `abi.encode` for channel ids and state hashes (go-nitro
  `NitroUtils.sol`);
- Poseidon for note commitments, note keys and nullifiers (the pool's circuits);
- 20-byte addresses, `uint256` amounts, `uint120` note values;
- the Solidity ABI and storage-layout rules.

Step 1 maps each symbolic term to its concrete value under one named
assumption: no Keccak or Poseidon collision among the values a run uses.

## What this asks of the specification

The translation in step 1 reads the operations' definitions. So the operations
are small executable functions over a typed state, built by composing existing
definitions, and each changes only its own fields. Proofs meet the size and
complexity criteria of `armada-laconic/docs/lean/verification.md` §6a.

## Alternatives considered

- Verity: rejected; it adds a young compiler to the trusted base and gives
  nothing that step 4 does not.
- A Bend2 specification: no shorter route
  (`armada-laconic/labbook/2026-10-27-bend2-to-evm.md`). Bend2 can still be an
  implementation language: EquiVM checks bytecode from any source.
