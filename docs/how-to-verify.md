# How to verify these proofs yourself

You do not need to trust us, this README, or any CI badge. Everything in this
repo can be independently re-checked on your own machine in ~5 minutes. This
guide assumes no prior Lean experience.

## 1. Install the Lean toolchain (once)

Install **elan** (Lean's version manager, like rustup for Rust):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"   # also added to your shell profile
```

You do **not** need to install Lean itself: the repo's `lean-toolchain` file
pins the exact compiler version (`leanprover/lean4:v4.33.1`), and elan
downloads it automatically on first use.

## 2. Clone and build

```bash
git clone https://github.com/AFDudley/armada-lean
cd armada-lean
git checkout nitro-proofs
lake exe cache get   # downloads the prebuilt Mathlib
lake build
```

Expected result: `lake build` ends with `Build completed successfully` and exit code 0.

**What this means:** every `theorem` in `ArmadaLean/*.lean` was re-checked,
proof step by proof step, by the Lean kernel. If any proof were wrong — or a
theorem statement didn't say what we claim — the build would fail. There is no
way to "force" a green build other than a correct proof.

The project depends on Mathlib `v4.33.1` (operator ruling 2026-10-27: use Mathlib
where it makes sense). `lake exe cache get` downloads Mathlib's prebuilt files, so
the build does not compile Mathlib. `lake-manifest.json` pins the Mathlib commit.

## 3. Check there are no unfinished proofs

A proof can be faked with `sorry` ("trust me"). Verify none exist:

```bash
grep -rn "sorry\|admit" ArmadaLean/
```

Expected result on branch `nitro-proofs`: only theorems in `ArmadaLean/Nitro/Liveness.lean`
that still wait for a proof. Their types are approved (tag `nitro-proofs-approved-2026-10-28`).

## 4. Audit the assumptions (the important part)

Proofs about a ZK system must assume *some* cryptography (no one proves
Poseidon is collision-resistant — that's a computational hardness assumption).
We made every such assumption an explicit, named `axiom`. Lean can tell you
exactly which assumptions any theorem depends on:

```bash
cat > /tmp/check_axioms.lean <<'EOF'
import ArmadaLean
#print axioms transact_value_conserved
#print axioms transact_no_double_spend
#print axioms merkleRoot_inj_leaf
#print axioms no_wraparound_minting
#print axioms inflation_attack_profitable
#print axioms mitigated_attack_unprofitable
#print axioms fee_conservation
EOF
lake env lean /tmp/check_axioms.lean
```

Compare against the recorded output in `docs/axioms-circuit.txt` and
`docs/axioms-contracts.txt`. What you should see:

- **Circuit theorems** may list `poseidon2`, `poseidon2_inj`, `poseidon3`,
  `EdDSAVerify`, `msgHashOf` — these are the declared cryptographic
  assumptions (read their doc comments in `ArmadaLean/Poseidon.lean` and
  `ArmadaLean/Transact.lean`).
- **`no_wraparound_minting` and all vault/fee theorems** depend only on
  `propext` / `Quot.sound` — Lean's standard logical axioms, i.e. they are
  unconditional mathematics.
- **`sorryAx` appears only for the Liveness theorems that still wait for a proof** —
  anywhere else it would indicate a hidden `sorry`.

## 5. Check the model matches the real code (the human part)

Lean verifies that the *model* is sound; only a human can verify the model
matches the deployed code. This is deliberately easy: each definition cites
the exact source lines it models, and the models are tiny. Suggested review
order (~30 min):

| Read this | And compare against |
|---|---|
| `ArmadaLean/Transact.lean` (`Constrained`) | `armada-circuits/src/operations/Transact.circom` (cited line-by-line) |
| `ArmadaLean/Merkle.lean` (`merkleStep`, `merkleRoot`) | `armada-circuits/src/lib/merkle.circom:39-54` |
| `ArmadaLean/RangeCheck.lean` (`bitsVal`) | circomlib `Num2Bits` semantics |
| `ArmadaLean/Vault.lean` (`c2s`, `c2a`) | `armada-poc/contracts/yield/ArmadaYieldVault.sol:492-515` |
| `ArmadaLean/Fee.lean` (`shieldFee`, `shieldBase`) | `armada-poc/contracts/privacy-pool/modules/ShieldModule.sol:336-354` |

## 6. (Optional) Modify something and watch it break

The fastest way to build confidence: change a theorem statement to something
false (e.g. claim the mitigated vault attack *is* profitable), run
`lake build`, and observe the proof no longer goes through. The kernel is the
referee.

## Troubleshooting

- **`lake: command not found`** → elan isn't on your PATH; run
  `export PATH="$HOME/.elan/bin:$PATH"` or restart your shell.
- **First build downloads the toolchain** (~500 MB) — normal, happens once.
- **macOS Gatekeeper prompt** on first `lean` run — allow in System Settings →
  Privacy & Security.
