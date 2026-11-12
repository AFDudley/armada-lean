# Departures: contract paths this model does not model

This file lists every contract path the pool model (`ArmadaLean/Pool.lean`,
`ArmadaLean/PoolSafety.lean`, `ArmadaLean/Fee.lean`) leaves out, at the pinned
commit `armada-poc` `64436c14`. Each entry names the source line, and the
effect on the pool theorems in `README.md`.

## 1. `setVerificationKey` has no set-once guard

Source: `PrivacyPool.sol:384-394` delegates to
`VerifierModule.sol:31-41`.

```solidity
function setVerificationKey(
    uint256 _nullifiers,
    uint256 _commitments,
    VerifyingKey calldata _verifyingKey
) external override onlyDelegatecall {
    require(msg.sender == owner, "VerifierModule: Only owner");
    verificationKeys[_nullifiers][_commitments] = _verifyingKey;
    emit VerifyingKeySet(_nullifiers, _commitments, _verifyingKey);
}
```

The owner can call this at any time, for any circuit shape, and the new key
silently overwrites the old one. There is no set-once check, no timelock and
no event filter that blocks a second call.

**Effect on the theorems.** Every `ArmadaLean.Transact.Step` and
`ArmadaLean.PoolSafety` theorem that lets a holder spend a note assumes a
`Constrained` or `OwnedConstrained` witness: a witness that satisfies the
*fixed* circuit this project models. If the owner swaps in a different
verification key, `VerifyAccepts`/`VerifyOwnedAccepts` (the axioms standing in
for the Groth16 verifier) would then accept proofs against a different
circuit than the one `Transact.lean`/`TransactOwned.lean` state. Nothing in
`PoolSafety.lean` derives that the pool's installed key, at the time of any
call, is the one the circuit model describes. A key swap voids every pool
theorem that depends on `Constrained` holding at the real contract (all of
`core_invariant`, `pool_no_double_spend`, `transact_spends_only_owned`, and
every theorem built on them).

`ArmadaLean/Fee.lean`'s header previously claimed the pool "sets verifying
keys and fees once at deployment" (citing an early labbook decision). That
claim is false for the pinned contract: fixed in this change (see §2 below for
the fee half; the key half has no Lean statement to correct, since no theorem
in this project assumes a set-once key — the departure above was simply
undocumented until now).

**Not modeled**, and not modelable without a new hypothesis: a theorem that
assumes "the installed key for every circuit shape never changes after
genesis" would need to add that as an explicit, named hypothesis to every
spend theorem, since the pinned contract gives no such guarantee on-chain.

## 2. Owner-adjustable shield fee

Source: `PrivacyPool.sol:404-410` (`setShieldFee`) and `PrivacyPool.sol:478-482`
(`setFeeModule`).

```solidity
function setShieldFee(uint120 _feeBps) external override {
    require(msg.sender == owner, "PrivacyPool: Only owner");
    require(feeModule == address(0), "PrivacyPool: use fee module");
    require(_feeBps <= MAX_SHIELD_FEE_BPS, "PrivacyPool: Fee too high");
    shieldFee = _feeBps;
    emit ShieldFeeSet(_feeBps);
}

function setFeeModule(address _feeModule) external override {
    require(msg.sender == owner, "PrivacyPool: Only owner");
    feeModule = _feeModule;
    emit FeeModuleSet(_feeModule);
}
```

The owner can raise or lower the flat fee at any time (bounded by
`MAX_SHIELD_FEE_BPS = 1000`, 10%, `PrivacyPool.sol:39`). `setFeeModule` can
swap in or remove a fee module at any time; while one is set, `setShieldFee`
reverts (`PrivacyPool.sol:406`, `require(feeModule == address(0), ...)`),
so the flat rate stops applying.

**Effect on the theorems, flat-rate changes.** `ArmadaLean.Fee.FeeRatio`
already models a changeable flat rate: `step_feeRatio_frame` and
`Pool.apply_setFeeRatio_not_admin` state that only the fee admin changes
`PoolState.feeRatio` (operator ruling 2026-11-06). The stale claim this
change fixes was in `ArmadaLean/Fee.lean`'s header comment, which quoted an
early labbook decision ("sets verifying keys and fees once at deployment")
without noting that the fee half of that sentence does not hold at the
pinned contract.

**A second, unmodeled fee path: the fee module split.** Source:
`ShieldModule.sol:303-385` (`_transferTokenIn`), the three-way branch
(spec section 7.3):

```solidity
if (_isPrivilegedShieldCaller(msg.sender)) {
    // fee = 0; pool pulls the full gross amount
} else if (feeModule != address(0)) {
    (uint256 armadaTake, uint256 integratorFee, uint256 totalFee) =
        IArmadaFeeModule(feeModule).calculateShieldFee(integrator, amount);
    _requireValidFeeSplit(amount, integrator, armadaTake, integratorFee, totalFee);
    // pool pulls (amount - totalFee); armadaTake goes to treasury,
    // integratorFee goes to `integrator` (caller-supplied, any address)
} else {
    // the flat shieldFee path ArmadaLean.Fee models
}
```

`_requireValidFeeSplit` (`ShieldModule.sol:237-250`) caps the fee-module
total at `MAX_FEE_MODULE_SHIELD_FEE_BPS = 1500` (15%, `ShieldModule.sol:42`),
a different and higher cap than the flat path's 10%
(`ArmadaLean.Fee.maxFeePercent`). The fee module can also split the total
between the treasury (`armadaTake`) and an arbitrary `integrator` address
the shielder names per call (`integratorFee`, `ShieldModule.sol:352-354`),
and `_isPrivilegedShieldCaller` (`ShieldModule.sol:258-263`, an adapter
registry gate) waives the fee to zero for a trusted caller.

**Effect on the theorems.** `shield_creates_exactly`
(`ArmadaLean.PoolSafety`) states that a shield of gross `x` creates a note of
exactly `shieldBase s.feeRatio x` and pays `shieldFee s.feeRatio x` to the
treasury, for every reachable state `s`. Its only state input is
`s.feeRatio`; nothing hypothesizes `feeModule = address(0)` or that no
adapter is privileged. So the theorem is stated as if it held in every
reachable state, but at a real state with a fee module installed, the
contract computes the note value from `IArmadaFeeModule.calculateShieldFee`
(an external call this project does not model) under a 15% cap, and can pay
part of the fee to an integrator the model's `PoolState` has no field for —
not from `s.feeRatio` under a 10% cap paid wholly to `s.treasury`. The
privileged-caller branch similarly creates a note of the full gross `x`
(zero fee), which `shield_creates_exactly` also does not state as a case.
`core_invariant`'s custody bookkeeping stays sound for the fee-module
branch specifically (the pool's own balance only ever gains
`amount - totalFee`, since `armadaTake` and `integratorFee` are pulled
`safeTransferFrom(msg.sender, ...)` directly, never through the pool's
balance), but `shield_creates_exactly`'s claimed note VALUE is wrong
whenever a fee module is installed, because the model's only fee formula is
`shieldBase`/`shieldFee` over `s.feeRatio`.

**Not modeled.** `ArmadaLean.Fee` and `PoolState` have no fee-module field,
no integrator fee, no 15% cap, and no privileged-caller zero-fee case.
`shield_creates_exactly` and the `can_happen` theorem built on it
(`shield_can_happen`) hold only for the flat-fee branch (`feeModule =
address(0)` and no privileged adapter); this project's statements do not
say so. Modeling the fee-module branch needs: a `PoolState` field for
whether a fee module is active, an opaque `calculateShieldFee`-shaped
function (parameterized like `VerifyAccepts`, since the fee module is an
external, upgradable contract), a `treasuryFees`-shaped ledger entry for the
integrator leg, and a restated `shield_creates_exactly` split into the two
(or three) cases. This is new work; no statement change is proposed here,
since fixing `shield_creates_exactly`'s hypotheses (adding `feeModule =
address(0)` and "no privileged adapter" as explicit hypotheses) is a change
to a `Spec` statement and needs the operator's approval under rule 8.3.

## 3. CCTP cross-chain shield and unshield

Source: `ShieldModule.sol:101-140` (`processIncomingShield`) and
`TransactModule.sol:116-134` (`atomicCrossChainUnshield`).

`processIncomingShield` is reached only from the router's CCTP message
handlers, after CCTP has minted USDC to the pool. It inserts one or more
notes in a single batch, with the first note absorbing the CCTP protocol fee.
`atomicCrossChainUnshield` validates and nullifies a transaction on this
chain, then burns USDC through CCTP to a named `finalRecipient` on another
chain, in one call.

**Effect on the theorems.** `ArmadaLean.PoolSafety` models `shield` and
`transact`/`transactOwned` as the only ways value enters or leaves pool
custody (`core_invariant`). Neither CCTP path has a `Step` constructor. So
`core_invariant`, `transact_unshield_exact` and `shield_creates_exactly` say
nothing about a CCTP-driven mint or burn: their custody bookkeeping is silent
on whether a CCTP-sourced note's `shieldFee` matches `Fee.shieldFee`, whether
the cross-chain burn amount matches the nullified value, or whether the
`destinationCaller` pin (`CCTPBindingLib`, issue #64) holds. These are real
contract paths with no corresponding `Step`, not paths the existing theorems
cover incompletely.

**Not modeled.** This project has no `Step.processIncomingShield` or
`Step.atomicCrossChainUnshield`. Modeling them needs new `Step` constructors,
a model of the CCTP mint/burn call (as an opaque effect with a declared value,
similar to how `VerifyAccepts` is opaque), and new custody-conservation
theorems for each. This is new work, not a fix to an existing claim; no
statement change is proposed here since none of the current theorems make a
false claim about CCTP — they are simply silent on it.

## 4. Batched shields and transacts: one tree-rollover decision per batch

Source: `TransactModule.sol:43` (`function transact(Transaction[] calldata
_transactions)`) and `ShieldModule.sol:101-140`'s `n`-note batch insert.

A single `transact` call takes a *list* of transactions and applies them in
one call, sharing one Merkle-tree rollover decision
(`IMerkleModule.getInsertionTreeNumberAndStartingIndex`) across every note the
batch inserts. `processIncomingShield` likewise batch-inserts `n` notes with
one `Shield` event and one rollover decision.

**Effect on the theorems.** `ArmadaLean.Pool.Step.transact` and `Step.shield`
each model *one* transaction or *one* shield applying to the pool state, with
its own tree-rollover decision. `PoolSafety.leaf_has_merkle_witness` and
`leaf_stable` are stated and proved per-leaf, over a sequence of single-note
`Step`s. Running `N` single-note `Step`s in a row and running one `N`-note
batch call are not shown equal: a batch shares one rollover decision across
all `N` insertions, where `N` single steps would each make (and could each
make differently) their own rollover decision. Nothing in `Pool.lean` derives
that the batch's one rollover decision matches what `N` separate `Step`s
would have produced.

**Not modeled.** No theorem states that a `transact([tx1, ..., txN])` batch
call, or an `n`-note `processIncomingShield`, has the same effect on pool
state as `N` sequential single-item `Step`s. This is a real gap in coverage:
anything specific to sharing one rollover decision across a batch (for
example, a batch that spans two trees because an earlier item in the same
batch filled the current tree) has no theorem at all, proved or otherwise.

## Statement changes needed

Item 2's flat-fee half needs no statement change: it is already correctly
modeled (`FeeRatio`, `step_feeRatio_frame`), and the fix in this branch is to
`ArmadaLean/Fee.lean`'s doc comment (a false claim about the fee half of a
"sets once" sentence), not to a `Spec` definition.

Item 2's fee-module half is a false claim, not a silent gap:
`shield_creates_exactly` (`ArmadaLean.Spec.PoolSafety`) is stated for every
reachable state `s`, with no hypothesis ruling out a fee module or a
privileged adapter. The exact proposed text, for the operator (rule 8.3):
add two hypotheses, `(hNoFeeModule : s.feeModule = none)` and `(hNoPrivileged
: ¬ s.PrivilegedShieldCaller caller)` (new `PoolState` fields this change
does not add), to `Spec.shield_creates_exactly` and every theorem built on
it (`shield_can_happen`). Counterexample without the fix: a reachable state
with a fee module installed and `armadaTake + integratorFee = 15% * x >
shieldFee s.feeRatio x` (the fee-module cap exceeds the flat-rate cap);
the real contract creates a note of `x - 0.15x`, not `shieldBase s.feeRatio
x`, so the theorem's conclusion is false at that state as currently stated.
Items 1, 3 and 4 are gaps this project never claimed to close (so no
existing theorem is false); closing them needs new `Step` constructors and
new theorems — new work, proposed to the operator separately, not a
correction to a current statement.

## Related, separately owned cleanup

- `held` is a ghost ledger and the README's "tokens the pool holds" language
  (finding 4's fourth bullet) is owned by a different branch
  (`statement/held-to-ledger`), not this one.
- The hash-assumption visibility finding (finding 5) and the Nitro split
  (finding 6) are owned by other branches.
