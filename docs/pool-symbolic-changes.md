# Pool model without contract layout or encoding (branch `pool-symbolic`)

Base: `pool-model` at `7f2d1ec`. Source of the findings: armada-laconic
`labbook/2026-10-26-pool-layout-audit.md` (P-1 to P-11). Operator rulings: 2026-10-26.
Toolchain: Lean v4.33.1, no Mathlib.

## Proof policy on this branch

- A theorem whose type is new, or whose hypotheses or conclusion changed, has the
  proof `sorry`. The operator approves the type first.
- A theorem whose type changed only because a definition moved (`Token` for `Nat`,
  `Term` for the bound-parameters hash) keeps a repaired proof.
- Exception, by operator instruction (2026-10-27): the fee theorems, `leaf_stable`,
  `shield_creates_exactly` and `shield_can_happen` have full proofs, because the old
  proofs port.
- A helper lemma that a kept proof needs is proved. So every kept statement stays
  free of `sorryAx` (checked with `#print axioms`, for example `core_invariant`,
  `pool_no_double_spend`, `pool_preimageOf_consistent`, `live_note_unspent`).

## Findings

### P-1. `token : Nat` → `Token`

- New file `ArmadaLean/Token.lean`: `structure Token where address : Term`, with
  `DecidableEq` and no arithmetic. `tokenId : Token → Term` is `_getTokenID`
  (TransactModule.sol:449-454). `tokenId_inj` (proved).
- `commitment (npk : Term) (token : Token) (value : Nat)` hashes `tokenId token`.
- `TransactWitness.token`, `TransactOwnedWitness.token`, `CommitmentPreimage.token`:
  type `Token`. `PoolState.live : Token → …`, `PoolState.held : Token → Nat`.
- Types changed only by the substitution (proof repaired): `commitment_owner_inj`,
  `commitment_mpk_inj` (`{token : Nat}` → `{token : Token}`), `spend_live_exact`
  (`{token : Nat}` → `{token : Token}`), `live_note_unspent` (`(t : Nat)` →
  `(t : Token)`), `transact_spend_can_happen` (`token : Nat` → `token : Token`).
- `hashCommitment_inj` (helper): proof repaired with `tokenId_inj`.

### P-2. `boundParamsHash : Nat` → symbolic hash of a `BoundParams` record

- New file `ArmadaLean/BoundParams.lean`. `BoundParams` has `treeNumber : Nat`,
  `unshield : Option Unshield`, `adaptContract : Option Term`, `adaptParams : Term`.
  The model omits `minGasPrice`, `chainID` and `commitmentCiphertext` (one chain, no gas,
  no ciphertexts).
- `hashBoundParams : BoundParams → Term` is a Keccak term of the fields.
  `hashBoundParams_inj` (proved, by construction) is the binding property.
- `TransactPublic.boundParamsHash` and `TransactOwnedPublic.boundParamsHash` have type
  `Term`. `msgHashOf` hashes the term directly (no `Term.val`).
- `Step.transact` and `Step.transactOwned` take `bp : BoundParams`,
  `hBound : pub.boundParamsHash = hashBoundParams bp` and
  `hAdapt : AdaptAllows bp caller` (TransactModule.sol:530-532). The tree number comes
  from `bp.treeNumber`; it is no longer a free argument.
- Departure: the contract hashes the unshield kind only (`UnshieldType`) and binds the
  recipient and the amount through the last output commitment. The model hashes the
  whole `Unshield`. Both bind the same data to the proof.

### P-3. No pause, no admin

- Deleted `PoolState.shieldsPaused`, `Step.shield`'s `hNotPaused`, and `Step.admin`.
- Deleted `transact_cannot_be_blocked` and `transactOwned_cannot_be_blocked`. Their
  conclusion `∃ s', Step { s with shieldsPaused := b } s'` covered the admin step only.
  Theorem 1 below replaces them for every step by every caller.

### P-4. "Absent" as `Option`, not a zero sentinel

- Deleted `isZeroPreimage`, its `Decidable` instance, `npk_preimage_not_zero`,
  `Step.transactOwned`'s `hNonZero`, and the `hOutputsNonZero` hypotheses.
- `recordStep` has no zero test: `fun c' => if c' = c then some preimage else reg c'`.
- `adaptContract : Option Term` (no zero address). `withdrawn : Option Unshield → Nat`.
- The plain path keeps `records : List (Term × CommitmentPreimage)` with
  `records.Sublist (transactOutputRecords w pub)`. A sublist names the disclosed outputs
  and has no "absent" value, so it needs no `Option`.
- `applyRecords_returns` (helper) lost `hNonZero`; proof repaired.
- `transactOwned_records_all`: before `(hNonZero : ∀ j, ¬ isZeroPreimage …)`; after no
  such hypothesis. `sorry`.

### P-5. Position statements for the adjudicator's `holdings` slot

- `leaf_stable` and its step lemma `step_leavesAt_stable` are kept (operator ruling,
  2026-10-26). The first version of this branch deleted them; that deletion was wrong.
  The audit's word "slot" meant the adjudicator's EVM storage slot (`holdings`). The
  append-only property of the Merkle tree is Railgun protocol meaning, not a slot, and
  it holds independently of any adjudicator use. Source: `MerkleModule` is an
  "Append-only incremental binary Merkle tree over Poseidon" (MerkleModule.sol:12;
  insertion at MerkleModule.sol:54-121), and the Railgun whitepaper keeps notes in
  "batch incremental Merkle trees" to which "The hashes of the output UTXOs are then
  added" (armada-laconic `.scratch/rewrite-B/railgun-whitepaper-2021.txt`:161-163,
  :234-235). The doc comments now cite these sources and do not mention the
  adjudicator.
- `leaf_stable`: type changed only for P-8. Before, `(s'.leavesAt' tn).getD pos d =
  (s.leavesAt' tn).getD pos d` with a default `d : Term`; after,
  `(s'.leavesAt' tn)[pos]? = (s.leavesAt' tn)[pos]?`, with no default. The range
  conjunct `pos < (s'.leavesAt' tn).length` and the hypothesis are unchanged. Proved,
  not `sorry`: `step_leavesAt_stable` is 19 lines (built on `insertLeaves_leavesAt` and
  `insertLeaves_leavesAt_length_ge`) and `leaf_stable` is 9 lines. `#print axioms
  leaf_stable` lists `EdDSAVerify, propext, Quot.sound` (no `sorryAx`).
- Kept as lemmas, each with the reason in its doc comment:
  `live_note_unspent` (theorems 1 and 3 need a live note's nullifier to be fresh),
  `live_leaf_matches` (theorem 3 builds each input's Merkle path from it),
  `live_values_spendable` (theorem 3 needs each input to pass the range check).
- The audit proposed `live_note_spendable`. Theorem 3 with `N = 1` is that statement
  for a contract-owned note. No plain-path twin was added.

### P-6. The 120-bit bound

Hashes are Dolev-Yao terms. Note values are numbers. The bound now has one name in the
circuit layer: `Spendable v := RangeChecked120 v` (`ArmadaLean/RangeCheck.lean`).

Evidence, from the proofs:
- Safety needs the bound in one place only: `no_wraparound_minting`, where the circuit's
  field equality `sumIn === sumOut` meets integer value conservation.
  `core_invariant` reaches it through `transact_balance`/`transactOwned_balance` →
  `transact_value_conserved`/`transactOwned_value_conserved`. The bound there comes from
  the circuit constraints `rangeIn`/`rangeOut` and the shape bound `N ≤ 8`, `M ≤ 4`,
  not from the pool state. No safety theorem reads a bound from the pool state.
- Liveness needs the bound in two places:
  1. A note can be an input only if its value passes the input range check. So every
     live note must be `Spendable` (`live_values_spendable`). `Step.shield` takes
     `hSpendable : Spendable value` for this (the contract gets it from `uint120 value`,
     PoolTypes.sol:82). Transact outputs get it from `rangeOut`.
  2. A merge (theorem 3) has one output of the inputs' sum. The sum must pass the output
     range check (`hSum`). Eight notes each below `2^120` can sum above `2^120`, so a
     merge of large notes is impossible. The adjudicator must allow for this.
- `live_values_lt_2pow120` (`p.2.value < 2 ^ 120`) became `live_values_spendable`
  (`Spendable p.2.value`). `sorry`.

### P-7. The unshield: protocol meaning or encoding?

Decision: **"the last output" and "the recipient in `npk`" are encoding. "At most one"
is protocol meaning.** The model carries `unshield : Option Unshield` with
`Unshield := {recipient : Term, value : Nat}` in the bound parameters.

Evidence:
- Railgun whitepaper (S-RG, 2021, section "RAILGUN Core System & Protocol"): "In our
  zero-knowledge program we have the following public inputs: • Adapt ID … • Deposit
  amount • Withdrawal amount • Merkle root • Nullifiers • Output UTXO hashes …" and,
  optional, "An address to withdraw from which must be public for non-zero
  withdrawals". The contract "transfers tokens from itself to the specified user
  wallet address in the public inputs, if a withdrawal amount is specified". So the
  protocol has one withdrawal amount and one address per transaction, as public data.
- ABDK audit of Railgun v1, 2021-04-01: CVF-7 (listing 7) shows `RailgunLogic.sol`
  checking `_depositAmount` and `_withdrawAmount` as separate parameters
  (`require(_withdrawAmount < 2**120, …)`), and CVF-21 (listing 21) shows `Verifier.sol`
  taking `uint256 _withdrawAmount` as a public input. The withdrawal was not an output
  note.
- Circuits: `armada-circuits/src/operations/Transact.circom` and `TransactOwned.circom`
  contain no unshield at all (no match for "unshield"). The `M` outputs are uniform.
- Contract: PoolTypes.sol:78 "For unshield outputs, `npk` encodes the recipient
  address." TransactModule.sol:313-331 "Hash must match last commitment".
  TransactModule.sol:413 `address recipient = address(uint160(uint256(_note.npk)));`.
  `BoundParams.unshield` is only the kind `NONE`/`NORMAL`/`REDIRECT`
  (PoolTypes.sol:24-31).
- Zokyo audit of Railgun v2, 2022-12-21, finding #1: "does not validate
  unshieldPreimage to contain a correct value. Without such validation, anyone could
  call a function providing its own address and get all tokens." The v2 carrying of
  the withdrawal in an output needs an extra contract check to bind it, which is a
  sign of an encoding.

Changes:
- `Step.transact`: deleted `unshieldTail`, `hSplit`, `hUnshieldLen`. Added
  `hOutputs : UnshieldRefines w bp.unshield newNotes`. `UnshieldRefines` (Pool.lean) is
  the one place where the encoding appears: no unshield → all outputs are new notes;
  `some u` → the outputs are the new notes followed by `⟨u.recipient, w.token,
  u.value⟩`.
- Custody falls by `withdrawn bp.unshield`. The ghost record `PoolState.payouts` gains
  `⟨w.token, u.recipient, u.value⟩`.
- `transact_unshield_exact`: before, a list fact over `unshieldTail`
  (`listSum unshieldTail = listSum spent - listSum new`); after, a step fact: for a
  `Step.transact` with `bp.unshield = some u`, a step exists whose payouts gain exactly
  `⟨w.token, u.recipient, u.value⟩`, whose custody falls by `u.value`, and
  `u.value = spent value - new value`. `sorry`.
- `unshield_can_happen`: before `(npkOut : Term) (valueOut : Nat) (hValuePos : …)`,
  conclusion `∃ s', Step s s'`; after `(bp) (hAdapt) (recipient value) (hU : bp.unshield
  = some ⟨recipient, value⟩)`, no unused `hValuePos`, conclusion adds
  `s'.payouts = s.payouts ++ [⟨token, recipient, value⟩]`. `sorry`.
- `REDIRECT` unshields (payout to `msg.sender`) are not modeled.

### P-8. `Term.val 0` and lookups with a default

- `emptyLeaf : Term` is an `opaque` constant for `ZERO_VALUE` (Merkle.lean). It is not an
  axiom. `treeRoot` pads with it. An `Inhabited Term` instance supports the `opaque`.
- A tree that does not exist has no leaves and no roots (`leavesAt`, `rootsAt` return
  the empty list). That is the empty collection, not a sentinel value.
- `treePath_correct` (helper) uses `getD i emptyLeaf`: slot `i` of the tree, which is the
  padding for `i ≥ length`. New helper `treePath_correct_of_getElem?` states it for
  `leaves[i]? = some leaf` (proved).
- `leaf_has_merkle_witness`: before `(hi : i < (s.leavesAt' tn).length)` and the leaf
  `(s.leavesAt' tn).getD i (Term.val 0)`; after `(hleaf : (s.leavesAt' tn)[i]? = some
  leaf)` and the leaf `leaf`. `sorry`.
- `live_leaf_matches`: before `(s.leavesAt' tn).getD pos (Term.val 0) = hashCommitment
  pre`; after `(s.leavesAt' tn)[pos]? = some (hashCommitment pre)`. `sorry`.
- `owned_spend_witness_exists`: `hLeafValue` before `leaves.getD (leavesIndices i)
  (Term.val 0) = …`; after `leaves[leavesIndices i]? = some …`. `sorry` (see P-10).
- `step_live_leaf_matches`, `reachable_live_leaf_matches` (helpers): default
  `Term.val 0` → `emptyLeaf`; proofs repaired. The default is never read, because every
  live position is in range.

### P-9. Shield fee as a ratio

- `Fee.lean`: `structure FeeRatio` (`num`, `den`, `den_pos : 0 < den`,
  `num_le_den : num ≤ den`). `shieldFee r amount := amount * r.num / r.den`.
  Deleted `BASIS` and `fee_exact_50bps` (its subject was the basis-point constant).
- `fee_bounded`, `fee_conservation`, `fee_monotone`: before `(feeBP : Nat)
  (h : feeBP ≤ BASIS)`; after `(r : FeeRatio)`. `fee_zero_below_threshold`: before
  `(h : amount < 200) : shieldFee 50 amount = 0`; after `(r : FeeRatio)
  (h : amount * r.num < r.den) : shieldFee r amount = 0`. All four are proved (the old
  proofs port; `fee_bounded` 5 lines, the others 1 to 2 lines). `#print axioms
  fee_conservation` lists `propext, Quot.sound`.
- Operator ruling, 2026-10-27: the shield fee is pool behaviour and belongs in the
  shield step. The pool computes `(base, fee)` with `_getFee` (ShieldModule.sol:353-371),
  gives the note `base`, and pays `fee` to the treasury. On the local path
  `_transferTokenIn` (ShieldModule.sol:324-340) pulls `base` into the pool and the fee
  from the caller to the treasury; on the cross-chain path `_applyShieldFee`
  (ShieldModule.sol:209-218) pays the fee from the pool's balance. The first version of
  this branch said the fee leg never passes through the pool and took the net amount;
  that was wrong for the cross-chain path, and the ruling puts the fee in the step on
  both paths.
- `PoolState.feeRatio : FeeRatio` is set at genesis (`genesis r`) and no step changes
  it (`step_feeRatio`, proved: `cases h <;> rfl`). `Reachable` starts from
  `genesis r` for some `r`. `PoolState.treasuryFees : Token → Nat` is the ghost record
  of fees paid to the treasury.
- `Step.shield (token : Token) (x : Nat) (npk : Term) (hValue : 0 < x)
  (hSpendable : Spendable (shieldBase s.feeRatio x))`. `x` is the gross amount. The note
  is `⟨npk, token, shieldBase s.feeRatio x⟩`; `held` grows by `shieldBase s.feeRatio x`;
  `treasuryFees token` grows by `shieldFee s.feeRatio x`. `hValue` is the contract's own
  check on the gross request (`_validateCommitmentPreimage`, ShieldModule.sol:244, called
  at :59 before the fee is taken). So with `num = den` the note value can be 0, as in
  the contract.
- The fee-module and privileged-caller branches of `_transferTokenIn`
  (ShieldModule.sol:286-323) are not modeled.

### P-10. No `ownedRandomOf` map

- Deleted `PoolState.ownedRandomOf`, `OwnedDisclosure`, `OwnedRandomRegistry`,
  `OwnedRandomConsistent`, `recordOwnedStep`, `recordOwnedStep_preserves_consistency`,
  `applyOwnedRecords`, `applyOwnedRecords_preserves_consistency`,
  `recordStep_preserves_other`, `applyRecords_preserves_other`, the steps' `ownedRecords`,
  `hOwnedRecords`, `ownedOutputs`, `hOwnedOutputs`, and `pool_ownedRandomOf_consistent`.
- Added `OwnedOpening := {ownerField : Term, random : Nat}`. `Step.transact` and
  `Step.transactOwned` take `openings : List (Term × OwnedOpening)`: the openings that
  the transaction publishes (decision 11). The ghost record `PoolState.published` keeps
  them. The pool does not check them; decision 11 puts the check in the adjudicator.
  So no theorem says "every published opening is correct".
- `owned_spend_witness_exists`: before `(ownedRandomOf : OwnedRandomRegistry)` and
  `hOwned : … ownedRandomOf (hashCommitment (preimages i)) = some ⟨ownerField, r⟩ ∧ …`;
  after `(published : List (Term × OwnedOpening))` and `hOwned : ∃ r,
  (hashCommitment (preimages i), ⟨ownerField, r⟩) ∈ published ∧ npk ownerField r =
  (preimages i).npk`. Also `token : Token`, `boundParamsHash : Term`, P-8 lookup, and a
  new conjunct `pub.boundParamsHash = boundParamsHash`. `sorry`.

### P-11. Trees as a list of trees

- `PoolState.trees : List TreeState` replaces `closedTrees`, `leaves`, `roots`. The last
  tree is the one that receives leaves. `genesisTrees = [⟨[], [treeRoot TreeDepth []]⟩]`
  and `(genesis r).trees = genesisTrees`.
- `transact_root_was_produced` and its helper `rootsAt_grounded`: `genesis.rootsAt' tn`
  became `rootsAt genesisTrees tn`, because `genesis` now takes the fee rate (P-9).
  Proofs repaired.
- `insertLeaves trees newLeaves`, `insertTree trees count`, `insertStart trees count`
  replace `insertResult`, `insertTreeNumber`, `insertStartPos`. One equation,
  `insertLeaves_getElem?` ("an insertion changes only the target tree, and extends
  it"), gives `insertLeaves_leavesAt`, `insertLeaves_rootsAt` and the old lemma set under
  new names (`insertLeaves_rootsAt_shape`, `_rootsAt_matches_leavesAt`,
  `_leavesAt_capacity`, `_leavesAt_stable`, `_leavesAt_length_ge`,
  `_leavesAt_new_matches`, `_target_length`, `insertStart_eq`). All proved.
- `shield_creates_exactly`: before, the new key is
  `(insertTreeNumber s.closedTrees s.leaves 1, insertStartPos s.leaves 1)`, with
  `hNotPaused`, `grossAmount`, `feeBP`, `hFeeBP`, `hRange`; after, `∃ tn pos` with
  `(s.leavesAt' tn)[pos]? = none` (fresh), `(s'.leavesAt' tn)[pos]? = some
  (hashCommitment note)`, and the same `live`/`held` facts; hypotheses `hValue`,
  `hSpendable`. After the P-9 ruling (2026-10-27) the type is:

  ```lean
  theorem shield_creates_exactly {s : PoolState} (token : Token) (x : Nat) (npk : Term)
      (hValue : 0 < x) (hSpendable : Spendable (shieldBase s.feeRatio x)) :
      ∃ s', Step s s' ∧ ∃ tn pos : Nat,
        (s.leavesAt' tn)[pos]? = none ∧
        (s'.leavesAt' tn)[pos]? = some (hashCommitment ⟨npk, token, shieldBase s.feeRatio x⟩) ∧
        s'.live token =
          ((tn, pos), (⟨npk, token, shieldBase s.feeRatio x⟩ : CommitmentPreimage)) :: s.live token ∧
        s'.held token = s.held token + shieldBase s.feeRatio x ∧
        s'.treasuryFees token = s.treasuryFees token + shieldFee s.feeRatio x ∧
        shieldBase s.feeRatio x + shieldFee s.feeRatio x = x ∧
        (∀ t, t ≠ token → s'.live t = s.live t ∧ s'.held t = s.held t ∧
          s'.treasuryFees t = s.treasuryFees t)
  ```

  Proved (8 lines; `fee_conservation` gives the sum). `#print axioms` lists
  `EdDSAVerify, propext, Quot.sound`.
- Not changed: an empty batch still pushes one root (audit, "Other observations").

## Other changed types (can-happen theorems)

- `shield_can_happen`: before `(token grossAmount feeBP : Nat) (hNotPaused) (hValue :
  0 < grossAmount) (hFeeBP) (hRange)`; after (P-9 ruling, 2026-10-27) `(token : Token)
  (x : Nat) (npk : Term) (hValue : 0 < x) (hSpendable : Spendable (shieldBase s.feeRatio
  x)) : ∃ s', Step s s'`, with `x` the gross amount. Proved (1 line).
- `transact_can_happen`: added `(caller) (bp) (hAdapt) (hNoUnshield : bp.unshield =
  none)`; `treeNumber` → `bp.treeNumber`; `token : Token`; removed
  `boundParamsHash : Nat`. `sorry`.
- `owned_transact_can_happen`: added `(bp) (hNoUnshield) (hAdapt)`; removed
  `hOutputsNonZero`, `treeNumber`, `boundParamsHash : Nat`; `token : Token`. `sorry`.
- `owned_spend_can_happen` (PoolOwned): `token : Token`, `boundParamsHash : Term`;
  removed `hOutputsNonZero` and the conjunct `∀ j, ¬ isZeroPreimage …`; added the
  conjunct `pub.boundParamsHash = boundParamsHash`. `sorry`.

## New theorems

### Theorem 1 — non-interference (`spend_not_blocked`, plus `transact_not_blocked`, `transactOwned_not_blocked`)

```lean
def SpendEnabled (s : PoolState) (tn : Nat) (root : Term) (token : Token)
    (entries : List ((Nat × Nat) × CommitmentPreimage)) (nulls : List Term) : Prop :=
  root ∈ s.rootsAt' tn ∧
  (∃ rest, removeAll (s.live token) entries = some rest) ∧
  ∃ spent', markSpent (s.spent tn) nulls = some spent'

def Spends (s s' : PoolState) (t : Token) (e : (Nat × Nat) × CommitmentPreimage) : Prop :=
  e ∈ s.live t ∧ e ∉ s'.live t

theorem spend_not_blocked {s s' : PoolState} (hs : Reachable s) (hstep : Step s s')
    {tn : Nat} {root nk : Term} {token : Token}
    {entries : List ((Nat × Nat) × CommitmentPreimage)}
    (hTree : ∀ e ∈ entries, e.1.1 = tn)
    (hEnabled : SpendEnabled s tn root token entries (entries.map fun e => nullifier nk e.1.2))
    (hDisjoint : ∀ e ∈ entries, ¬ Spends s s' token e) :
    SpendEnabled s' tn root token entries (entries.map fun e => nullifier nk e.1.2)
```

`SpendEnabled` is exactly the three checks of `Step.transact`/`Step.transactOwned` that
read the state (`hRoot`, `hRemove`, `hNullify`). All other hypotheses read only the
transaction. The two corollaries state it with `transactSpentPositions` /
`ownedSpentPositions` and `List.ofFn pub.nullifiers`.

**Follows cheaply: yes.** A full proof of `spend_not_blocked` and of
`transact_not_blocked` type-checks in 149 lines, in the gitignored file
`.scratch/thm1.lean` of this worktree (checked with `lake env lean`). It needs three
small lemmas (`removeAll_some_of_mem`, `removed_not_live`,
`step_new_nullifier_spends`) and the existing `LiveSpentInvariant` (parts 1, 2 and 5).
The model keeps `sorry` per the policy above.

### Theorem 2 — spend binding (`spend_bound_to_adapt`)

```lean
theorem spend_bound_to_adapt {boundHash : Term} {bp₀ bp : BoundParams} {a caller : Term}
    (hProof : boundHash = hashBoundParams bp₀) (hA : bp₀.adaptContract = some a)
    (hStep : boundHash = hashBoundParams bp) (hAdapt : AdaptAllows bp caller) :
    caller = a ∧ bp = bp₀
```

`hStep` and `hAdapt` are the `hBound` and `hAdapt` hypotheses of `Step.transact` and
`Step.transactOwned`. So any step that executes a proof bound to `bp₀` has caller `a`
and the same `adaptParams` (the channel) and the same unshield.

**Follows cheaply: yes.** A 3-line proof (`hashBoundParams_inj`, then `hAdapt`)
type-checks in `.scratch/thm2.lean`.

Limit: the theorem is stated over the step's checks, not over a labelled step. `Step`
has no label that names its caller or its proof, so "the step that executes this proof"
is the constructor's hypotheses.

The adapt check is protocol meaning, not an Armada addition: the same ABDK audit (just
before CVF-7) quotes Railgun v1 `RailgunLogic.sol`: `if (_adaptIDcontract != address(0))
{ require(_adaptIDcontract == msg.sender, "AdaptID doesn't match caller contract"); }`.

### Theorem 3 — owned merge (`owned_merge_can_happen`)

```lean
theorem owned_merge_can_happen {s : PoolState} (hs : Reachable s) {N : Nat}
    (hN0 : 0 < N) (hN : N ≤ 8)
    (owner : Term) (token : Token) (bp : BoundParams)
    (hNoUnshield : bp.unshield = none) (hAdapt : AdaptAllows bp owner)
    (pos : Fin N → Nat) (pre : Fin N → CommitmentPreimage) (random : Fin N → Nat)
    (hLive : ∀ i, ((bp.treeNumber, pos i), pre i) ∈ s.live token)
    (hDistinct : (List.ofFn pos).Pairwise (· ≠ ·))
    (hOpen : ∀ i, npk owner (random i) = (pre i).npk)
    (npkOut : Term)
    (hSum : Spendable (listSum (List.ofFn fun i => (pre i).value))) :
    ∃ s', Step s s' ∧
      (∀ i, ((bp.treeNumber, pos i), pre i) ∉ s'.live token) ∧
      (∃ tn' pos' : Nat, ((tn', pos'),
        (⟨npkOut, token, listSum (List.ofFn fun i => (pre i).value)⟩ : CommitmentPreimage))
          ∈ s'.live token) ∧
      s'.held token = s.held token
```

**Follows cheaply: moderately, not proved.** [INFERENCE] Estimate 150 to 250 lines. The
proof builds the witness from `live_leaf_matches`, `live_note_unspent`,
`live_values_spendable`, `reachable_rootAt_matches_leavesAt` and
`reachable_leavesAt_capacity`, and reuses `removeAll_some_of_mem` and `removed_not_live`
from theorem 1. It needs one new invariant: every entry of `s.live t` has token `t`.
That invariant holds (each step inserts notes of the step's own token) but is not yet
stated.

Two findings from the type:
1. `hSum` is necessary. The merged value must pass the output range check (P-6).
2. The deployed owned circuits have one input only: `armada-circuits/src/main/` holds
   `main_1x1_owned`, `main_1x2_owned`, `main_1x3_owned` and no owned shape with `N > 1`.
   `Step.transactOwned` admits `N ≤ 8`, so the theorem holds in the model, but the
   deployment needs owned verifying keys with `N > 1` for the merge to exist on chain.

## Theorems whose type changed (for operator approval)

Type changed, proved (operator instruction 2026-10-27, old proofs port):
`fee_bounded`, `fee_conservation`, `fee_monotone`, `fee_zero_below_threshold` (P-9);
`shield_creates_exactly` (P-3, P-6, P-9, P-11); `shield_can_happen` (P-3, P-6, P-9).

`sorry` (type changed in hypotheses or conclusion):
`owned_spend_can_happen` (P-1, P-2, P-4); `transact_unshield_exact` (P-7);
`transactOwned_records_all` (P-4); `transact_can_happen` (P-1, P-2, P-7);
`unshield_can_happen` (P-1, P-2, P-7); `owned_transact_can_happen` (P-1, P-2, P-4);
`leaf_has_merkle_witness` (P-8); `owned_spend_witness_exists` (P-1, P-2, P-8, P-10);
`live_leaf_matches` (P-1, P-8); `live_values_spendable` (P-6, was
`live_values_lt_2pow120`).

`sorry` (new): `spend_not_blocked`, `transact_not_blocked`, `transactOwned_not_blocked`,
`spend_bound_to_adapt`, `owned_merge_can_happen`.

Proof repaired (type changed only by a moved definition): `commitment_owner_inj`,
`commitment_mpk_inj`, `spend_live_exact`, `live_note_unspent`,
`transact_spend_can_happen`, `transact_root_was_produced` (`genesisTrees`, P-9).

Restored with a changed type (P-8: `Option` lookup for `getD` with a default), proved
by operator ruling: `leaf_stable`, `step_leavesAt_stable` (see P-5).

Helpers with a new or changed type, proved: `tokenId_inj`, `hashBoundParams_inj`,
`optionTerm_inj`, `unshieldTerm_inj`, `treePath_correct`, `treePath_correct_of_getElem?`,
`value_ofFn_eq`, `value_ofFn_pos_eq`, `transact_balance`, `unshieldRefines_length_le`,
`unshieldRefines_mem`, `applyRecords_returns`, the `insertLeaves_*`/`insertTree_*`
lemmas, `step_live_leaf_matches`, `reachable_live_leaf_matches`,
`genesis_live_values_spendable`, `step_preserves_live_values_spendable`,
`genesis_invariant`, `genesis_live_spent_invariant`, `rootsAt_grounded` (all now take or
use the fee rate of `genesis r`), `step_feeRatio` (new).

## Removed theorems

| Theorem | Finding | Reason |
|---|---|---|
| `transact_cannot_be_blocked`, `transactOwned_cannot_be_blocked` | P-3 | covered only `Step.admin`; replaced by theorem 1 |
| `live_values_lt_2pow120` | P-6 | renamed `live_values_spendable`; the bound is `Spendable` |
| `pool_ownedRandomOf_consistent` | P-10 | no `ownedRandomOf` map; the pool does not check openings |
| `npk_preimage_not_zero` | P-4 | no zero sentinel |
| `fee_exact_50bps` | P-9 | no basis-point constant |

## Axioms

`grep -rn '^axiom' ArmadaLean` lists `EdDSAVerify`, `VerifyAccepts` and
`VerifyOwnedAccepts`. The last two existed before this change. They are uninterpreted
predicates for "the Groth16 verifier accepts", the same kind as `EdDSAVerify`. Only the
can-happen theorems and the completeness structures mention them; `Step` does not.
`emptyLeaf` is `opaque`, not an axiom.
