/-
  ArmadaLean.Pool — the privacy pool contract's state and operations.

  Why this model exists (see `.scratch/rewrite-B/POOL-model.md` in armada-laconic): the
  Armada pool holds other people's tokens. Its central promise is that value in the pool
  exists only as notes, and every token the pool holds backs exactly one unspent note.
  armada-lean already proves the cryptographic core (ArmadaLean.Transact,
  ArmadaLean.TransactOwned): one valid proof spends distinct notes and conserves value,
  and a contract-owned spend is bound to its owner. This module adds the bookkeeping the
  pool contract itself performs across many calls: which notes are live, which nullifiers
  are spent, which roots are valid, and which tokens the pool holds.

  The pool cannot see a note's value; it only ever reads a note's commitment (a Poseidon
  hash). `PoolState.live` is therefore GHOST state: the model's own knowledge of every
  live note's real preimage, which the contract itself never stores for an encrypted
  output. This is what lets the theorems in ArmadaLean.PoolSafety state the value
  invariant at all. `PoolState.preimageOf`, by contrast, mirrors the real public
  `PrivacyPoolStorage.preimageOf` mapping (PrivacyPoolStorage.sol:248): the pool writes an
  entry there only for a commitment it has itself hashed and matched to a proof.

  Scope: local `shield` (ShieldModule.sol:45-90), local `transact` including a local
  unshield (TransactModule.sol:43-96), and `transactOwned` (TransactModule.sol:488-519).
  Out of scope, per the brief: `processIncomingShield` and `atomicCrossChainUnshield`
  (CCTP-mediated token movement; CCTP is out of scope and these two entry points' only
  pool-relevant difference from the local paths is where the moved tokens come from or
  go, which this model does not represent) and the yield vault. The pool's own books do
  not otherwise depend on CCTP: nullifier marking, Merkle insertion and the preimage
  registry follow the same shape on every entry point, and the local paths exercise that
  shape in full.

  A spend's circuit-level facts (Merkle membership, nullifier derivation, value
  conservation) come from `ArmadaLean.Transact.Constrained` /
  `ArmadaLean.TransactOwned.OwnedConstrained`, exactly as ArmadaLean.PoolOwned already
  takes them. This model does not additionally reconstruct the incremental Merkle tree
  that `MerkleModule.insertLeaves` builds (MerkleModule.sol:54-121): `PoolState.roots`
  tracks only *which* field elements the pool has produced as a root (so a proof cannot
  name a root the pool never computed — `transact_root_was_produced` below), the same way
  ArmadaLean.Merkle's `merkleRoot_inj_leaf` binds one membership proof to one leaf without
  modelling the whole tree. ABDK's 2021-04-01 audit of Railgun's `Commitments.sol`
  (`.scratch/rewrite-B/sources/railgun-audit-2021-04-01-ABDK.pdf`, sha256
  `3b2129ab6440272f8dbe70f843a8a9e61068d644d1a860b61c36ce93339e380a`) spends findings
  CVF-33, CVF-34, CVF-41 and CVF-42 entirely on the gas-optimized incremental-insertion
  algorithm (the same `filledSubTrees`/rollover shape `MerkleModule.insertLeaves` uses);
  every one of those findings is about gas, not soundness, which is the same conclusion
  this model reaches by not re-deriving that algorithm.

  S-RG: RAILGUN Project Whitepaper, 2021-07-14.
  <https://resources.cryptocompare.com/asset-management/1823/1674569706520.pdf>,
  sha256 `84ab2207efbbf689503652c42b4861bca5562549961f69fe648feb6dedb83aa8`. Section
  "RAILGUN Core System & Protocol" splits the checks between the circuit and the
  contract; this model cites only the contract's share, at the definitions below. S-RG is
  a 2021 pre-launch design: Armada's contracts, not S-RG, are the source wherever they
  differ. S-RG's ADD/SPLIT/REMOVE names are not used here (Armada's contracts say
  `shield`/`transact`/`transactOwned`); S-RG's 25-basis-point deposit AND withdrawal fees
  do not match Armada, which charges a shield-in fee only (`shieldFee`, Fee.lean,
  ShieldModule.sol:343-371) and no withdrawal fee (TransactModule.sol:32, "Unshields are
  always free").

  DEPARTURE (contract, confirmed by reading the source): the brief that commissioned this
  model expected a shield to create "one fee note for the fee", matching the design at
  `labbook/2026-10-18-treasury-governance-baal-safe-shielded.md` decision 15 ("ShieldModule
  creates the fee note to the Safe's npk"). The merged `ShieldModule.sol` does not do this.
  `_transferTokenIn`'s flat-fee branch (ShieldModule.sol:324-340) and fee-module branch
  (ShieldModule.sol:295-323) both pay the fee leg with
  `token.safeTransferFrom(msg.sender, treasury, ...)` — straight from the caller's wallet
  to `treasury`, never through the pool's own balance and never as a commitment. No fee
  note is created on the `shield` path; `Step.shield` below models this (one note, of the
  post-fee value, and no second note). Separately, `_recognizeFee`
  (PrivacyPoolStorage.sol:280-285) recognizes ANY output — shield, transact or
  transactOwned — whose `npk` equals the governance `feeRecipient`, which is the already-
  named departure (brief, "transact outputs counted as fees"): `TransactModule
  ._recordPreimages` (TransactModule.sol:587-604) calls `_recognizeFee` for every
  transact/transactOwned public output, not only a genuine shield-in fee, against
  labbook T9.

  DEPARTURE (contract, `testingMode`): `PrivacyPool.verify`/`verifyOwned`
  (PrivacyPool.sol:506-601) return `true` unconditionally when `testingMode` is on, with
  no witness at all. `Step.transact`/`Step.transactOwned` below always require a genuine
  `Constrained`/`OwnedConstrained` witness to transition, i.e. they model the pool exactly
  when `testingMode` is off (or, equivalently, whenever the submitted proof happens to be
  genuine regardless of the flag); the safety theorems in ArmadaLean.PoolSafety hold under
  that same restriction, stated at each theorem, not as a global axiom. This mirrors a
  historical Railgun defect: ABDK finding CVF-58 (Critical, Fixed) on `Snark.sol`: "The
  function always returns true. It should return (out[0] != 0)" — an unconditional-accept
  verifier bug, fixed before Railgun's launch. Armada's `testingMode`/`VERIFICATION_BYPASS`
  (PrivacyPool.sol:508-510, 547-549, 564-566, 596-598) is the same defect, kept
  intentionally for testing and never removed from the merged contract (the sibling
  labbook entry's R8 calls for its removal; it is still present).
-/
import ArmadaLean.PoolOwned
import ArmadaLean.Transact
import ArmadaLean.Fee

/-! ### Removing a sub-multiset of live notes

A spend names its inputs by commitment (the ghost `CommitmentPreimage` the model recorded
when each note was created), not by position: two live notes can carry the identical
preimage (e.g. two separate shields of the same amount to the same recipient), so "the
notes this spend removes" is a sub-*multiset* of `live`, not a sub-set. `removeAll` mirrors
`ArmadaLean.PoolOwned.markSpent`'s shape (fail the first time a requested element is
missing) at the multiset level, using `List.erase` to drop one matching occurrence at a
time. -/

/-- Remove one occurrence of each of `spent` from `pool`, in order, failing (`none`) the
    first time an element is not present. This is the ghost-state analogue of a spend: the
    pool contract itself performs no such removal (it only ever marks nullifiers, via
    `ArmadaLean.PoolOwned.markSpent`); this function removes the *notes* those nullifiers
    name from the model's own live-note bookkeeping. -/
def removeAll : List CommitmentPreimage → List CommitmentPreimage →
    Option (List CommitmentPreimage)
  | pool, [] => some pool
  | pool, n :: ns => if pool.elem n then removeAll (pool.erase n) ns else none

/-- A successful `removeAll` splits the pool's total value exactly into the removed
    notes' value and the remaining notes' value. The multiset identity underlying both
    `removeAll_sum` and `removeAll_perm`: removing `n` from `pool` is a reordering
    (`List.perm_cons_erase`) followed by dropping the head, so `listSum` (which only sees
    values, not positions) cannot tell the two apart. -/
theorem removeAll_sum {pool spent pool' : List CommitmentPreimage}
    (h : removeAll pool spent = some pool') :
    listSum (pool.map CommitmentPreimage.value) =
      listSum (spent.map CommitmentPreimage.value) +
        listSum (pool'.map CommitmentPreimage.value) := by
  induction spent generalizing pool with
  | nil =>
    unfold removeAll at h
    cases h
    simp [listSum]
  | cons n ns ih =>
    unfold removeAll at h
    by_cases hmem : pool.elem n
    · rw [if_pos hmem] at h
      have hmem' : n ∈ pool := List.elem_iff.mp hmem
      have hperm : pool.Perm (n :: pool.erase n) := List.perm_cons_erase hmem'
      have heq : listSum (pool.map CommitmentPreimage.value) =
          listSum ((n :: pool.erase n).map CommitmentPreimage.value) :=
        listSum_perm (List.Perm.map CommitmentPreimage.value hperm)
      have ihh := ih h
      simp only [List.map_cons, listSum] at heq ⊢
      omega
    · rw [if_neg hmem] at h
      exact absurd h (by simp)

/-- A successful `removeAll` is a reordering: `pool` is exactly the removed notes plus
    the remainder, as a multiset. This is "a spend removes exactly the notes it spends
    from the live set" at the list level. -/
theorem removeAll_perm {pool spent pool' : List CommitmentPreimage}
    (h : removeAll pool spent = some pool') : pool.Perm (spent ++ pool') := by
  induction spent generalizing pool with
  | nil =>
    unfold removeAll at h
    cases h
    exact List.Perm.refl _
  | cons n ns ih =>
    unfold removeAll at h
    by_cases hmem : pool.elem n
    · rw [if_pos hmem] at h
      have hmem' : n ∈ pool := List.elem_iff.mp hmem
      have step1 : pool.Perm (n :: pool.erase n) := List.perm_cons_erase hmem'
      have step2 : (n :: pool.erase n).Perm (n :: (ns ++ pool')) :=
        List.Perm.cons n (ih h)
      exact step1.trans step2
    · rw [if_neg hmem] at h
      exact absurd h (by simp)

/-! ### The on-chain preimage registry

`PrivacyPoolStorage.preimageOf` (PrivacyPoolStorage.sol:248) is written by three call
sites: `ShieldModule.shield`/`processIncomingShield` write one entry per shielded note,
unconditionally (ShieldModule.sol:71, :136); `TransactModule._recordPreimages`
(TransactModule.sol:590-604) writes one entry per non-zero `publicOutputs` entry, for
both `transact` (optional) and `transactOwned` (mandatory). `ArmadaLean.PoolOwned`
already proves the per-call consistency lemma (`recordStep_preserves_consistency`); this
section lifts it to an arbitrary batch of records so one lemma covers all three call
sites. -/

/-- Apply a batch of `(commitment, preimage)` records to a registry, in order — the
    pool-level generalization of `ArmadaLean.PoolOwned.recordPreimages` that does not
    assume the batch comes from one transaction's `Fin K` output indexing. -/
def applyRecords (reg : PreimageRegistry) : List (Nat × CommitmentPreimage) → PreimageRegistry
  | [] => reg
  | (c, p) :: rest => applyRecords (recordStep reg c p) rest

/-- `applyRecords` preserves registry consistency, given every record is valid (hashes to
    the commitment it is recorded under) — the same hypothesis
    `ArmadaLean.PoolOwned.preimageOf_consistent` takes per-transaction, here taken per
    batch. -/
theorem applyRecords_preserves_consistency {reg : PreimageRegistry}
    (hreg : RegistryConsistent reg) {records : List (Nat × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1) :
    RegistryConsistent (applyRecords reg records) := by
  induction records generalizing reg with
  | nil => exact hreg
  | cons cp rest ih =>
    obtain ⟨c, p⟩ := cp
    apply ih
    · exact recordStep_preserves_consistency hreg
        (hvalid (c, p) List.mem_cons_self)
    · intro cp' hcp'
      exact hvalid cp' (List.mem_cons_of_mem (c, p) hcp')

/-! ### Pool state -/

/-- The pool's state, at the level this model needs. `live t` is the model's ghost
    knowledge of every currently-unspent note of token `t` (S-RG, "How Does RAILGUN
    Work?": the output notes of a split "are added to the live pool"; Armada has no
    `dead` pool — a spent note stays in the Merkle tree forever, only its nullifier is
    marked, so `live` here is the model's own "not yet spent" bookkeeping, not a second
    on-chain list). `spent` is the nullifier set
    (`ArmadaLean.PoolOwned.NullifierSet`, one tree's slice, as that module already
    documents). `roots` is every Merkle root the pool itself has produced
    (`PrivacyPoolStorage.rootHistory`, PrivacyPoolStorage.sol:171, flattened across
    trees the same way `NullifierSet` is). `held t` is the pool's own custody of token
    `t` — not `IERC20.balanceOf`, which a caller can inflate with a raw, pool-unmediated
    `transfer` that credits no note (sibling labbook entry §3a, the surplus/R4 discussion);
    `held` is the ledger the three modeled operations maintain, which is exactly what the
    core invariant is about. `preimageOf` mirrors `PrivacyPoolStorage.preimageOf`. The
    three `Bool` fields mirror `IShieldPauseController.shieldsPaused` /
    `.emergencyPaused` / `.withdrawOnlyMode`, read by `ShieldModule
    ._requireShieldsNotPaused` and `TransactModule._requireNotEmergencyPaused` /
    `._requireNotWithdrawOnly`. -/
structure PoolState where
  live : Nat → List CommitmentPreimage
  spent : NullifierSet
  roots : List Nat
  held : Nat → Nat
  preimageOf : PreimageRegistry
  shieldsPaused : Bool
  emergencyPaused : Bool
  withdrawOnlyMode : Bool

/-- The state right after deployment (`PrivacyPool.initialize`, PrivacyPool.sol:81-127,
    which calls `MerkleModule.initializeMerkle`, MerkleModule.sol:26-38): no notes, no
    spent nullifiers, the one root of the empty tree, no custody, an empty registry,
    nothing paused. `emptyRoot` stands for whatever `initializeMerkle` computes from
    `ZERO_VALUE` (PrivacyPoolStorage.sol:150); this model does not recompute that hash
    (see the module comment on `roots`). -/
def genesis (emptyRoot : Nat) : PoolState :=
  { live := fun _ => [], spent := [], roots := [emptyRoot], held := fun _ => 0,
    preimageOf := fun _ => none, shieldsPaused := false, emergencyPaused := false,
    withdrawOnlyMode := false }

/-! ### Operations

Each constructor below takes, as explicit hypotheses, exactly the checks the named
contract function performs before it changes state — "an accepted proof means its
circuit constraints hold" is not reached for directly; the circuit-level facts
(`Constrained`/`OwnedConstrained`) are discharged by the caller who builds a `Step` value,
the same way `ArmadaLean.PoolOwned.owned_owner_binding` takes `OwnedConstrained` as a
hypothesis rather than a global fact. -/

/-- One valid transition of the pool. -/
inductive Step : PoolState → PoolState → Prop where
  /-- Local shield (`ShieldModule.shield`, ShieldModule.sol:45-90). One `ShieldRequest`
      creates exactly one note of the shielded amount minus the fee
      (`_transferTokenIn`/`_getFee`, ShieldModule.sol:277-371, reusing
      `ArmadaLean.Fee.shieldBase`); see the module comment for why no second, fee, note
      is created. `hNotPaused` is `_requireShieldsNotPaused`
      (ShieldModule.sol:393-397). `hValue` is `_validateCommitmentPreimage`'s `_note
      .value > 0` check (ShieldModule.sol:243-244) — the blocklist and field-range
      checks on the same line are elided (Pool module comment: they gate *which* shields
      succeed, not the value invariant). S-RG, "RAILGUN Core System & Protocol": "Then
      the smart contract transfers tokens from the user wallet to itself, if a deposit
      amount is specified ... The hashes of the output UTXOs are then added to the
      Merkle tree so they can be spent in the future." -/
  | shield {s : PoolState} (token npk grossAmount feeBP newRoot : Nat)
      (hNotPaused : s.shieldsPaused = false)
      (hValue : 0 < grossAmount) (hFeeBP : feeBP ≤ BASIS) :
      Step s
        (let note : CommitmentPreimage := ⟨npk, token, shieldBase feeBP grossAmount⟩
         { s with
             live := fun t => if t = token then note :: s.live t else s.live t,
             held := fun t => if t = token then s.held t + note.value else s.held t,
             roots := newRoot :: s.roots,
             preimageOf := recordStep s.preimageOf (hashCommitment note) note })
  /-- Local `TransactModule.transact` (TransactModule.sol:43-96), covering both a pure
      transfer and a transfer with a local unshield (`unshieldValue = 0` means no
      unshield — TransactModule.sol:301-303 rejects a zero-value unshield output, so the
      correspondence is exact). `hRoot` is `rootHistory[treeNumber][merkleRoot]`
      (`_validateCommonContext`, TransactModule.sol:538). `hRemove`/`hNullify` are the
      ghost-level and on-chain halves of "spend these inputs": `hRemove` is licensed by
      the proof's `Constrained.merkle`/root-history facts (soundness: a Merkle-membership
      proof against a historical root cannot name a note the pool never created — Pool
      module comment), `hNullify` is `_accumulateAndNullify`
      (TransactModule.sol:373-399). `hBalance` is `transact_value_conserved`
      (ArmadaLean.Transact), split so the unshield's payout is excluded from the new live
      notes. `hValid`/`records` is `_validatePublicOutputs`/`_recordPreimages`
      (TransactModule.sol:544-604). S-RG: "The contract checks to make sure: ... That it
      hasn't seen the nullifiers before, eliminating any double spends[;] The Merkle root
      is the current or a previous Merkle root, to prevent users from making up UTXOs."
      Zokyo's 2022-12-21 audit of `RailgunLogic.sol`
      (`.scratch/rewrite-B/sources/railgun-audit-2022-12-21-Zokyo.pdf`, sha256
      `b974caa94f7eee9f3f52e7996e4251ac1581523af161a5c83b7468cb06f3a9a9`), finding #1
      ("Transaction validation is out of the scope", Medium, Resolved): "the current
      implementation ... does not validate unshieldPreimage to contain a correct value
      [;] anyone could call a function providing its own address and get all tokens."
      Armada's `_validateTransaction` already carries this fix (TransactModule.sol
      :295-331, the unshield npk/value/token checks and the
      `_hashCommitment(unshieldPreimage) == commitments[last]` check), which is what
      licenses taking "the unshield payout is this transaction's real notes' value" as a
      sound hypothesis here. The same audit, finding #2 ("Possible re-entrancy", Medium,
      Resolved), recommends marking a transaction processed before any token moves;
      `_accumulateAndNullify` already runs for every transaction in the batch
      (TransactModule.sol:63-73) before any unshield payout
      (TransactModule.sol:76-80) — `hNullify` is taken before `held` changes below for
      the same reason. -/
  | transact {s : PoolState} (token : Nat)
      (spentNotes newNotes rest : List CommitmentPreimage) (spent' : NullifierSet)
      (spentNullifiers : List Nat) (root newRoot unshieldValue : Nat)
      (records : List (Nat × CommitmentPreimage))
      (hEmergency : s.emergencyPaused = false)
      (hWithdrawOnly : unshieldValue = 0 → s.withdrawOnlyMode = false)
      (hRoot : root ∈ s.roots)
      (hRemove : removeAll (s.live token) spentNotes = some rest)
      (hNullify : markSpent s.spent spentNullifiers = some spent')
      (hBalance : listSum (spentNotes.map CommitmentPreimage.value) =
          listSum (newNotes.map CommitmentPreimage.value) + unshieldValue)
      (hValid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1) :
      Step s
        { s with
            live := fun t => if t = token then newNotes ++ rest else s.live t,
            spent := spent',
            held := fun t => if t = token then s.held t - unshieldValue else s.held t,
            roots := newRoot :: s.roots,
            preimageOf := applyRecords s.preimageOf records }
  /-- `TransactModule.transactOwned` (TransactModule.sol:488-519): the same bookkeeping
      shape as `transact`, with no unshield (`_validateOwnedTransaction` rejects any
      `unshield != NONE`, TransactModule.sol:619-623) and every output's preimage
      mandatory (`_validatePublicOutputs(requireAll = true)`, TransactModule.sol:630-634
      — `records` therefore has one entry per new note here, unlike `transact` where it
      is optional). `hWithdrawOnly` is unconditional, not an implication like `transact`'s:
      `_requireNotWithdrawOnly` demands `unshield != NONE` for every transaction in
      withdraw-only mode, which an owned transaction (unshield always `NONE`) can never
      satisfy, so a `transactOwned` call always reverts while withdraw-only mode is on. -/
  | transactOwned {s : PoolState} (token : Nat)
      (spentNotes newNotes rest : List CommitmentPreimage) (spent' : NullifierSet)
      (spentNullifiers : List Nat) (root newRoot : Nat)
      (records : List (Nat × CommitmentPreimage))
      (hEmergency : s.emergencyPaused = false)
      (hWithdrawOnly : s.withdrawOnlyMode = false)
      (hRoot : root ∈ s.roots)
      (hRemove : removeAll (s.live token) spentNotes = some rest)
      (hNullify : markSpent s.spent spentNullifiers = some spent')
      (hBalance : listSum (spentNotes.map CommitmentPreimage.value) =
          listSum (newNotes.map CommitmentPreimage.value))
      (hValid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1) :
      Step s
        { s with
            live := fun t => if t = token then newNotes ++ rest else s.live t,
            spent := spent',
            roots := newRoot :: s.roots,
            preimageOf := applyRecords s.preimageOf records }
  /-- The administrative paths that change neither notes, nullifiers, roots nor custody:
      `setShieldPauseContract`'s three flags, read through `IShieldPauseController
      .shieldsPaused`/`.emergencyPaused`/`.withdrawOnlyMode`. Owner functions that change
      only configuration unrelated to these three flags (`setShieldFee`,
      `setFeeRecipient`, `addToBlocklist`, `setVerificationKey`,
      `setVerificationKeyOwned`, `setTestingMode`, ...) are not modeled individually: none
      of them touches `live`, `spent`, `roots`, `held` or `preimageOf`, so every one of
      them is this same no-op on the fields the safety theorems are about. -/
  | admin {s : PoolState} (shieldsPaused emergencyPaused withdrawOnlyMode : Bool) :
      Step s
        { s with shieldsPaused := shieldsPaused, emergencyPaused := emergencyPaused,
                 withdrawOnlyMode := withdrawOnlyMode }

/-- Every state the pool can reach from deployment, by any sequence of calls from any
    caller — the quantifier the brief's four promises range over. -/
inductive Reachable (emptyRoot : Nat) : PoolState → Prop where
  | genesis : Reachable emptyRoot (genesis emptyRoot)
  | step {s s' : PoolState} (hs : Reachable emptyRoot s) (hstep : Step s s') :
      Reachable emptyRoot s'
