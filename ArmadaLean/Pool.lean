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
  hash, modeled symbolically — `ArmadaLean.Poseidon.Term`). `PoolState.live` is therefore
  GHOST state: the model's own knowledge of every live note's real preimage, which the
  contract itself never stores for an encrypted output. This is what lets the theorems in
  ArmadaLean.PoolSafety state the value invariant at all. `PoolState.preimageOf`, by
  contrast, mirrors the real public `PrivacyPoolStorage.preimageOf` mapping
  (PrivacyPoolStorage.sol:248): the pool writes an entry there only for a commitment it
  has itself hashed and matched to a proof.

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
  takes them. `PoolState.leaves` is the pool's actual Merkle tree, as the contract builds
  it: the ordered list of every commitment `MerkleModule.insertLeaves`
  (MerkleModule.sol:54-121) has ever inserted, public exactly as the real leaves are
  (`Shield`/`Transact`/`TransactOwned` events carry every commitment hash). Every root a
  `Step` pushes onto `roots` is `ArmadaLean.Merkle.treeRoot TreeDepth leaves`, computed
  from this list, not chosen — so a step cannot name a root that does not match what it
  actually inserted, and `ArmadaLean.PoolSafety.leaf_has_merkle_witness` proves every
  inserted leaf has a real Merkle path to a root the pool produced. ABDK's 2021-04-01
  audit of Railgun's `Commitments.sol`
  (`.scratch/rewrite-B/sources/railgun-audit-2021-04-01-ABDK.pdf`, sha256
  `3b2129ab6440272f8dbe70f843a8a9e61068d644d1a860b61c36ce93339e380a`) spends findings
  CVF-33, CVF-34, CVF-41 and CVF-42 entirely on the gas-optimized incremental-insertion
  algorithm (the same `filledSubTrees`/rollover shape `MerkleModule.insertLeaves` uses);
  every one of those findings is about gas, not soundness — `ArmadaLean.Merkle.treeRoot`
  computes the same final value that algorithm does, non-incrementally (see
  `ArmadaLean.Merkle`'s module comment for the one-tree-only departure this requires).

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

  DEPARTURE (contract → design, owner-controlled freeze removed): the merged contract
  lets the owner block every spend and unshield at any time. `PrivacyPool
  .setShieldPauseContract` (PrivacyPool.sol:466-470) is owner-gated with no restriction
  on when or to what address it is called, and it installs an `IShieldPauseController`
  whose `emergencyPaused()` or `withdrawOnlyMode()` `TransactModule` reads before every
  `transact` and `transactOwned` (`_requireNotEmergencyPaused`/`_requireNotWithdrawOnly`,
  TransactModule.sol:460-475, called at :48, :52, :491-492): an emergency pause blocks
  every spend outright, and withdraw-only mode blocks a pure transfer (a `transact` with
  no unshield output) and blocks every owned transaction unconditionally (the owned
  path's `unshield` is always `NONE`, so it can never satisfy
  `_requireNotWithdrawOnly`'s `unshield != NONE` escape). The Armada design removes this
  owner power entirely: `Step.transact` and `Step.transactOwned` below carry no pause
  check of any kind, so no step any caller — the owner included — can take ever blocks
  an otherwise-valid spend
  (`ArmadaLean.PoolSafety.transact_cannot_be_blocked`/`.transactOwned_cannot_be_blocked`).
  `PoolState` below therefore drops `emergencyPaused` and `withdrawOnlyMode`; only
  `shieldsPaused` remains, and it gates `Step.shield` alone — a shield pause, if the
  design keeps one, blocks only new value entering the pool, never an existing note's
  owner from spending or exiting it.
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
def applyRecords (reg : PreimageRegistry) : List (Term × CommitmentPreimage) → PreimageRegistry
  | [] => reg
  | (c, p) :: rest => applyRecords (recordStep reg c p) rest

/-- `applyRecords` preserves registry consistency, given every record is valid (hashes to
    the commitment it is recorded under) — the same hypothesis
    `ArmadaLean.PoolOwned.preimageOf_consistent` takes per-transaction, here taken per
    batch. -/
theorem applyRecords_preserves_consistency {reg : PreimageRegistry}
    (hreg : RegistryConsistent reg) {records : List (Term × CommitmentPreimage)}
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

/-- `applyRecords` distributes over `++`: folding two batches in sequence is the same
    as folding their concatenation. -/
theorem applyRecords_append (reg : PreimageRegistry) (l1 l2 : List (Term × CommitmentPreimage)) :
    applyRecords reg (l1 ++ l2) = applyRecords (applyRecords reg l1) l2 := by
  induction l1 generalizing reg with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.cons_append]
    obtain ⟨c, p⟩ := hd
    show applyRecords (recordStep reg c p) (tl ++ l2) = _
    rw [ih (recordStep reg c p)]
    rfl

/-- `hashCommitment` is injective: two preimages with the same commitment are the same
    preimage. Collision resistance of `Term.hash3` (by construction,
    `ArmadaLean.Poseidon`), the same fact `ArmadaLean.TransactOwned.commitment_owner_inj`
    and `ArmadaLean.Transact.commitment_mpk_inj` already rest on, applied to the
    preimage's own `(npk, token, value)` triple. -/
theorem hashCommitment_inj {p1 p2 : CommitmentPreimage} (h : hashCommitment p1 = hashCommitment p2) :
    p1 = p2 := by
  obtain ⟨h1, h2, h3⟩ := Term.hash3_inj h
  cases p1; cases p2
  simp_all [Term.val.injEq]

/-- Once `reg` already answers key `c` with `p`, folding a batch through it cannot
    change that answer, provided every later record touching key `c` agrees with `p` —
    the invariant `applyRecords_returns` below bootstraps and carries through a whole
    batch. -/
theorem applyRecords_preserves_key {reg : PreimageRegistry} {records : List (Term × CommitmentPreimage)}
    {c : Term} {p : CommitmentPreimage} (hreg : reg c = some p)
    (hagree : ∀ cp ∈ records, cp.1 = c → cp.2 = p) :
    applyRecords reg records c = some p := by
  induction records generalizing reg with
  | nil => exact hreg
  | cons hd tl ih =>
    obtain ⟨c', p'⟩ := hd
    unfold applyRecords
    refine ih ?_ (fun cp hcp => hagree cp (List.mem_cons_of_mem _ hcp))
    show recordStep reg c' p' c = some p
    unfold recordStep
    by_cases hz : isZeroPreimage p'
    · rw [if_pos hz]; exact hreg
    · rw [if_neg hz]
      by_cases hcc : c = c'
      · rw [if_pos hcc]
        have := hagree (c', p') List.mem_cons_self hcc.symm
        simp only [] at this
        rw [this]
      · rw [if_neg hcc]; exact hreg

/-- **A valid, non-zero batch is recoverable from the registry it produces.** If every
    record in a batch hashes to its own key and is never the zero preimage (so
    `recordStep` never skips it — `_validatePublicOutputs`'s non-zero requirement), then
    for any record `(c, p)` in the batch, `applyRecords` settles on `p` at key `c`,
    whatever else is in the batch: a later record sharing key `c` must, by
    `hashCommitment_inj`, carry the identical preimage `p`, so even an overwrite leaves
    the answer unchanged. The key lemma behind `transactOwned_records_all`. -/
theorem applyRecords_returns {reg : PreimageRegistry} {records : List (Term × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    (hNonZero : ∀ cp ∈ records, ¬ isZeroPreimage cp.2)
    {c : Term} {p : CommitmentPreimage} (hmem : (c, p) ∈ records) :
    applyRecords reg records c = some p := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  rw [hsplit, applyRecords_append]
  unfold applyRecords
  apply applyRecords_preserves_key
  · unfold recordStep
    rw [if_neg (hNonZero (c, p) (hsplit ▸ List.mem_append_right pre List.mem_cons_self))]
    simp
  · intro cp hcp hcpeq
    have hcpmem : cp ∈ records := by
      rw [hsplit]
      exact List.mem_append_right pre (List.mem_cons_of_mem _ hcp)
    have hcpval := hvalid cp hcpmem
    have hpval := hvalid (c, p) hmem
    rw [hcpeq] at hcpval
    exact hashCommitment_inj (hcpval.trans hpval.symm)

/-- The `(commitment, preimage)` pair a plain `Transact` output would record, if
    disclosed — the full candidate batch `Step.transact`'s `records` is a sublist of. -/
def transactOutputRecords {N M : Nat} (w : TransactWitness N M)
    (pub : TransactPublic N M) : List (Term × CommitmentPreimage) :=
  List.ofFn fun j => (pub.commitmentsOut j, (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))

/-- Every candidate record a plain `Transact` could disclose is valid: its commitment
    key is exactly its own `hashCommitment` (`Constrained.outputs`). -/
theorem transactOutputRecords_valid {N M : Nat} {w : TransactWitness N M} {pub : TransactPublic N M}
    (hC : Constrained w pub) :
    ∀ cp ∈ transactOutputRecords w pub, hashCommitment cp.2 = cp.1 := by
  intro cp hcp
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
  rw [← hj]
  exact (hC.outputs j).symm

/-- The `(commitment, preimage)` pair an owned `TransactOwned` output records —
    `transactOwned` discloses every one (`_validatePublicOutputs(requireAll = true)`,
    TransactModule.sol:630-634), so this is `Step.transactOwned`'s whole batch, not a
    candidate list a caller trims. -/
def ownedOutputRecords {N M : Nat} (w : TransactOwnedWitness N M)
    (pub : TransactOwnedPublic N M) : List (Term × CommitmentPreimage) :=
  List.ofFn fun j => (pub.commitmentsOut j, (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))

/-- Every owned output's record is valid: its commitment key is exactly its own
    `hashCommitment` (`OwnedConstrained.outputs`). -/
theorem ownedOutputRecords_valid {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (hC : OwnedConstrained w pub) :
    ∀ cp ∈ ownedOutputRecords w pub, hashCommitment cp.2 = cp.1 := by
  intro cp hcp
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
  rw [← hj]
  exact (hC.outputs j).symm

/-! ### Pool state -/

/-- The pool's state, at the level this model needs. `live t` is the model's ghost
    knowledge of every currently-unspent note of token `t` (S-RG, "How Does RAILGUN
    Work?": the output notes of a split "are added to the live pool"; Armada has no
    `dead` pool — a spent note stays in the Merkle tree forever, only its nullifier is
    marked, so `live` here is the model's own "not yet spent" bookkeeping, not a second
    on-chain list). `spent` is the nullifier set
    (`ArmadaLean.PoolOwned.NullifierSet`, one tree's slice, as that module already
    documents). `leaves` is the pool's real Merkle tree: every commitment
    `MerkleModule.insertLeaves` has ever inserted, in insertion order — public data
    (module comment). `roots` is every Merkle root the pool itself has produced
    (`PrivacyPoolStorage.rootHistory`, PrivacyPoolStorage.sol:171, flattened across
    trees the same way `NullifierSet` is) — always `ArmadaLean.Merkle.treeRoot
    TreeDepth leaves` at the point it was pushed, never a free choice. `held t` is the
    pool's own custody of token `t` — not `IERC20.balanceOf`, which a caller can
    inflate with a raw, pool-unmediated `transfer` that credits no note (sibling
    labbook entry §3a, the surplus/R4 discussion); `held` is the ledger the three
    modeled operations maintain, which is exactly what the core invariant is about.
    `preimageOf` mirrors `PrivacyPoolStorage.preimageOf`. `shieldsPaused` mirrors
    `IShieldPauseController.shieldsPaused`, read by `ShieldModule
    ._requireShieldsNotPaused` — the one freeze the Armada design keeps, and it gates
    `Step.shield` alone (module comment, freeze-removal departure). -/
structure PoolState where
  live : Nat → List CommitmentPreimage
  spent : NullifierSet
  leaves : List Term
  roots : List Term
  held : Nat → Nat
  preimageOf : PreimageRegistry
  shieldsPaused : Bool

/-- The state right after deployment (`PrivacyPool.initialize`, PrivacyPool.sol:81-127,
    which calls `MerkleModule.initializeMerkle`, MerkleModule.sol:26-38): no leaves, no
    spent nullifiers, the one root of the empty tree (`ArmadaLean.Merkle.treeRoot
    TreeDepth []`, computed — not a free parameter standing for the real pinned
    `ZERO_VALUE`-derived constant, PrivacyPoolStorage.sol:150; see the module comment on
    `Term.val 0` as this model's stand-in zero value), no custody, an empty registry,
    not paused. -/
def genesis : PoolState :=
  { live := fun _ => [], spent := [], leaves := [], roots := [treeRoot TreeDepth []],
    held := fun _ => 0, preimageOf := fun _ => none, shieldsPaused := false }

/-! ### Deriving notes from a witness

A spend's input and output notes are never free choices: they are read off the witness
a `Constrained`/`OwnedConstrained` proof already pins down. These four definitions are
the single place that reads them off, reused by every `Step` constructor and every
`can_happen` theorem below, so "which notes did this spend touch" has exactly one
answer, derived, not asserted. -/

/-- The commitment preimages of a plain `TransactWitness`'s `N` inputs: input `i` opens
    the commitment at `npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i)`
    (Transact.circom:74-84). -/
def transactSpentNotes {N M : Nat} (w : TransactWitness N M) :
    List CommitmentPreimage :=
  List.ofFn fun i =>
    (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token,
      w.valueIn i⟩ : CommitmentPreimage)

/-- The commitment preimages of a plain `TransactWitness`'s `M` outputs, in witness
    order (Transact.circom:105-113). The circuit does not distinguish a kept note from
    an unshield payout; `Step.transact` below splits this list into the two. -/
def transactAllOutputs {N M : Nat} (w : TransactWitness N M) : List CommitmentPreimage :=
  List.ofFn fun j => (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)

/-- The commitment preimages of an owned `TransactOwnedWitness`'s `N` inputs: input `i`
    opens the commitment at `npk (Term.val pub.ownerField) (w.randomIn i)`
    (TransactOwned.circom:66-76). -/
def ownedSpentNotes {N M : Nat} (pub : TransactOwnedPublic N M)
    (w : TransactOwnedWitness N M) :
    List CommitmentPreimage :=
  List.ofFn fun i =>
    (⟨npk (Term.val pub.ownerField) (w.randomIn i), w.token, w.valueIn i⟩ : CommitmentPreimage)

/-- The commitment preimages of an owned `TransactOwnedWitness`'s `M` outputs. All of
    them stay live: `transactOwned` never unshields
    (`_validateOwnedTransaction`, TransactModule.sol:619-623). -/
def ownedNewNotes {N M : Nat} (w : TransactOwnedWitness N M) : List CommitmentPreimage :=
  List.ofFn fun j => (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)

/-! ### Operations

Each constructor below takes, as explicit hypotheses, exactly the checks the named
contract function performs before it changes state — "an accepted proof means its
circuit constraints hold" is not reached for directly; the circuit-level facts
(`Constrained`/`OwnedConstrained`) are discharged by the caller who builds a `Step` value,
the same way `ArmadaLean.PoolOwned.owned_owner_binding` takes `OwnedConstrained` as a
hypothesis rather than a global fact. -/

/-- One valid transition of the pool. -/
inductive Step : PoolState → PoolState → Prop where
  /-- Local `ShieldModule.shield` (ShieldModule.sol:45-90).
      One `ShieldRequest` creates exactly one note of the shielded amount minus the fee
      (`_transferTokenIn`/`_getFee`, ShieldModule.sol:277-371, reusing
      `ArmadaLean.Fee.shieldBase`); see the module comment for why no second, fee, note
      is created. `npk` is the shielded note's public key, a term the caller supplies
      directly (the shield circuit does not derive it — the recipient computes their own
      `npk` off-chain and the shielder just names it, same role as `npkOut` in a
      `transact`). The note's commitment is appended to `leaves`
      (`MerkleModule.insertLeaves`, MerkleModule.sol:54-121) and the pushed root is
      `ArmadaLean.Merkle.treeRoot TreeDepth` of the result — computed, not a free
      parameter — so a shield cannot name a root that does not match the leaf it just
      inserted. `hCapacity` is the one-tree capacity bound (`ArmadaLean.Merkle`'s
      module comment, the rollover departure): the tree holds at most `2 ^ TreeDepth`
      leaves. `hNotPaused` is `_requireShieldsNotPaused` (ShieldModule.sol:393-397).
      `hValue` is `_validateCommitmentPreimage`'s `_note.value > 0` check
      (ShieldModule.sol:243-244) — the blocklist and field-range checks on the same line
      are elided (Pool module comment: they gate *which* shields succeed, not the value
      invariant). S-RG, "RAILGUN Core System & Protocol": "Then the smart contract
      transfers tokens from the user wallet to itself, if a deposit amount is specified
      ... The hashes of the output UTXOs are then added to the Merkle tree so they can
      be spent in the future." -/
  | shield {s : PoolState} (token grossAmount feeBP : Nat) (npk : Term)
      (hNotPaused : s.shieldsPaused = false)
      (hValue : 0 < grossAmount) (hFeeBP : feeBP ≤ BASIS)
      (hCapacity : s.leaves.length + 1 ≤ 2 ^ TreeDepth) :
      Step s
        (let note : CommitmentPreimage := ⟨npk, token, shieldBase feeBP grossAmount⟩
         let leaves' := s.leaves ++ [hashCommitment note]
         { s with
             live := fun t => if t = token then note :: s.live t else s.live t,
             held := fun t => if t = token then s.held t + note.value else s.held t,
             leaves := leaves',
             roots := treeRoot TreeDepth leaves' :: s.roots,
             preimageOf := recordStep s.preimageOf (hashCommitment note) note })
  /-- Local `TransactModule.transact` (TransactModule.sol:43-96), covering both a pure
      transfer and a transfer with a local unshield. `w`/`pub` are the proof's own
      witness and public inputs; `hC : Constrained w pub` is the soundness hypothesis
      ("an accepted proof means its circuit constraints hold") — this is what ties
      `transactSpentNotes w` to notes the spender actually derived from keys it holds,
      not a free choice (see `ArmadaLean.PoolSafety.transact_spends_only_owned`).
      `hN`/`hM` are the registered circuit shapes: `VerifierModule.setVerificationKey`
      (VerifierModule.sol:32-47) registers one key per `(nullifierCount,
      commitmentCount)` pair, and an unregistered shape reverts
      (`verifyingKey.alpha1.x != 0` check, PrivacyPool.sol:519); the 19 registered plain
      shapes (`armada-circuits/src/main/main_{1x1,1x2,1x3,2x1,2x2,2x3,3x1,3x2,3x3,4x1,
      4x2,4x3,5x1,5x2,6x1,6x2,7x1,8x1,8x4}.circom`) all satisfy `N ≤ 8 ∧ M ≤ 4`, the
      exact bound `transact_value_conserved` needs. `hRoot` is
      `rootHistory[treeNumber][merkleRoot]` (`_validateCommonContext`,
      TransactModule.sol:538). `hSplit`/`hUnshieldLen` separate the circuit's uniform `M`
      outputs (`transactAllOutputs`) into the notes that stay live and, at most, one
      unshield payout — the circuit itself draws no such line
      (TransactOwned.circom/Transact.circom treat every output alike); the pool does, via
      `boundParams.unshield`/`commitmentCiphertext.length` (TransactModule.sol:289-337).
      `hRemove` is the ghost-level half of "spend these inputs", licensed by the proof's
      `Constrained.merkle`/root-history facts (soundness: a Merkle-membership proof
      against a historical root cannot name a note the pool never created — Pool module
      comment); `hNullify` is its on-chain half, `_accumulateAndNullify`
      (TransactModule.sol:373-399). `hRecords` is `_validatePublicOutputs
      (requireAll = false)`/`_recordPreimages` (TransactModule.sol:544-604): disclosure
      is optional, so `records` is any sublist of the outputs' own `(commitment,
      preimage)` pairs (`transactOutputRecords`), in witness order — never an unrelated
      list, since `List.Sublist` forces every disclosed entry to be one of the circuit's
      own outputs (`transactOutputRecords_valid` then gives `hashCommitment`
      correctness for free, not as a separate hypothesis). The balance fact itself is
      not a hypothesis here: `ArmadaLean.PoolSafety.step_preserves_invariant` derives
      it from `transact_value_conserved hN hM hC` at the point it is needed, exactly
      as the contract's own guarantee rests on the circuit constraints and nothing
      else. S-RG: "The contract checks to make sure: ... That it hasn't seen the
      nullifiers before, eliminating any double spends[;] The Merkle root is the
      current or a previous Merkle root, to prevent users from making up UTXOs."
      Zokyo's 2022-12-21 audit of `RailgunLogic.sol`
      (`.scratch/rewrite-B/sources/railgun-audit-2022-12-21-Zokyo.pdf`, sha256
      `b974caa94f7eee9f3f52e7996e4251ac1581523af161a5c83b7468cb06f3a9a9`), finding #1
      ("Transaction validation is out of the scope", Medium, Resolved): "the current
      implementation ... does not validate unshieldPreimage to contain a correct value
      [;] anyone could call a function providing its own address and get all tokens."
      Armada's `_validateTransaction` already carries this fix (TransactModule.sol
      :295-331, the unshield npk/value/token checks and the
      `_hashCommitment(unshieldPreimage) == commitments[last]` check), which is what
      licenses `hSplit` reading the unshield payout off the circuit's own output. The
      same audit, finding #2 ("Possible re-entrancy", Medium, Resolved), recommends
      marking a transaction processed before any token moves; `_accumulateAndNullify`
      already runs for every transaction in the batch (TransactModule.sol:63-73) before
      any unshield payout (TransactModule.sol:76-80) — `hNullify` is taken before `held`
      changes below for the same reason. `newNotes` alone are appended to `leaves`
      (`_accumulateAndNullify`'s "excluding unshield output" loop,
      TransactModule.sol:391-396) and the pushed root is `ArmadaLean.Merkle.treeRoot
      TreeDepth` of the result — computed, not a free parameter.
      `hCapacity` is the one-tree capacity bound (`ArmadaLean.Merkle`'s module comment,
      the rollover departure).

      DEPARTURE (contract, owner-controlled freeze removed): the merged contract checks
      `_requireNotEmergencyPaused`/`_requireNotWithdrawOnly` before every `transact`
      (called at TransactModule.sol:48, :52; the checks themselves at :460-475), which
      can revert the whole call whenever the owner has installed a controller
      (`PrivacyPool.setShieldPauseContract`, owner-gated, no restriction on when,
      PrivacyPool.sol:466-470) whose `emergencyPaused()` or `withdrawOnlyMode()` returns
      true. This constructor carries no such check: the Armada design removes the
      owner's power to block a spend. `hRoot`, `hRemove` and `hNullify` are the only
      preconditions that gate a `transact`, and none of them reads `s.shieldsPaused` —
      `ArmadaLean.PoolSafety.transact_cannot_be_blocked` proves no step any caller can
      take, the owner included, changes whether they hold. -/
  | transact {s : PoolState} {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M)
      (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
      (newNotes unshieldTail rest : List CommitmentPreimage) (spent' : NullifierSet)
      (records : List (Term × CommitmentPreimage))
      (hRoot : pub.merkleRoot ∈ s.roots)
      (hSplit : transactAllOutputs w = newNotes ++ unshieldTail)
      (hUnshieldLen : unshieldTail.length ≤ 1)
      (hRemove : removeAll (s.live w.token) (transactSpentNotes w) = some rest)
      (hNullify : markSpent s.spent (List.ofFn pub.nullifiers) = some spent')
      (hRecords : records.Sublist (transactOutputRecords w pub))
      (hCapacity : s.leaves.length + newNotes.length ≤ 2 ^ TreeDepth) :
      Step s
        (let leaves' := s.leaves ++ newNotes.map hashCommitment
         { s with
            live := fun t => if t = w.token then newNotes ++ rest else s.live t,
            spent := spent',
            held := fun t => if t = w.token
                then s.held t - listSum (unshieldTail.map CommitmentPreimage.value)
                else s.held t,
            leaves := leaves',
            roots := treeRoot TreeDepth leaves' :: s.roots,
            preimageOf := applyRecords s.preimageOf records })
  /-- `TransactModule.transactOwned` (TransactModule.sol:488-519): the same bookkeeping
      shape as `transact`, with no unshield (`_validateOwnedTransaction` rejects any
      `unshield != NONE`, TransactModule.sol:619-623) and every output's preimage
      mandatory (`_validatePublicOutputs(requireAll = true)`, TransactModule.sol:630-634):
      every owned output is disclosed, so the registry update is fixed to
      `ownedOutputRecords w pub` — the circuit's whole output batch, not a candidate
      list a caller trims (unlike `transact`, where disclosure is optional). `hNonZero`
      is `_validatePublicOutputs(requireAll = true)`'s own check that no owned output
      may be the zero preimage (TransactModule.sol:567-571, "Missing public output").
      `hC : OwnedConstrained w pub` is the soundness hypothesis; `caller`/`hCaller` is
      the authorization check (`msg.sender == address(uint160(uint256(ownerField)))`,
      TransactModule.sol:636-639) — together these are exactly what
      `ArmadaLean.PoolSafety.transactOwned_spends_only_owned`
      (`ArmadaLean.PoolOwned.owned_owner_binding`) needs. `hN`/`hM`: the registered owned
      shapes (`armada-circuits/src/main/main_{1x1,1x2,1x3}_owned.circom`) all have
      `N = 1 ≤ 8` and `M ≤ 3 ≤ 4`, well inside the bound
      `transactOwned_value_conserved` needs; this model uses the same `N ≤ 8 ∧ M ≤ 4`
      bound as the plain path rather than the tighter true one, since that is the bound
      the existing proof already supplies. Every output is appended to `leaves`
      (`MerkleModule.insertLeaves`, MerkleModule.sol:54-121) and the pushed root is
      `ArmadaLean.Merkle.treeRoot TreeDepth` of the result — computed, not a free
      parameter. `hCapacity` is the one-tree capacity bound (`ArmadaLean.Merkle`'s
      module comment, the rollover departure).

      DEPARTURE (contract, owner-controlled freeze removed): the merged contract checks
      `_requireNotEmergencyPaused`/`_requireNotWithdrawOnly` before `transactOwned` too
      (called at TransactModule.sol:491-492; the checks themselves at :460-475) —
      withdraw-only mode in particular always blocks an owned transaction outright,
      since the owned path's `unshield` is always `NONE` and `_requireNotWithdrawOnly`
      demands `unshield != NONE` for every transaction while withdraw-only mode is on.
      This constructor carries no such check: the Armada design removes the owner's
      power to block a spend, owned included. `hRoot`, `hRemove` and `hNullify` are the
      only preconditions that gate a `transactOwned`, and none of them reads
      `s.shieldsPaused` — `ArmadaLean.PoolSafety.transactOwned_cannot_be_blocked` proves
      no step any caller can take, the owner included, changes whether they hold. -/
  | transactOwned {s : PoolState} {N M : Nat} (w : TransactOwnedWitness N M)
      (pub : TransactOwnedPublic N M) (hN : N ≤ 8) (hM : M ≤ 4)
      (hC : OwnedConstrained w pub) (caller : Nat) (hCaller : caller = addressOf pub.ownerField)
      (rest : List CommitmentPreimage) (spent' : NullifierSet)
      (hRoot : pub.merkleRoot ∈ s.roots)
      (hRemove : removeAll (s.live w.token) (ownedSpentNotes pub w) = some rest)
      (hNullify : markSpent s.spent (List.ofFn pub.nullifiers) = some spent')
      (hNonZero : ∀ j, ¬ isZeroPreimage
        (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
      (hCapacity : s.leaves.length + M ≤ 2 ^ TreeDepth) :
      Step s
        (let leaves' := s.leaves ++ (ownedNewNotes w).map hashCommitment
         { s with
            live := fun t => if t = w.token then ownedNewNotes w ++ rest else s.live t,
            spent := spent',
            leaves := leaves',
            roots := treeRoot TreeDepth leaves' :: s.roots,
            preimageOf := applyRecords s.preimageOf (ownedOutputRecords w pub) })
  /-- The one remaining administrative path that changes pool state at all:
      `setShieldPauseContract` installs a controller whose `IShieldPauseController
      .shieldsPaused` this model reads (`ShieldModule._requireShieldsNotPaused`,
      ShieldModule.sol:393-397) — the Armada design keeps this one freeze, and only
      this one: it blocks `Step.shield` alone (module comment, freeze-removal
      departure). Every other owner function (`setShieldFee`, `setFeeRecipient`,
      `addToBlocklist`, `setVerificationKey`, `setVerificationKeyOwned`,
      `setTestingMode`, ...) changes configuration this model does not represent and is
      not modeled individually: none of them touches `live`, `spent`, `roots`, `held`
      or `preimageOf`, so every one of them is this same no-op on the fields the safety
      theorems are about. -/
  | admin {s : PoolState} (shieldsPaused : Bool) :
      Step s { s with shieldsPaused := shieldsPaused }

/-- Every state the pool can reach from deployment, by any sequence of calls from any
    caller — the quantifier the brief's four promises range over. `genesis` is now a
    concrete value (the empty-tree root is computed, not a free parameter — see
    `genesis`'s doc comment), so `Reachable` no longer needs to be indexed by it. -/
inductive Reachable : PoolState → Prop where
  | genesis : Reachable genesis
  | step {s s' : PoolState} (hs : Reachable s) (hstep : Step s s') :
      Reachable s'
