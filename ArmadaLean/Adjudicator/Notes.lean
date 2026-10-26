/-
  ArmadaLean.Adjudicator.Notes — the Armada layer: the adjudicator's money
  is pool notes, not a raw balance.

  The pool itself — its state, its `shield`/`transact`/`transactOwned` steps
  and their safety theorems (the core invariant, no double spend, preimage
  consistency, ownership binding, value conservation from a real,
  shape-bounded circuit witness) — lives in the root `ArmadaLean.Pool`/
  `ArmadaLean.PoolSafety` modules (branch `pool-model`, commit `d406cea`).
  The adjudicator is an ORDINARY caller of that pool: it defines no pool
  state, no live-note ledger and no preimage registry of its own.
  `AdjudicatorState` (`State.lean`) embeds `ArmadaLean.PoolState` directly.

  `pool-model`'s `d406cea` models the tree the contract rolls over to once
  full (`MerkleModule.insertLeaves`, MerkleModule.sol:62-70): a leaf position
  is now a `(treeNumber, position)` pair, `PoolState.live`/`.spent` are keyed
  by tree number (`ArmadaLean.Pool.PoolState.live`/`.spent`), and no `Step`
  constructor carries a capacity hypothesis any more (a full tree rolls over
  instead of refusing an insertion). `DepositStep` and `PoolOwnedSpendStep`
  below name the TWO call shapes the adjudicator uses, each an instance of
  `ArmadaLean.Pool`'s own `Step.transact`/`Step.transactOwned` SHAPE (same
  witness fields, same `N ≤ 8`/`M ≤ 4` registered-circuit bound, same
  `removeAll`/`markSpent`/`applyRecords`/`applyOwnedRecords` bookkeeping, via
  `ArmadaLean.transactSpentPositions`/`transactAllOutputs`/
  `ownedSpentPositions`/`ownedNewNotes`, now all `(treeNumber, position)`-
  keyed): the adjudicator derives no SEPARATE balance or removal rule of its
  own; it builds the exact pool state `Step.transact`/`Step.transactOwned`
  would produce for the SAME witness, so every pool-level fact about that
  constructor (`transact_balance`, `transactOwned_balance`,
  `transact_spends_only_owned`) applies unchanged. Neither `DepositStep` nor
  `PoolOwnedSpendStep`/`DepositMergeStep` carries a pause check any more:
  `pool-model`'s `30d7a65` removed the owner's power to block a spend —
  `Step.transact`/`Step.transactOwned` take no `emergencyPaused`/
  `withdrawOnlyMode` condition.

  A note is identified by its `(treeNumber, position)` Merkle leaf key, not
  by its content (`Pool.lean`'s module comment): the circuit derives a
  spend's nullifier from the leaf position a proof names, within the tree
  the proof's own `boundParams.treeNumber` fixes, never from a scan for a
  matching value, and two live notes can carry the identical preimage
  without ever sharing a key. `AdjudicatorState.holdings` (`State.lean`)
  follows the same rule: a channel's holding names exactly one note by its
  `(treeNumber, position)` key, with the commitment carried alongside as a
  check. `DepositStep` reports the key its own output landed at (the batch's
  own `(insertTreeNumber, insertStartPos)`, offset by the output's own index
  within the batch — `withTreePositionsFrom`'s own convention);
  `PoolOwnedSpendStep`'s "some" branch nullifies the key a holding already
  names, and reports the key its own merged/remainder output lands at, the
  same way.

  Commitments, note public keys (`npk`) and Merkle roots are `Term`s
  (`ArmadaLean.Poseidon`, the symbolic Dolev-Yao hash model); `self`/
  `token`/`amount` stay plain `Nat`s. The adjudicator's own note key,
  wherever this file mints one, is `npk (Term.val self) r` — `self` is a
  raw address, embedded `Term.val` before hashing, exactly the convention
  `ArmadaLean.TransactOwned`'s own `ownerField` uses (`TransactOwned.lean`'s
  `user_npk_ne_contract_npk`, which separates a user's hash-rooted `npk`
  from a contract's value-rooted one, rests on this).

  `DepositStep` DISCLOSES its own output as contract-owned, through the
  pool's `ownedRecords` (`Step.transact`'s approved-design optional extra,
  `Pool.lean`'s module comment on `OwnedDisclosure`): the random `r` its own
  `∃r, w.npkOut idx = npk (Term.val self) r` existential names is exactly
  what `ownedRecords` supplies, alongside `self` as the owner field — this
  is what later lets `ArmadaLean.owned_spend_witness_exists` reconstruct a
  spend witness for this note from public data alone
  (`ArmadaLean.PoolSafety.pool_ownedRandomOf_consistent`), with no secret
  carried by this theorem's own hypotheses. `PoolOwnedSpendStep`'s own
  `transactOwned` call discloses every note it MINTS AS CONTRACT-OWNED
  (`ownedPreimages`) this way UNCONDITIONALLY (the pool's own `requireAll
  = true` rule for the owned path): every note the adjudicator ever
  holds — fresh from a deposit, or minted by a merge or a transfer's own
  remainder — is contract-owned on the public record from the moment it
  is minted. A `.transfer` call's own PAYOUT outputs (`payoutPreimages`)
  are the opposite case: they are keyed to a recipient the adjudicator
  does not control, so no such disclosure exists, or could exist, for
  them (`ArmadaLean.TransactOwned.user_npk_ne_contract_npk`: a user's
  own note key is never of the `npk (Term.val ownerField) r` form a
  contract-owned disclosure names).

  Naming the witness explicitly — not hiding behind an opaque `Pool.Step`
  hypothesis — is what lets a deposit's OWN condition (the adjudicator-
  owned output) tie to a SPECIFIC `transact` call rather than admit any
  OTHER pool transition (a `shield`, say) that happened to also leave a
  matching commitment live: `Pool.Step` alone does not say WHICH
  constructor fired, and `notedValue_conserved` would be false if a
  `.deposit` could be satisfied by a value-creating `shield` instead.
  `DepositStep`'s witness obeys the registered-shape bound (`hN : N ≤ 8`,
  `hM : M ≤ 4`) the pool's own `transact_value_conserved`/`transact_
  balance` need.

  `PoolOwnedSpendStep`'s own adjudicator condition is that the witness's
  own outputs (`ArmadaLean.ownedNewNotes w`) ARE EXACTLY the payout notes
  and remainder note its rule computes (`payoutPreimages ++
  ownedPreimages`, built in `Operations.lean`'s `.transfer` case from
  `heldValue`/`transferEffects`) — not a separately-asserted list the
  pool is trusted to mint on the adjudicator's say-so. The circuit's own
  output-commitment check (`OwnedConstrained.outputs`) already ties
  `ownedNewNotes w` to `pub`'s public commitments, so this condition
  names no new trust, only which notes are meant. This is what lets
  `notedValue_conserved` go through from `ArmadaLean.transactOwned_
  balance` alone, with no separate assumption that `heldValue` correctly
  reports the nullified note's true value: if it ever disagreed, no
  witness could satisfy BOTH `ownedNewNotes w = payoutPreimages ++
  ownedPreimages` (whose total is `heldValue`, by `Operations.lean`'s own
  `remainder`/`totalPayouts` construction) AND the circuit's balance
  (whose total is the spent note's TRUE Merkle-tree value) — the step
  would simply not exist, which is the safe outcome, not a fact this
  file needs to assume.
-/
import ArmadaLean.PoolSafety

namespace ArmadaLean.Adjudicator

/-- `c` is currently a live (unspent) note of some token at some leaf
    `(treeNumber, position)` key: the pool's own ghost bookkeeping
    (`PoolState.live`, `Pool.lean`) records a preimage for it. The
    adjudicator-level reading of "a channel's holding is a note the pool
    still backs". -/
def PoolIsLive (s : PoolState) (c : Term) : Prop :=
  ∃ t tn pos pre, ((tn, pos), pre) ∈ s.live t ∧ hashCommitment pre = c

/-!
## Deposit: a plain, EdDSA-signed spend with one contract-owned output

Builds exactly the pool state `ArmadaLean.Step.transact` (`Pool.lean`)
produces for this witness, with `unshieldTail := []` (a plain funding
deposit keeps every output live; no unshield payout) — naming which one
of its outputs is the adjudicator's own, at which `(treeNumber, position)`
key. `npk` derivation reuses `ArmadaLean.TransactOwned`'s own formula,
`npk[i] = Poseidon(ownerField, randomIn[i])` (`TransactOwned.circom:66-70`)
— the same derivation `transactOwned`'s owner uses.
-/

/-- One adjudicator-funding `pool.transact` call: the depositor's own
    `N`-note, EdDSA-signed spend (`ArmadaLean.Constrained`, the base
    circuit, registered-shape bound `hN`/`hM` — `ArmadaLean.Pool.
    Step.transact`'s own bound), with one of its `M` outputs disclosed as
    a preimage owned by `self`, on `token`, worth `amount`, landing
    at `(treeNumber, position)`. `self` IS the owner field here, no
    `addressOf` detour (`TransactOwned.circom:13`, `ownerField =
    uint256(uint160(owner))` — a contract's own address, which this
    model now represents as a `Term` directly, `ShieldedRagequit.sol:147`,
    `bytes32(uint256(uint160(address(this))))`): the real contract checks
    the deposited note's own key against `Poseidon(self, random)` for its
    own deployed address directly. Every other output (private change) is
    also recorded, matching `Step.transact`'s own effect: all `M` outputs
    join the pool's live set, each at its own `(treeNumber, position)` key
    (`ArmadaLean.withTreePositionsFrom`), not only the adjudicator's own —
    `treeNumber`/`position` are the output batch's own landing tree/start
    position (`insertTreeNumber`/`insertStartPos`, rolling the pool's
    current tree over first if the batch would not fit, module comment),
    `idx` offset within the batch. `spendTreeNumber` is the proof's own
    `boundParams.treeNumber`, the one tree the depositor's OWN spent
    inputs' membership proofs and nullifiers are checked against — may
    differ from `treeNumber`, the tree the fresh outputs land in, since a
    rollover may have moved the pool's current tree on since the spent
    notes were minted. `records` is a sublist of `ArmadaLean.
    transactOutputRecords w pub` — `Step.transact`'s own convention —
    which already gives `hashCommitment` correctness for every disclosed
    entry (`ArmadaLean.transactOutputRecords_valid`), no separate
    hypothesis needed. The adjudicator's OWN output's preimage MUST itself
    be in `records` (`holdings_never_zero_valued`'s own invariant needs
    this to read a value back at all), and this output is ADDITIONALLY
    disclosed as contract-owned through `ownedRecords`, with the same
    random `r` the holding's own `npk` names — this is what lets
    `ArmadaLean.owned_spend_witness_exists` build a later spend witness
    for it from public data alone. -/
def DepositStep {N M : Nat} (before : PoolState) (self : Term) (token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (spendTreeNumber treeNumber position : Nat) (after : PoolState) : Prop :=
  ∃ r, w.npkOut idx = npk self r ∧
  pub.commitmentsOut idx = commitment (w.npkOut idx) token amount ∧
  w.token = token ∧
  treeNumber = insertTreeNumber before.closedTrees before.leaves M ∧
  position = insertStartPos before.leaves M + idx.val ∧
  ∃ (_hN : N ≤ 8) (_hM : M ≤ 4) (_hC : Constrained w pub)
    (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
    (records : List (Term × CommitmentPreimage)),
    pub.merkleRoot ∈ before.rootsAt' spendTreeNumber ∧
    removeAll (before.live w.token) (transactSpentPositions spendTreeNumber w) = some rest ∧
    markSpent (before.spent spendTreeNumber) (List.ofFn pub.nullifiers) = some spent' ∧
    records.Sublist (transactOutputRecords w pub) ∧
    (pub.commitmentsOut idx, (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage)) ∈ records ∧
    after = (let res := insertResult before.closedTrees before.leaves before.roots ((transactAllOutputs w).map hashCommitment)
      { before with
        live := fun t => if t = w.token
          then withTreePositionsFrom treeNumber (insertStartPos before.leaves M)
            (transactAllOutputs w) ++ rest
          else before.live t,
        spent := fun n => if n = spendTreeNumber then spent' else before.spent n,
        closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
        preimageOf := applyRecords before.preimageOf records,
        ownedRandomOf := applyOwnedRecords before.ownedRandomOf
          [(pub.commitmentsOut idx, (⟨self, r⟩ : OwnedDisclosure))] })

/-- LIVENESS ASSUMPTION (EdDSA completeness, pool layer) — assumed, not
    proven. `eddsaCompleteness` says: if an execution's own ghost signing
    record (`signedBy`, read generically — `AdjudicatorState.poolSignedBy`,
    `State.lean`, at the one call site) has recorded that the holder of
    `pk` signed `msgHash`, some signature verifying under `EdDSAVerify`
    exists. Standard EdDSA completeness (any held private key can sign any
    message it is asked to) made SAFE by the gate: a caller cannot make
    the hypothesis true for a key they do not hold, because
    `AdjudicatorState.poolSignedBy` only grows through `Operations.lean`'s
    `.signNote`, whose `Step` case only succeeds when the ACTOR submitting
    it holds `pk`. `msgHash` is a `Term` (`EdDSAVerify`'s own signature,
    `ArmadaLean.Transact`). Stated generically over the ghost relation
    (not fixed to one state type) so it can live here, before `State.lean`
    defines `AdjudicatorState`, with no import cycle. -/
structure PoolSignatureLiveness where
  eddsaCompleteness : ∀ (signedBy : (Nat × Nat) → Term → Prop) (pk : Nat × Nat) (msgHash : Term),
    signedBy pk msgHash → ∃ signature : Nat × Nat × Nat, EdDSAVerify pk signature msgHash

/-!
## One `transactOwned` spend: nullify at most one owned note, mint fresh
ones (the adjudicator, as an ORDINARY caller of `ArmadaLean.PoolOwned`)

Builds exactly the pool state `ArmadaLean.Step.transactOwned` (`Pool.lean`)
produces for this witness: no unshield, every output mandatory, every
output disclosed contract-owned through `ownedRandomOf`. The adjudicator's
OWN condition is that the witness's own outputs (`ownedNewNotes w`) ARE
EXACTLY the payout notes and remainder note its own rule computed
(`outputPreimages`) — see this file's module comment for why this is what
lets `notedValue_conserved` hold with no separate trust in `heldValue`'s
own accuracy.
-/

/-- One adjudicator-initiated `pool.transactOwned` call: nullifies, by
    `(treeNumber, position)` key, at most one of the adjudicator's own
    previously-owned commitments and mints exactly `payoutPreimages ++
    ownedPreimages`, read off the circuit's own witness (`ArmadaLean.
    ownedNewNotes`), landing at sequential `(treeNumber, position)` keys
    starting at the output batch's own landing tree/start position
    (`ArmadaLean.withTreePositionsFrom`, `insertTreeNumber`/
    `insertStartPos`). `payoutPreimages` are notes keyed to a recipient the
    adjudicator does not control (`.transfer`'s own payout outputs,
    `Operations.lean`); `ownedPreimages` are notes that stay contract-owned
    (a `.transfer` remainder). Requires the pool's OWN owner-authorization
    convention (`self = pub.ownerField`, matching `Step.transactOwned`'s
    own `hCaller`, `caller = pub.ownerField` — a direct `Term` equality,
    `self` now the contract's own Keccak address term, no truncation) and
    the registered-shape bound (`hM`, `ArmadaLean.
    transactOwned_value_conserved`'s own requirement) — the adjudicator
    supplies no mechanism and no arithmetic of its own. `removeAll`
    (`Pool.lean`) removes the nullified note by its own `(treeNumber,
    position)` key (`ArmadaLean.ownedSpentPositions`), matching the
    Merkle-membership fact `OwnedConstrained.merkle` already names; the
    "some" branch's own equations tie the witness's own `leavesIndices 0`
    and the proof's own `spendTreeNumber` to the key the caller names.
    Every output's preimage is disclosed (`preimageOf`'s own update):
    `transactOwned`'s `_validatePublicOutputs (requireAll = true)`
    (`Pool.lean`'s own `Step.transactOwned` comment) makes this MANDATORY
    for every output, payout or owned alike, matching `ArmadaLean.
    ownedOutputRecords w pub` directly. `ownedRandom`/the disclosure
    conjunct is the matching MANDATORY `ownedRandomOf` disclosure
    (`Step.transactOwned`'s own hypotheses), covering EVERY index of
    `ownedPreimages` exactly once (no caller can omit one by naming an
    incomplete list, the gap the rollover migration had left open — an
    operator ruling restores it): `ownedRandom j` is the random behind
    index `j`'s own key (`w.npkOut (Fin.natAdd payoutPreimages.length
    j) = npk self (ownedRandom j)`), applied through `ownedRandomOf`
    at that SAME index (`Fin.natAdd payoutPreimages.length j`), for the
    `ownedPreimages` SUFFIX only: a payout note's own key is the
    recipient's, never one the adjudicator derives `npk pub.ownerField
    r` for, so no such disclosure could ever exist for it — only a note
    that STAYS contract-owned carries one. `hNonZero` carries
    the same check's rejection of a zero preimage; `ArmadaLean.
    transactOwned_records_all` is what lets `holdings_never_zero_valued`
    read each output's own preimage back. `nullified`, when
    `some ((spendTreeNumber, pos), c)`, names the tree, the position
    within it, and the commitment being spent — the commitment is a check
    against the holding's own recorded value. `M` is `payoutPreimages.
    length + ownedPreimages.length`, the registered-shape bound the
    witness's own type index uses directly (not `outputs.length`, kept a
    separate `let` so `Fin.natAdd payoutPreimages.length _` — needing
    `Fin M` — matches the witness's own index type without a cast). -/
def PoolOwnedSpendStep (before : PoolState) (self : Term) (token : Nat)
    (nullified : Option ((Nat × Nat) × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage) (after : PoolState) : Prop :=
  let M := payoutPreimages.length + ownedPreimages.length
  let outputs := payoutPreimages ++ ownedPreimages
  let treeNumber := insertTreeNumber before.closedTrees before.leaves M
  let position := insertStartPos before.leaves M
  let res := insertResult before.closedTrees before.leaves before.roots
    (outputs.map hashCommitment)
  match nullified with
  | none =>
    ∃ (w : TransactOwnedWitness 0 M)
      (pub : TransactOwnedPublic 0 M)
      (_hM : M ≤ 4) (_hC : OwnedConstrained w pub)
      (spent' : NullifierSet) (ownedRandom : Fin ownedPreimages.length → Nat)
      (_hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)),
      self = pub.ownerField ∧
      w.token = token ∧
      ownedNewNotes w = outputs ∧
      pub.merkleRoot ∈ before.rootsAt' treeNumber ∧
      markSpent (before.spent treeNumber) (List.ofFn pub.nullifiers) = some spent' ∧
      (∀ j : Fin ownedPreimages.length, w.npkOut (Fin.natAdd payoutPreimages.length j) =
        npk self (ownedRandom j)) ∧
      after = { before with
        live := fun t => if t = token
          then withTreePositionsFrom treeNumber position outputs ++ before.live t
          else before.live t,
        spent := fun n => if n = treeNumber then spent' else before.spent n,
        closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
        preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub),
        ownedRandomOf := applyOwnedRecords before.ownedRandomOf
          ((List.finRange ownedPreimages.length).map fun j =>
            (pub.commitmentsOut (Fin.natAdd payoutPreimages.length j),
              (⟨self, ownedRandom j⟩ : OwnedDisclosure))) }
  | some ((spendTreeNumber, pos), c) =>
    ∃ (w : TransactOwnedWitness 1 M)
      (pub : TransactOwnedPublic 1 M)
      (_hM : M ≤ 4) (_hC : OwnedConstrained w pub)
      (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet)
      (ownedRandom : Fin ownedPreimages.length → Nat)
      (_hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)),
      self = pub.ownerField ∧
      w.token = token ∧
      ownedNewNotes w = outputs ∧
      w.leavesIndices 0 = pos ∧
      commitment (npk pub.ownerField (w.randomIn 0)) w.token (w.valueIn 0) = c ∧
      pub.merkleRoot ∈ before.rootsAt' spendTreeNumber ∧
      removeAll (before.live token) (ownedSpentPositions spendTreeNumber pub w) = some rest ∧
      markSpent (before.spent spendTreeNumber) (List.ofFn pub.nullifiers) = some spent' ∧
      (∀ j : Fin ownedPreimages.length, w.npkOut (Fin.natAdd payoutPreimages.length j) =
        npk self (ownedRandom j)) ∧
      after = { before with
        live := fun t => if t = token
          then withTreePositionsFrom treeNumber position outputs ++ rest
          else before.live t,
        spent := fun n => if n = spendTreeNumber then spent' else before.spent n,
        closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
        preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub),
        ownedRandomOf := applyOwnedRecords before.ownedRandomOf
          ((List.finRange ownedPreimages.length).map fun j =>
            (pub.commitmentsOut (Fin.natAdd payoutPreimages.length j),
              (⟨self, ownedRandom j⟩ : OwnedDisclosure))) }

/-!
## Deposit top-up: merge the old holding with a fresh deposit note

`.deposit` (`Operations.lean`) must never REPLACE a channel's existing
holding with a fresh note worth only the new `amount` (that would discard
the prior value — see `Lemmas.lean`'s `deposit_sets_heldValue`), nor let the
two notes sit side by side (`AdjudicatorState.holdings` names at most one
note per `(asset, channelId)`). When a channel already holds a note, a
top-up MERGES the old holding and the fresh deposit note into one note of
their sum, via `ArmadaLean.Pool.Step.transactOwned` with `N = 2` nullified
inputs and `M = 1` minted output.
-/

/-- One `pool.transactOwned` merge call: nullifies the channel's old
    holding note (at `(oldTreeNumber, oldPos)`, commitment `oldHolding`,
    within spend-tree `spendTreeNumber`) and the freshly deposited note (at
    `(newTreeNumber, newPos)`, commitment `newNote`, same spend tree — both
    inputs' membership proofs and nullifiers are checked against the ONE
    `spendTreeNumber` a `transactOwned` proof names, `Pool.lean`'s own
    `Step.transactOwned` comment), and mints exactly one merged note,
    `merged` (a `Term`), at `(mergedTreeNumber, mergedPos)`, read off the
    circuit's own public output. The pool's own balance check
    (`OwnedConstrained.balance`, `ArmadaLean.transactOwned_value_conserved`)
    ties `merged`'s value to the sum of the two spent notes' true
    Merkle-tree values. `npk = npk self r` for some secret `r`: the same
    convention `DepositStep`'s own holding note uses, since this is still a
    deposit-side note, not `.transfer`'s remainder. -/
def DepositMergeStep (before : PoolState) (self : Term) (token : Nat)
    (oldTreeNumber oldPos : Nat) (oldHolding : Term) (newTreeNumber newPos : Nat)
    (newNote : Term) (merged : Term) (spendTreeNumber mergedTreeNumber mergedPos : Nat)
    (after : PoolState) : Prop :=
  mergedTreeNumber = insertTreeNumber before.closedTrees before.leaves 1 ∧
  mergedPos = insertStartPos before.leaves 1 ∧
  ∃ (w : TransactOwnedWitness 2 1) (pub : TransactOwnedPublic 2 1)
    (_hC : OwnedConstrained w pub)
    (rest : List ((Nat × Nat) × CommitmentPreimage)) (spent' : NullifierSet) (r randomOut : Nat)
    (_hNonZero : ¬ isZeroPreimage (⟨w.npkOut 0, w.token, w.valueOut 0⟩ : CommitmentPreimage)),
    self = pub.ownerField ∧
    w.token = token ∧
    w.npkOut 0 = npk self r ∧
    merged = pub.commitmentsOut 0 ∧
    w.leavesIndices 0 = oldPos ∧
    w.leavesIndices 1 = newPos ∧
    commitment (npk pub.ownerField (w.randomIn 0)) w.token (w.valueIn 0) = oldHolding ∧
    commitment (npk pub.ownerField (w.randomIn 1)) w.token (w.valueIn 1) = newNote ∧
    oldTreeNumber = spendTreeNumber ∧ newTreeNumber = spendTreeNumber ∧
    pub.merkleRoot ∈ before.rootsAt' spendTreeNumber ∧
    removeAll (before.live token) (ownedSpentPositions spendTreeNumber pub w) = some rest ∧
    markSpent (before.spent spendTreeNumber) (List.ofFn pub.nullifiers) = some spent' ∧
    npk pub.ownerField randomOut = w.npkOut 0 ∧
    after = (let res := insertResult before.closedTrees before.leaves before.roots ((ownedNewNotes w).map hashCommitment)
      { before with
        live := fun t => if t = token
          then withTreePositionsFrom mergedTreeNumber mergedPos (ownedNewNotes w) ++ rest
          else before.live t,
        spent := fun n => if n = spendTreeNumber then spent' else before.spent n,
        closedTrees := res.1, leaves := res.2.1, roots := res.2.2,
        preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub),
        ownedRandomOf := applyOwnedRecords before.ownedRandomOf
          [(pub.commitmentsOut 0, (⟨pub.ownerField, randomOut⟩ : OwnedDisclosure))] })

end ArmadaLean.Adjudicator
