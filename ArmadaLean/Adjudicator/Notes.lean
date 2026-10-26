/-
  ArmadaLean.Adjudicator.Notes — the Armada layer: the adjudicator's money
  is pool notes, not a raw balance.

  The pool itself — its state, its `shield`/`transact`/`transactOwned` steps
  and their safety theorems (the core invariant, no double spend, preimage
  consistency, ownership binding, value conservation from a real,
  shape-bounded circuit witness) — lives in the root `ArmadaLean.Pool`/
  `ArmadaLean.PoolSafety` modules (branch `pool-model`, commit `5d8a5f7`).
  The adjudicator is an ORDINARY caller of that pool: it defines no pool
  state, no live-note ledger and no preimage registry of its own.
  `AdjudicatorState` (`State.lean`) embeds `ArmadaLean.PoolState` directly.

  `DepositStep` and `PoolOwnedSpendStep` below name the TWO call shapes the
  adjudicator uses, each an instance of `ArmadaLean.Pool`'s own
  `Step.transact`/`Step.transactOwned` SHAPE (same witness fields, same
  `N ≤ 8`/`M ≤ 4` registered-circuit bound, same `removeAll`/`markSpent`/
  `applyRecords`/`applyOwnedRecords` bookkeeping, via `ArmadaLean.
  transactSpentPositions`/`transactAllOutputs`/`ownedSpentPositions`/
  `ownedNewNotes`): the adjudicator derives no SEPARATE balance or removal
  rule of its own; it builds the exact pool state `Step.transact`/`Step.
  transactOwned` would produce for the SAME witness, so every pool-level
  fact about that constructor (`transact_balance`, `transactOwned_balance`,
  `transact_spends_only_owned`) applies unchanged. Neither `DepositStep` nor
  `PoolOwnedSpendStep`/`DepositMergeStep` carries a pause check any more:
  `pool-model`'s `30d7a65` removed the owner's power to block a spend —
  `Step.transact`/`Step.transactOwned` take no `emergencyPaused`/
  `withdrawOnlyMode` condition.

  A note is identified by its Merkle LEAF POSITION, not by its content
  (`Pool.lean`'s module comment): the circuit derives a spend's nullifier
  from the leaf position a proof names, never from a scan for a matching
  value, and two live notes can carry the identical preimage without ever
  sharing a position. `AdjudicatorState.holdings` (`State.lean`) follows the
  same rule: a channel's holding names exactly one note by its leaf
  position, with the commitment carried alongside as a check. `DepositStep`
  reports the position its own output landed at (`before.leaves.length +
  idx`, the exact position `withPositionsFrom` tags it with);
  `PoolOwnedSpendStep`'s "some" branch nullifies the position a holding
  already names, and reports the position its own merged/remainder output
  lands at, the same way.

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
    position: the pool's own ghost bookkeeping (`PoolState.live`,
    `Pool.lean`) records a preimage for it. The adjudicator-level reading
    of "a channel's holding is a note the pool still backs". -/
def PoolIsLive (s : PoolState) (c : Term) : Prop :=
  ∃ t pos pre, (pos, pre) ∈ s.live t ∧ hashCommitment pre = c

/-!
## Deposit: a plain, EdDSA-signed spend with one contract-owned output

Builds exactly the pool state `ArmadaLean.Step.transact` (`Pool.lean`)
produces for this witness, with `unshieldTail := []` (a plain funding
deposit keeps every output live; no unshield payout) — naming which one
of its outputs is the adjudicator's own, at which leaf position. `npk`
derivation reuses `ArmadaLean.TransactOwned`'s own formula, `npk[i] =
Poseidon(ownerField, randomIn[i])` (`TransactOwned.circom:66-70`) — the
same derivation `transactOwned`'s owner uses.
-/

/-- One adjudicator-funding `pool.transact` call: the depositor's own
    `N`-note, EdDSA-signed spend (`ArmadaLean.Constrained`, the base
    circuit, registered-shape bound `hN`/`hM` — `ArmadaLean.Pool.
    Step.transact`'s own bound), with one of its `M` outputs disclosed as
    a preimage owned by `ownerField`, on `token`, worth `amount`, landing
    at leaf position `position`. `self = addressOf ownerField` (`Armada
    Lean.addressOf`), the same owner-authorization convention `Pool
    Owned`'s owned path uses (`PoolOwned.owned_owner_binding`'s `caller =
    addressOf ownerField`): the real contract checks the deposited note's
    own key against `Poseidon(ownerField, random)` for its own deployed
    address, `uint256(uint160(address(this)))`, at most 160 bits, not
    `self` directly — a bare `npk (Term.val self) r` would let a held
    note name an owner no later owned spend (`.transfer`'s own remainder,
    a merge) could ever match against `OwnedConstrained`'s `self =
    addressOf pub.ownerField`. Every other output (private change) is
    also recorded, matching `Step.transact`'s own effect: all `M` outputs
    join the pool's live set, each at its own sequential position
    (`ArmadaLean.withPositionsFrom`), not only the adjudicator's own.
    `records` is a sublist of `ArmadaLean.transactOutputRecords w pub` —
    `Step.transact`'s own convention — which already gives
    `hashCommitment` correctness for every disclosed entry
    (`ArmadaLean.transactOutputRecords_valid`), no separate hypothesis
    needed. The adjudicator's OWN output's preimage MUST itself be in
    `records` (`holdings_never_zero_valued`'s own invariant needs this to
    read a value back at all), and this output is ADDITIONALLY disclosed
    as contract-owned through `ownedRecords`, with the same random `r`
    and `ownerField` the holding's own `npk` names — this is what lets
    `ArmadaLean.owned_spend_witness_exists` build a later spend witness
    for it from public data alone. -/
def DepositStep {N M : Nat} (before : PoolState) (self token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (position : Nat) (after : PoolState) : Prop :=
  ∃ r ownerField, self = addressOf ownerField ∧ w.npkOut idx = npk (Term.val ownerField) r ∧
  pub.commitmentsOut idx = commitment (w.npkOut idx) token amount ∧
  w.token = token ∧
  position = before.leaves.length + idx.val ∧
  ∃ (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    (rest : List (Nat × CommitmentPreimage)) (spent' : NullifierSet)
    (records : List (Term × CommitmentPreimage))
    (hCapacity : before.leaves.length + M ≤ 2 ^ TreeDepth),
    pub.merkleRoot ∈ before.roots ∧
    removeAll (before.live w.token) (transactSpentPositions w) = some rest ∧
    markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
    records.Sublist (transactOutputRecords w pub) ∧
    (pub.commitmentsOut idx, (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage)) ∈ records ∧
    after = { before with
      live := fun t => if t = w.token
        then withPositionsFrom before.leaves.length (transactAllOutputs w) ++ rest
        else before.live t,
      spent := spent',
      leaves := before.leaves ++ (transactAllOutputs w).map hashCommitment,
      roots := treeRoot TreeDepth (before.leaves ++ (transactAllOutputs w).map hashCommitment) ::
        before.roots,
      preimageOf := applyRecords before.preimageOf records,
      ownedRandomOf := applyOwnedRecords before.ownedRandomOf
        [(pub.commitmentsOut idx, (⟨ownerField, r⟩ : OwnedDisclosure))] }

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

/-- One adjudicator-initiated `pool.transactOwned` call: nullifies, by leaf
    position, at most one of the adjudicator's own previously-owned
    commitments and mints exactly `payoutPreimages ++ ownedPreimages`, read
    off the circuit's own witness (`ArmadaLean.ownedNewNotes`), landing at
    sequential positions starting at `before.leaves.length`
    (`ArmadaLean.withPositionsFrom`). `payoutPreimages` are notes keyed to a
    recipient the adjudicator does not control (`.transfer`'s own payout
    outputs, `Operations.lean`); `ownedPreimages` are notes that stay
    contract-owned (a `.transfer` remainder). Requires the pool's OWN
    owner-authorization convention (`self = ArmadaLean.addressOf
    pub.ownerField`, matching `ArmadaLean.owned_owner_binding`'s `caller =
    addressOf ownerField`) and the registered-shape bound (`hM`,
    `ArmadaLean.transactOwned_value_conserved`'s own requirement) — the
    adjudicator supplies no mechanism and no arithmetic of its own.
    `removeAll` (`Pool.lean`) removes the nullified note by its own leaf
    position (`ArmadaLean.ownedSpentPositions`), matching the Merkle-
    membership fact `OwnedConstrained.merkle` already names; the "some"
    branch's `hPos` ties the witness's own `leavesIndices 0` to the
    position the caller names. Every output's preimage is disclosed
    (`preimageOf`'s own update): `transactOwned`'s `_validatePublicOutputs
    (requireAll = true)` (`Pool.lean`'s own `Step.transactOwned` comment)
    makes this MANDATORY for every output, payout or owned alike, matching
    `ArmadaLean.ownedOutputRecords w pub` directly. `randomOut`/its own
    disclosure hypothesis is the matching mandatory `ownedRandomOf`
    disclosure (`Step.transactOwned`'s own hypotheses), but ONLY for the
    `ownedPreimages` SUFFIX (indices `payoutPreimages.length` and up, via
    `Fin.natAdd`): a payout note's own key is the recipient's, never one
    the adjudicator (or anyone it can name as `ownerField`) derives
    `npk (Term.val pub.ownerField) r` for, so no such disclosure could ever
    exist for it — only a note that STAYS contract-owned carries one.
    `hNonZero` carries the same check's rejection of a zero preimage;
    `ArmadaLean.transactOwned_records_all` is what lets
    `holdings_never_zero_valued` read each output's own preimage back.
    `nullified`, when `some (pos, c)`, names both the position and the
    commitment being spent — the commitment is a check against the
    holding's own recorded value. -/
def PoolOwnedSpendStep (before : PoolState) (self token : Nat)
    (nullified : Option (Nat × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage) (after : PoolState) : Prop :=
  match nullified with
  | none =>
    ∃ (w : TransactOwnedWitness 0 (payoutPreimages.length + ownedPreimages.length))
      (pub : TransactOwnedPublic 0 (payoutPreimages.length + ownedPreimages.length))
      (hM : payoutPreimages.length + ownedPreimages.length ≤ 4) (hC : OwnedConstrained w pub)
      (spent' : NullifierSet) (randomOut : Fin ownedPreimages.length → Nat)
      (hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
      (hCapacity : before.leaves.length + (payoutPreimages.length + ownedPreimages.length) ≤
        2 ^ TreeDepth),
      self = addressOf pub.ownerField ∧
      w.token = token ∧
      ownedNewNotes w = payoutPreimages ++ ownedPreimages ∧
      pub.merkleRoot ∈ before.roots ∧
      markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
      (∀ j, npk (Term.val pub.ownerField) (randomOut j) =
        w.npkOut (Fin.natAdd payoutPreimages.length j)) ∧
      after = { before with
        live := fun t => if t = token
          then withPositionsFrom before.leaves.length (payoutPreimages ++ ownedPreimages) ++
            before.live t
          else before.live t,
        spent := spent',
        leaves := before.leaves ++ (payoutPreimages ++ ownedPreimages).map hashCommitment,
        roots := treeRoot TreeDepth
          (before.leaves ++ (payoutPreimages ++ ownedPreimages).map hashCommitment) ::
          before.roots,
        preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub),
        ownedRandomOf := applyOwnedRecords before.ownedRandomOf
          (List.ofFn fun j : Fin ownedPreimages.length =>
            (pub.commitmentsOut (Fin.natAdd payoutPreimages.length j),
              (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure))) }
  | some (pos, c) =>
    ∃ (w : TransactOwnedWitness 1 (payoutPreimages.length + ownedPreimages.length))
      (pub : TransactOwnedPublic 1 (payoutPreimages.length + ownedPreimages.length))
      (hM : payoutPreimages.length + ownedPreimages.length ≤ 4) (hC : OwnedConstrained w pub)
      (rest : List (Nat × CommitmentPreimage)) (spent' : NullifierSet)
      (randomOut : Fin ownedPreimages.length → Nat)
      (hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
      (hCapacity : before.leaves.length + (payoutPreimages.length + ownedPreimages.length) ≤
        2 ^ TreeDepth),
      self = addressOf pub.ownerField ∧
      w.token = token ∧
      ownedNewNotes w = payoutPreimages ++ ownedPreimages ∧
      w.leavesIndices 0 = pos ∧
      commitment (npk (Term.val pub.ownerField) (w.randomIn 0)) w.token (w.valueIn 0) = c ∧
      pub.merkleRoot ∈ before.roots ∧
      removeAll (before.live token) (ownedSpentPositions pub w) = some rest ∧
      markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
      (∀ j, npk (Term.val pub.ownerField) (randomOut j) =
        w.npkOut (Fin.natAdd payoutPreimages.length j)) ∧
      after = { before with
        live := fun t => if t = token
          then withPositionsFrom before.leaves.length (payoutPreimages ++ ownedPreimages) ++ rest
          else before.live t,
        spent := spent',
        leaves := before.leaves ++ (payoutPreimages ++ ownedPreimages).map hashCommitment,
        roots := treeRoot TreeDepth
          (before.leaves ++ (payoutPreimages ++ ownedPreimages).map hashCommitment) ::
          before.roots,
        preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub),
        ownedRandomOf := applyOwnedRecords before.ownedRandomOf
          (List.ofFn fun j : Fin ownedPreimages.length =>
            (pub.commitmentsOut (Fin.natAdd payoutPreimages.length j),
              (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure))) }


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
    holding note (at leaf position `oldPos`, commitment `oldHolding`) and
    the freshly deposited note (at leaf position `newPos`, commitment
    `newNote`), and mints exactly one merged note, `merged` (a `Term`),
    at leaf position `mergedPos`, read off the circuit's own public
    output. The pool's own balance check (`OwnedConstrained.balance`,
    `ArmadaLean.transactOwned_value_conserved`) ties `merged`'s value to
    the sum of the two spent notes' true Merkle-tree values. `npk = npk
    (Term.val self) r` for some secret `r`: the same convention
    `DepositStep`'s own holding note uses, since this is still a
    deposit-side note, not `.transfer`'s remainder (`npk = Term.val self`
    directly). -/
def DepositMergeStep (before : PoolState) (self token : Nat)
    (oldPos : Nat) (oldHolding : Term) (newPos : Nat) (newNote : Term)
    (merged : Term) (mergedPos : Nat) (after : PoolState) : Prop :=
  mergedPos = before.leaves.length ∧
  ∃ (w : TransactOwnedWitness 2 1) (pub : TransactOwnedPublic 2 1)
    (hC : OwnedConstrained w pub)
    (rest : List (Nat × CommitmentPreimage)) (spent' : NullifierSet) (r randomOut : Nat)
    (hNonZero : ¬ isZeroPreimage (⟨w.npkOut 0, w.token, w.valueOut 0⟩ : CommitmentPreimage))
    (hCapacity : before.leaves.length + 1 ≤ 2 ^ TreeDepth),
    self = addressOf pub.ownerField ∧
    w.token = token ∧
    w.npkOut 0 = npk (Term.val self) r ∧
    merged = pub.commitmentsOut 0 ∧
    w.leavesIndices 0 = oldPos ∧
    w.leavesIndices 1 = newPos ∧
    commitment (npk (Term.val pub.ownerField) (w.randomIn 0)) w.token (w.valueIn 0) = oldHolding ∧
    commitment (npk (Term.val pub.ownerField) (w.randomIn 1)) w.token (w.valueIn 1) = newNote ∧
    pub.merkleRoot ∈ before.roots ∧
    removeAll (before.live token) (ownedSpentPositions pub w) = some rest ∧
    markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
    npk (Term.val pub.ownerField) randomOut = w.npkOut 0 ∧
    after = { before with
      live := fun t => if t = token
        then withPositionsFrom before.leaves.length (ownedNewNotes w) ++ rest
        else before.live t,
      spent := spent',
      leaves := before.leaves ++ (ownedNewNotes w).map hashCommitment,
      roots := treeRoot TreeDepth (before.leaves ++ (ownedNewNotes w).map hashCommitment) ::
        before.roots,
      preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub),
      ownedRandomOf := applyOwnedRecords before.ownedRandomOf
        [(pub.commitmentsOut 0, (⟨pub.ownerField, randomOut⟩ : OwnedDisclosure))] }

end ArmadaLean.Adjudicator
