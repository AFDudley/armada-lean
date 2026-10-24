/-
  ArmadaLean.Adjudicator.Notes — the Armada layer: the adjudicator's money
  is pool notes, not a raw balance.

  The pool itself — its state, its `shield`/`transact`/`transactOwned` steps
  and their safety theorems (the core invariant, no double spend, preimage
  consistency, ownership binding, value conservation from a real,
  shape-bounded circuit witness) — lives in the root `ArmadaLean.Pool`/
  `ArmadaLean.PoolSafety` modules (branch `pool-model`, commit `ad9a6f1`).
  The adjudicator is an ORDINARY caller of that pool: it defines no pool
  state, no live-note ledger and no preimage registry of its own.
  `AdjudicatorState` (`State.lean`) embeds `ArmadaLean.PoolState` directly.

  `DepositStep` and `PoolOwnedSpendStep` below name the TWO call shapes the
  adjudicator uses, each an instance of `ArmadaLean.Pool`'s own
  `Step.transact`/`Step.transactOwned` SHAPE (same witness fields, same
  `N ≤ 8`/`M ≤ 4` registered-circuit bound, same `removeAll`/`markSpent`/
  `applyRecords` bookkeeping, via `ArmadaLean.transactSpentNotes`/
  `transactAllOutputs`/`ownedSpentNotes`/`ownedNewNotes`): the adjudicator
  derives no SEPARATE balance or removal rule of its own; it builds the
  exact pool state `Step.transact`/`Step.transactOwned` would produce for
  the SAME witness, so every pool-level fact about that constructor
  (`transact_balance`, `transactOwned_balance`, `transact_spends_only_
  owned`) applies unchanged — the adjudicator never re-derives, and never
  separately trusts, a balance or removal fact the pool step already
  proves from the witness alone.

  Naming the witness explicitly — not hiding behind an opaque `Pool.Step`
  hypothesis — is what lets a deposit's OWN condition (the adjudicator-
  owned output) tie to a SPECIFIC `transact` call rather than admit any
  OTHER pool transition (a `shield`, say) that happened to also leave a
  matching commitment live: `Pool.Step` alone does not say WHICH
  constructor fired, and `notedValue_conserved` would be false if a
  `.deposit` could be satisfied by a value-creating `shield` instead.
  `DepositStep`'s witness obeys the registered-shape bound (`hN : N ≤ 8`,
  `hM : M ≤ 4`) the pool's own `transact_value_conserved`/`transact_
  balance` need — the old unbounded `∃ N M` (an earlier revision of this
  file) is what made `notedValue_conserved`'s `.deposit` case unprovable;
  the bound closes that gap.

  `PoolOwnedSpendStep`'s own adjudicator condition is that the witness's
  own outputs (`ArmadaLean.ownedNewNotes w`) ARE EXACTLY the payout notes
  and remainder note its rule computes (`outputPreimages`, built in
  `Operations.lean`'s `.transfer` case from `heldValue`/`transferEffects`)
  — not a separately-asserted list the pool is trusted to mint on the
  adjudicator's say-so. The circuit's own output-commitment check
  (`OwnedConstrained.outputs`) already ties `ownedNewNotes w` to `pub`'s
  public commitments, so this condition names no new trust, only which
  notes are meant. This is what lets `notedValue_conserved` go through
  from `ArmadaLean.transactOwned_balance` alone, with no separate
  assumption that `heldValue` correctly reports the nullified note's true
  value: if it ever disagreed, no witness could satisfy BOTH
  `ownedNewNotes w = outputPreimages` (whose total is `heldValue`, by
  `Operations.lean`'s own `remainder`/`totalPayouts` construction) AND the
  circuit's balance (whose total is the spent note's TRUE Merkle-tree
  value) — the step would simply not exist, which is the safe outcome,
  not a fact this file needs to assume. -/
import ArmadaLean.PoolSafety

namespace ArmadaLean.Adjudicator

/-- `c` is currently a live (unspent) note of some token: the pool's own
    ghost bookkeeping (`PoolState.live`, `Pool.lean`) records a preimage
    for it. The adjudicator-level reading of "a channel's holding is a
    note the pool still backs". -/
def PoolIsLive (s : PoolState) (c : Nat) : Prop :=
  ∃ t pre, pre ∈ s.live t ∧ hashCommitment pre = c

/-!
## Deposit: a plain, EdDSA-signed spend with one contract-owned output

Builds exactly the pool state `ArmadaLean.Step.transact` (`Pool.lean`)
produces for this witness, with `unshieldTail := []` (a plain funding
deposit keeps every output live; no unshield payout) — naming which one
of its outputs is the adjudicator's own. `npk` derivation reuses
`ArmadaLean.TransactOwned`'s own formula, `npk[i] = Poseidon(ownerField,
randomIn[i])` (`TransactOwned.circom:66-70`) — the same derivation
`transactOwned`'s owner uses. -/

/-- One adjudicator-funding `pool.transact` call: the depositor's own
    `N`-note, EdDSA-signed spend (`ArmadaLean.Constrained`, the base
    circuit, registered-shape bound `hN`/`hM` — `ArmadaLean.Pool.
    Step.transact`'s own bound), with one of its `M` outputs disclosed as
    a preimage owned by `self` (the adjudicator), on `token`, worth
    `amount`. Every other output (private change) is also recorded,
    matching `Step.transact`'s own effect: all `M` outputs join the
    pool's live set, not only the adjudicator's own. `records` is a
    sublist of `ArmadaLean.transactOutputRecords w pub` — `Step.
    transact`'s own convention, now that the pool models `_validate
    PublicOutputs(requireAll = false)` exactly — which already gives
    `hashCommitment` correctness for every disclosed entry
    (`ArmadaLean.transactOutputRecords_valid`), no separate hypothesis
    needed. The adjudicator's OWN output's preimage MUST itself be in
    `records` (`holdings_never_zero_valued`'s own invariant needs this
    to read a value back at all — the pool's own per-output disclosure
    is OPTIONAL, but the adjudicator cannot read back a holding it
    never asked the pool to publish). -/
def DepositStep {N M : Nat} (before : PoolState) (self token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (after : PoolState) : Prop :=
  (∃ r, w.npkOut idx = npk self r) ∧
  pub.commitmentsOut idx = commitment (w.npkOut idx) token amount ∧
  w.token = token ∧
  ∃ (hN : N ≤ 8) (hM : M ≤ 4) (hC : Constrained w pub)
    (rest : List CommitmentPreimage) (spent' : NullifierSet) (newRoot : Nat)
    (records : List (Nat × CommitmentPreimage)),
    before.emergencyPaused = false ∧
    before.withdrawOnlyMode = false ∧
    pub.merkleRoot ∈ before.roots ∧
    removeAll (before.live w.token) (transactSpentNotes w) = some rest ∧
    markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
    records.Sublist (transactOutputRecords w pub) ∧
    (pub.commitmentsOut idx, (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage)) ∈ records ∧
    after = { before with
      live := fun t => if t = w.token then transactAllOutputs w ++ rest else before.live t,
      spent := spent',
      preimageOf := applyRecords before.preimageOf records }

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
    it holds `pk`. Stated generically over the ghost relation (not fixed
    to one state type) so it can live here, before `State.lean` defines
    `AdjudicatorState`, with no import cycle. -/
structure PoolSignatureLiveness where
  eddsaCompleteness : ∀ (signedBy : (Nat × Nat) → Nat → Prop) (pk : Nat × Nat) (msgHash : Nat),
    signedBy pk msgHash → ∃ signature : Nat × Nat × Nat, EdDSAVerify pk signature msgHash

/-!
## One `transactOwned` spend: nullify at most one owned note, mint fresh
ones (the adjudicator, as an ORDINARY caller of `ArmadaLean.PoolOwned`)

Builds exactly the pool state `ArmadaLean.Step.transactOwned` (`Pool.lean`)
produces for this witness: no unshield, every output mandatory. The
adjudicator's OWN condition is that the witness's own outputs
(`ownedNewNotes w`) ARE EXACTLY the payout notes and remainder note its
own rule computed (`outputPreimages`) — see this file's module comment for
why this is what lets `notedValue_conserved` hold with no separate trust
in `heldValue`'s own accuracy. -/

/-- One adjudicator-initiated `pool.transactOwned` call: nullifies at most
    one of the adjudicator's own previously-owned commitments and mints
    exactly `outputPreimages`, read off the circuit's own witness
    (`ArmadaLean.ownedNewNotes`). Requires the pool's OWN owner-
    authorization convention (`self = ArmadaLean.addressOf pub.ownerField`,
    matching `ArmadaLean.owned_owner_binding`'s `caller = addressOf
    ownerField`) and the registered-shape bound (`hM`,
    `ArmadaLean.transactOwned_value_conserved`'s own requirement) — the
    adjudicator supplies no mechanism and no arithmetic of its own.
    `removeAll` (`Pool.lean`) removes the nullified note by its own
    preimage value (`ArmadaLean.ownedSpentNotes`), matching the Merkle-
    membership fact `OwnedConstrained.merkle` already names. Every output's
    preimage is disclosed (`preimageOf`'s own update): `transactOwned`'s
    `_validatePublicOutputs(requireAll = true)` (`Pool.lean`'s own
    `Step.transactOwned` comment) makes this MANDATORY, not optional like
    a plain `transact`'s, so the registry update is fixed to
    `ArmadaLean.ownedOutputRecords w pub` directly — the pool's own
    batch, not a separately-asserted list. `hNonZero` carries the same
    check's rejection of a zero preimage (`Step.transactOwned`'s own
    hypothesis); `ArmadaLean.transactOwned_records_all` is what lets
    `holdings_never_zero_valued` read each output's own preimage back,
    with no bespoke `applyRecords` argument needed here. -/
def PoolOwnedSpendStep (before : PoolState) (self token : Nat)
    (nullifiedCommitment : Option Nat) (outputPreimages : List CommitmentPreimage)
    (after : PoolState) : Prop :=
  match nullifiedCommitment with
  | none =>
    ∃ (w : TransactOwnedWitness 0 outputPreimages.length)
      (pub : TransactOwnedPublic 0 outputPreimages.length)
      (hM : outputPreimages.length ≤ 4) (hC : OwnedConstrained w pub)
      (spent' : NullifierSet) (newRoot : Nat)
      (hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)),
      self = addressOf pub.ownerField ∧
      w.token = token ∧
      ownedNewNotes w = outputPreimages ∧
      before.emergencyPaused = false ∧
      before.withdrawOnlyMode = false ∧
      pub.merkleRoot ∈ before.roots ∧
      markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
      after = { before with
        live := fun t => if t = token then outputPreimages ++ before.live t else before.live t,
        spent := spent',
        preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub) }
  | some c =>
    ∃ (w : TransactOwnedWitness 1 outputPreimages.length)
      (pub : TransactOwnedPublic 1 outputPreimages.length)
      (hM : outputPreimages.length ≤ 4) (hC : OwnedConstrained w pub)
      (rest : List CommitmentPreimage) (spent' : NullifierSet) (newRoot : Nat)
      (hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)),
      self = addressOf pub.ownerField ∧
      w.token = token ∧
      ownedNewNotes w = outputPreimages ∧
      commitment (npk pub.ownerField (w.randomIn 0)) w.token (w.valueIn 0) = c ∧
      pub.merkleRoot ∈ before.roots ∧
      removeAll (before.live token) (ownedSpentNotes pub w) = some rest ∧
      markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
      after = { before with
        live := fun t => if t = token then outputPreimages ++ rest else before.live t,
        spent := spent',
        preimageOf := applyRecords before.preimageOf (ownedOutputRecords w pub) }

end ArmadaLean.Adjudicator
