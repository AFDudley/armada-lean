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
  adjudicator uses. `DepositStep` now requires `ArmadaLean.Pool.Step`
  itself — a real `transact` transition the pool model already proves
  conserves value and spends only owned notes (`transact_balance`,
  `transact_spends_only_owned`) — and adds only the adjudicator's OWN
  condition on top: one of the resulting live notes is adjudicator-owned,
  on the deposit's token, worth the deposit's amount. The adjudicator
  states no witness, no shape bound and no removal/balance logic of its
  own for `.deposit`; the pool step already supplies all three.
  `PoolOwnedSpendStep` (the owned path `.transfer` uses) is unchanged from
  the prior revision: contract-owned notes are a pool feature the
  adjudicator calls exactly as any other owning contract would, and its
  own shape (nullifying at most one note, minting a caller-named list) was
  never the unbounded-witness problem `DepositStep` had. -/
import ArmadaLean.PoolSafety

namespace ArmadaLean.Adjudicator

/-- `c` is currently a live (unspent) note of some token: the pool's own
    ghost bookkeeping (`PoolState.live`, `Pool.lean`) records a preimage
    for it. The adjudicator-level reading of "a channel's holding is a
    note the pool still backs". -/
def PoolIsLive (s : PoolState) (c : Nat) : Prop :=
  ∃ t pre, pre ∈ s.live t ∧ hashCommitment pre = c

/-!
## Deposit: the pool's own `transact`, with one adjudicator-owned output

`DepositStep` requires `ArmadaLean.Pool.Step before after` directly: a real
`transact` transition, with a real `Constrained` witness obeying the
registered circuit shapes (`N ≤ 8`, `M ≤ 4`, `Pool.lean`'s `Step.transact`),
value-conserving by `ArmadaLean.transact_balance` and spending only notes
their deriving key's holder could produce (`ArmadaLean.
transact_spends_only_owned`) — none of this is restated here; the pool
step already proves it. The adjudicator adds only its own condition: the
deposit's output, named by its commitment `outCommitment`, is a live note
owned by `self` (`npk self r` for some randomness `r`, the same
`ArmadaLean.TransactOwned` derivation `transactOwned`'s owner uses), on
`token`, worth `amount`. -/

/-- One adjudicator-funding `pool.transact` call: a real pool `Step` (the
    depositor's own EdDSA-signed spend, re-minted into fresh outputs) in
    which the resulting live set contains an adjudicator-owned note,
    `outCommitment`, of the deposit's own `(token, amount)`. -/
def DepositStep (before : PoolState) (self token amount outCommitment : Nat)
    (after : PoolState) : Prop :=
  Step before after ∧
  ∃ pre : CommitmentPreimage, (∃ r, pre.npk = npk self r) ∧ pre.token = token ∧
    pre.value = amount ∧ hashCommitment pre = outCommitment ∧ pre ∈ after.live token

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

Matches `ArmadaLean.Step.transactOwned` (`Pool.lean`): no unshield, every
output's preimage mandatory. The adjudicator's OWN entitlement to nullify
the channel's prior collateral is `ArmadaLean.owned_owner_binding`'s
argument (circuit-level: `OwnedConstrained` plus `self = addressOf
pub.ownerField`), carried here exactly as the former model carried it;
`Step.transactOwned`'s own hypotheses (not an authorization check — see
`Pool.lean`'s module comment) do not duplicate it. -/

/-- One adjudicator-initiated `pool.transactOwned` call: nullifies at most
    one of the adjudicator's own previously-owned commitments and mints one
    fresh commitment per `outputPreimages` entry. Requires the pool's OWN
    acceptance check (`ArmadaLean.VerifyOwnedAccepts`) and its OWN
    owner-authorization convention (`self = ArmadaLean.addressOf
    pub.ownerField`, matching `ArmadaLean.owned_owner_binding`'s `caller =
    addressOf ownerField`) — the adjudicator supplies no mechanism of its
    own. `removeAll` (`Pool.lean`) removes the nullified note by its own
    preimage value, matching the Merkle-membership fact
    `OwnedConstrained.merkle` already names. -/
def PoolOwnedSpendStep (before : PoolState) (self token : Nat)
    (nullifiedCommitment : Option Nat) (outputPreimages : List CommitmentPreimage)
    (after : PoolState) : Prop :=
  (∀ pre ∈ outputPreimages, pre.token = token) ∧
  before.emergencyPaused = false ∧
  before.withdrawOnlyMode = false ∧
  match nullifiedCommitment with
  | none =>
    ∃ (pub : TransactOwnedPublic 0 outputPreimages.length),
      self = addressOf pub.ownerField ∧
      VerifyOwnedAccepts pub ∧
      (∀ j, pub.commitmentsOut j = commitment (outputPreimages.get j).npk token (outputPreimages.get j).value) ∧
      markSpent before.spent (List.ofFn pub.nullifiers) = some before.spent ∧
      after = { before with
        live := fun t => if t = token then outputPreimages ++ before.live t else before.live t,
        preimageOf := applyRecords before.preimageOf
          (outputPreimages.map fun pre => (commitment pre.npk token pre.value, pre)) }
  | some c =>
    ∃ (pub : TransactOwnedPublic 1 outputPreimages.length)
      (w : TransactOwnedWitness 1 outputPreimages.length) (root : Nat), root ∈ before.roots ∧
      self = addressOf pub.ownerField ∧
      VerifyOwnedAccepts pub ∧
      (∀ j, pub.commitmentsOut j = commitment (outputPreimages.get j).npk token (outputPreimages.get j).value) ∧
      OwnedConstrained w pub ∧
      merkleRoot (commitment (npk pub.ownerField (w.randomIn 0)) token (w.valueIn 0)) (w.pathElements 0) = root ∧
      commitment (npk pub.ownerField (w.randomIn 0)) token (w.valueIn 0) = c ∧
      (∃ rest, removeAll (before.live token)
          [(⟨npk pub.ownerField (w.randomIn 0), token, w.valueIn 0⟩ : CommitmentPreimage)] = some rest ∧
        ∃ spent', markSpent before.spent (List.ofFn pub.nullifiers) = some spent' ∧
          after = { before with
            live := fun t => if t = token then outputPreimages ++ rest else before.live t,
            spent := spent',
            preimageOf := applyRecords before.preimageOf
              (outputPreimages.map fun pre => (commitment pre.npk token pre.value, pre)) })

end ArmadaLean.Adjudicator
