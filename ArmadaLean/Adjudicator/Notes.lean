/-
  ArmadaLean.Adjudicator.Notes — the Armada layer: the adjudicator's money
  is pool notes, not a raw balance.

  The pool itself — its state, its `shield`/`transact`/`transactOwned` steps
  and their safety theorems (the core invariant, no double spend, preimage
  consistency) — now lives in the root `ArmadaLean.Pool`/`ArmadaLean.
  PoolSafety` modules (branch `pool-model`). The adjudicator is an ORDINARY
  caller of that pool: it defines no pool state, no live-note ledger and no
  preimage registry of its own. `AdjudicatorState` (`State.lean`) embeds
  `ArmadaLean.PoolState` directly.

  `DepositStep` and `PoolOwnedSpendStep` below name the TWO call shapes the
  adjudicator uses, each an instance of the pool's own bookkeeping
  (`removeAll`, `markSpent`, `applyRecords`, `hashCommitment` — all
  `ArmadaLean.Pool`): a deposit is the pool's `transact` (base `Transact`
  circuit, EdDSA-signed by the depositor) with one output disclosed as
  adjudicator-owned; a payout is the pool's `transactOwned` (owned circuit,
  `ArmadaLean.TransactOwned`/`ArmadaLean.PoolOwned`), nullifying the
  channel's old collateral and minting the payout notes. Naming the exact
  spent note by its own preimage (not by a derived hash the pool computes a
  different way) fixes the gap the previous model had: `removeAll` matches
  a note by its own `CommitmentPreimage` value, the same value the
  circuit's own Merkle-membership check already names, never by an
  unrelated derived quantity (the former model's bug, matching a nullifier
  value instead of the spent note's own commitment). -/
import ArmadaLean.PoolSafety

namespace ArmadaLean.Adjudicator

/-- `c` is currently a live (unspent) note of some token: the pool's own
    ghost bookkeeping (`PoolState.live`, `Pool.lean`) records a preimage
    for it. The adjudicator-level reading of "a channel's holding is a
    note the pool still backs" (replaces the former model's own
    `PoolState.isLive`, now that the pool's live-note ledger is
    `ArmadaLean.PoolState.live` itself). -/
def PoolIsLive (s : PoolState) (c : Nat) : Prop :=
  ∃ t pre, pre ∈ s.live t ∧ hashCommitment pre = c

/-!
## Deposit: a plain, EdDSA-signed spend with one contract-owned output

Matches `ArmadaLean.Step.transact` (`Pool.lean`) with `unshieldValue := 0`:
a plain transfer, naming which one of its (possibly several) new notes is
the adjudicator's own. `npk` derivation reuses `ArmadaLean.TransactOwned`'s
own formula, `npk[i] = Poseidon(ownerField, randomIn[i])`
(`TransactOwned.circom:66-70`) — the same derivation `transactOwned`'s
owner uses. -/

/-- One adjudicator-funding `pool.transact` call: the depositor's own
    `N`-note, EdDSA-signed spend (`ArmadaLean.Constrained`, the base
    circuit — deposit's signer is the depositing user, not the
    adjudicator), with one of its `M` outputs disclosed as a preimage
    owned by `self` (the adjudicator), on `token`, worth `amount`. Every
    other output (private change) is also recorded, matching
    `ArmadaLean.Step.transact`'s own effect: all `M` outputs join the
    pool's live set, not only the adjudicator's own. -/
def DepositStep {N M : Nat} (before : PoolState) (self token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (after : PoolState) : Prop :=
  Constrained w pub ∧
  (∃ r, w.npkOut idx = npk self r) ∧
  pub.commitmentsOut idx = commitment (w.npkOut idx) token amount ∧
  before.emergencyPaused = false ∧
  before.withdrawOnlyMode = false ∧
  (∃ root ∈ before.roots, ∀ i,
    merkleRoot
      (commitment (npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i))
        w.token (w.valueIn i))
      (w.pathElements i) = root) ∧
  (∃ rest,
    removeAll (before.live w.token)
      (List.ofFn fun i : Fin N =>
        (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i), w.token, w.valueIn i⟩ :
          CommitmentPreimage))
      = some rest ∧
    ∃ spent', markSpent before.spent (List.ofFn (nullifier w.nullifyingKey ∘ w.leavesIndices)) = some spent' ∧
    after = { before with
      live := fun t => if t = w.token then
          (List.ofFn fun j : Fin M => (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)) ++ rest
        else before.live t,
      spent := spent',
      preimageOf := applyRecords before.preimageOf
        ((List.ofFn fun j : Fin M => (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage)).map
          fun p => (hashCommitment p, p)) })

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
