/-
  ArmadaLean.Adjudicator.Notes — the Armada layer: the adjudicator's money
  is pool notes, not a raw balance.

  No S1-S4 paper covers this file. Its source is the Armada design: the
  owned-note spend circuit (`armada-circuits/src/operations/
  TransactOwned.circom`), the pool contract's owned path
  (`armada-poc/contracts/privacy-pool/{modules/TransactModule.sol,
  PrivacyPool.sol}`), and the armada-nitro rule (`State.lean`'s
  `AdjudicatorState`, `holdings` field). Every definition below reuses
  the pool primitives already proven in the root `ArmadaLean` modules
  (`Poseidon`, `Nullifier`, `Merkle`, `Transact`, `ValueConservation`):
  the adjudicator model uses these notes, commitments and nullifiers,
  and defines no new ones. `State.lean` embeds `PoolState` inside the
  full adjudicator state; `Operations.lean` calls the relations this
  file defines.

  Contract-owned notes are a POOL feature, not an adjudicator feature:
  the adjudicator, the Safe, and the ragequit contract are all ORDINARY
  callers of the pool's `transactOwned` entry point, so the owned-note
  circuit model, its soundness/completeness assumptions, and its safety
  theorems live in `ArmadaLean.TransactOwned`/`ArmadaLean.PoolOwned`
  (root `ArmadaLean` modules, branch `owned-notes`), not here. This
  file now IMPORTS that model instead of duplicating it;
  `PoolOwnedSpendStep` below calls its definitions directly, the same
  way any other owning caller would.
-/
import ArmadaLean.PoolOwned

namespace ArmadaLean.Adjudicator

/-!
## The pool's core invariant

The armada-nitro rule (`State.lean`'s `AdjudicatorState`, `holdings`
field): a channel's holding is a note in the pool, owned by the
adjudicator; it is never a number the adjudicator stores.

This model therefore gives the adjudicator exactly one way to touch value:
spend/mint through the pool's `transact`/`transactOwned` entry points. It
never credits a raw balance and never calls the pool's `shield`/`unshield`
directly — the armada-nitro rule's "no public `deposit` path". Each
individual spend conserves value by the circuit's own proof —
`ArmadaLean.transact_value_conserved` (`Transact.lean`) for the base
circuit `DepositTransacted` below uses, `ArmadaLean.
transactOwned_value_conserved` (`TransactOwned.lean`) for the owned
circuit `PoolOwnedSpendStep` below uses — and `Safety.lean`'s
`notedValue_conserved` is the Lean statement that this holds across
every operation this adjudicator performs.
-/

/-- A note's plaintext preimage: the fields the pool's `CommitmentPreimage`
    carries (`IArmadaPool.sol:20-24`) for a note this model always treats
    as `TokenType.ERC20` (the only type the adjudicator's `isAsset`/
    `configuredAssets` list admits, `ArmadaNitroAdjudicator.sol`). `npk` and
    `value` match the root pool model's fields exactly; `token` is reused
    unchanged from `ArmadaLean.Transact.TransactWitness.token`. Distinct
    from `ArmadaLean.CommitmentPreimage` (`PoolOwned.lean`) — the SAME
    shape, kept as its own type here because `liveNotes` below also holds
    REGULAR (non-owned) deposit-change notes, which the pool-level type is
    not named for. -/
structure NotePreimage where
  npk : Nat
  token : Nat
  value : Nat

/-- The pool's live-note ledger: which commitments are currently unspent,
    each paired with the preimage the pool recorded when it minted that
    commitment (`IArmadaPool.preimageOf`). `ArmadaLean.PoolOwned`'s
    preimage registry (`PreimageRegistry`, `RegistryConsistent`,
    `recordPreimages`) models exactly this for the owned path;
    `ArmadaLean.preimageOf_consistent` proves every preimage the pool
    records there hashes to the commitment it is recorded for.
    `usedNullifiers`
    is the pool's separate double-spend record — a nullifier is a function
    of the spender's key and the leaf index (`ArmadaLean.nullifier`), not
    of the commitment, so it is tracked apart from `liveNotes`; it holds
    exactly the `NullifierSet` shape `ArmadaLean.markSpent`
    (`PoolOwned.lean`) reads and grows. `poolSignedBy` is the pool layer's
    own EOA signing record (the SAME kind of execution-tracked fact
    `AdjudicatorState.signedBy` is for the Nitro layer, `State.lean`):
    which `(babyjubjubPublicKey, msgHash)` pairs this execution has
    recorded a genuine EdDSA signature for. Grows only through
    `Operations.lean`'s `.signNote` `Call`, which only ever adds to the
    signing key's OWN row. -/
structure PoolState where
  liveNotes : List (Nat × NotePreimage)
  usedNullifiers : NullifierSet
  poolSignedBy : (Nat × Nat) → Nat → Prop

/-- `c` is currently a live (unspent, preimage-known) note. -/
def PoolState.isLive (s : PoolState) (c : Nat) : Prop :=
  ∃ pre, (c, pre) ∈ s.liveNotes

/-- The pool's recorded preimage for `c`, read live and never cached
    (`IArmadaPool.preimageOf`): the note's value read from the pool's
    own record, which `ArmadaLean.preimageOf_consistent`
    (`PoolOwned.lean`) proves trustworthy — never a cached or
    caller-asserted value. -/
def PoolState.preimageOf (s : PoolState) (c : Nat) : Option NotePreimage :=
  (s.liveNotes.find? (fun p => p.1 == c)).map Prod.snd

/-- The pool's own record of how much of `token` sits behind live notes
    right now: the sum of every live note's value for that token — the
    armada-nitro rule (`State.lean`) read as a sum. -/
def PoolState.notedValue (s : PoolState) (token : Nat) : Nat :=
  listSum ((s.liveNotes.filter (fun p => p.2.token = token)).map (fun p => p.2.value))

/-!
## Deposit: a plain, EdDSA-signed spend with one contract-owned output

`ArmadaLean.TransactOwned`'s own formula, `npk[i] = Poseidon(ownerField,
randomIn[i])` (`TransactOwned.circom:66-70`, `TransactOwned.lean`), is
where a note key derives from a public `owner` address; `ArmadaLean.
PoolOwned`'s preimage registry is where the creator's preimage is
published at the creating transaction. Stated directly here: a
`transact` output can be contract-owned — the caller supplies the
output's full
preimage in the clear, the pool checks `commitments[i] ==
poseidon(preimage)` with `preimage.npk` derived from a public `owner`
address, and the pool stores `preimageOf[commitments[i]] = preimage`.
The INPUT side of the transaction is unchanged: a normal user note,
spent with the user's own EdDSA signature. Only the output is
contract-owned. This is the BASE `Transact` circuit
(`ArmadaLean.Transact`, already proven in the root model), not
`TransactOwned` — deposit's signer is the depositing user, not the
adjudicator, so it uses the base circuit's own EdDSA check, not the
owned-note path `PoolOwnedSpendStep` below calls.

`Constrained w pub`'s `sig` field (`Transact.lean:119`) requires
`EdDSAVerify w.publicKey w.signature (msgHashOf pub)` — the root pool
layer's own signature check, a bare `axiom` this phase does not touch
(`Assumptions.lean`'s module comment). `EdDSAVerify` alone says nothing
about when a witness exists; `PoolSignatureLiveness.eddsaCompleteness`
below supplies the missing half, GATED on the SAME execution-tracked
fact `PoolState.poolSignedBy` records: it only fires once the depositor
has actually recorded, via `Operations.lean`'s `.signNote` `Call`, that
THIS key signed THIS message — the same unforgeability-by-construction
`.sign` uses for the Nitro layer (`Operations.lean`'s module comment,
quoting Nitro-2019-219.pdf §3.1 and ForceMove-2018.pdf §3.1.3). -/

/-- LIVENESS ASSUMPTION (EdDSA completeness, pool layer) — assumed, not
    proven. `eddsaCompleteness` says: if THIS execution has recorded
    (`PoolState.poolSignedBy`) that the holder of `pk` signed `msgHash`,
    some signature verifying under `EdDSAVerify` exists. Standard EdDSA
    completeness (any held private key can sign any message it is asked
    to) made SAFE by the gate: a caller cannot make the hypothesis true
    for a key they do not hold, because `poolSignedBy` only grows
    through `.signNote`, whose `Step` case (`Operations.lean`) only
    succeeds when the ACTOR submitting it holds `pk`. Unrelated to owned
    notes — this is the BASE circuit's own completeness, the same
    discipline `ArmadaLean.OwnedProofCompleteness` (`PoolOwned.lean`)
    follows for the owned circuit. -/
structure PoolSignatureLiveness where
  eddsaCompleteness : ∀ (s : PoolState) (pk : Nat × Nat) (msgHash : Nat),
    s.poolSignedBy pk msgHash →
    ∃ signature : Nat × Nat × Nat, EdDSAVerify pk signature msgHash

/-- Intended design (see the departures report for how the CURRENT
    `depositFromNote` differs): a deposit is a `Transact.Constrained`
    transaction (root pool model, EdDSA-signed by the depositor) whose
    output at `idx` is disclosed as a `NotePreimage` owned by `self` (the
    adjudicator), on `token`, worth `amount`. `npk` derivation reuses
    `ArmadaLean.TransactOwned`'s own formula, `npk[i] = Poseidon(
    ownerField, randomIn[i])` (`TransactOwned.circom:66-70`,
    `TransactOwned.lean`) — the same derivation for `transactOwned`'s
    owner. -/
def DepositTransacted {N M : Nat} (self token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M)
    (idx : Fin M) : Prop :=
  Constrained w pub ∧
  (∃ r, w.npkOut idx = npk self r) ∧
  pub.commitmentsOut idx = commitment (w.npkOut idx) token amount

/-- The pool-state effect of a deposit: the depositor's spent input notes
    leave `liveNotes`, and EVERY output of the transaction joins it: the
    output recorded here is the note's own preimage, which `ArmadaLean.
    preimageOf_consistent` (`PoolOwned.lean`) proves hashes to the
    commitment it is recorded for. All `M` outputs are recorded, not
    only the deposit output at `idx`: a
    plain `transact` may return private change to the depositor alongside
    the one contract-owned output (`Constrained` places no bound on `M`),
    and dropping those change outputs would make this model under-count
    the pool's own `notedValue` after a deposit (`Safety.lean`'s
    `notedValue_conserved`). -/
def DepositPoolStep {N M : Nat} (before : PoolState) (self token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M)
    (idx : Fin M) (after : PoolState) : Prop :=
  DepositTransacted self token amount w pub idx ∧
  (∀ i, before.isLive
    (commitment (npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i))
      w.token (w.valueIn i))) ∧
  after.liveNotes =
    (before.liveNotes.filter (fun p => ∀ i, p.1 ≠ nullifier w.nullifyingKey (w.leavesIndices i))) ++
    List.ofFn (fun j : Fin M =>
      (pub.commitmentsOut j, (⟨w.npkOut j, w.token, w.valueOut j⟩ : NotePreimage))) ∧
  after.poolSignedBy = before.poolSignedBy

/-!
## One `transactOwned` spend: nullify at most one owned note, mint fresh
ones (the adjudicator, as an ORDINARY caller of `ArmadaLean.PoolOwned`)

`PoolSpend.sol`'s own doc comment names what this function must do:
"`mintOwnedCommitments`: submit one `pool.transactOwned` transaction that
nullifies `nullifiers` (0 or 1 entries here) and mints one fresh owned
commitment per `outputs` entry" (`PoolSpend.sol:34-39`). This model's
version derives every self-owned output's `npk` as `npk self r` for a
fresh `r` — DEPARTURE (`departures-found.md` item 4, "Wrong `npk`"): the
current code instead uses the raw adjudicator address as `npk` directly
(`ArmadaNitroAdjudicator.sol:106,125`; `PoolSpend.sol`'s `settleReclaim`
and `notePreimage`), which does not match `TransactOwned.circom:66-70`'s
`npk = Poseidon(ownerField, random)`. A note minted with a raw address as
`npk` can never be proven spendable through the owned circuit (`ArmadaLean
.commitment_owner_inj`'s collision-resistance premise makes finding a
matching `random` infeasible), so the current code's remainder and
reclaim notes are stuck. This model's `PoolOwnedSpendStep` requires the
CORRECT derivation, matching the circuit.

DEPARTURE (`departures-found.md` item 6, "Zero proof"): the current
`PoolSpend.mintOwnedCommitments` (`src/armada/libraries/PoolSpend.sol:
38-76`) passes a hard-coded zero `SnarkProof` to `pool.transactOwned`
instead of a real proof, so `ArmadaLean.VerifyOwnedAccepts` genuinely
never holds for the current code's calls outside `testingMode`. This
model requires a `VerifyOwnedAccepts` witness for every mint
(`PoolOwnedSpendStep` below) because that is what the CORRECT design
must do; the current code's zero-proof shortcut is exactly the bug the
departures report, not a rule this model follows. -/

/-- One adjudicator-initiated `pool.transactOwned` call: nullifies at most
    one of the adjudicator's own previously-owned commitments and mints one
    fresh commitment per `outputPreimages` entry, with each output's
    commitment computed by the pool's own hash (`ArmadaLean.hashCommitment`,
    `PoolSpend.sol:48-57`: "mirrors `TransactModule._hashCommitment`").
    Requires the pool's OWN acceptance check (`ArmadaLean.
    VerifyOwnedAccepts`, `PoolOwned.lean`) and its OWN owner-authorization
    convention (`self = ArmadaLean.addressOf pub.ownerField`, matching
    `ArmadaLean.owned_owner_binding`'s `caller = addressOf ownerField`) —
    the adjudicator supplies no mechanism of its own; it calls the pool's
    rule exactly as any other owning contract (the Safe, the ragequit
    contract) would. `markSpent` (`PoolOwned.lean`) threads
    `usedNullifiers` through the SAME freshness check
    `ArmadaLean.owned_no_double_spend` proves sound. -/
def PoolOwnedSpendStep (before : PoolState) (self token : Nat)
    (nullifiedCommitment : Option Nat) (outputPreimages : List NotePreimage)
    (after : PoolState) : Prop :=
  (∀ pre ∈ outputPreimages, pre.token = token) ∧
  (match nullifiedCommitment with
    | none => True
    | some c => before.isLive c) ∧
  (∃ N : Nat, ∃ pub : TransactOwnedPublic N outputPreimages.length,
    self = addressOf pub.ownerField ∧
    VerifyOwnedAccepts pub ∧
    (∀ j : Fin outputPreimages.length,
      pub.commitmentsOut j = commitment (outputPreimages.get j).npk token (outputPreimages.get j).value) ∧
    N = (if nullifiedCommitment.isSome then 1 else 0) ∧
    (∀ _hc : nullifiedCommitment.isSome = true,
      ∃ (w : TransactOwnedWitness N outputPreimages.length) (i : Fin N),
        OwnedConstrained w pub ∧
        commitment (npk pub.ownerField (w.randomIn i)) token (w.valueIn i) =
          nullifiedCommitment.getD 0) ∧
    markSpent before.usedNullifiers (List.ofFn pub.nullifiers) = some after.usedNullifiers) ∧
  after.liveNotes = (before.liveNotes.filter (fun p => nullifiedCommitment ≠ some p.1)) ++
    (outputPreimages.map (fun pre => (commitment pre.npk token pre.value, pre))) ∧
  after.poolSignedBy = before.poolSignedBy

end ArmadaLean.Adjudicator
