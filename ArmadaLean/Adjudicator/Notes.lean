/-
  ArmadaLean.Adjudicator.Notes — the Armada layer: the adjudicator's money
  is pool notes, not a raw balance.

  No S1-S4 paper covers this file. Its source is the Armada design: the
  owned-note spend circuit (`armada-circuits/src/operations/
  TransactOwned.circom`), the pool contract's owned path
  (`armada-poc/contracts/privacy-pool/{modules/TransactModule.sol,
  PrivacyPool.sol}`), and the lab book
  (`armada-laconic/labbook/2026-10-18-contract-owned-notes-and-zk-channel-
  apps.md`). Every definition below reuses the pool primitives already
  proven in the root `ArmadaLean` modules (`Poseidon`, `Nullifier`,
  `Merkle`, `Transact`, `ValueConservation`) — per the brief, "The
  adjudicator model uses these notes, commitments and nullifiers. It does
  not define new ones." `State.lean` embeds `PoolState` inside the full
  adjudicator state; `Operations.lean` calls the relations this file
  defines.
-/
import ArmadaLean.Transact

namespace ArmadaLean.Adjudicator

/-!
## The pool's core invariant

Lab book §3a (`labbook/2026-10-18-contract-owned-notes-and-zk-channel-
apps.md`): "The pool's core invariant is that value in the pool exists
only as notes: every token the pool holds backs exactly one unspent note,
and the only moves are shield, transact and unshield (ruling
2026-10-22T09:42:09Z)."

Lab book decision 9: "The adjudicator owns its channel collateral as
notes, so the collateral never leaves the pool and there is no public
`deposit` path, no raw-transfer surplus, and no `sweep`."

This model therefore gives the adjudicator exactly one way to touch value:
spend/mint through the pool's `transact`/`transactOwned` entry points. It
never credits a raw balance and never calls the pool's `shield`/`unshield`
directly (decision 9's "no public `deposit` path"). `Safety.lean`'s
`notedValue_conserved` is the Lean statement of the quoted invariant for
every operation this adjudicator performs.
-/

/-- A note's plaintext preimage: the fields the pool's `CommitmentPreimage`
    carries (`IArmadaPool.sol:20-24`) for a note this model always treats
    as `TokenType.ERC20` (the only type the adjudicator's `isAsset`/
    `configuredAssets` list admits, `ArmadaNitroAdjudicator.sol`). `npk` and
    `value` match the root pool model's fields exactly; `token` is reused
    unchanged from `ArmadaLean.Transact.TransactWitness.token`. -/
structure NotePreimage where
  npk : Nat
  token : Nat
  value : Nat

/-- The pool's live-note ledger: which commitments are currently unspent,
    each paired with the preimage the pool recorded when it minted that
    commitment (lab book decision 3: "the creator publishes the preimage in
    the creating transaction"; `IArmadaPool.preimageOf`). `usedNullifiers`
    is the pool's separate double-spend record — a nullifier is a function
    of the spender's key and the leaf index (`ArmadaLean.nullifier`), not
    of the commitment, so it is tracked apart from `liveNotes`. -/
structure PoolState where
  liveNotes : List (Nat × NotePreimage)
  usedNullifiers : List Nat

/-- `c` is currently a live (unspent, preimage-known) note. -/
def PoolState.isLive (s : PoolState) (c : Nat) : Prop :=
  ∃ pre, (c, pre) ∈ s.liveNotes

/-- The pool's recorded preimage for `c`, read live and never cached
    (`IArmadaPool.preimageOf`; N1a brief S2: "it returns... else
    `pool.preimageOf(holdings[asset][channelId]).value`"; husband-review
    note on N1a: "`heldValue` never trusts a value the pool did not
    attest"). -/
def PoolState.preimageOf (s : PoolState) (c : Nat) : Option NotePreimage :=
  (s.liveNotes.find? (fun p => p.1 == c)).map Prod.snd

/-- The pool's own record of how much of `token` sits behind live notes
    right now: the sum of every live note's value for that token (lab book
    §3a's "every token the pool holds backs exactly one unspent note",
    quoted above, read as a sum). -/
def PoolState.notedValue (s : PoolState) (token : Nat) : Nat :=
  listSum ((s.liveNotes.filter (fun p => p.2.token = token)).map (fun p => p.2.value))

/-!
## The owned-spend circuit (`TransactOwned.circom`)

Mirrors `armada-circuits/src/operations/TransactOwned.circom` exactly,
which itself states what it changes from the base circuit: "A Transact
variant for a note owned by a contract instead of a user keypair... npk[i]
= Poseidon(ownerField, randomIn[i]) replaces the master-public-key
derivation in Transact.circom... nullifier = Poseidon(ownerField,
leafIndex)" (`TransactOwned.circom:1-24,89-97`). The commitment and
nullifier formulas are therefore EXACTLY `ArmadaLean.commitment` and
`ArmadaLean.nullifier`, reused unchanged — only the key that feeds them
(`ownerField` instead of a signed master public key) differs, so this
model defines no new hash use.

Lab book decision 1: "A Safe can own shielded notes through a `Transact`
variant that derives the note keys from a public `owner` address and
disables the EdDSA check, because the hook already exists at
`Transact.circom:158`." Decision 2: "The pool authorizes a contract-owned
spend by `msg.sender == owner`... because the contract holds no spending
key" (`IArmadaPool.transactOwned`'s doc comment: "the pool checks
`msg.sender == owner`... Callable only by the owning contract."). This
model's `OwnedConstrained.ownerMatches` field is that check.
-/

/-- Witness of the `TransactOwned` circuit (`TransactOwned.circom:42-53`).
    Same shape as `ArmadaLean.Transact.TransactWitness`, minus the spending
    key/signature fields `TransactOwned.circom` drops (no EdDSA), plus
    `ownerField` in their place. -/
structure OwnedWitness (N M : Nat) where
  token : Nat
  ownerField : Nat
  randomIn : Fin N → Nat
  valueIn : Fin N → Nat
  pathElements : Fin N → List (Nat × Bool)
  leavesIndices : Fin N → Nat
  npkOut : Fin M → Nat
  valueOut : Fin M → Nat

/-- Public inputs of `TransactOwned` (`TransactOwned.circom:10`: "Public
    inputs: [merkleRoot, boundParamsHash, nullifiers[N], commitmentsOut[M],
    ownerField]" — matching exactly what `PrivacyPool.verifyOwned` builds,
    `PrivacyPool.sol:577-590`: "`inputs = [merkleRoot, boundParamsHash,
    nullifiers..., commitments..., ownerField]`"). The circuit's two public
    OUTPUTS, `npk[N]` and `transcriptHash`, are not modeled as separate
    fields: `verifyOwned`'s own `inputs` array (the ground truth for what
    this model checks) has no room for them (`uint256[](3 + nullifiersLength
    + commitmentsLength)`), so they carry no content this adjudicator layer
    reads. -/
structure OwnedPublic (N M : Nat) where
  merkleRoot : Nat
  boundParamsHash : Nat
  nullifiers : Fin N → Nat
  commitmentsOut : Fin M → Nat
  ownerField : Nat

/-- The full constraint system of `TransactOwned` (`TransactOwned.circom:
57-148`), mirroring `ArmadaLean.Transact.Constrained`'s structure field for
field. -/
structure OwnedConstrained {N M : Nat} (w : OwnedWitness N M)
    (pub : OwnedPublic N M) : Prop where
  /-- Every Merkle path has the production depth 16
      (`TransactOwned.circom:48,79`). -/
  pathLen : ∀ i, (w.pathElements i).length = 16
  /-- The circuit's public `ownerField` input is the witness's own
      (`TransactOwned.circom:36,68`; "the pool checks `msg.sender ==
      owner`", `IArmadaPool.transactOwned`'s doc comment, lab book
      decision 2). -/
  ownerMatches : pub.ownerField = w.ownerField
  /-- 1a-1c: each input note's commitment opens to the public root along
      its path (`TransactOwned.circom:66-87`). Reuses `ArmadaLean.npk`/
      `commitment`/`merkleRoot` unchanged (no new notes or commitments). -/
  merkle : ∀ i,
    merkleRoot
      (commitment (npk w.ownerField (w.randomIn i)) w.token (w.valueIn i))
      (w.pathElements i) = pub.merkleRoot
  /-- 1d: nullifier derivation, `nullifier = Poseidon(ownerField,
      leafIndex)` (`TransactOwned.circom:89-97`). Reuses `ArmadaLean.
      nullifier` unchanged — it is already exactly this formula with `nk :=
      ownerField`. -/
  nullifiers : ∀ i, pub.nullifiers i = nullifier w.ownerField (w.leavesIndices i)
  /-- 2: output commitments (`TransactOwned.circom:100-109`). -/
  outputs : ∀ j, pub.commitmentsOut j = commitment (w.npkOut j) w.token (w.valueOut j)
  /-- 3 (inputs/outputs): every value passes `Num2Bits(120)`
      (`TransactOwned.circom:112-121`). -/
  rangeIn : ∀ i, RangeChecked120 (w.valueIn i)
  rangeOut : ∀ j, RangeChecked120 (w.valueOut j)
  /-- 3: value conservation, checked in the field
      (`TransactOwned.circom:123-135`; same `sumIn === sumOut` pattern as
      the base circuit). -/
  balance : fieldEq (listSum (List.ofFn w.valueIn)) (listSum (List.ofFn w.valueOut))
  /-- Input notes are pairwise distinct, the same `IsEqual`-style guard the
      base circuit uses (SECURITY_REVIEW.md Finding 2 fix, reused unchanged
      — `TransactOwned.circom` has no separate distinctness block, but the
      pool's shared Merkle-tree/nullifier plumbing makes this the condition
      under which `ArmadaLean.distinct_leaves_distinct_nullifiers` applies). -/
  distinct : ∀ i j, i ≠ j → w.leavesIndices i ≠ w.leavesIndices j

/-!
## Assumption 3: an accepted proof means its constraints hold (owned
circuit)

Phase 1 brief, "Why this model exists": "that an accepted proof means its
constraints hold." `PrivacyPool.verifyOwned` (`PrivacyPool.sol:562-601`) is
the on-chain check: "Construct public inputs array... `bool validity =
Snark.verify(verifyingKey, _transaction.proof, inputs);`... return
validity." The adjudicator never inspects a proof itself — the same
abstraction `ArmadaLean.EdDSAVerify` already uses for a signature
(`Transact.lean:29`), one level further removed (a Groth16 verifier accepts
or rejects; this model does not model the verifier's arithmetic, only that
accepting implies a satisfying witness existed). -/

/-- An opaque fact: "some Groth16 proof the caller supplied verifies
    against this public-input vector under the pool's owned verifying key"
    (`PrivacyPool.verifyOwned`, quoted above). -/
axiom OwnedProofAccepted : {N M : Nat} → OwnedPublic N M → Prop

/-- CRYPTOGRAPHIC ASSUMPTION 3 (an accepted proof means its constraints
    hold) — assumed, not proven. Groth16 soundness for the owned
    verifying-key set: a caller cannot make `verifyOwned` accept a
    public-input vector no witness satisfies (`PrivacyPool.sol:562-601`;
    `TransactOwned.circom`, full file). Every theorem about a `pool.
    transactOwned` call takes this as a hypothesis on the call's
    `OwnedProofAccepted` fact, never on a witness a caller merely asserts. -/
axiom ownedProof_sound {N M : Nat} (pub : OwnedPublic N M) :
    OwnedProofAccepted pub → ∃ w : OwnedWitness N M, OwnedConstrained w pub

/-!
DEPARTURE (`departures-found.md` item 6, "Zero proof"): the current
`PoolSpend.mintOwnedCommitments` (`src/armada/libraries/PoolSpend.sol:
38-76`) passes a hard-coded zero `SnarkProof` to `pool.transactOwned`
instead of a real proof, so `OwnedProofAccepted` never genuinely holds for
the current code's calls outside `testingMode`. This model requires
`OwnedProofAccepted` for every mint (`PoolOwnedSpendStep` below) because
that is what the CORRECT design must do; the current code's zero-proof
shortcut is exactly the bug the departures report, not a rule this model
follows. This note has no Lean binding: it records why `ownedProof_sound`
above is still the right axiom to state, not a weaker one that would
excuse the current code's shortcut.
-/

/-!
## One `transactOwned` spend: nullify at most one owned note, mint fresh
ones

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
`npk` can never be proven spendable through the owned circuit (assumption
1, hash non-invertibility, makes finding a matching `random` infeasible),
so the current code's remainder and reclaim notes are stuck. This model's
`PoolOwnedSpendStep` requires the CORRECT derivation, matching the circuit. -/

/-- One adjudicator-initiated `pool.transactOwned` call: nullifies at most
    one of the adjudicator's own previously-owned commitments and mints one
    fresh commitment per `outputPreimages` entry, with each output's
    commitment computed by the pool's own hash (`PoolSpend.hashCommitment`,
    `PoolSpend.sol:48-57`: "mirrors `TransactModule._hashCommitment`").
    Requires an accepted owned proof (assumption 3) binding exactly this
    nullifier/output shape under `ownerField = self`. -/
def PoolOwnedSpendStep (before : PoolState) (self token : Nat)
    (nullifiedCommitment : Option Nat) (outputPreimages : List NotePreimage)
    (after : PoolState) : Prop :=
  (∀ pre ∈ outputPreimages, pre.token = token) ∧
  (match nullifiedCommitment with
    | none => True
    | some c => before.isLive c) ∧
  (∃ N : Nat, ∃ pub : OwnedPublic N outputPreimages.length,
    pub.ownerField = self ∧
    OwnedProofAccepted pub ∧
    (∀ j : Fin outputPreimages.length,
      pub.commitmentsOut j = commitment (outputPreimages.get j).npk token (outputPreimages.get j).value) ∧
    N = (if nullifiedCommitment.isSome then 1 else 0) ∧
    (∀ _hc : nullifiedCommitment.isSome = true,
      ∃ i : Fin N, ∃ w : OwnedWitness N outputPreimages.length, OwnedConstrained w pub ∧
        commitment (npk self (w.randomIn i)) token (w.valueIn i) = nullifiedCommitment.getD 0)) ∧
  after.liveNotes = (before.liveNotes.filter (fun p => nullifiedCommitment ≠ some p.1)) ++
    (outputPreimages.map (fun pre => (commitment pre.npk token pre.value, pre)))

/-!
## Deposit: a plain, EdDSA-signed spend with one contract-owned output

N2a brief point 1: "A `transact` output can be contract-owned: the caller
supplies the output's full `CommitmentPreimage` in the clear... the pool
checks `commitments[i] == poseidon(preimage)` with `preimage.npk` derived
from a public `owner` address, and the pool stores `preimageOf[
commitments[i]] = preimage`... The input side of the transaction is
unchanged: a normal user note, spent with the user's own EdDSA signature.
Only the output is contract-owned." This is the BASE `Transact` circuit
(`ArmadaLean.Transact`, already proven in the root model), not
`TransactOwned` — deposit's signer is the depositing user, not the
adjudicator, so it cannot fit `PoolOwnedSpendStep` above (which requires
`ownerField = self` on every input). -/

/-- N2a (intended design — see the departures report for how the CURRENT
    `depositFromNote` differs): a deposit is a `Transact.Constrained`
    transaction (root pool model, EdDSA-signed by the depositor) whose
    output at `idx` is disclosed as a `NotePreimage` owned by `self` (the
    adjudicator), on `token`, worth `amount`. `npk` derivation reuses
    `TransactOwned.circom`'s formula (N2a brief point 1: "`preimage.npk`
    derived from a public `owner` address... same derivation P2 defines for
    `transactOwned`'s owner"). -/
def DepositTransacted {N M : Nat} (self token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M)
    (idx : Fin M) : Prop :=
  Constrained w pub ∧
  (∃ r, w.npkOut idx = npk self r) ∧
  pub.commitmentsOut idx = commitment (w.npkOut idx) token amount

/-- The pool-state effect of a deposit: the depositor's spent input notes
    leave `liveNotes`, and EVERY output of the transaction joins it (N2a
    S2: "After `pool.transact(transactions)` returns, require `pool.
    preimageOf(newCommitment).value == amount`... then set `holdings[asset][
    channelId] = newCommitment`"). All `M` outputs are recorded, not only
    the deposit output at `idx`: a plain `transact` may return private
    change to the depositor alongside the one contract-owned output
    (`Constrained` places no bound on `M`), and dropping those change
    outputs would make this model under-count the pool's own `notedValue`
    after a deposit (`Safety.lean`'s `notedValue_conserved`). -/
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
      (pub.commitmentsOut j, (⟨w.npkOut j, w.token, w.valueOut j⟩ : NotePreimage)))

end ArmadaLean.Adjudicator
