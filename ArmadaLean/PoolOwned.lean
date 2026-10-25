/-
  ArmadaLean.PoolOwned — the pool contract's owned path and its storage.

  Models `TransactModule.transactOwned` (armada-poc
  contracts/privacy-pool/modules/TransactModule.sol:488-519) and the state it
  reads and writes: `PrivacyPoolStorage.nullifiers` (:174), `PrivacyPoolStorage
  .preimageOf` (:248), and `PrivacyPool.verifyOwned` (PrivacyPool.sol:562-601).
  Imports `ArmadaLean.TransactOwned` and builds on `OwnedConstrained` — "the
  accepted proof's witness satisfies every circuit constraint" is the named
  hypothesis every theorem below takes (the brief's soundness assumption:
  Poseidon cannot be inverted or collided — modeled symbolically,
  `ArmadaLean.Poseidon` — and an accepted proof means its circuit constraints
  hold). Only `owned_spend_can_happen` additionally takes an explicit
  `OwnedProofCompleteness` hypothesis, the converse assumption.

  Theorems proved here:
  * `owned_owner_binding` — no one except the owning contract can spend its
    note (TransactModule.sol:636-639, the `msg.sender == ownerField` check).
  * `owned_no_double_spend` — no note is spent twice
    (`_accumulateAndNullify`, TransactModule.sol:379-386).
  * `preimageOf_consistent` — every preimage the pool records hashes to the
    commitment it is recorded for (`_recordPreimages`, TransactModule.sol
    :590-604, gated by `_validatePublicOutputs`, :550-578).
  * `owned_spend_can_happen` — an owned spend by the real owner, with an
    accepted proof, succeeds.

  DEPARTURE (decision 2 of labbook/2026-10-18-contract-owned-notes-and-zk-
  channel-apps.md, recorded as open in its §3a): the design called for a
  public `balance[owner]` registry. The merged code never builds one;
  `preimageOf` (below) is what actually gives a caller the data decision 2
  wanted — one entry per commitment, not a running balance. `preimageOf_
  consistent` is the guarantee that entry is trustworthy.
-/
import ArmadaLean.TransactOwned

/-- EVM address truncation: `address(uint160(x))`
    (TransactModule.sol:637, `_validateOwnedTransaction`'s authorization
    check). An address is a raw `Nat`, never a hash term. -/
def addressOf (x : Nat) : Nat := x % 2 ^ 160

/-- The data committed into a Merkle leaf for a contract-owned output
    (`PoolTypes.sol:79-83`, `struct CommitmentPreimage`). `npk` is a term (a
    note public key); `token` abstracts `_getTokenID(token)` the same way
    `TransactOwnedWitness.token` does (ArmadaLean.TransactOwned), and `value`
    is the note value — both raw numbers, never hashed by this preimage
    itself. -/
structure CommitmentPreimage where
  npk : Term
  token : Nat
  value : Nat
  deriving DecidableEq

/-- `_hashCommitment` (TransactModule.sol:441-443, ShieldModule.sol:376-378):
    `PoseidonT4.poseidon([npk, tokenID, value])`, the same 3-argument
    Poseidon as `commitment` in ArmadaLean.Transact — reused directly, no
    second commitment hash is defined here. -/
def hashCommitment (pre : CommitmentPreimage) : Term := commitment pre.npk pre.token pre.value

/-- An output that stays ciphertext-only carries an all-zero preimage
    (`_isZeroPreimage`, TransactModule.sol:582-585) and is skipped by
    `_recordPreimages`. The real contract compares the raw stored `npk`
    field to the literal `bytes32(0)`; the symbolic equivalent is comparing
    the term to `Term.val 0`, the raw-value embedding of that same literal —
    a genuine Poseidon output (`Term.hash ...`) can never equal `Term.val 0`
    (`Term.val_ne_hash`), so this sentinel can only ever be set deliberately,
    exactly as in the real contract, never hit by coincidence. -/
def isZeroPreimage (pre : CommitmentPreimage) : Prop :=
  pre.npk = Term.val 0 ∧ pre.value = 0 ∧ pre.token = 0

instance (pre : CommitmentPreimage) : Decidable (isZeroPreimage pre) := by
  unfold isZeroPreimage; infer_instance

/-! ### `verifyOwned` acceptance (PrivacyPool.sol:562-601)

Soundness — "an accepted proof's witness satisfies `OwnedConstrained`" — is
the hypothesis every theorem below already takes directly as
`OwnedConstrained w pub`, exactly as `ArmadaLean.Transact` takes `Constrained
w pub`. The reverse direction, completeness, is a separate assumption used
only by `owned_spend_can_happen`. -/

/-- `VerifyOwnedAccepts pub` holds iff some Groth16 proof over `pub`'s public
    inputs makes `PrivacyPool.verifyOwned` return `true`
    (PrivacyPool.sol:562-601). Left abstract: this model does not represent
    Groth16 proof objects, the same way `EdDSAVerify` is left abstract in
    ArmadaLean.Transact. -/
axiom VerifyOwnedAccepts : {N M : Nat} → TransactOwnedPublic N M → Prop

/--
Groth16 completeness, named as an explicit hypothesis rather than a global
axiom: for a witness/public pair that together satisfy every TransactOwned
.circom constraint (`OwnedConstrained`), a prover can build a proof that
`PrivacyPool.verifyOwned` accepts. This is the converse of soundness: the
owned verifying-key set never rejects a real satisfying witness.
`owned_spend_can_happen` takes one instance of this record as an explicit
argument, so the assumption is visible at its call site and nowhere else —
no other theorem in this file can reach for it. -/
structure OwnedProofCompleteness where
  complete : ∀ {N M : Nat} {w : TransactOwnedWitness N M} {pub : TransactOwnedPublic N M},
    OwnedConstrained w pub → VerifyOwnedAccepts pub

/-! ### Owner binding (TransactModule.sol:636-639) -/

/--
**Owner binding**: no one except the owning contract can spend its note.

Take a note truly created for owner `trueOwner` with randomness
`trueRandom` (its commitment is `commitment (npk (Term.val trueOwner)
trueRandom) token value`, by construction — ArmadaLean.TransactOwned's
`outputs` field, read at the transaction that minted it). If an accepted
owned spend's input `i` opens the same commitment value (`hSameNote`),
`commitment_owner_inj` forces its `ownerField` to equal `trueOwner`; the
pool's own authorization check (`msg.sender ==
address(uint160(uint256(ownerField)))`, TransactModule.sol:636-639, `hAuth`)
then forces the caller to be `addressOf trueOwner`. A caller that is not the
owning contract can never satisfy both, so it can never produce an accepted
spend of that note. -/
theorem owned_owner_binding {N M : Nat} {w : TransactOwnedWitness N M}
    {pub : TransactOwnedPublic N M} (_h : OwnedConstrained w pub) (i : Fin N)
    {trueOwner trueRandom : Nat}
    (hSameNote :
      commitment (npk (Term.val pub.ownerField) (w.randomIn i)) w.token (w.valueIn i) =
      commitment (npk (Term.val trueOwner) trueRandom) w.token (w.valueIn i))
    {caller : Nat} (hAuth : caller = addressOf pub.ownerField) :
    caller = addressOf trueOwner := by
  rw [hAuth, commitment_owner_inj hSameNote]

/-! ### No double spend (`_accumulateAndNullify`, TransactModule.sol:379-386) -/

/-- The pool's spent-nullifier set for one Merkle tree
    (`PrivacyPoolStorage.sol:174`, `mapping(uint256 => mapping(bytes32 =>
    bool)) public nullifiers`, one tree's slice). `treeNumber` is a further
    key of the real mapping that this model elides: the freshness/
    distinctness argument below holds the same way inside any one tree.
    Nullifiers are terms. -/
abbrev NullifierSet := List Term

/-- Marking one call's nullifiers spent (`_accumulateAndNullify`,
    TransactModule.sol:379-386): each nullifier must not already be in
    `spent`; the pool reverts the whole call (`"Note already spent"`, :384)
    the first time one already is, returning `none` here. -/
def markSpent (spent : NullifierSet) : List Term → Option NullifierSet
  | [] => some spent
  | n :: ns => if n ∈ spent then none else markSpent (n :: spent) ns

/--
**No note is spent twice.** If a call's nullifier-marking succeeds
(`markSpent spent ns = some _`, i.e. the pool did not revert), the
nullifiers `ns` it just marked are pairwise distinct from each other and
none of them was already in `spent` beforehand. Applied to a whole history
of calls (each one's `spent` is the previous call's `spent'`), this is
exactly "no nullifier is ever marked twice": a note's nullifier can only
ever pass this check once, in the one call that first spends it. -/
theorem owned_no_double_spend {spent spent' : NullifierSet} {ns : List Term}
    (h : markSpent spent ns = some spent') :
    ns.Pairwise (· ≠ ·) ∧ ∀ n ∈ ns, n ∉ spent := by
  induction ns generalizing spent with
  | nil => exact ⟨List.Pairwise.nil, fun n hn => absurd hn List.not_mem_nil⟩
  | cons n ns ih =>
    unfold markSpent at h
    by_cases hn : n ∈ spent
    · rw [if_pos hn] at h
      exact absurd h (by simp)
    · rw [if_neg hn] at h
      obtain ⟨hpw, hfresh⟩ := ih h
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
      · intro a ha heq
        exact hfresh a ha (List.mem_cons.mpr (Or.inl heq.symm))
      · intro m hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact hm ▸ hn
        · exact fun hmspent => hfresh m hm (List.mem_cons_of_mem n hmspent)

/-- Converse of `owned_no_double_spend`, used by `owned_spend_can_happen`: a
    batch of pairwise-distinct, previously-unspent nullifiers always marks
    cleanly (the pool never reverts `_accumulateAndNullify` on a genuinely
    fresh batch). -/
theorem markSpent_succeeds {spent : NullifierSet} {ns : List Term}
    (hpw : ns.Pairwise (· ≠ ·)) (hfresh : ∀ n ∈ ns, n ∉ spent) :
    ∃ spent', markSpent spent ns = some spent' := by
  induction ns generalizing spent with
  | nil => exact ⟨spent, rfl⟩
  | cons n ns ih =>
    obtain ⟨ha, hpw'⟩ := List.pairwise_cons.mp hpw
    have hn : n ∉ spent := hfresh n List.mem_cons_self
    have hfresh' : ∀ m ∈ ns, m ∉ (n :: spent) := by
      intro m hm hmem
      rcases List.mem_cons.mp hmem with hmem | hmem
      · exact ha m hm hmem.symm
      · exact hfresh m (List.mem_cons_of_mem n hm) hmem
    obtain ⟨spent', hspent'⟩ := ih hpw' hfresh'
    refine ⟨spent', ?_⟩
    unfold markSpent
    rw [if_neg hn]
    exact hspent'

/-! ### Preimage consistency (`_recordPreimages`, TransactModule.sol:590-604) -/

/-- The pool's preimage registry (`PrivacyPoolStorage.sol:248`, `mapping
    (bytes32 => CommitmentPreimage) public preimageOf`): `none` means no
    preimage was ever recorded for that commitment. Keyed by commitment term. -/
abbrev PreimageRegistry := Term → Option CommitmentPreimage

/-- The registry invariant: every recorded preimage hashes to the
    commitment key it is recorded under. -/
def RegistryConsistent (reg : PreimageRegistry) : Prop :=
  ∀ c pre, reg c = some pre → hashCommitment pre = c

/-- Recording one output (TransactModule.sol:593-599): a zero preimage is
    skipped (:594-596); otherwise the registry entry at `c` becomes
    `preimage` (:598). -/
def recordStep (reg : PreimageRegistry) (c : Term) (preimage : CommitmentPreimage) :
    PreimageRegistry :=
  fun c' => if isZeroPreimage preimage then reg c' else if c' = c then some preimage else reg c'

/-- Recording every output of one transaction (`_recordPreimages`'s loop,
    TransactModule.sol:590-604), `commitments` and `publicOutputs` running
    in parallel, index for index. -/
def recordPreimages {K : Nat} (commitments : Fin K → Term)
    (publicOutputs : Fin K → CommitmentPreimage) (reg : PreimageRegistry) : PreimageRegistry :=
  (List.finRange K).foldl (fun r i => recordStep r (commitments i) (publicOutputs i)) reg

/-- A property preserved by every step of a left fold is preserved by the
    whole fold. -/
theorem foldl_preserves {α β : Type} (f : α → β → α) (P : α → Prop)
    (hstep : ∀ a b, P a → P (f a b)) : ∀ (l : List β) (a : α), P a → P (l.foldl f a)
  | [], _, ha => ha
  | b :: bs, a, ha => foldl_preserves f P hstep bs (f a b) (hstep a b ha)

theorem recordStep_preserves_consistency {reg : PreimageRegistry} (hreg : RegistryConsistent reg)
    {c : Term} {preimage : CommitmentPreimage} (hvalid : hashCommitment preimage = c) :
    RegistryConsistent (recordStep reg c preimage) := by
  intro c' pre' hc'
  unfold recordStep at hc'
  by_cases hz : isZeroPreimage preimage
  · rw [if_pos hz] at hc'
    exact hreg c' pre' hc'
  · rw [if_neg hz] at hc'
    by_cases heq : c' = c
    · rw [if_pos heq] at hc'
      cases hc'
      rw [heq]
      exact hvalid
    · rw [if_neg heq] at hc'
      exact hreg c' pre' hc'

theorem recordPreimages_preserves_consistency {K : Nat} (commitments : Fin K → Term)
    (publicOutputs : Fin K → CommitmentPreimage)
    (hvalid : ∀ i, hashCommitment (publicOutputs i) = commitments i)
    {reg : PreimageRegistry} (hreg : RegistryConsistent reg) :
    RegistryConsistent (recordPreimages commitments publicOutputs reg) := by
  unfold recordPreimages
  exact foldl_preserves (fun r i => recordStep r (commitments i) (publicOutputs i)) RegistryConsistent
    (fun r i hr => recordStep_preserves_consistency hr (hvalid i)) (List.finRange K) reg hreg

/--
**Preimage consistency**: every preimage the pool records hashes to the
commitment it is recorded for. `_validatePublicOutputs` (TransactModule.sol
:550-578) requires `hashCommitment (publicOutputs i) = commitments i` for
every non-zero entry *before* `_recordPreimages` (:590-604) ever runs
(`transactOwned`, :500-506); starting from the empty registry (deployment)
and folding every transaction ever processed through `recordPreimages`
preserves that one fact by induction, so it holds of the live `preimageOf`
mapping at every block. -/
theorem preimageOf_consistent {K : Nat} (commitments : Fin K → Term)
    (publicOutputs : Fin K → CommitmentPreimage)
    (hvalid : ∀ i, hashCommitment (publicOutputs i) = commitments i) :
    RegistryConsistent (recordPreimages commitments publicOutputs (fun _ => none)) :=
  recordPreimages_preserves_consistency commitments publicOutputs hvalid
    (fun _ _ h => by simp at h)

/-! ### Public random for a contract-owned note (`PoolTypes.sol:79-83`, `TransactModule
._recordPreimages`, TransactModule.sol:590-604, DEPARTURE)

DEPARTURE (contract, confirmed by reading the source): the merged contract's
`CommitmentPreimage` struct (`PoolTypes.sol:79-83`) has exactly three fields — `npk`,
`token`, `value` — and `_recordPreimages` (TransactModule.sol:590-604) writes exactly
that struct to `preimageOf`, nothing more. The random value behind a contract-owned
note's `npk = Poseidon(ownerField, random)` (TransactOwned.circom:66-70) is never
recorded anywhere the real contract exposes, so only the note's own creator — the one
party who chose `random` — can ever build the `TransactOwned` proof that spends it. The
approved design changes this: when a note is created for a contract owner, the creator
additionally supplies `ownerField` and `random` alongside the preimage; the pool checks
`npk (Term.val ownerField) random = npk` and records `random` (paired with `ownerField`,
so a reader can tell which owner it is claimed for) in a second, public registry. This
applies to every owned-path output (`Step.transactOwned`, mandatory, matching
`_validatePublicOutputs(requireAll = true)`'s existing mandatory disclosure) and to any
plain-`transact` output additionally disclosed as contract-owned (`Step.transact`,
optional — a deposit to the adjudicator is one such output). Any later caller who knows
its own `ownerField` can then read this registry and the ordinary `preimageOf` registry
and construct a spend witness entirely from public data
(`ArmadaLean.PoolSafety.owned_spend_witness_exists`). -/

/-- One contract-owned note's recorded random, alongside the owner it was disclosed for
    — `PoolState.ownedRandomOf`'s value type. -/
structure OwnedDisclosure where
  ownerField : Nat
  random : Nat

/-- The public registry of disclosed owned-note randoms (`PoolState.ownedRandomOf`),
    keyed by commitment, parallel to `PreimageRegistry`: `none` unless the note was
    disclosed as contract-owned. -/
abbrev OwnedRandomRegistry := Term → Option OwnedDisclosure

/-- The registry invariant: every recorded owned disclosure's random genuinely
    reconstructs the commitment's own `npk`, against the matching `preimageOf` entry —
    the pool's own check before it ever writes an entry here. -/
def OwnedRandomConsistent (reg : PreimageRegistry) (rreg : OwnedRandomRegistry) : Prop :=
  ∀ c d, rreg c = some d → ∃ pre, reg c = some pre ∧ npk (Term.val d.ownerField) d.random = pre.npk

/-- Recording one commitment's owned disclosure: unconditional overwrite at key `c`,
    mirroring `recordStep`'s shape (no zero-skip here — an `npk` built from `random`
    is always a genuine hash term, never the zero sentinel, `npk_preimage_not_zero`
    below). -/
def recordOwnedStep (rreg : OwnedRandomRegistry) (c : Term) (d : OwnedDisclosure) :
    OwnedRandomRegistry :=
  fun c' => if c' = c then some d else rreg c'

/-- A preimage whose `npk` is reconstructed from an owner field and a random value can
    never be the zero sentinel: `npk` is always `Term.hash2 ...` (a genuine Poseidon
    output), and `Term.val 0` can never equal a hash term (`Term.val_ne_hash`, by
    construction). This is what lets `recordOwnedStep` skip no owned disclosure the way
    `recordStep` skips a zero preimage. -/
theorem npk_preimage_not_zero {ownerField random : Nat} {pre : CommitmentPreimage}
    (h : npk (Term.val ownerField) random = pre.npk) : ¬ isZeroPreimage pre := by
  rintro ⟨hz, -, -⟩
  rw [← h] at hz
  unfold npk at hz
  exact Term.val_ne_hash 0 _ hz.symm

/-- `recordOwnedStep` preserves `OwnedRandomConsistent`, given the new entry's random
    genuinely reconstructs the npk of whatever `reg` already holds at that key. -/
theorem recordOwnedStep_preserves_consistency {reg : PreimageRegistry} {rreg : OwnedRandomRegistry}
    (hconsistent : OwnedRandomConsistent reg rreg)
    {c : Term} {pre : CommitmentPreimage} {d : OwnedDisclosure}
    (hreg : reg c = some pre) (hnpk : npk (Term.val d.ownerField) d.random = pre.npk) :
    OwnedRandomConsistent reg (recordOwnedStep rreg c d) := by
  intro c' d' hc'
  unfold recordOwnedStep at hc'
  by_cases heq : c' = c
  · rw [if_pos heq] at hc'
    cases hc'
    exact ⟨pre, heq ▸ hreg, hnpk⟩
  · rw [if_neg heq] at hc'
    exact hconsistent c' d' hc'


/-- `recordOwnedStep` preserves an already-known entry, given the new
    disclosure's own commitment check (`hvalid0`, the step-level shape
    every caller of this lemma already has to hand): a NEW record at the
    SAME key `c` as the known one must, by `reg`'s own preimage being a
    function and `npk_inj`, carry the IDENTICAL `⟨self, r⟩` pair back —
    two disclosures of the same commitment can never disagree. What lets
    an adjudicator-owned note's own disclosure survive a LATER unrelated
    disclosure that happens to name the same key, the `OwnedRandomOf`
    sibling of `applyRecords_preserves_known`. -/
theorem recordOwnedStep_preserves_known {reg : PreimageRegistry} {rreg : OwnedRandomRegistry}
    {c0 : Term} {d0 : OwnedDisclosure}
    (hvalid0 : ∃ pre, reg c0 = some pre ∧ npk (Term.val d0.ownerField) d0.random = pre.npk)
    {c : Term} {self r : Nat} {pre : CommitmentPreimage}
    (hknown : rreg c = some ⟨self, r⟩) (hreg : reg c = some pre)
    (hnpk : pre.npk = npk (Term.val self) r) :
    recordOwnedStep rreg c0 d0 c = some ⟨self, r⟩ := by
  unfold recordOwnedStep
  by_cases heq : c = c0
  · obtain ⟨pre0, hreg0, hnpk0⟩ := hvalid0
    rw [heq] at hreg
    rw [hreg] at hreg0
    cases hreg0
    rw [hnpk] at hnpk0
    obtain ⟨hmpk, hrand⟩ := npk_inj hnpk0
    have hd0 : d0 = ⟨self, r⟩ := by
      have hmpk' : d0.ownerField = self := Term.val.inj hmpk
      cases d0
      simp_all
    rw [if_pos heq, hd0]
  · rw [if_neg heq]; exact hknown

/-! ### Can happen (proof completeness) -/

/--
**Can happen**: an owned spend by the real owner, with an accepted proof,
succeeds. `ownerField`, `token`, `randomIn`, `valueIn`, `leavesIndices`,
`pathElements`, `npkOut`, `valueOut` are the real owner's own data — the
witness for `N` notes it genuinely holds at Merkle root `root`, re-minted
into `M` fresh outputs of equal total value. `owned_spend_can_happen`
clears every pool-level gate this model covers: the circuit constraints
hold (`OwnedConstrained`, by construction), `verifyOwned` accepts
(`hComplete.complete`, the one completeness assumption), the caller is
authorized (`hCaller`), every output's preimage is valid and non-zero so
`_validatePublicOutputs(requireAll = true)` (TransactModule.sol:630-634)
passes, and the nullifiers are fresh so `_accumulateAndNullify` does not
revert (`markSpent_succeeds`, using `distinct_leaves_distinct_nullifiers`
from ArmadaLean.Nullifier to turn the owner's genuinely-distinct note
positions into pairwise-distinct nullifiers). -/
theorem owned_spend_can_happen {N M : Nat} (hComplete : OwnedProofCompleteness)
    (ownerField token boundParamsHash : Nat) (root : Term)
    (randomIn valueIn : Fin N → Nat) (leavesIndices : Fin N → Nat)
    (pathElements : Fin N → List (Term × Bool))
    (npkOut : Fin M → Term) (valueOut : Fin M → Nat)
    (hPathLen : ∀ i, (pathElements i).length = 16)
    (hMerkle : ∀ i,
      merkleRoot (commitment (npk (Term.val ownerField) (randomIn i)) token (valueIn i))
        (pathElements i) = root)
    (hRangeIn : ∀ i, RangeChecked120 (valueIn i))
    (hRangeOut : ∀ j, RangeChecked120 (valueOut j))
    (hBalance : listSum (List.ofFn valueIn) = listSum (List.ofFn valueOut))
    (hDistinctLeaves : (List.ofFn leavesIndices).Pairwise (· ≠ ·))
    (spent : NullifierSet) (hFresh : ∀ i, nullifier ownerField (leavesIndices i) ∉ spent)
    (hOutputsNonZero : ∀ j, npkOut j ≠ Term.val 0)
    (caller : Nat) (hCaller : caller = addressOf ownerField) :
    ∃ (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M),
      OwnedConstrained w pub ∧
      VerifyOwnedAccepts pub ∧
      caller = addressOf pub.ownerField ∧
      (∀ j, hashCommitment ⟨npkOut j, token, valueOut j⟩ = pub.commitmentsOut j) ∧
      (∀ j, ¬ isZeroPreimage (⟨npkOut j, token, valueOut j⟩ : CommitmentPreimage)) ∧
      ∃ spent', markSpent spent (List.ofFn pub.nullifiers) = some spent' := by
  let w : TransactOwnedWitness N M :=
    { token := token, randomIn := randomIn, valueIn := valueIn, pathElements := pathElements,
      leavesIndices := leavesIndices, npkOut := npkOut, valueOut := valueOut }
  let pub : TransactOwnedPublic N M :=
    { merkleRoot := root, boundParamsHash := boundParamsHash,
      nullifiers := fun i => nullifier ownerField (leavesIndices i),
      commitmentsOut := fun j => commitment (npkOut j) token (valueOut j),
      ownerField := ownerField }
  have hConstrained : OwnedConstrained w pub :=
    { pathLen := hPathLen, merkle := hMerkle, nullifiers := fun _ => rfl,
      outputs := fun _ => rfl, rangeIn := hRangeIn, rangeOut := hRangeOut,
      balance := congrArg (· % p) hBalance }
  refine ⟨w, pub, hConstrained, hComplete.complete hConstrained, hCaller, fun _ => rfl, ?_, ?_⟩
  · intro j hz
    exact hOutputsNonZero j hz.1
  · apply markSpent_succeeds
    · have hmap := distinct_leaves_distinct_nullifiers ownerField (List.ofFn leavesIndices)
        hDistinctLeaves
      have heq : (List.ofFn leavesIndices).map (nullifier ownerField)
          = List.ofFn (fun i => nullifier ownerField (leavesIndices i)) := List.map_ofFn
      rwa [heq] at hmap
    · intro n hn
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hn
      rw [← hi]
      exact hFresh i
