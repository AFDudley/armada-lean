/-
  Non-vacuity witnesses (`armada-laconic/docs/lean/verification.md` §5a,
  `docs/spec-module-design.md`) for the pool state machine
  (`ArmadaLean/PoolSafety.lean`, `ArmadaLean/PoolOwned.lean`). For every spec entry of
  those two modules whose hypotheses a concrete value can satisfy, one `example` builds
  values for the binders and proves every hypothesis. No example uses the theorem's
  conclusion.

  The owned path (`ArmadaLean.TransactOwned.OwnedConstrained`) carries no EdDSA
  signature: authorization is the plain term equality `pub.ownerField = caller`
  (`ArmadaLean.TransactOwned` module comment). Every fixture below that needs a spend
  uses the owned path for exactly that reason: the plain path's `Constrained` bundles
  `EdDSAVerify w.publicKey w.signature (msgHashOf pub)`
  (`ArmadaLean.Transact.Constrained.sig`), and `EdDSAVerify` is an opaque axiom with no
  defining equation (`axiom EdDSAVerify : (Nat × Nat) → (Nat × Nat × Nat) → Term → Prop`,
  `ArmadaLean.Transact`), so no concrete instance of it is provable. The witnesses that
  need one stay open; `PoolSafety.lean`'s and `PoolOwned.lean`'s witness files record
  each one's reason at its own declaration.
-/
import ArmadaLean.PoolSafety
import Mathlib.Tactic.Says

namespace ArmadaLean.PoolNonVacuity

open ArmadaLean

/-! ## Shared values -/

/-- No shield fee: the deployment fee rate every fixture below uses. -/
def r0 : FeeRatio := ⟨0, 1, by decide, by decide, by decide⟩

def tok0 : Token := ⟨Term.val 100⟩

/-- A contract-owner address (`Address`): `42`. -/
def ownerAddr : Address := ⟨42, by decide⟩

/-- The term of `ownerAddr`: the `ownerField` of every owned fixture below, and the
    caller of every owned spend. -/
def ownerA : Term := Term.val ownerAddr

/-- The fee-admin address of every fixture below. -/
def feeAdmin0 : Term := Term.keccak [Term.val 7]

/-- The treasury address of every fixture below. -/
def treasury0 : Term := Term.keccak [Term.val 8]

/-- The genesis state, with `r0`'s fee rate, fee admin `feeAdmin0` and treasury
    `treasury0`. -/
def g0 : PoolState := genesis r0 feeAdmin0 treasury0

theorem g0_reach : Reachable g0 := .genesis r0 feeAdmin0 treasury0

/-! ## A standalone owned witness/public pair

`OwnedConstrained` never reads the pool state: its `merkle` field only asks that the
claimed root is `merkleRoot` of the claimed leaf along the claimed path, which holds by
`rfl` once the public root is *defined* as that value, and that the path's bits are the
bits of the leaf index. No real Merkle tree is needed for a spec entry that only needs a
satisfying `OwnedConstrained` pair, not a pair tied to a genuine reachable state's tree. -/

/-- A fixed 16-entry path with every direction bit `false`: the path of leaf index `0`,
    for an `OwnedConstrained` pair that answers only to its own definition of
    `merkleRoot`, not to a real tree. -/
def pad16 : List (Term × Bool) := List.replicate 16 (Term.val 0, false)

def w1 : TransactOwnedWitness 1 1 where
  token := tok0
  randomIn := fun _ => 0
  valueIn := fun _ => 5
  pathElements := fun _ => pad16
  leavesIndices := fun _ => 0
  npkOut := fun _ => npk ownerA 1
  valueOut := fun _ => 5

def pub1 : TransactOwnedPublic 1 1 where
  merkleRoot := merkleRoot (commitment (npk ownerA 0) tok0 5) pad16
  boundParamsHash := Term.val 0
  nullifiers := fun _ => nullifier ownerA 0
  commitmentsOut := fun _ => commitment (npk ownerA 1) tok0 5
  owner := ownerAddr

theorem hOC1 : OwnedConstrained w1 pub1 where
  merkle := fun _ =>
    { len := show pad16.length = 16 by decide
      bits := show bitsVal (pad16.map Prod.snd) = 0 by decide
      root_eq := rfl }
  nullifiers := fun _ => rfl
  outputs := fun _ => rfl
  rangeIn := fun _ => spendable_of_lt (show (5 : Nat) < 2 ^ 120 by decide)
  rangeOut := fun _ => spendable_of_lt (show (5 : Nat) < 2 ^ 120 by decide)
  balance := rfl

/-! ## Group A: standalone witnesses (no reachable state) -/

/-- `Spec.live_positions_distinct_nullifiers`. -/
theorem live_positions_distinct_nullifiers.nonvacuity :
    ∃ (nk : Term) (p₁ p₂ : Nat), p₁ ≠ p₂ := ⟨Term.val 0, 0, 1, by decide⟩

/-- `Spec.spend_live_exact`. -/
theorem spend_live_exact.nonvacuity :
    ∃ (s : PoolState) (token : Token)
      (spentPositions : List ((Nat × Nat) × CommitmentPreimage))
      (newNotes : List CommitmentPreimage) (rest : List ((Nat × Nat) × CommitmentPreimage))
      (treeNumber startPos : Nat), removeAll (s.live token) spentPositions = some rest :=
  ⟨g0, tok0, [], [], [], 0, 0, rfl⟩

/-- `Spec.shield_creates_exactly`. -/
theorem shield_creates_exactly.nonvacuity :
    ∃ (s : PoolState) (token : Token) (x : Nat) (npkT : Term),
      0 < x ∧ Spendable (shieldBase s.feeRatio x) :=
  ⟨g0, tok0, 5, npk ownerA 2, by decide, spendable_of_lt (by decide)⟩

/-- `Spec.transact_root_was_produced`. -/
theorem transact_root_was_produced.nonvacuity :
    ∃ (s : PoolState) (tn : Nat) (root : Term), Reachable s ∧ root ∈ s.rootsAt' tn :=
  ⟨g0, 0, treeRoot TreeDepth [], g0_reach, List.mem_cons_self⟩

/-- `Spec.transactOwned_spends_only_owned` and `Spec.owned_owner_binding` (same shape:
    a satisfying `OwnedConstrained` pair, a note whose claimed owner matches its true
    owner, and a caller equal to that owner). -/
theorem transactOwned_spends_only_owned.nonvacuity :
    ∃ (N M : Nat) (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M),
      OwnedConstrained w pub ∧
      ∃ (i : Fin N) (trueOwner : Term) (trueRandom : Nat),
        commitment (npk pub.ownerField (w.randomIn i)) w.token (w.valueIn i) =
          commitment (npk trueOwner trueRandom) w.token (w.valueIn i) ∧
        ∃ caller : Term, caller = pub.ownerField :=
  ⟨1, 1, w1, pub1, hOC1, ⟨0, by decide⟩, ownerA, 0, rfl, ownerA, rfl⟩

/-- `Spec.PoolOwned.owned_owner_binding`: the same shape as
    `transactOwned_spends_only_owned.nonvacuity`. -/
theorem owned_owner_binding.nonvacuity :
    ∃ (N M : Nat) (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M),
      OwnedConstrained w pub ∧
      ∃ (i : Fin N) (trueOwner : Term) (trueRandom : Nat),
        commitment (npk pub.ownerField (w.randomIn i)) w.token (w.valueIn i) =
          commitment (npk trueOwner trueRandom) w.token (w.valueIn i) ∧
        ∃ caller : Term, caller = pub.ownerField :=
  transactOwned_spends_only_owned.nonvacuity

/-- `Spec.transactOwned_records_all`. -/
theorem transactOwned_records_all.nonvacuity :
    ∃ (reg : PreimageRegistry) (N M : Nat) (w : TransactOwnedWitness N M)
      (pub : TransactOwnedPublic N M), OwnedConstrained w pub ∧ ∃ _j : Fin M, True :=
  ⟨fun _ => none, 1, 1, w1, pub1, hOC1, ⟨0, by decide⟩, trivial⟩

/-- `Spec.PoolOwned.owned_no_double_spend`. -/
theorem owned_no_double_spend.nonvacuity :
    ∃ (spent spent' : NullifierSet) (ns : List Term), markSpent spent ns = some spent' :=
  ⟨[], [], [], rfl⟩

/-- `Spec.PoolOwned.preimageOf_consistent`. -/
theorem preimageOf_consistent.nonvacuity :
    ∃ (K : Nat) (commitments : Fin K → Term) (publicOutputs : Fin K → CommitmentPreimage),
      ∀ i, hashCommitment (publicOutputs i) = commitments i :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0⟩

/-- `Spec.owned_spend_witness_exists`: `N = M = 1`, one owned preimage disclosed with
    its own opening, re-minted into one output of equal value. -/
theorem owned_spend_witness_exists.nonvacuity :
    ∃ (owner : Address) (token : Token) (boundParamsHash : Term)
      (preimages : Fin 1 → CommitmentPreimage) (leavesIndices : Fin 1 → Nat)
      (leaves : List Term) (published : List (Term × OwnedOpening)),
      (∀ i, (preimages i).token = token) ∧
      (∀ i, ∃ r, (hashCommitment (preimages i), (⟨Term.val owner, r⟩ : OwnedOpening)) ∈ published ∧
        npk (Term.val owner) r = (preimages i).npk) ∧
      (∀ i, leavesIndices i < 2 ^ TreeDepth) ∧
      (∀ i, leaves[leavesIndices i]? = some (hashCommitment (preimages i))) ∧
      ∃ (npkOut : Fin 1 → Term) (valueOut : Fin 1 → Nat),
        (∀ i, RangeChecked120 (preimages i).value) ∧ (∀ j, RangeChecked120 (valueOut j)) ∧
        listSum (List.ofFn fun i => (preimages i).value) = listSum (List.ofFn valueOut) := by
  refine ⟨ownerAddr, tok0, Term.val 0, fun _ => ⟨npk ownerA 3, tok0, 5⟩, fun _ => 0,
    [hashCommitment ⟨npk ownerA 3, tok0, 5⟩], [(hashCommitment ⟨npk ownerA 3, tok0, 5⟩, ⟨ownerA, 3⟩)],
    fun _ => rfl,
    fun _ => ⟨3, show (hashCommitment (⟨npk ownerA 3, tok0, 5⟩ : CommitmentPreimage),
        (⟨ownerA, 3⟩ : OwnedOpening)) ∈
        [(hashCommitment (⟨npk ownerA 3, tok0, 5⟩ : CommitmentPreimage), (⟨ownerA, 3⟩ : OwnedOpening))]
        by decide, rfl⟩,
    fun _ => show (0 : Nat) < 2 ^ TreeDepth by decide, fun _ => rfl,
    fun _ => npk ownerA 9, fun _ => 5, fun _ => spendable_of_lt (show (5 : Nat) < 2 ^ 120 by decide),
    fun _ => spendable_of_lt (show (5 : Nat) < 2 ^ 120 by decide), rfl⟩

/-- `Spec.spend_bound_to_adapt`. -/
theorem spend_bound_to_adapt.nonvacuity :
    ∃ (boundHash : Term) (bp₀ bp : BoundParams) (a caller : Term),
      boundHash = hashBoundParams bp₀ ∧ bp₀.adaptContract = some a ∧
      boundHash = hashBoundParams bp ∧ AdaptAllows bp caller :=
  let bp₀ : BoundParams := ⟨0, none, some ownerA, Term.val 0⟩
  ⟨hashBoundParams bp₀, bp₀, bp₀, ownerA, ownerA, rfl, rfl, rfl,
    fun a' h => by injection h⟩

/-! ## A reachable fixture after one shield -/

/-- A note key over the address `11`: `npk (Term.val 11) random`. The owned path needs no
    master public key, and this fixture needs no signature either. `11` is a valid
    160-bit address, so the owned pending spend `w3`/`pub3` below opens this note with
    `owner := ⟨11, _⟩`. -/
def npk0 : Term := npk (Term.val 11) 0

/-- The note `g0`'s one shield creates: value `5`, no fee (`r0`). -/
def note0 : CommitmentPreimage := ⟨npk0, tok0, 5⟩

theorem hValue0 : (0 : Nat) < 5 := by decide
theorem hSpendable0 : Spendable (shieldBase r0 5) :=
  spendable_of_lt (show shieldBase r0 5 < 2 ^ 120 by decide)

/-- `g0` after one shield of `note0`: the destination state of
    `Step.shield tok0 5 npk0 hValue0 hSpendable0`, written out so later lemmas can
    unfold it by `decide`. -/
def s1 : PoolState :=
  let note : CommitmentPreimage := ⟨npk0, tok0, shieldBase r0 5⟩
  let tn := insertTree g0.trees 1
  let pos := insertStart g0.trees 1
  { g0 with
      live := fun t => if t = tok0 then ((tn, pos), note) :: g0.live t else g0.live t,
      held := fun t => if t = tok0 then g0.held t + note.value else g0.held t,
      trees := insertLeaves g0.trees [hashCommitment note],
      preimageOf := recordStep g0.preimageOf (hashCommitment note) note,
      treasuryFees := fun t => if t = tok0
        then g0.treasuryFees t + shieldFee r0 5 else g0.treasuryFees t }

theorem g0_to_s1 : Step g0 s1 := Step.shield tok0 5 npk0 hValue0 hSpendable0
theorem s1_reach : Reachable s1 := g0_reach.step g0_to_s1

theorem s1_live_tok0 : s1.live tok0 = [((0, 0), note0)] := by decide
theorem s1_leavesAt0 : s1.leavesAt' 0 = [hashCommitment note0] := by decide
theorem s1_note0_live : ((0, 0), note0) ∈ s1.live tok0 := s1_live_tok0 ▸ List.mem_cons_self

/-- `Spec.live_note_unspent`. -/
theorem live_note_unspent.nonvacuity :
    ∃ (s : PoolState) (t : Token) (tn pos : Nat) (pre : CommitmentPreimage),
      Reachable s ∧ ((tn, pos), pre) ∈ s.live t :=
  ⟨s1, tok0, 0, 0, note0, s1_reach, s1_note0_live⟩

/-- `Spec.live_leaf_matches`. -/
theorem live_leaf_matches.nonvacuity :
    ∃ (s : PoolState) (t : Token) (tn pos : Nat) (pre : CommitmentPreimage),
      Reachable s ∧ ((tn, pos), pre) ∈ s.live t :=
  live_note_unspent.nonvacuity

/-- `Spec.leaf_has_merkle_witness`. -/
theorem leaf_has_merkle_witness.nonvacuity :
    ∃ (s : PoolState) (tn i : Nat) (leaf : Term),
      Reachable s ∧ (s.leavesAt' tn)[i]? = some leaf :=
  ⟨s1, 0, 0, hashCommitment note0, s1_reach, by rw [s1_leavesAt0]; rfl⟩

/-- `Spec.shield_can_happen`. -/
theorem shield_can_happen.nonvacuity :
    ∃ (s : PoolState) (token : Token) (x : Nat) (npkT : Term),
      Reachable s ∧ 0 < x ∧ Spendable (shieldBase s.feeRatio x) :=
  ⟨g0, tok0, 5, npk0, g0_reach, hValue0, hSpendable0⟩

/-- `Spec.spent_monotone`. -/
theorem spent_monotone.nonvacuity : ∃ (s s' : PoolState), Step s s' := ⟨g0, s1, g0_to_s1⟩

/-! ## A reachable fixture with a live owned note -/

/-- An owned note: `npk ownerA 7`, value `6`. A second shield, atop `s1`, creates it. -/
def noteOwned : CommitmentPreimage := ⟨npk ownerA 7, tok0, 6⟩

theorem hValue1 : (0 : Nat) < 6 := by decide
theorem hSpendable1 : Spendable (shieldBase r0 6) :=
  spendable_of_lt (show shieldBase r0 6 < 2 ^ 120 by decide)

/-- `s1` after one shield of `noteOwned`: the destination of
    `Step.shield tok0 6 (npk ownerA 7) hValue1 hSpendable1`. -/
def s2 : PoolState :=
  let note : CommitmentPreimage := ⟨npk ownerA 7, tok0, shieldBase r0 6⟩
  let tn := insertTree s1.trees 1
  let pos := insertStart s1.trees 1
  { s1 with
      live := fun t => if t = tok0 then ((tn, pos), note) :: s1.live t else s1.live t,
      held := fun t => if t = tok0 then s1.held t + note.value else s1.held t,
      trees := insertLeaves s1.trees [hashCommitment note],
      preimageOf := recordStep s1.preimageOf (hashCommitment note) note,
      treasuryFees := fun t => if t = tok0
        then s1.treasuryFees t + shieldFee r0 6 else s1.treasuryFees t }

theorem s1_to_s2 : Step s1 s2 := Step.shield tok0 6 (npk ownerA 7) hValue1 hSpendable1
theorem s2_reach : Reachable s2 := s1_reach.step s1_to_s2

theorem s2_live_tok0 : s2.live tok0 = [((0, 1), noteOwned), ((0, 0), note0)] := by decide
theorem s2_leavesAt0 : s2.leavesAt' 0 = [hashCommitment note0, hashCommitment noteOwned] := by
  decide
theorem s2_spent0 : s2.spent 0 = [] := by decide
theorem s2_noteOwned_live : ((0, 1), noteOwned) ∈ s2.live tok0 :=
  s2_live_tok0 ▸ List.mem_cons_self
theorem s2_note0_live : ((0, 0), note0) ∈ s2.live tok0 :=
  s2_live_tok0 ▸ List.mem_cons_of_mem _ List.mem_cons_self

/-- `Spec.owned_merge_can_happen`: one live owned note of `tok0` (`noteOwned`,
    position `(0, 1)` of `s2`), owned by `ownerAddr`, merged into one output. -/
theorem owned_merge_can_happen.nonvacuity :
    ∃ (s : PoolState) (hN0 : (0 : Nat) < 1) (owner : Address) (token : Token) (bp : BoundParams)
      (pos : Fin 1 → Nat) (pre : Fin 1 → CommitmentPreimage) (random : Fin 1 → Nat),
      Reachable s ∧ bp.unshield = none ∧ AdaptAllows bp (Term.val owner) ∧
      (∀ i, ((bp.treeNumber, pos i), pre i) ∈ s.live token) ∧
      (List.ofFn pos).Pairwise (· ≠ ·) ∧ (∀ i, npk (Term.val owner) (random i) = (pre i).npk) ∧
      ∃ npkOut : Term, Spendable (listSum (List.ofFn fun i => (pre i).value)) := by
  refine ⟨s2, by decide, ownerAddr, tok0, ⟨0, none, none, Term.val 0⟩, fun _ => 1,
    fun _ => noteOwned, fun _ => 7, s2_reach, rfl, fun a h => by injection h,
    fun _ => s2_noteOwned_live, ?_, fun _ => rfl, ownerA,
    spendable_of_lt (show (6 : Nat) < 2 ^ 120 by decide)⟩
  exact List.pairwise_singleton _ _

/-! ## A reachable fixture after spending the owned note -/

/-- No unshield, no adapt contract: the bound parameters of the spend below. -/
def bp0 : BoundParams := ⟨0, none, none, Term.val 0⟩

theorem hAdapt0 : AdaptAllows bp0 ownerA := fun _ h => by injection h

/-- A `TransactOwned` spend of `noteOwned` (position `(0, 1)` of `s2`), re-minting it
    into one fresh output of the same value, owned by `ownerA` again. -/
def w2 : TransactOwnedWitness 1 1 where
  token := tok0
  randomIn := fun _ => 7
  valueIn := fun _ => 6
  pathElements := fun _ => treePath TreeDepth (s2.leavesAt' 0) 1
  leavesIndices := fun _ => 1
  npkOut := fun _ => npk ownerA 99
  valueOut := fun _ => 6

def pub2 : TransactOwnedPublic 1 1 where
  merkleRoot := treeRoot TreeDepth (s2.leavesAt' 0)
  boundParamsHash := hashBoundParams bp0
  nullifiers := fun _ => nullifier ownerA 1
  commitmentsOut := fun _ => commitment (npk ownerA 99) tok0 6
  owner := ownerAddr

theorem hC2 : OwnedConstrained w2 pub2 where
  merkle := fun _ =>
    treePath_merkleProof TreeDepth (s2.leavesAt' 0) 1 (show (1 : Nat) < 2 ^ TreeDepth by decide)
      (by rw [s2_leavesAt0]; rfl)
  nullifiers := fun _ => rfl
  outputs := fun _ => rfl
  rangeIn := fun _ => spendable_of_lt (show (6 : Nat) < 2 ^ 120 by decide)
  rangeOut := fun _ => spendable_of_lt (show (6 : Nat) < 2 ^ 120 by decide)
  balance := rfl

/-- The live entries of `tok0` left after removing `noteOwned`: just `note0`. -/
def restAfterSpend : List ((Nat × Nat) × CommitmentPreimage) := [((0, 0), note0)]

theorem hRemove2 : removeAll (s2.live tok0) (ownedSpentPositions bp0.treeNumber pub2 w2) =
    some restAfterSpend := by
  rw [s2_live_tok0]; decide

theorem hNullify2 : markSpent (s2.spent 0) (List.ofFn pub2.nullifiers) =
    some [nullifier ownerA 1] := by
  rw [s2_spent0]; decide

theorem hRoot2 : pub2.merkleRoot ∈ s2.rootsAt' 0 := List.mem_cons_self

/-- `s2` after spending `noteOwned`: the destination of
    `Step.transactOwned w2 pub2 bp0 … hRoot2 hRemove2 hNullify2`. -/
def s3 : PoolState :=
  let tn := insertTree s2.trees 1
  let pos := insertStart s2.trees 1
  { s2 with
      live := fun t => if t = tok0
        then withTreePositionsFrom tn pos (ownedNewNotes w2) ++ restAfterSpend else s2.live t,
      spent := fun n => if n = 0 then [nullifier ownerA 1] else s2.spent n,
      trees := insertLeaves s2.trees ((ownedNewNotes w2).map hashCommitment),
      preimageOf := applyRecords s2.preimageOf (ownedOutputRecords w2 pub2),
      published := s2.published ++ [] }

theorem s2_to_s3 : Step s2 s3 :=
  Step.transactOwned w2 pub2 bp0 (by decide) (by decide) hC2 ownerA rfl rfl hAdapt0 rfl
    restAfterSpend [nullifier ownerA 1] [] hRoot2 hRemove2 hNullify2
theorem s3_reach : Reachable s3 := s2_reach.step s2_to_s3

theorem s3_spent0 : s3.spent 0 = [nullifier ownerA 1] := by decide
theorem s3_note0_live : ((0, 0), note0) ∈ s3.live tok0 := by
  show ((0, 0), note0) ∈ withTreePositionsFrom (insertTree s2.trees 1) (insertStart s2.trees 1)
      (ownedNewNotes w2) ++ restAfterSpend
  exact List.mem_append_right _ List.mem_cons_self


/-- `Spec.pool_no_double_spend`: `s3` already has `nullifier ownerA 1` spent in tree
    `0`; a later `markSpent` call with no nullifiers trivially succeeds. -/
theorem pool_no_double_spend.nonvacuity :
    ∃ (s0 s : PoolState), Reachable s0 ∧ ReachableFrom s0 s ∧
      ∃ n : Term, n ∈ s0.spent 0 ∧ ∃ spent' : NullifierSet, markSpent (s.spent 0) [] = some spent' :=
  ⟨s3, s3, s3_reach, .refl, nullifier ownerA 1, by rw [s3_spent0]; exact List.mem_cons_self,
    s3.spent 0, rfl⟩

/-- `Spec.spend_not_blocked`: a pending spend of `note0` (position `(0, 0)` of `s2`) is
    still enabled after the step `s2 → s3`, which spends only `noteOwned`. -/
theorem spend_not_blocked.nonvacuity :
    ∃ (s s' : PoolState), Step s s' ∧
      ∃ (tn : Nat) (root nk : Term) (token : Token)
        (entries : List ((Nat × Nat) × CommitmentPreimage)),
        Reachable s ∧ (∀ e ∈ entries, e.1.1 = tn) ∧
        SpendEnabled s tn root token entries (entries.map fun e => nullifier nk e.1.2) ∧
        ∀ e ∈ entries, ¬ Spends s s' token e := by
  refine ⟨s2, s3, s2_to_s3, 0, treeRoot TreeDepth (s2.leavesAt' 0), Term.val 11, tok0,
    [((0, 0), note0)], s2_reach, by decide,
    ⟨hRoot2, ⟨[((0, 1), noteOwned)], ?_⟩, [nullifier (Term.val 11) 0], ?_⟩, ?_⟩
  · rw [s2_live_tok0]; rfl
  · rw [s2_spent0]; decide
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    exact fun h => h.2 s3_note0_live

/-- A `TransactOwned` pending spend of `note0` (position `(0, 0)` of `s2`), separate
    from the actual spend `w2`/`pub2` of `noteOwned` that builds `s3`. -/
def w3 : TransactOwnedWitness 1 1 where
  token := tok0
  randomIn := fun _ => 0
  valueIn := fun _ => 5
  pathElements := fun _ => treePath TreeDepth (s2.leavesAt' 0) 0
  leavesIndices := fun _ => 0
  npkOut := fun _ => npk ownerA 55
  valueOut := fun _ => 5

def pub3 : TransactOwnedPublic 1 1 where
  merkleRoot := treeRoot TreeDepth (s2.leavesAt' 0)
  boundParamsHash := hashBoundParams bp0
  nullifiers := fun _ => nullifier (Term.val 11) 0
  commitmentsOut := fun _ => commitment (npk ownerA 55) tok0 5
  owner := ⟨11, by decide⟩

theorem hC3 : OwnedConstrained w3 pub3 where
  merkle := fun _ =>
    treePath_merkleProof TreeDepth (s2.leavesAt' 0) 0 (show (0 : Nat) < 2 ^ TreeDepth by decide)
      (by rw [s2_leavesAt0]; rfl)
  nullifiers := fun _ => rfl
  outputs := fun _ => rfl
  rangeIn := fun _ => spendable_of_lt (show (5 : Nat) < 2 ^ 120 by decide)
  rangeOut := fun _ => spendable_of_lt (show (5 : Nat) < 2 ^ 120 by decide)
  balance := rfl

theorem ownedSpentPositions3 : ownedSpentPositions bp0.treeNumber pub3 w3 = [((0, 0), note0)] := rfl

/-- `Spec.transactOwned_not_blocked`: a pending `TransactOwned` spend of `note0` is
    still enabled after `s2 → s3`, which spends only `noteOwned`. -/
theorem transactOwned_not_blocked.nonvacuity :
    ∃ (s s' : PoolState), Step s s' ∧
      ∃ (N M : Nat) (w : TransactOwnedWitness N M) (pub : TransactOwnedPublic N M)
        (bp : BoundParams), Reachable s ∧ OwnedConstrained w pub ∧
        SpendEnabled s bp.treeNumber pub.merkleRoot w.token
          (ownedSpentPositions bp.treeNumber pub w) (List.ofFn pub.nullifiers) ∧
        ∀ e ∈ ownedSpentPositions bp.treeNumber pub w, ¬ Spends s s' w.token e := by
  refine ⟨s2, s3, s2_to_s3, 1, 1, w3, pub3, bp0, s2_reach, hC3,
    ⟨hRoot2, ⟨[((0, 1), noteOwned)], ?_⟩, [nullifier (Term.val 11) 0], ?_⟩, ?_⟩
  · show removeAll (s2.live tok0) [((0, 0), note0)] = some [((0, 1), noteOwned)]
    rw [s2_live_tok0]; rfl
  · show markSpent (s2.spent 0) (List.ofFn pub3.nullifiers) = some [nullifier (Term.val 11) 0]
    rw [s2_spent0]; decide
  · rw [ownedSpentPositions3]
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact fun h => h.2 s3_note0_live

/-- `Spec.leaf_stable`. -/
theorem leaf_stable.nonvacuity :
    ∃ (s s' : PoolState) (tn pos : Nat), ReachableFrom s s' ∧ pos < (s.leavesAt' tn).length :=
  ⟨s1, s1, 0, 0, .refl, by rw [s1_leavesAt0]; decide⟩

end ArmadaLean.PoolNonVacuity
