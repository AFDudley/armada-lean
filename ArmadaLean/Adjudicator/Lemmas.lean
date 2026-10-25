/-
  ArmadaLean.Adjudicator.Lemmas — helper facts the `Safety.lean` proofs need
  about the payout math (`afford`, `transferEffects`, `Outcome.lean`). Each
  lemma states one fact in plain words; `Safety.lean` imports this file and
  cites the lemma it uses by name.
-/
import ArmadaLean.Adjudicator.Reachability

namespace ArmadaLean.Adjudicator

/-! ## `afford`: the priority-order payout never overpays, and never pays an
    allocation more than its own recorded amount -/

/-- `afford` never pays out, in total, more than the surplus it started with
    (S2 §5.2's Turbo Value Algorithm: `x = min(payout, remainingFunds)` at
    every step, so the running total never exceeds the starting surplus). -/
theorem afford_sum_le (allocs : List Allocation) (surplus : Nat) :
    listSum (afford allocs surplus) ≤ surplus := by
  induction allocs generalizing surplus with
  | nil => simp [afford, listSum]
  | cons a as ih =>
    simp only [afford, listSum]
    have hih := ih (surplus - min a.amount surplus)
    have hpaid : min a.amount surplus ≤ surplus := Nat.min_le_right _ _
    omega

/-- `afford` produces one paid amount per allocation. -/
theorem afford_length (allocs : List Allocation) (surplus : Nat) :
    (afford allocs surplus).length = allocs.length := by
  induction allocs generalizing surplus with
  | nil => simp [afford]
  | cons a as ih => simp [afford, ih]

/-- Every `(allocation, paid)` pair `afford` produces pays the allocation no
    more than its own recorded amount (`paid = min a.amount remaining ≤
    a.amount`). -/
theorem afford_le (allocs : List Allocation) (surplus : Nat) :
    ∀ p ∈ allocs.zip (afford allocs surplus), p.2 ≤ p.1.amount := by
  induction allocs generalizing surplus with
  | nil => simp
  | cons a as ih =>
    simp only [afford, List.zip_cons_cons]
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · subst h; exact Nat.min_le_left _ _
    · exact ih (surplus - min a.amount surplus) _ h

/-! ## Summing a filtered sublist never exceeds summing the whole list -/

/-- Dropping entries from a list never increases the sum of a `Nat`-valued
    function over what remains: summing `g` over a `filterMap`-selected
    sublist is at most summing `g` over the whole list. -/
theorem filterMap_ite_sum_le {α : Type} (l : List α) (q : α → Bool) (g : α → Nat) :
    listSum (l.filterMap (fun x => if q x then some (g x) else none)) ≤ listSum (l.map g) := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    by_cases hq : q x = true
    · rw [List.filterMap_cons, if_pos hq, List.map_cons]
      simp only [listSum]
      omega
    · rw [List.filterMap_cons, if_neg hq, List.map_cons]
      simp only [listSum]
      omega

/-! ## `transferEffects`: bounds and provenance for what it actually pays -/

/-- Selecting a subset of positions out of `(allocations, afforded amounts)`,
    carried as `Allocation.amount`-tagged records, never sums to more than
    summing every afforded amount. The generic shape behind
    `transferEffects`'s `totalPayouts`. -/
theorem indexed_filterMap_amount_sum_le (allocs : List Allocation) (paidAt : List Nat)
    (hlen : paidAt.length = allocs.length) (sel : Nat → Bool) :
    listSum ((((List.range allocs.length).zip (allocs.zip paidAt)).filterMap
        (fun p : Nat × Allocation × Nat =>
          if sel p.1 then some ({p.2.1 with amount := p.2.2} : Allocation) else none)).map
      Allocation.amount) ≤ listSum paidAt := by
  rw [List.map_filterMap]
  have hopt : (fun (p : Nat × Allocation × Nat) =>
      Option.map Allocation.amount
        (if sel p.1 then some ({p.2.1 with amount := p.2.2} : Allocation) else none))
      = (fun (p : Nat × Allocation × Nat) => if sel p.1 then some p.2.2 else none) := by
    funext p
    by_cases h : sel p.1 <;> simp [h]
  rw [hopt]
  have hb := filterMap_ite_sum_le ((List.range allocs.length).zip (allocs.zip paidAt))
    (fun p => sel p.1) (fun p => p.2.2)
  have hmapeq : ((List.range allocs.length).zip (allocs.zip paidAt)).map
      (fun (p : Nat × Allocation × Nat) => p.2.2) = paidAt := by
    have h1 : ((List.range allocs.length).zip (allocs.zip paidAt)).map
        (fun (p : Nat × Allocation × Nat) => p.2) = allocs.zip paidAt := by
      apply List.map_snd_zip
      rw [List.length_zip, hlen]
      simp
    calc ((List.range allocs.length).zip (allocs.zip paidAt)).map
          (fun (p : Nat × Allocation × Nat) => p.2.2)
        = (((List.range allocs.length).zip (allocs.zip paidAt)).map
            (fun (p : Nat × Allocation × Nat) => p.2)).map Prod.snd := by
          rw [List.map_map]; rfl
      _ = (allocs.zip paidAt).map Prod.snd := by rw [h1]
      _ = paidAt := by
          apply List.map_snd_zip
          exact Nat.le_of_eq hlen
  rw [hmapeq] at hb
  exact hb

/-- `transferEffects`'s total payout never exceeds the surplus it was given
    (`heldValue`, at the call site): the total of every position's
    priority-order affordable amount (`afford_sum_le`), selecting only some
    positions cannot pay more than selecting all of them
    (`indexed_filterMap_amount_sum_le`). -/
theorem transferEffects_totalPayouts_le (allocs : List Allocation) (surplus : Nat)
    (indices : List Nat) :
    (transferEffects allocs surplus indices).2.2 ≤ surplus := by
  show listSum
      ((((List.range allocs.length).zip (allocs.zip (afford allocs surplus))).filterMap
        (fun p : Nat × Allocation × Nat =>
          if indices.isEmpty || p.1 ∈ indices then some ({ p.2.1 with amount := p.2.2 } : Allocation)
          else none)).map Allocation.amount) ≤ surplus
  exact Nat.le_trans
    (indexed_filterMap_amount_sum_le allocs (afford allocs surplus) (afford_length allocs surplus)
      (fun i => indices.isEmpty || i ∈ indices))
    (afford_sum_le allocs surplus)

/-- Every allocation `transferEffects` actually pays out now shares its
    destination with, and is paid no more than, some allocation already
    recorded in the original list (clause 24, `MultiAssetHolder.sol:135-191`:
    a payout can only move an already-recorded allocation's own funds). -/
theorem transferEffects_exit_provenance (allocs : List Allocation) (surplus : Nat)
    (indices : List Nat) :
    ∀ paid ∈ (transferEffects allocs surplus indices).2.1,
      ∃ original ∈ allocs, paid.destination = original.destination ∧ paid.amount ≤ original.amount := by
  show ∀ paid ∈ (((List.range allocs.length).zip (allocs.zip (afford allocs surplus))).filterMap
      (fun p : Nat × Allocation × Nat =>
        if indices.isEmpty || p.1 ∈ indices then some ({ p.2.1 with amount := p.2.2 } : Allocation)
        else none)),
      ∃ original ∈ allocs, paid.destination = original.destination ∧ paid.amount ≤ original.amount
  intro paid hpaid
  obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hpaid
  by_cases hsel : indices.isEmpty || a.1 ∈ indices
  · rw [if_pos hsel] at hfa
    have hpaid_eq : ({ a.2.1 with amount := a.2.2 } : Allocation) = paid := Option.some.inj hfa
    have ha2 : a.2 ∈ allocs.zip (afford allocs surplus) := (List.of_mem_zip ha).2
    refine ⟨a.2.1, (List.of_mem_zip ha2).1, ?_, ?_⟩
    · rw [← hpaid_eq]
    · rw [← hpaid_eq]
      exact afford_le allocs surplus a.2 ha2
  · rw [if_neg hsel] at hfa
    exact absurd hfa (by simp)

/-! ## A reusable induction principle over the reachable set -/

/-- A property preserved by every single `Step` holds at every state
    `AppliesAll` reaches from a state where it already holds: induction on
    the call list. -/
theorem appliesAll_preserves {sig : SignatureAssumptions}
    {appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop}
    {P : AdjudicatorState → Prop}
    (hstep : ∀ actor call s s', P s → Step sig appRel actor s call s' → P s') :
    ∀ {calls : List (Actor × Call)} {s s' : AdjudicatorState},
      P s → AppliesAll sig appRel s calls s' → P s'
  | [], s, s', hP, happ => by rw [show s' = s from happ]; exact hP
  | (actor, call) :: rest, s, s', hP, happ => by
      obtain ⟨mid, hc, hrest⟩ := happ
      exact appliesAll_preserves hstep (hstep actor call s mid hP hc) hrest

/-- A property that holds at deployment and is preserved by every `Step`
    holds at every reachable state. The induction tool every invariant over
    `Reachable` in `Safety.lean` uses. -/
theorem reachable_preserves {sig : SignatureAssumptions}
    {appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop}
    {P : AdjudicatorState → Prop} {deployed s : AdjudicatorState}
    (hbase : P deployed)
    (hstep : ∀ actor call s s', P s → Step sig appRel actor s call s' → P s')
    (hreach : Reachable sig appRel deployed s) : P s := by
  obtain ⟨calls, happ⟩ := hreach
  exact appliesAll_preserves hstep hbase happ

/-! ## One Step-level fact every call case keeps: the configured-asset list -/

/-- Every `Step` case leaves `configuredAssets` untouched (`Operations.lean`):
    the deploy-time asset list is a constant no call ever rewrites. -/
theorem step_configuredAssets (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s') :
    s'.configuredAssets = s.configuredAssets := by
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_, _, _, _, _, _, h, _, _, _, _⟩ := hstep
    exact h
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _, _, _⟩ := hstep
    exact h
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _, _, _, _⟩ := hstep
    exact h
  | bulkTransferAllAssets cid outcome claimedStateHash => exact hstep.elim
  | bulkConcludeAndTransferAllAssets fp candidate => exact hstep.elim
  | tick newNow =>
    obtain ⟨_, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | sign p d =>
    obtain ⟨_, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, h, _, _, _⟩ := hstep
    exact h


/-- Every `Step` case leaves `self` untouched (`Operations.lean`): the
    adjudicator's own deployed address is a constant no call ever
    rewrites. -/
theorem step_self (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s') :
    s'.self = s.self := by
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | bulkTransferAllAssets cid outcome claimedStateHash => exact hstep.elim
  | bulkConcludeAndTransferAllAssets fp candidate => exact hstep.elim
  | tick newNow =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | sign p d =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact h

/-! ## Another Step-level fact every call case keeps: `signedBy` only grows -/

/-- `signedBy` only grows across a single `Step`: only `.sign` adds to it,
    and only ever to the signer's own row (`Operations.lean`'s `.sign`
    case); every other call leaves it unchanged. The tool
    `finalized_outcome_was_concluded_or_challenged` (`Safety.lean`) needs
    to carry a `SignedByAll` fact, established at one `.conclude` call,
    forward across every LATER step up to the state actually queried. -/
theorem step_signedBy_mono (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s') :
    ∀ p d, s.signedBy p d → s'.signedBy p d := by
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | bulkTransferAllAssets cid outcome claimedStateHash => exact hstep.elim
  | bulkConcludeAndTransferAllAssets fp candidate => exact hstep.elim
  | tick newNow =>
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | sign p d =>
    obtain ⟨_, h⟩ := hstep
    rw [h.1]; exact fun p' d' hp => Or.inr hp
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h]; exact fun p d hp => hp

/-- Marking a single nullifier spent: it fails iff the nullifier is already
    spent, and otherwise prepends it (`ArmadaLean.markSpent`, `PoolOwned.lean`). -/
theorem markSpent_single (spent : NullifierSet) (n : Term) :
    markSpent spent [n] = if n ∈ spent then none else some (n :: spent) := by
  unfold markSpent
  split <;> rfl

/-- `.transfer`'s own output list (`Operations.lean`: `payoutOutputs ++`
    the conditional remainder note) never names a `0`-value preimage:
    `payoutOutputs` drops a zero-amount entry by `filterMap`, and the
    remainder note is appended only when the remainder is nonzero. -/
theorem payout_outputs_nonzero (exitAllocs : List Allocation) (remainder asset self : Nat) :
    ∀ pre ∈ (exitAllocs.filterMap (fun a =>
        if a.amount = 0 then none else some (⟨a.destination, asset, a.amount⟩ : CommitmentPreimage))) ++
        (if remainder = 0 then [] else [(⟨Term.val self, asset, remainder⟩ : CommitmentPreimage)]),
      pre.value ≠ 0 := by
  intro pre hpre
  rcases List.mem_append.mp hpre with hc | hc
  · obtain ⟨a, _ha, hfa⟩ := List.mem_filterMap.mp hc
    by_cases hamt : a.amount = 0
    · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
    · rw [if_neg hamt] at hfa
      have heq := Option.some.inj hfa
      rw [← heq]
      exact hamt
  · by_cases hrem : remainder = 0
    · rw [if_pos hrem] at hc; exact absurd hc List.not_mem_nil
    · rw [if_neg hrem] at hc
      rw [List.mem_singleton] at hc
      rw [hc]
      exact hrem


/-! ## `applyRecords` at one key: reading back a just-written preimage, and
    carrying a known one forward through unrelated writes

Both lemmas lean on the same fact: `commitment`'s hash
(`ArmadaLean.hashCommitment`) is injective (`ArmadaLean.Poseidon.Term.
hash3_inj`), so two VALID entries (`hvalid`'s own hypothesis) sharing
one commitment key must carry the SAME preimage — a batch can never
silently overwrite a known holding's registry entry with a different
value, honest or not. -/

/-- `hashCommitment` is injective: two preimages hashing to the same
    commitment are the same preimage (`ArmadaLean.Poseidon.Term.
    hash3_inj`, the symbolic Poseidon collision-resistance fact, proved
    from `Term`'s own constructors — `pool-model`'s `af91ab2` — already
    used by `Transact.lean` and `TransactOwned.lean`). -/
theorem hashCommitment_inj {p q : CommitmentPreimage} (h : hashCommitment p = hashCommitment q) :
    p = q := by
  unfold hashCommitment commitment at h
  obtain ⟨h1, h2, h3⟩ := Term.hash3_inj h
  have h2' := Term.val.inj h2
  have h3' := Term.val.inj h3
  cases p; cases q
  simp_all

/-- Applying a valid record batch to a registry that already reads `pre` at
    `c` (consistently, `hashCommitment pre = c`) still reads `pre` at `c`
    afterward: any entry in the batch sharing key `c` must, by `hvalid` and
    `hashCommitment_inj`, carry the value `pre` itself, so whether or not
    the batch touches `c`, the final value there is unchanged. -/
theorem applyRecords_preserves_known {records : List (Term × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    (reg : PreimageRegistry) (c : Term) (pre : CommitmentPreimage)
    (hknown : reg c = some pre) (hconsist : hashCommitment pre = c) :
    applyRecords reg records c = some pre := by
  induction records generalizing reg with
  | nil => exact hknown
  | cons cp rest ih =>
    obtain ⟨c0, p0⟩ := cp
    unfold applyRecords
    apply ih (fun cp' hcp' => hvalid cp' (List.mem_cons_of_mem _ hcp'))
    unfold recordStep
    by_cases hz : isZeroPreimage p0
    · simp only [if_pos hz]; exact hknown
    · simp only [if_neg hz]
      by_cases hc0 : c0 = c
      · have hp0eq : hashCommitment p0 = c0 := hvalid (c0, p0) List.mem_cons_self
        have hp0c : hashCommitment p0 = c := hc0 ▸ hp0eq
        have hpp : p0 = pre := hashCommitment_inj (hp0c.trans hconsist.symm)
        rw [if_pos hc0.symm, hpp]
      · rw [if_neg (fun h => hc0 h.symm)]; exact hknown

/-- Applying a valid record batch that names `(c, p)` reads back `p` at key
    `c` afterward, as long as `p` is not the all-zero skip marker
    (`ArmadaLean.PoolOwned.isZeroPreimage`, which `recordStep` never
    writes). -/
theorem applyRecords_reads {records : List (Term × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    (reg : PreimageRegistry) (c : Term) (p : CommitmentPreimage)
    (hmem : (c, p) ∈ records) (hnz : ¬ isZeroPreimage p) :
    applyRecords reg records c = some p := by
  induction records generalizing reg with
  | nil => simp at hmem
  | cons cp0 rest ih =>
    obtain ⟨c0, p0⟩ := cp0
    unfold applyRecords
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hc hp
      subst hc; subst hp
      have hstep : recordStep reg c p c = some p := by
        unfold recordStep; rw [if_neg hnz, if_pos rfl]
      exact applyRecords_preserves_known (fun cp hcp => hvalid cp (List.mem_cons_of_mem _ hcp))
        (recordStep reg c p) c p hstep (hvalid (c, p) List.mem_cons_self)
    · exact ih (fun cp hcp => hvalid cp (List.mem_cons_of_mem _ hcp)) (recordStep reg c0 p0) hmem'

/-! ## `holdings`/`pool.preimageOf` step invariant: `holdings_never_zero_
    valued` (`Safety.lean`) needs more than its own call's step, since a
    DIFFERENT channel's holding must also survive THIS call's `records`
    batch unscathed — carried as an inductive invariant over EVERY `Step`,
    not just `.deposit`/`.transfer`'s own. -/

/-- One `Step`'s effect on the invariant `holdings_never_zero_valued`
    needs: if every current holding already reads back a nonzero,
    self-consistent preimage, the SAME holds after one more `Step`. The
    `hashCommitment pre = qc` conjunct (beyond what the THEOREM itself
    asks) is the induction's own bookkeeping: it is what lets
    `applyRecords_preserves_known` show an UNRELATED holding's preimage
    survives a batch that happens to also touch its key (by
    `hashCommitment_inj`, any entry sharing that key must carry the SAME
    preimage). `.deposit` and `.transfer` are the only cases that write
    `holdings`/`pool.preimageOf`; every other case leaves both fields
    exactly as they were. -/
theorem holdings_preimage_nonzero_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (hstep : Step sig appRel actor s call s') :
    ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
  cases call with
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, hmatch⟩ := hinner
    obtain ⟨_r, _hown, hcommit, htoken, hposition, hN, hM, hC, rest, spent', records, hCapacity,
      hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
      fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
    have hval : w.valueOut idx = amount := by
      have hout := hC.outputs idx
      rw [htoken, hcommit] at hout
      exact (Term.val.inj (Term.hash3_inj hout).2.2).symm
    have hnz : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
      unfold isZeroPreimage
      intro ⟨_, hv, _⟩
      rw [hval] at hv
      have hcheck : amount = 0 := hv
      omega
    have hread := applyRecords_reads hvalid s.pool.preimageOf (pub.commitmentsOut idx)
      ⟨w.npkOut idx, w.token, w.valueOut idx⟩ hidxrec hnz
    have hchain : ∀ qc pre, s.pool.preimageOf qc = some pre → hashCommitment pre = qc →
        midPool.preimageOf qc = some pre := fun qc pre hpre hconsist => by
      rw [heq]; exact applyRecords_preserves_known hvalid s.pool.preimageOf qc pre hpre hconsist
    rcases hh : s.holdings asset channelId with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, hholdseq⟩ := hmatch
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc
      unfold update at hc
      by_cases ha : qasset = asset
      · subst ha
        by_cases hcid : qcid = channelId
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          have hqc : (position, pub.commitmentsOut idx) = (qpos, qc) := Option.some.inj hc
          have hqc' : pub.commitmentsOut idx = qc := (Prod.mk.injEq _ _ _ _ ▸ hqc).2
          rw [hqc'] at hread
          refine ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, ?_, ?_, ?_⟩
          · rw [hpoolEq, heq]; exact hread
          · rw [hval]
            intro hz; have hcheck2 : amount = 0 := hz; omega
          · exact (hC.outputs idx).symm.trans hqc'
        · rw [if_pos rfl, if_neg hcid] at hc
          obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qpos qc hc
          refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
          rw [hpoolEq]
          exact hchain qc pre_old hpre_old hconsist_old
      · rw [if_neg ha] at hc
        obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qpos qc hc
        refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
        rw [hpoolEq]
        exact hchain qc pre_old hpre_old hconsist_old
    · obtain ⟨oldPos, oldHoldingVal⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergedPos, hmerge, hholdseq⟩ := hmatch
      obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv asset channelId oldPos oldHoldingVal hh
      obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity',
        hown', htoken', hnpkOut', hmergedEq, _hleaf0, _hleaf1, hcommitOld, hcommitNew, hroot',
        hremove', hnullify', _hrandomOut', heq'⟩ := hmerge
      have hvalOld' : w'.valueIn 0 = pre_old.value := by
        have hh2 := hcommitOld.trans hconsist_old.symm
        unfold hashCommitment at hh2
        exact Term.val.inj (Term.hash3_inj hh2).2.2
      have hvalPos : w'.valueIn 0 ≠ 0 := hvalOld' ▸ hval_old
      have hbalance := transactOwned_value_conserved w' pub' (by decide) (by decide) hC'
      have hvalOutPos : w'.valueOut 0 ≠ 0 := by
        have hsum : w'.valueIn 0 + (w'.valueIn 1 + 0) = w'.valueOut 0 + 0 := hbalance
        omega
      have hnzOut : ¬ isZeroPreimage (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) := by
        unfold isZeroPreimage
        intro ⟨_, hv, _⟩
        exact hvalOutPos hv
      have hreadM := applyRecords_reads (ownedOutputRecords_valid hC') midPool.preimageOf
        (pub'.commitmentsOut 0) ⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩
        (List.mem_ofFn.mpr ⟨0, rfl⟩) hnzOut
      have hchain2 : ∀ qc pre, s.pool.preimageOf qc = some pre → hashCommitment pre = qc →
          s'.pool.preimageOf qc = some pre := fun qc pre hpre hconsist => by
        rw [heq']
        exact applyRecords_preserves_known (ownedOutputRecords_valid hC') midPool.preimageOf qc pre
          (hchain qc pre hpre hconsist) hconsist
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc
      unfold update at hc
      by_cases ha : qasset = asset
      · subst ha
        by_cases hcid : qcid = channelId
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          have hqc : (mergedPos, merged) = (qpos, qc) := Option.some.inj hc
          have hqc' : merged = qc := (Prod.mk.injEq _ _ _ _ ▸ hqc).2
          rw [hmergedEq] at hqc'
          rw [hqc'] at hreadM
          refine ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, ?_, hvalOutPos, ?_⟩
          · rw [heq']; exact hreadM
          · exact (hC'.outputs 0).symm.trans hqc'
        · rw [if_pos rfl, if_neg hcid] at hc
          obtain ⟨pre_old2, hpre_old2, hval_old2, hconsist_old2⟩ := hinv qasset qcid qpos qc hc
          exact ⟨pre_old2, hchain2 qc pre_old2 hpre_old2 hconsist_old2, hval_old2, hconsist_old2⟩
      · rw [if_neg ha] at hc
        obtain ⟨pre_old2, hpre_old2, hval_old2, hconsist_old2⟩ := hinv qasset qcid qpos qc hc
        exact ⟨pre_old2, hchain2 qc pre_old2 hpre_old2 hconsist_old2, hval_old2, hconsist_old2⟩
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨hmatch, hholdseq, _hchanseq⟩ := hrest
    change PoolOwnedSpendStep s.pool s.self (outcome.get ⟨assetIndex, hidx⟩).asset
      (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid)
      ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
        if a.amount = 0 then none
        else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ : CommitmentPreimage)) ++
        (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
            (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
         then []
         else [(⟨Term.val s.self, (outcome.get ⟨assetIndex, hidx⟩).asset,
           heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
             (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ : CommitmentPreimage)]))
      s'.pool at hmatch
    change s'.holdings = update s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset
      (update (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset) cid
        (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
            (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
         then none
         else some (s.pool.leaves.length +
             ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
                 if a.amount = 0 then none
                 else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ :
                   CommitmentPreimage)) ++
               (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                   (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                     (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
                then []
                else [(⟨Term.val s.self, (outcome.get ⟨assetIndex, hidx⟩).asset,
                  heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                    (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ :
                    CommitmentPreimage)])).length - 1,
           commitment (Term.val s.self) (outcome.get ⟨assetIndex, hidx⟩).asset
             (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
               (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2)))) at hholdseq
    intro qasset qcid qpos qc hc
    rw [hholdseq] at hc
    unfold update at hc
    generalize hAO : outcome.get ⟨assetIndex, hidx⟩ = assetOutcome at hc hmatch
    generalize hRemDef : heldValue s assetOutcome.asset cid -
      (transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.2 =
      remainder at hc hmatch
    have hvalid_outputs : ∀ cp ∈ ((transferEffects assetOutcome.allocations
        (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
          if a.amount = 0 then none
          else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
        (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)), hashCommitment cp.2 = cp.1 := by
      intro cp hcp
      obtain ⟨pre, hmem, hcpeq⟩ := List.mem_map.mp hcp
      have htok : pre.token = assetOutcome.asset := by
        rcases List.mem_append.mp hmem with hc1 | hc2
        · obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hc1
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl
        · by_cases hrem : remainder = 0
          · rw [if_pos hrem] at hc2; exact absurd hc2 (List.not_mem_nil)
          · rw [if_neg hrem] at hc2
            rw [List.mem_singleton] at hc2
            exact hc2 ▸ rfl
      rw [← hcpeq]
      show hashCommitment pre = commitment pre.npk assetOutcome.asset pre.value
      rw [← htok]
      rfl
    have hrelated : ∀ (hpre : s'.pool.preimageOf = applyRecords s.pool.preimageOf
        (((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)))),
        remainder ≠ 0 → commitment (Term.val s.self) assetOutcome.asset remainder = qc →
        ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
      intro hpre hrem hqc
      have hnz : ¬ isZeroPreimage (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage) :=
        fun hz => hrem hz.2.1
      have hmemout : (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage) ∈
          ((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])) := by
        rw [if_neg hrem]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      have hmemout2 : (qc, (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)) ∈
          ((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)) := by
        rw [← hqc]
        exact List.mem_map.mpr ⟨_, hmemout, rfl⟩
      refine ⟨⟨Term.val s.self, assetOutcome.asset, remainder⟩, ?_, hrem, hqc⟩
      rw [hpre]
      exact applyRecords_reads hvalid_outputs s.pool.preimageOf qc
        (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage) hmemout2 hnz
    have hunrelated : ∀ (hpre : s'.pool.preimageOf = applyRecords s.pool.preimageOf
        (((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)))),
        s.holdings qasset qcid = some (qpos, qc) →
        ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
      intro hpre hc'
      obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qpos qc hc'
      refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
      rw [hpre]
      exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre_old hpre_old hconsist_old
    rcases hc0 : s.holdings assetOutcome.asset cid with _ | c0
    · simp only [hc0] at hmatch
      obtain ⟨w, pub, _hM, hC, _spent', _randomOut, hNonZero, _hCapacity, _hown, htoken, hnewnotes,
        _hroot, _hmark, _hRandomOut, heq⟩ := hmatch
      have hrecordseq : ownedOutputRecords w pub = ((transferEffects assetOutcome.allocations
          (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)) := by
        have hstep1 := congrArg
          (List.map (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre))) hnewnotes
        rw [← hstep1]
        unfold ownedOutputRecords ownedNewNotes
        rw [List.map_ofFn]
        congr 1
        funext j
        congr 1
        exact (hC.outputs j).trans (by rw [htoken])
      have hpre0 : s'.pool.preimageOf = applyRecords s.pool.preimageOf
          (((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
              (fun a => if a.amount = 0 then none
                else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
            (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
            (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre))) := by
        rw [← hrecordseq]
        exact congrArg PoolState.preimageOf heq
      by_cases heqch : qasset = assetOutcome.asset ∧ qcid = cid
      · obtain ⟨ha, hcid⟩ := heqch
        subst ha; subst hcid
        rw [if_pos rfl, if_pos rfl] at hc
        by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc; exact absurd hc (by simp)
        · rw [if_neg hrem] at hc
          exact hrelated hpre0 hrem (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hc).2
      · have hc' : s.holdings qasset qcid = some (qpos, qc) := by
          by_cases ha : qasset = assetOutcome.asset
          · subst ha
            by_cases hcid : qcid = cid
            · exact absurd ⟨rfl, hcid⟩ heqch
            · rw [if_pos rfl, if_neg hcid] at hc; exact hc
          · rw [if_neg ha] at hc; exact hc
        exact hunrelated hpre0 hc'
    · simp only [hc0] at hmatch
      obtain ⟨w, pub, _, hC, _, _, _, hNonZero, _, _, htoken, hnewnotes, _, _, _, _, _, _, heq⟩ := hmatch
      have hrecordseq : ownedOutputRecords w pub = ((transferEffects assetOutcome.allocations
          (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)) := by
        have hstep1 := congrArg
          (List.map (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre))) hnewnotes
        rw [← hstep1]
        unfold ownedOutputRecords ownedNewNotes
        rw [List.map_ofFn]
        congr 1
        funext j
        congr 1
        exact (hC.outputs j).trans (by rw [htoken])
      have hpre0 : s'.pool.preimageOf = applyRecords s.pool.preimageOf
          (((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
              (fun a => if a.amount = 0 then none
                else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
            (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
            (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre))) := by
        rw [← hrecordseq]
        exact congrArg PoolState.preimageOf heq
      by_cases heqch : qasset = assetOutcome.asset ∧ qcid = cid
      · obtain ⟨ha, hcid⟩ := heqch
        subst ha; subst hcid
        rw [if_pos rfl, if_pos rfl] at hc
        by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc; exact absurd hc (by simp)
        · rw [if_neg hrem] at hc
          exact hrelated hpre0 hrem (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hc).2
      · have hc' : s.holdings qasset qcid = some (qpos, qc) := by
          by_cases ha : qasset = assetOutcome.asset
          · subst ha
            by_cases hcid : qcid = cid
            · exact absurd ⟨rfl, hcid⟩ heqch
            · rw [if_pos rfl, if_neg hcid] at hc; exact hc
          · rw [if_neg ha] at hc; exact hc
        exact hunrelated hpre0 hc'
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _hsa, _hidx1, _h5, _h6, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | bulkTransferAllAssets channelId outcome claimedStateHash => exact hstep.elim
  | bulkConcludeAndTransferAllAssets fp candidate => exact hstep.elim
  | tick newNow =>
    obtain ⟨_, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | signNote pk msgHash =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
/-- Tagging a `List.ofFn` batch with positions names exactly `(start + i, f i)` at each
    index `i` — the membership form `withPositionsFrom_map` does not give directly. -/
theorem withPositionsFrom_ofFn {α : Type} {N : Nat} (start : Nat) (f : Fin N → α) :
    withPositionsFrom start (List.ofFn f) = List.ofFn (fun i : Fin N => (start + i.val, f i)) := by
  induction N generalizing start with
  | zero => simp [List.ofFn_zero, withPositionsFrom]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    unfold withPositionsFrom
    congr 1
    rw [show (fun i : Fin n => f i.succ) = (f ∘ Fin.succ) from rfl, ih (start + 1) (f ∘ Fin.succ)]
    congr 1
    funext i
    simp [Function.comp]
    omega

/-- Tagging an appended list splits into tagging each half, the second half's
    tags continuing on from where the first half's left off. Used to locate a
    `.transfer` call's own remainder note, appended after its payout notes, at
    its exact position within `withPositionsFrom`. -/
theorem withPositionsFrom_append {α : Type} (start : Nat) (l1 l2 : List α) :
    withPositionsFrom start (l1 ++ l2) =
      withPositionsFrom start l1 ++ withPositionsFrom (start + l1.length) l2 := by
  induction l1 generalizing start with
  | nil => simp [withPositionsFrom]
  | cons a rest ih =>
    show (start, a) :: withPositionsFrom (start + 1) (rest ++ l2) =
        ((start, a) :: withPositionsFrom (start + 1) rest) ++ withPositionsFrom (start + (a :: rest).length) l2
    rw [List.cons_append, ih (start + 1)]
    congr 3
    rw [List.length_cons]
    omega

/-- A position-tagged pair's membership in `withPositionsFrom` drops to its own
    preimage's membership in the underlying list, positions forgotten. -/
theorem withPositionsFrom_mem_snd {α : Type} {start : Nat} {l : List α} {pos : Nat} {a : α}
    (h : (pos, a) ∈ withPositionsFrom start l) : a ∈ l := by
  have hmap : a ∈ (withPositionsFrom start l).map (fun p : Nat × α => id p.2) :=
    List.mem_map.mpr ⟨(pos, a), h, rfl⟩
  rwa [withPositionsFrom_map id, List.map_id] at hmap

/-- The combined invariant `holdings_point_to_live_notes`/`value_exists_only_as_notes`
    (`Safety.lean`) need, one `Step` at a time: a holding names exactly one leaf
    position, that position is live with the holding's own commitment, it is within
    the pool's own leaf range, and no two DIFFERENT holdings ever name the same
    position (`.deposit`/`.transfer`/merge always write a FRESH position — at least
    `before.leaves.length`, strictly above every existing holding's own position by
    the bound clause — so the freshly-written position can never collide with an
    unrelated holding's; `removeAll` then only ever removes the exact `(position,
    preimage)` pairs this step's own witness names, so an unrelated holding's own pair
    survives by the same freshness argument applied at the PRIOR state). Positions,
    not commitments: two different channels' notes can carry the identical commitment
    (two deposits that reuse randomness, or two `.transfer` remainders, whose own
    commitment `commitment (Term.val self) asset remainder` carries no randomness at
    all), but they can never share a leaf position — `Pool.lean`'s module comment. -/
theorem holdings_position_live_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ s.pool.live qasset ∧ hashCommitment pre = qc ∧
        (pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r)) ∧
      qpos < s.pool.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', s.holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos))
    (hstep : Step sig appRel actor s call s') :
    ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ s'.pool.live qasset ∧ hashCommitment pre = qc ∧
        (pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r)) ∧
      qpos < s'.pool.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', s'.holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  have userDisjoint : ∀ (pre : CommitmentPreimage),
      (pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r) →
      ∀ pk' nk' r', pre.npk ≠ npk (masterPublicKey pk' nk') r' := by
    intro pre hown pk' nk' r' hcontra
    rcases hown with h1 | ⟨r, h2⟩
    · rw [h1] at hcontra
      exact Term.val_ne_hash s.self _ hcontra
    · rw [h2] at hcontra
      exact user_npk_ne_contract_npk hcontra.symm
  have trivial : s'.pool = s.pool → s'.holdings = s.holdings →
      ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
        (∃ pre, (qpos, pre) ∈ s'.pool.live qasset ∧ hashCommitment pre = qc ∧
          (pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r)) ∧
        qpos < s'.pool.leaves.length ∧
        (∀ qasset' qcid' qpos' qc', s'.holdings qasset' qcid' = some (qpos', qc') →
          (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
    intro hpool hhold qasset qcid qpos qc hc
    rw [hpool]
    rw [hhold] at hc
    obtain ⟨h1, h2, h3⟩ := hinv qasset qcid qpos qc hc
    refine ⟨h1, h2, ?_⟩
    intro qasset' qcid' qpos' qc' hc'
    rw [hhold] at hc'
    exact h3 qasset' qcid' qpos' qc' hc'
  cases call with
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpool, hhold, _⟩ := hstep
    exact trivial hpool hhold
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpool, hhold, _⟩ := hstep
    exact trivial hpool hhold
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpool, hhold, _⟩ := hstep
    exact trivial hpool hhold
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, hpool, hhold, _⟩ := hstep
    exact trivial hpool hhold
  | bulkTransferAllAssets _ _ _ => exact hstep.elim
  | bulkConcludeAndTransferAllAssets _ _ => exact hstep.elim
  | tick newNow =>
    obtain ⟨_, _, hpool, hhold, _⟩ := hstep
    exact trivial hpool hhold
  | sign p d =>
    obtain ⟨_, _, hpool, _, hhold, _⟩ := hstep
    exact trivial hpool hhold
  | signNote pk msgHash =>
    obtain ⟨_, _, hpool, _, hhold, _⟩ := hstep
    exact trivial hpool hhold
  | deposit channelId0 expectedHeld tok amount =>
    have hstep0 := hstep
    obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hselfeq, _hnow, _hsigned⟩ := hstep0
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, hmatch⟩ := hinner
    obtain ⟨r, hown, hcommit, htoken, hposition, hN, hM, hC, rest, spent', records, hCapacity,
      hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
      fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
    have hcap : (transactAllOutputs w).length = M := List.length_ofFn
    rcases hh : s.holdings tok channelId0 with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, hholdseq⟩ := hmatch
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc; unfold update at hc
      by_cases ha : qasset = tok
      · subst ha
        by_cases hcid : qcid = channelId0
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          have hqc : (position, pub.commitmentsOut idx) = (qpos, qc) := Option.some.inj hc
          have hpeq : position = qpos := (Prod.ext_iff.mp hqc).1
          have hceq : pub.commitmentsOut idx = qc := (Prod.ext_iff.mp hqc).2
          have hown2 : (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage).npk =
              Term.val s.self ∨ ∃ r', (⟨w.npkOut idx, w.token, w.valueOut idx⟩ :
                CommitmentPreimage).npk = npk (Term.val s.self) r' :=
            Or.inr ⟨r, hown⟩
          refine ⟨⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, ?_, ?_, hown2⟩, ?_, ?_⟩
          · rw [hpoolEq, heq]
            show (qpos, (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage)) ∈
                (if qasset = w.token then
                    withPositionsFrom s.pool.leaves.length (transactAllOutputs w) ++ rest
                  else s.pool.live qasset)
            rw [if_pos htoken.symm, ← hpeq, hposition]
            apply List.mem_append.mpr
            left
            unfold transactAllOutputs
            rw [withPositionsFrom_ofFn]
            exact List.mem_ofFn.mpr ⟨idx, rfl⟩
          · exact (hC.outputs idx).symm.trans hceq
          · rw [hpoolEq, heq]
            show qpos < (s.pool.leaves ++ (transactAllOutputs w).map hashCommitment).length
            rw [List.length_append, List.length_map, hcap, ← hpeq, hposition]
            omega
          · intro qasset' qcid' qpos' qc' hc'
            rw [hholdseq] at hc'; unfold update at hc'
            intro hne
            by_cases ha' : qasset' = qasset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = qcid
              · exact absurd (Prod.ext ha' hcid') hne
              · rw [if_neg hcid'] at hc'
                obtain ⟨_, hbound_old2, _⟩ := hinv qasset qcid' qpos' qc' hc'
                omega
            · rw [if_neg ha'] at hc'
              obtain ⟨_, hbound_old2, _⟩ := hinv qasset' qcid' qpos' qc' hc'
              omega
        · rw [if_pos rfl, if_neg hcid] at hc
          have hc2 : s.holdings qasset qcid = some (qpos, qc) := hc
          obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
            hinv qasset qcid qpos qc hc2
          refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
          · rw [hpoolEq, heq]
            show (qpos, pre_old) ∈
                (if qasset = w.token then
                    withPositionsFrom s.pool.leaves.length (transactAllOutputs w) ++ rest
                  else s.pool.live qasset)
            rw [if_pos htoken.symm]
            apply List.mem_append.mpr
            right
            have hsp0 : (qpos, pre_old) ∉ transactSpentPositions w := by
              intro hmemspent
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
              have hpreeq : pre_old = (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j),
                  w.token, w.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
              exact userDisjoint pre_old hown_old w.publicKey w.nullifyingKey (w.randomIn j)
                (by rw [hpreeq])
            have hmemperm : (qpos, pre_old) ∈ transactSpentPositions w ++ rest :=
              (removeAll_perm hRemove).mem_iff.mp (htoken ▸ hpre_old)
            exact (List.mem_append.mp hmemperm).resolve_left hsp0
          · rw [hpoolEq, heq]
            show qpos < (s.pool.leaves ++ (transactAllOutputs w).map hashCommitment).length
            rw [List.length_append]
            omega
          · intro qasset' qcid' qpos' qc' hc'
            rw [hholdseq] at hc'; unfold update at hc'
            intro hne
            by_cases ha' : qasset' = qasset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = channelId0
              · rw [if_pos hcid'] at hc'
                have hqc' : (position, pub.commitmentsOut idx) = (qpos', qc') := Option.some.inj hc'
                have hpeq' : position = qpos' := (Prod.ext_iff.mp hqc').1
                rw [← hpeq', hposition]
                omega
              · rw [if_neg hcid'] at hc'
                exact hdist_old qasset qcid' qpos' qc' hc' (fun h =>
                  hne (ha' ▸ h : (qasset', qcid') = (qasset, qcid)))
            · rw [if_neg ha'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' hc' (fun h => ha' (congrArg Prod.fst h))
      · have hc2 : s.holdings qasset qcid = some (qpos, qc) := by
          rw [if_neg ha] at hc; exact hc
        obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
          hinv qasset qcid qpos qc hc2
        refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
        · rw [hpoolEq, heq]
          show (qpos, pre_old) ∈
              (if qasset = w.token then
                  withPositionsFrom s.pool.leaves.length (transactAllOutputs w) ++ rest
                else s.pool.live qasset)
          rw [if_neg (htoken ▸ ha)]
          exact hpre_old
        · rw [hpoolEq, heq]
          show qpos < (s.pool.leaves ++ (transactAllOutputs w).map hashCommitment).length
          rw [List.length_append]
          omega
        · intro qasset' qcid' qpos' qc' hc'
          rw [hholdseq] at hc'; unfold update at hc'
          intro hne
          by_cases ha' : qasset' = tok
          · subst ha'
            by_cases hcid' : qcid' = channelId0
            · subst hcid'
              rw [if_pos rfl, if_pos rfl] at hc'
              have hqc' : (position, pub.commitmentsOut idx) = (qpos', qc') := Option.some.inj hc'
              have hpeq' : position = qpos' := (Prod.ext_iff.mp hqc').1
              rw [hposition] at hpeq'
              omega
            · rw [if_pos rfl, if_neg hcid'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' hc' (fun h => ha (congrArg Prod.fst h).symm)
          · rw [if_neg ha'] at hc'
            exact hdist_old qasset' qcid' qpos' qc' hc' hne
    · obtain ⟨oldPos, oldHoldingVal⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergedPos, hmerge, hholdseq⟩ := hmatch
      obtain ⟨hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity',
        hown', htoken', hnpkOut', hmergedEq, hleaf0, hleaf1, hcommitOld, hcommitNew, hroot',
        hremove', hnullify', hrandomOut', heq'⟩ := hmerge
      obtain ⟨⟨preOld, hpreOld, hvalOld, hownOld⟩, hboundOld, hdistOld⟩ :=
        hinv tok channelId0 oldPos oldHoldingVal hh
      have hsurvivesDeposit : ∀ (pos : Nat) (pre : CommitmentPreimage),
          (pre.npk = Term.val s.self ∨ ∃ r'', pre.npk = npk (Term.val s.self) r'') →
          (pos, pre) ∈ s.pool.live tok → (pos, pre) ∈ midPool.live tok := by
        intro pos pre hownpre hmem
        rw [heq]
        show (pos, pre) ∈
            (if tok = w.token then withPositionsFrom s.pool.leaves.length (transactAllOutputs w) ++ rest
              else s.pool.live tok)
        rw [if_pos htoken.symm]
        apply List.mem_append.mpr
        right
        have hsp0 : (pos, pre) ∉ transactSpentPositions w := by
          intro hmemspent
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
          have hpreeq : pre = (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j),
              w.token, w.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
          exact userDisjoint pre hownpre w.publicKey w.nullifyingKey (w.randomIn j) (by rw [hpreeq])
        have hmemperm : (pos, pre) ∈ transactSpentPositions w ++ rest :=
          (removeAll_perm hRemove).mem_iff.mp (htoken ▸ hmem)
        exact (List.mem_append.mp hmemperm).resolve_left hsp0
      have hsurvivesMerge : ∀ (pos : Nat) (pre : CommitmentPreimage),
          pos ≠ oldPos → pos ≠ position →
          (pos, pre) ∈ midPool.live tok → (pos, pre) ∈ s'.pool.live tok := by
        intro pos pre hneOld hneFresh hmem
        rw [heq']
        show (pos, pre) ∈
            (if tok = tok then withPositionsFrom midPool.leaves.length (ownedNewNotes w') ++ rest'
              else midPool.live tok)
        rw [if_pos rfl]
        apply List.mem_append.mpr
        right
        have hsp0 : (pos, pre) ∉ ownedSpentPositions pub' w' := by
          intro hmemspent
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
          match j with
          | 0 => exact hneOld ((congrArg Prod.fst hj).symm.trans hleaf0)
          | 1 => exact hneFresh ((congrArg Prod.fst hj).symm.trans hleaf1)
        have hmemperm : (pos, pre) ∈ ownedSpentPositions pub' w' ++ rest' :=
          (removeAll_perm hremove').mem_iff.mp hmem
        exact (List.mem_append.mp hmemperm).resolve_left hsp0
      have hmidLen : s.pool.leaves.length ≤ midPool.leaves.length := by
        rw [heq]
        show s.pool.leaves.length ≤ (s.pool.leaves ++ (transactAllOutputs w).map hashCommitment).length
        rw [List.length_append]
        omega
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc; unfold update at hc
      by_cases ha : qasset = tok
      · subst ha
        by_cases hcid : qcid = channelId0
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          have hqc : (mergedPos, merged) = (qpos, qc) := Option.some.inj hc
          have hpeq : mergedPos = qpos := (Prod.ext_iff.mp hqc).1
          have hceq : merged = qc := (Prod.ext_iff.mp hqc).2
          have hown2 : (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage).npk =
              Term.val s.self ∨ ∃ r'', (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ :
                CommitmentPreimage).npk = npk (Term.val s.self) r'' :=
            Or.inr ⟨r', hnpkOut'⟩
          refine ⟨⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, ?_, ?_, hown2⟩, ?_, ?_⟩
          · rw [heq']
            show (qpos, (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage)) ∈
                (if qasset = qasset then
                    withPositionsFrom midPool.leaves.length (ownedNewNotes w') ++ rest'
                  else midPool.live qasset)
            rw [if_pos rfl, ← hpeq, hmergedPos]
            apply List.mem_append.mpr
            left
            unfold ownedNewNotes
            rw [withPositionsFrom_ofFn]
            exact List.mem_ofFn.mpr ⟨0, rfl⟩
          · rw [hmergedEq] at hceq
            exact (hC'.outputs 0).symm.trans hceq
          · rw [heq']
            show qpos < (midPool.leaves ++ (ownedNewNotes w').map hashCommitment).length
            rw [List.length_append, List.length_map]
            have : (ownedNewNotes w').length = 1 := List.length_ofFn
            omega
          · intro qasset' qcid' qpos' qc' hc'
            rw [hholdseq] at hc'; unfold update at hc'
            intro hne
            by_cases ha' : qasset' = qasset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = qcid
              · exact absurd (by rw [ha', hcid']) hne
              · rw [if_neg hcid'] at hc'
                obtain ⟨_, hbound_old2, _⟩ := hinv qasset qcid' qpos' qc' hc'
                omega
            · rw [if_neg ha'] at hc'
              obtain ⟨_, hbound_old2, _⟩ := hinv qasset' qcid' qpos' qc' hc'
              omega
        · rw [if_pos rfl, if_neg hcid] at hc
          have hc2 : s.holdings qasset qcid = some (qpos, qc) := hc
          obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
            hinv qasset qcid qpos qc hc2
          have hqposneold : qpos ≠ oldPos :=
            hdistOld qasset qcid qpos qc hc2 (fun h => hcid (congrArg Prod.snd h))
          have hqposnefresh : qpos ≠ position := by
            intro heqpos
            rw [heqpos, hposition] at hbound_old
            omega
          have hmidmem : (qpos, pre_old) ∈ midPool.live qasset :=
            hsurvivesDeposit qpos pre_old hown_old hpre_old
          refine ⟨⟨pre_old, hsurvivesMerge qpos pre_old hqposneold hqposnefresh hmidmem, hval_old,
            hown_old⟩, ?_, ?_⟩
          · rw [heq']
            show qpos < (midPool.leaves ++ (ownedNewNotes w').map hashCommitment).length
            rw [List.length_append]
            omega
          · intro qasset' qcid' qpos' qc' hc'
            rw [hholdseq] at hc'; unfold update at hc'
            intro hne
            by_cases ha' : qasset' = qasset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = channelId0
              · rw [if_pos hcid'] at hc'
                have hqc' : (mergedPos, merged) = (qpos', qc') := Option.some.inj hc'
                have hpeq' : mergedPos = qpos' := (Prod.ext_iff.mp hqc').1
                rw [← hpeq', hmergedPos]
                omega
              · rw [if_neg hcid'] at hc'
                exact hdist_old qasset qcid' qpos' qc' hc' (fun h =>
                  hne (ha' ▸ h : (qasset', qcid') = (qasset, qcid)))
            · rw [if_neg ha'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' hc' (fun h => ha' (congrArg Prod.fst h))
      · have hc2 : s.holdings qasset qcid = some (qpos, qc) := by
          rw [if_neg ha] at hc; exact hc
        obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
          hinv qasset qcid qpos qc hc2
        have hqposneold : qpos ≠ oldPos :=
          hdistOld qasset qcid qpos qc hc2 (fun h => ha (congrArg Prod.fst h))
        have hqposnefresh : qpos ≠ position := by
          intro heqpos
          rw [heqpos, hposition] at hbound_old
          omega
        have hmidmem : (qpos, pre_old) ∈ midPool.live qasset := by
          rw [heq]
          show (qpos, pre_old) ∈
              (if qasset = w.token then
                  withPositionsFrom s.pool.leaves.length (transactAllOutputs w) ++ rest
                else s.pool.live qasset)
          rw [if_neg (htoken ▸ ha)]
          exact hpre_old
        refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
        · rw [heq']
          show (qpos, pre_old) ∈
              (if qasset = tok then
                  withPositionsFrom midPool.leaves.length (ownedNewNotes w') ++ rest'
                else midPool.live qasset)
          rw [if_neg ha]
          exact hmidmem
        · rw [heq']
          show qpos < (midPool.leaves ++ (ownedNewNotes w').map hashCommitment).length
          rw [List.length_append]
          omega
        · intro qasset' qcid' qpos' qc' hc'
          rw [hholdseq] at hc'; unfold update at hc'
          intro hne
          by_cases ha' : qasset' = tok
          · subst ha'
            by_cases hcid' : qcid' = channelId0
            · subst hcid'
              rw [if_pos rfl, if_pos rfl] at hc'
              have hqc' : (mergedPos, merged) = (qpos', qc') := Option.some.inj hc'
              have hpeq' : mergedPos = qpos' := (Prod.ext_iff.mp hqc').1
              rw [← hpeq', hmergedPos]
              omega
            · rw [if_pos rfl, if_neg hcid'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' hc' (fun h => ha (congrArg Prod.fst h).symm)
          · rw [if_neg ha'] at hc'
            exact hdist_old qasset' qcid' qpos' qc' hc' hne
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨hmatch, hholdseq, _hchanseq⟩ := hrest
    change PoolOwnedSpendStep s.pool s.self (outcome.get ⟨assetIndex, hidx⟩).asset
      (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid)
      ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
        if a.amount = 0 then none
        else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ : CommitmentPreimage)) ++
        (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
            (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
         then []
         else [(⟨Term.val s.self, (outcome.get ⟨assetIndex, hidx⟩).asset,
           heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
             (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ : CommitmentPreimage)]))
      s'.pool at hmatch
    change s'.holdings = update s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset
      (update (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset) cid
        (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
            (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
         then none
         else some (s.pool.leaves.length +
             ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
                 if a.amount = 0 then none
                 else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ :
                   CommitmentPreimage)) ++
               (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                   (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                     (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
                then []
                else [(⟨Term.val s.self, (outcome.get ⟨assetIndex, hidx⟩).asset,
                  heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                    (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ :
                    CommitmentPreimage)])).length - 1,
           commitment (Term.val s.self) (outcome.get ⟨assetIndex, hidx⟩).asset
             (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
               (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2)))) at hholdseq
    generalize hAO : outcome.get ⟨assetIndex, hidx⟩ = assetOutcome at hmatch hholdseq
    generalize hRemDef : heldValue s assetOutcome.asset cid -
      (transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.2 =
      remainder at hmatch hholdseq
    generalize hOutDef : ((transferEffects assetOutcome.allocations
        (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
          if a.amount = 0 then none
          else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
        (if remainder = 0 then [] else [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])) =
      outputs at hmatch hholdseq
    rcases hh : s.holdings assetOutcome.asset cid with _ | ⟨oldPos, oldC⟩
    · rw [hh] at hmatch
      obtain ⟨w, pub, hM, hC, spent', randomOut, hNonZero, hCapacity, hself0, htoken, houtpre,
        hroot, hmarkspent, hrandomOut, heq⟩ := hmatch
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc; unfold update at hc
      by_cases ha : qasset = assetOutcome.asset
      · rw [if_pos ha] at hc
        rw [ha]
        by_cases hcid : qcid = cid
        · rw [if_pos hcid] at hc
          rw [hcid]
          by_cases hrem : remainder = 0
          · rw [if_pos hrem] at hc; exact absurd hc (by simp)
          · rw [if_neg hrem] at hc
            have hqc : (s.pool.leaves.length + outputs.length - 1,
                commitment (Term.val s.self) assetOutcome.asset remainder) = (qpos, qc) :=
              Option.some.inj hc
            have hpeq : s.pool.leaves.length + outputs.length - 1 = qpos := (Prod.ext_iff.mp hqc).1
            have hceq : commitment (Term.val s.self) assetOutcome.asset remainder = qc :=
              (Prod.ext_iff.mp hqc).2
            have hsplit : outputs = (transferEffects assetOutcome.allocations
                (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
                  if a.amount = 0 then none
                  else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
                [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)] := by
              rw [← hOutDef, if_neg hrem]
            have hlen : outputs.length = ((transferEffects assetOutcome.allocations
                (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
                  if a.amount = 0 then none
                  else some (⟨a.destination, assetOutcome.asset, a.amount⟩ :
                    CommitmentPreimage))).length + 1 := by
              rw [hsplit, List.length_append, List.length_singleton]
            have hown2 : (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage).npk =
                Term.val s.self ∨ ∃ r'', (⟨Term.val s.self, assetOutcome.asset, remainder⟩ :
                  CommitmentPreimage).npk = npk (Term.val s.self) r'' := Or.inl rfl
            refine ⟨⟨⟨Term.val s.self, assetOutcome.asset, remainder⟩, ?_, ?_, hown2⟩, ?_, ?_⟩
            · rw [heq]
              show (qpos, (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)) ∈
                  (if assetOutcome.asset = assetOutcome.asset then
                      withPositionsFrom s.pool.leaves.length outputs ++ s.pool.live assetOutcome.asset
                    else s.pool.live assetOutcome.asset)
              have hposeq : s.pool.leaves.length + outputs.length - 1 =
                  s.pool.leaves.length + ((transferEffects assetOutcome.allocations
                    (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
                      if a.amount = 0 then none
                      else some (⟨a.destination, assetOutcome.asset, a.amount⟩ :
                        CommitmentPreimage))).length := by omega
              rw [if_pos rfl, ← hpeq, hposeq, hsplit, withPositionsFrom_append]
              apply List.mem_append.mpr
              left
              apply List.mem_append.mpr
              right
              simp [withPositionsFrom]
            · exact hceq
            · rw [heq]
              show qpos < (s.pool.leaves ++ outputs.map hashCommitment).length
              rw [List.length_append, List.length_map]
              omega
            · intro qasset' qcid' qpos' qc' hc'
              rw [hholdseq] at hc'; unfold update at hc'
              intro hne
              by_cases ha' : qasset' = assetOutcome.asset
              · rw [if_pos ha'] at hc'
                by_cases hcid' : qcid' = cid
                · exact absurd (show (qasset', qcid') = (assetOutcome.asset, cid) by
                    rw [ha', hcid']) hne
                · rw [if_neg hcid'] at hc'
                  obtain ⟨_, hbound_old2, _⟩ := hinv assetOutcome.asset qcid' qpos' qc' hc'
                  omega
              · rw [if_neg ha'] at hc'
                obtain ⟨_, hbound_old2, _⟩ := hinv qasset' qcid' qpos' qc' hc'
                omega
        · rw [if_neg hcid] at hc
          have hc2 : s.holdings qasset qcid = some (qpos, qc) := ha ▸ hc
          obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
            hinv qasset qcid qpos qc hc2
          refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
          · rw [heq]
            show (qpos, pre_old) ∈
                (if assetOutcome.asset = assetOutcome.asset then
                    withPositionsFrom s.pool.leaves.length outputs ++ s.pool.live assetOutcome.asset
                  else s.pool.live assetOutcome.asset)
            rw [if_pos rfl]
            exact List.mem_append.mpr (Or.inr (ha ▸ hpre_old))
          · rw [heq]
            show qpos < (s.pool.leaves ++ outputs.map hashCommitment).length
            rw [List.length_append]
            omega
          · intro qasset' qcid' qpos' qc' hc'
            rw [hholdseq] at hc'; unfold update at hc'
            intro hne
            by_cases ha' : qasset' = assetOutcome.asset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = cid
              · rw [if_pos hcid'] at hc'
                by_cases hrem : remainder = 0
                · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
                · rw [if_neg hrem] at hc'
                  have hqc' : (s.pool.leaves.length + outputs.length - 1,
                      commitment (Term.val s.self) assetOutcome.asset remainder) = (qpos', qc') :=
                    Option.some.inj hc'
                  have hpeq' : s.pool.leaves.length + outputs.length - 1 = qpos' :=
                    (Prod.ext_iff.mp hqc').1
                  have houtlen1 : outputs.length ≥ 1 := by
                    rw [← hOutDef, if_neg hrem, List.length_append, List.length_singleton]
                    omega
                  omega
              · rw [if_neg hcid'] at hc'
                exact hdist_old qasset qcid' qpos' qc' (ha ▸ hc')
                  (fun h => by
                    injection h with _ hqc
                    exact hne (by rw [ha', hqc]))
            · rw [if_neg ha'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' hc'
                (fun h => ha' ((congrArg Prod.fst h).trans ha))
      · have hc2 : s.holdings qasset qcid = some (qpos, qc) := by
          rw [if_neg ha] at hc; exact hc
        obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
          hinv qasset qcid qpos qc hc2
        refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
        · rw [heq]
          show (qpos, pre_old) ∈
              (if qasset = assetOutcome.asset then
                  withPositionsFrom s.pool.leaves.length outputs ++ s.pool.live qasset
                else s.pool.live qasset)
          rw [if_neg ha]
          exact hpre_old
        · rw [heq]
          show qpos < (s.pool.leaves ++ outputs.map hashCommitment).length
          rw [List.length_append]
          omega
        · intro qasset' qcid' qpos' qc' hc'
          rw [hholdseq] at hc'; unfold update at hc'
          intro hne
          by_cases ha' : qasset' = assetOutcome.asset
          · rw [if_pos ha'] at hc'
            by_cases hcid' : qcid' = cid
            · rw [if_pos hcid'] at hc'
              by_cases hrem : remainder = 0
              · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
              · rw [if_neg hrem] at hc'
                have hqc' : (s.pool.leaves.length + outputs.length - 1,
                    commitment (Term.val s.self) assetOutcome.asset remainder) = (qpos', qc') :=
                  Option.some.inj hc'
                have hpeq' : s.pool.leaves.length + outputs.length - 1 = qpos' :=
                  (Prod.ext_iff.mp hqc').1
                have houtlen1 : outputs.length ≥ 1 := by
                  rw [← hOutDef, if_neg hrem, List.length_append, List.length_singleton]
                  omega
                omega
            · rw [if_neg hcid'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' (ha' ▸ hc') hne
          · rw [if_neg ha'] at hc'
            exact hdist_old qasset' qcid' qpos' qc' hc' hne
    · rw [hh] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', randomOut, hNonZero, hCapacity, hself0, htoken, houtpre,
        hleavesIdx0, hcommitOld, hroot, hremove, hmarkspent, hrandomOut, heq⟩ := hmatch
      obtain ⟨⟨preOld, hpreOld, hvalOld, hownOld⟩, hboundOld, hdistOld⟩ :=
        hinv assetOutcome.asset cid oldPos oldC hh
      have hsurvivesSpend : ∀ (pos : Nat) (pre : CommitmentPreimage),
          pos ≠ oldPos →
          (pos, pre) ∈ s.pool.live assetOutcome.asset → (pos, pre) ∈ s'.pool.live assetOutcome.asset := by
        intro pos pre hnepos hmem
        rw [heq]
        show (pos, pre) ∈
            (if assetOutcome.asset = assetOutcome.asset then
                withPositionsFrom s.pool.leaves.length outputs ++ rest
              else s.pool.live assetOutcome.asset)
        rw [if_pos rfl]
        apply List.mem_append.mpr
        right
        have hsp0 : (pos, pre) ∉ ownedSpentPositions pub w := by
          intro hmemspent
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
          rw [Subsingleton.elim j 0] at hj
          exact hnepos ((congrArg Prod.fst hj).symm.trans hleavesIdx0)
        have hmemperm : (pos, pre) ∈ ownedSpentPositions pub w ++ rest :=
          (removeAll_perm hremove).mem_iff.mp hmem
        exact (List.mem_append.mp hmemperm).resolve_left hsp0
      have hmidLen : s.pool.leaves.length ≤ s'.pool.leaves.length := by
        rw [heq]
        show s.pool.leaves.length ≤ (s.pool.leaves ++ outputs.map hashCommitment).length
        rw [List.length_append]
        omega
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc; unfold update at hc
      by_cases ha : qasset = assetOutcome.asset
      · rw [if_pos ha] at hc
        rw [ha]
        by_cases hcid : qcid = cid
        · rw [if_pos hcid] at hc
          rw [hcid]
          by_cases hrem : remainder = 0
          · rw [if_pos hrem] at hc; exact absurd hc (by simp)
          · rw [if_neg hrem] at hc
            have hqc : (s.pool.leaves.length + outputs.length - 1,
                commitment (Term.val s.self) assetOutcome.asset remainder) = (qpos, qc) :=
              Option.some.inj hc
            have hpeq : s.pool.leaves.length + outputs.length - 1 = qpos := (Prod.ext_iff.mp hqc).1
            have hceq : commitment (Term.val s.self) assetOutcome.asset remainder = qc :=
              (Prod.ext_iff.mp hqc).2
            have hsplit : outputs = (transferEffects assetOutcome.allocations
                (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
                  if a.amount = 0 then none
                  else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
                [(⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)] := by
              rw [← hOutDef, if_neg hrem]
            have hlen : outputs.length = ((transferEffects assetOutcome.allocations
                (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
                  if a.amount = 0 then none
                  else some (⟨a.destination, assetOutcome.asset, a.amount⟩ :
                    CommitmentPreimage))).length + 1 := by
              rw [hsplit, List.length_append, List.length_singleton]
            have hown2 : (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage).npk =
                Term.val s.self ∨ ∃ r'', (⟨Term.val s.self, assetOutcome.asset, remainder⟩ :
                  CommitmentPreimage).npk = npk (Term.val s.self) r'' := Or.inl rfl
            refine ⟨⟨⟨Term.val s.self, assetOutcome.asset, remainder⟩, ?_, ?_, hown2⟩, ?_, ?_⟩
            · rw [heq]
              show (qpos, (⟨Term.val s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)) ∈
                  (if assetOutcome.asset = assetOutcome.asset then
                      withPositionsFrom s.pool.leaves.length outputs ++ rest
                    else s.pool.live assetOutcome.asset)
              have hposeq : s.pool.leaves.length + outputs.length - 1 =
                  s.pool.leaves.length + ((transferEffects assetOutcome.allocations
                    (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
                      if a.amount = 0 then none
                      else some (⟨a.destination, assetOutcome.asset, a.amount⟩ :
                        CommitmentPreimage))).length := by omega
              rw [if_pos rfl, ← hpeq, hposeq, hsplit, withPositionsFrom_append]
              apply List.mem_append.mpr
              left
              apply List.mem_append.mpr
              right
              simp [withPositionsFrom]
            · exact hceq
            · rw [heq]
              show qpos < (s.pool.leaves ++ outputs.map hashCommitment).length
              rw [List.length_append, List.length_map]
              omega
            · intro qasset' qcid' qpos' qc' hc'
              rw [hholdseq] at hc'; unfold update at hc'
              intro hne
              by_cases ha' : qasset' = assetOutcome.asset
              · rw [if_pos ha'] at hc'
                by_cases hcid' : qcid' = cid
                · exact absurd (show (qasset', qcid') = (assetOutcome.asset, cid) by
                    rw [ha', hcid']) hne
                · rw [if_neg hcid'] at hc'
                  obtain ⟨_, hbound_old2, _⟩ := hinv assetOutcome.asset qcid' qpos' qc' hc'
                  omega
              · rw [if_neg ha'] at hc'
                obtain ⟨_, hbound_old2, _⟩ := hinv qasset' qcid' qpos' qc' hc'
                omega
        · rw [if_neg hcid] at hc
          have hc2 : s.holdings qasset qcid = some (qpos, qc) := ha ▸ hc
          obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
            hinv qasset qcid qpos qc hc2
          have hqposneold : qpos ≠ oldPos :=
            hdistOld qasset qcid qpos qc hc2 (fun h => hcid (congrArg Prod.snd h))
          refine ⟨⟨pre_old, hsurvivesSpend qpos pre_old hqposneold (ha ▸ hpre_old), hval_old,
            hown_old⟩, ?_, ?_⟩
          · rw [heq]
            show qpos < (s.pool.leaves ++ outputs.map hashCommitment).length
            rw [List.length_append]
            omega
          · intro qasset' qcid' qpos' qc' hc'
            rw [hholdseq] at hc'; unfold update at hc'
            intro hne
            by_cases ha' : qasset' = assetOutcome.asset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = cid
              · rw [if_pos hcid'] at hc'
                by_cases hrem : remainder = 0
                · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
                · rw [if_neg hrem] at hc'
                  have hqc' : (s.pool.leaves.length + outputs.length - 1,
                      commitment (Term.val s.self) assetOutcome.asset remainder) = (qpos', qc') :=
                    Option.some.inj hc'
                  have hpeq' : s.pool.leaves.length + outputs.length - 1 = qpos' :=
                    (Prod.ext_iff.mp hqc').1
                  have houtlen1 : outputs.length ≥ 1 := by
                    rw [← hOutDef, if_neg hrem, List.length_append, List.length_singleton]
                    omega
                  omega
              · rw [if_neg hcid'] at hc'
                exact hdist_old qasset qcid' qpos' qc' (ha ▸ hc')
                  (fun h => by
                    injection h with _ hqc
                    exact hne (by rw [ha', hqc]))
            · rw [if_neg ha'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' hc'
                (fun h => ha' ((congrArg Prod.fst h).trans ha))
      · have hc2 : s.holdings qasset qcid = some (qpos, qc) := by
          rw [if_neg ha] at hc; exact hc
        obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
          hinv qasset qcid qpos qc hc2
        refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
        · rw [heq]
          show (qpos, pre_old) ∈
              (if qasset = assetOutcome.asset then
                  withPositionsFrom s.pool.leaves.length outputs ++ rest
                else s.pool.live qasset)
          rw [if_neg ha]
          exact hpre_old
        · rw [heq]
          show qpos < (s.pool.leaves ++ outputs.map hashCommitment).length
          rw [List.length_append]
          omega
        · intro qasset' qcid' qpos' qc' hc'
          rw [hholdseq] at hc'; unfold update at hc'
          intro hne
          by_cases ha' : qasset' = assetOutcome.asset
          · rw [if_pos ha'] at hc'
            by_cases hcid' : qcid' = cid
            · rw [if_pos hcid'] at hc'
              by_cases hrem : remainder = 0
              · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
              · rw [if_neg hrem] at hc'
                have hqc' : (s.pool.leaves.length + outputs.length - 1,
                    commitment (Term.val s.self) assetOutcome.asset remainder) = (qpos', qc') :=
                  Option.some.inj hc'
                have hpeq' : s.pool.leaves.length + outputs.length - 1 = qpos' :=
                  (Prod.ext_iff.mp hqc').1
                have houtlen1 : outputs.length ≥ 1 := by
                  rw [← hOutDef, if_neg hrem, List.length_append, List.length_singleton]
                  omega
                omega
            · rw [if_neg hcid'] at hc'
              exact hdist_old qasset' qcid' qpos' qc' (ha' ▸ hc') hne
          · rw [if_neg ha'] at hc'
            exact hdist_old qasset' qcid' qpos' qc' hc' hne

/-- A successful `.deposit` into a channel with NO prior holding sets
    `heldValue` to exactly its own `amount` argument (`DepositStep`'s own
    mechanics mint a note worth `amount` directly). When the channel
    already holds a note, `.deposit` instead MERGES — see
    `deposit_merge_sets_heldValue` below. The same `applyRecords_reads`
    read-back `holdings_preimage_nonzero_step`'s own `.deposit` case
    already uses. -/
theorem deposit_sets_heldValue
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (channelId : Term) (expectedHeld asset amount : Nat)
    (hstep : Step sig appRel actor s (.deposit channelId expectedHeld asset amount) s')
    (hnone : s.holdings asset channelId = none) :
    heldValue s' asset channelId = amount := by
  obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, hmatch⟩ := hinner
  obtain ⟨_r, _hown, hcommit, htoken, _hposition, _hN, _hM, hC, _rest, _spent', records, _hCapacity,
    _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
  rw [hnone] at hmatch
  obtain ⟨hpoolEq, hholdseq⟩ := hmatch
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have hval : w.valueOut idx = amount := by
    have hout := hC.outputs idx
    rw [htoken, hcommit] at hout
    exact (Term.val.inj (Term.hash3_inj hout).2.2).symm
  have hnz : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
    unfold isZeroPreimage
    intro ⟨_, hv, _⟩
    rw [hval] at hv
    have hcheck : amount = 0 := hv
    omega
  have hread := applyRecords_reads hvalid s.pool.preimageOf (pub.commitmentsOut idx)
    ⟨w.npkOut idx, w.token, w.valueOut idx⟩ hidxrec hnz
  unfold heldValue
  rw [hholdseq]
  unfold update
  rw [if_pos rfl, if_pos rfl]
  show ((s'.pool.preimageOf (pub.commitmentsOut idx)).map CommitmentPreimage.value).getD 0 = amount
  rw [hpoolEq, heq]
  dsimp only
  rw [hread]
  simp [hval]

/-- A successful `.deposit` into a channel that ALREADY holds a note
    increases `heldValue` by exactly `amount` — the two notes MERGE
    (`Notes.lean`'s `DepositMergeStep`), rather than the fresh note
    replacing or sitting alongside the old one. `depositBinding`
    (`ArmadaNitroAdjudicator.sol:60-72`) is exactly this: a deposit
    always adds to, never replaces, the prior holding. -/
theorem deposit_merge_sets_heldValue
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (channelId : Term) (expectedHeld asset amount : Nat)
    (hstep : Step sig appRel actor s (.deposit channelId expectedHeld asset amount) s')
    (hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (oldPos : Nat) (oldHolding : Term) (hsome : s.holdings asset channelId = some (oldPos, oldHolding)) :
    heldValue s' asset channelId = heldValue s asset channelId + amount := by
  obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, hmatch⟩ := hinner
  obtain ⟨_r, _hown, hcommit, htoken, _hposition, _hN, _hM, hC, _rest, _spent', records, _hCapacity,
    _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
  rw [hsome] at hmatch
  obtain ⟨merged, mergedPos, hmerge, hholdseq⟩ := hmatch
  obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv asset channelId oldPos oldHolding hsome
  obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity', hown',
    htoken', hnpkOut', hmergedEq, _hleaf0, _hleaf1, hcommitOld, hcommitNew, hroot', hremove',
    hnullify', _hrandomOut', heq'⟩ := hmerge
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have hvalNew : w.valueOut idx = amount := by
    have hout := hC.outputs idx
    rw [htoken, hcommit] at hout
    exact (Term.val.inj (Term.hash3_inj hout).2.2).symm
  have hnzNew : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
    unfold isZeroPreimage
    intro ⟨_, hv, _⟩
    rw [hvalNew] at hv
    have hcheck : amount = 0 := hv
    omega
  have hNewKey : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) =
      pub.commitmentsOut idx := hvalid _ hidxrec
  have hvalOld' : w'.valueIn 0 = pre_old.value := by
    have hh2 := hcommitOld.trans hconsist_old.symm
    unfold hashCommitment at hh2
    exact Term.val.inj (Term.hash3_inj hh2).2.2
  have hvalNewIn' : w'.valueIn 1 = amount := by
    have heqcommit : commitment (npk (Term.val pub'.ownerField) (w'.randomIn 1)) w'.token (w'.valueIn 1) =
        commitment (w.npkOut idx) w.token (w.valueOut idx) := hcommitNew.trans hNewKey.symm
    rw [← hvalNew]
    exact Term.val.inj (Term.hash3_inj heqcommit).2.2
  have hbalance := transactOwned_value_conserved w' pub' (by decide) (by decide) hC'
  have hvalOutSum : w'.valueOut 0 = w'.valueIn 0 + w'.valueIn 1 := by
    have hsum : w'.valueIn 0 + (w'.valueIn 1 + 0) = w'.valueOut 0 + 0 := hbalance
    omega
  have hvalOutPos : w'.valueOut 0 ≠ 0 := by
    rw [hvalOutSum, hvalOld']
    omega
  have hnzOut : ¬ isZeroPreimage (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) := by
    unfold isZeroPreimage
    intro ⟨_, hv, _⟩
    exact hvalOutPos hv
  have hreadM := applyRecords_reads (ownedOutputRecords_valid hC') midPool.preimageOf
    (pub'.commitmentsOut 0) ⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩
    (List.mem_ofFn.mpr ⟨0, rfl⟩) hnzOut
  unfold heldValue
  rw [hsome, hholdseq]
  unfold update
  rw [if_pos rfl, if_pos rfl]
  show ((s'.pool.preimageOf merged).map CommitmentPreimage.value).getD 0 =
    ((s.pool.preimageOf oldHolding).map CommitmentPreimage.value).getD 0 + amount
  rw [hmergedEq, heq']
  dsimp only
  rw [hreadM, hpre_old]
  simp [hvalOutSum, hvalOld', hvalNewIn']

/-- A channel id is never an external (address-sized) destination:
    `channelId fp` is always a `Term.hash` term (`channelIdOf`'s own
    definition, `Assumptions.lean`), and `isExternal` names only
    `Term.val` terms (`Outcome.lean`) — a raw value can never equal a
    genuine hash, by construction (`Term.val_ne_hash`). Replaces the
    old `exists_internal_channelId`/`no_long_nodup_bounded_list`
    pigeonhole argument the `Nat`-channelId model needed: with `Term`
    channel ids, EVERY `channelId fp` already satisfies `.deposit`'s
    `¬isExternal` requirement, for any `fp` at all. -/
theorem channelId_not_external (fp : FixedPart) : ¬ isExternal (channelId fp) := by
  rintro ⟨a, _, heq⟩
  unfold channelId channelIdOf at heq
  exact Term.val_ne_hash a _ heq.symm

end ArmadaLean.Adjudicator
