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
    (hinv : ∀ qasset qcid qc, s.holdings qasset qcid = some qc →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (hstep : Step sig appRel actor s call s') :
    ∀ qasset qcid qc, s'.holdings qasset qcid = some qc →
      ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
  cases call with
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, midPool, hdstep, hmatch⟩ := hinner
    obtain ⟨_hown, hcommit, htoken, _hN, _hM, hC, _rest, _spent', _newRoot, records,
      _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
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
      intro qasset qcid qc hc
      rw [hholdseq] at hc
      unfold update at hc
      by_cases ha : qasset = asset
      · subst ha
        by_cases hcid : qcid = channelId
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          have hqc : pub.commitmentsOut idx = qc := Option.some.inj hc
          rw [hqc] at hread
          refine ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, ?_, ?_, ?_⟩
          · rw [hpoolEq, heq]; exact hread
          · rw [hval]
            intro hz; have hcheck2 : amount = 0 := hz; omega
          · exact (hC.outputs idx).symm.trans hqc
        · rw [if_pos rfl, if_neg hcid] at hc
          obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qc hc
          refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
          rw [hpoolEq]
          exact hchain qc pre_old hpre_old hconsist_old
      · rw [if_neg ha] at hc
        obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qc hc
        refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
        rw [hpoolEq]
        exact hchain qc pre_old hpre_old hconsist_old
    · rw [hh] at hmatch
      obtain ⟨merged, hmerge, hholdseq⟩ := hmatch
      obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv asset channelId oldHolding hh
      obtain ⟨w', pub', hC', rest', spent'', r', hNonZero', hown', htoken', hnpkOut',
        hmergedEq, hcommitOld, hcommitNew, hroot', hremove', hnullify', heq'⟩ := hmerge
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
      intro qasset qcid qc hc
      rw [hholdseq] at hc
      unfold update at hc
      by_cases ha : qasset = asset
      · subst ha
        by_cases hcid : qcid = channelId
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          have hqc : merged = qc := Option.some.inj hc
          rw [hmergedEq] at hqc
          rw [hqc] at hreadM
          refine ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, ?_, hvalOutPos, ?_⟩
          · rw [heq']; exact hreadM
          · exact (hC'.outputs 0).symm.trans hqc
        · rw [if_pos rfl, if_neg hcid] at hc
          obtain ⟨pre_old2, hpre_old2, hval_old2, hconsist_old2⟩ := hinv qasset qcid qc hc
          exact ⟨pre_old2, hchain2 qc pre_old2 hpre_old2 hconsist_old2, hval_old2, hconsist_old2⟩
      · rw [if_neg ha] at hc
        obtain ⟨pre_old2, hpre_old2, hval_old2, hconsist_old2⟩ := hinv qasset qcid qc hc
        exact ⟨pre_old2, hchain2 qc pre_old2 hpre_old2 hconsist_old2, hval_old2, hconsist_old2⟩
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qc hc
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
         else some (commitment (Term.val s.self) (outcome.get ⟨assetIndex, hidx⟩).asset
           (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
             (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2)))) at hholdseq
    intro qasset qcid qc hc
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
        s.holdings qasset qcid = some qc →
        ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
      intro hpre hc'
      obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qc hc'
      refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
      rw [hpre]
      exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre_old hpre_old hconsist_old
    rcases hc0 : s.holdings assetOutcome.asset cid with _ | c0
    · simp only [hc0] at hmatch
      obtain ⟨w, pub, _hM, hC, _spent', _newRoot, hNonZero, _hown, htoken, hnewnotes,
        _hroot, _hmark, heq⟩ := hmatch
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
          exact hrelated hpre0 hrem (Option.some.inj hc)
      · have hc' : s.holdings qasset qcid = some qc := by
          by_cases ha : qasset = assetOutcome.asset
          · subst ha
            by_cases hcid : qcid = cid
            · exact absurd ⟨rfl, hcid⟩ heqch
            · rw [if_pos rfl, if_neg hcid] at hc; exact hc
          · rw [if_neg ha] at hc; exact hc
        exact hunrelated hpre0 hc'
    · simp only [hc0] at hmatch
      obtain ⟨w, pub, _, hC, _, _, _, hNonZero, _, htoken, hnewnotes, _, _, _, _, heq⟩ := hmatch
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
          exact hrelated hpre0 hrem (Option.some.inj hc)
      · have hc' : s.holdings qasset qcid = some qc := by
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
    intro qasset qcid qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | bulkTransferAllAssets channelId outcome claimedStateHash => exact hstep.elim
  | bulkConcludeAndTransferAllAssets fp candidate => exact hstep.elim
  | tick newNow =>
    obtain ⟨_, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    intro qasset qcid qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | signNote pk msgHash =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    intro qasset qcid qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩

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
  obtain ⟨N, M, w, pub, idx, midPool, hdstep, hmatch⟩ := hinner
  obtain ⟨_hown, hcommit, htoken, _hN, _hM, hC, _rest, _spent', _newRoot, records,
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
    (hinv : ∀ qasset qcid qc, s.holdings qasset qcid = some qc →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (oldHolding : Term) (hsome : s.holdings asset channelId = some oldHolding) :
    heldValue s' asset channelId = heldValue s asset channelId + amount := by
  obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨N, M, w, pub, idx, midPool, hdstep, hmatch⟩ := hinner
  obtain ⟨_hown, hcommit, htoken, _hN, _hM, hC, _rest, _spent', _newRoot, records,
    _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
  rw [hsome] at hmatch
  obtain ⟨merged, hmerge, hholdseq⟩ := hmatch
  obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv asset channelId oldHolding hsome
  obtain ⟨w', pub', hC', rest', spent'', r', hNonZero', hown', htoken', hnpkOut',
    hmergedEq, hcommitOld, hcommitNew, hroot', hremove', hnullify', heq'⟩ := hmerge
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

/-! ## Multiplicity: enough live copies for every holding sharing a value

Two different channels' deposits — or two different channels'
`.transfer` remainders, whose own commitment `commitment (Term.val
self) asset remainder` carries no randomness at all, only the shared
adjudicator address and a plain amount — can mint the IDENTICAL
commitment. `holdings_point_to_live_notes`/`value_exists_only_as_notes`
(`Safety.lean`) need the number of LIVE copies of any commitment's own
preimage to be at least the number of DISTINCT `(asset, channelId)`
holdings pointing at it, not just "some copy is live": a plain
membership invariant would not survive an UNRELATED channel's
`.transfer` consuming the shared value's only live copy.
-/

/-- `removeAll`'s own multiset identity (`removeAll_perm`,
    `ArmadaLean.Pool`), read as a count: the pool's count of any
    preimage splits exactly into the spent list's count and the
    remainder's count. -/
theorem removeAll_count {pool spent rest : List CommitmentPreimage}
    (h : removeAll pool spent = some rest) (pre : CommitmentPreimage) :
    List.count pre pool = List.count pre spent + List.count pre rest := by
  have hperm := (removeAll_perm h).count_eq pre
  rwa [List.count_append] at hperm

/-- The counting invariant `holdings_point_to_live_notes` needs, one
    `Step` at a time: every other `Step` case leaves both `holdings`
    and `pool` untouched (`trivial`, below); `.deposit` and `.transfer`
    are the only two that move value. -/
theorem holdings_live_count_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hnz : ∀ qasset qcid qc, s.holdings qasset qcid = some qc →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (hinv : ∀ asset (pre : CommitmentPreimage) (L : List Term), L.Nodup →
      (∀ cid ∈ L, s.holdings asset cid = some (hashCommitment pre)) →
      (0 < L.length → pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r) ∧
      L.length ≤ List.count pre (s.pool.live asset))
    (hstep : Step sig appRel actor s call s') :
    ∀ asset (pre : CommitmentPreimage) (L : List Term), L.Nodup →
      (∀ cid ∈ L, s'.holdings asset cid = some (hashCommitment pre)) →
      (0 < L.length → pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r) ∧
      L.length ≤ List.count pre (s'.pool.live asset) := by
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
      ∀ asset (pre : CommitmentPreimage) (L : List Term), L.Nodup →
        (∀ cid ∈ L, s'.holdings asset cid = some (hashCommitment pre)) →
        (0 < L.length → pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r) ∧
        L.length ≤ List.count pre (s'.pool.live asset) := by
    intro hpool hhold asset pre L hnodup hmem
    rw [hpool]
    apply hinv asset pre L hnodup
    intro cid hcid
    rw [← hhold]
    exact hmem cid hcid
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
    obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, hselfeq, _hnow, _hsigned⟩ := hstep0
    obtain ⟨N, M, w, pub, idx, midPool, hdstep, hmatch⟩ := hinner
    obtain ⟨hown, hcommit, htoken, _hN, _hM, hC, rest, _spent', _newRoot, _records, _hRoot, hRemove,
      _hNullify, _hSublist, _hidxrec, heq⟩ := hdstep
    intro asset pre L hnodup hmem
    rcases hh : s.holdings tok channelId0 with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpooleq, hholdseq⟩ := hmatch
      by_cases hasset : asset = tok
      · subst hasset
        have hcnt := removeAll_count hRemove pre
        rw [htoken] at hcnt
        by_cases hcid : channelId0 ∈ L
        · have hL'notin : channelId0 ∉ L.erase channelId0 := hnodup.not_mem_erase
          have hLlen : (L.erase channelId0).length + 1 = L.length := by
            have hl := (List.perm_cons_erase hcid).length_eq
            simp only [List.length_cons] at hl; omega
          have hqc : hashCommitment pre = pub.commitmentsOut idx := by
            have hm := hmem channelId0 hcid
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_pos rfl] at hm
            exact (Option.some.inj hm).symm
          have houts : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) =
              pub.commitmentsOut idx := (hC.outputs idx).symm
          have hpreeq : pre = (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) :=
            hashCommitment_inj (hqc.trans houts.symm)
          have hL'mem : ∀ cid ∈ L.erase channelId0, s.holdings asset cid = some (hashCommitment pre) := by
            intro cid hcidL'
            have hcidL : cid ∈ L := List.mem_of_mem_erase hcidL'
            have hne : cid ≠ channelId0 := fun heqc => hL'notin (heqc ▸ hcidL')
            have hm := hmem cid hcidL
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_neg hne] at hm
            exact hm
          have hown2 : pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r := by
            obtain ⟨r, hr⟩ := hown
            exact Or.inr ⟨r, by rw [hpreeq]; exact hr⟩
          refine ⟨fun _ => hown2, ?_⟩
          rw [hpooleq, heq]
          show L.length ≤ List.count pre
              (if asset = w.token then transactAllOutputs w ++ rest else s.pool.live asset)
          rw [if_pos htoken.symm, List.count_append]
          have hsp0 : pre ∉ transactSpentNotes w := by
            intro hmemspent
            obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
            exact userDisjoint pre hown2 w.publicKey w.nullifyingKey (w.randomIn j)
              (congrArg CommitmentPreimage.npk hj).symm
          rw [List.count_eq_zero_of_not_mem hsp0] at hcnt
          have hmintcount : 0 < List.count pre (transactAllOutputs w) := by
            rw [hpreeq]
            exact List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨idx, rfl⟩)
          have hL'nodup : (L.erase channelId0).Nodup := hnodup.erase channelId0
          have hL'bound := (hinv asset pre (L.erase channelId0) hL'nodup hL'mem).2
          omega
        · have hLmem : ∀ cid ∈ L, s.holdings asset cid = some (hashCommitment pre) := by
            intro cid hcidL
            have hne : cid ≠ channelId0 := fun heqc => hcid (heqc ▸ hcidL)
            have hm := hmem cid hcidL
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_neg hne] at hm
            exact hm
          have hLbound := hinv asset pre L hnodup hLmem
          obtain ⟨hownres, hcntres⟩ := hLbound
          refine ⟨hownres, ?_⟩
          rw [hpooleq, heq]
          show L.length ≤ List.count pre
              (if asset = w.token then transactAllOutputs w ++ rest else s.pool.live asset)
          rw [if_pos htoken.symm, List.count_append]
          by_cases hLempty : L.length = 0
          · omega
          · have hownpre := hownres (Nat.pos_of_ne_zero hLempty)
            have hsp0 : pre ∉ transactSpentNotes w := by
              intro hmemspent
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
              exact userDisjoint pre hownpre w.publicKey w.nullifyingKey (w.randomIn j)
                (congrArg CommitmentPreimage.npk hj).symm
            rw [List.count_eq_zero_of_not_mem hsp0] at hcnt
            omega
      · have hholdeq : s'.holdings asset = s.holdings asset := by
          rw [hholdseq]; unfold update; funext cid; rw [if_neg hasset]
        have hliveeq : s'.pool.live asset = s.pool.live asset := by
          rw [hpooleq, heq]
          show (if asset = w.token then transactAllOutputs w ++ rest else s.pool.live asset) =
            s.pool.live asset
          rw [if_neg (htoken ▸ hasset)]
        rw [hliveeq]
        apply hinv asset pre L hnodup
        intro cid hcid
        have hm := hmem cid hcid
        rw [hholdeq] at hm
        exact hm
    · rw [hh] at hmatch
      obtain ⟨merged, hmerge, hholdseq⟩ := hmatch
      obtain ⟨w', pub', hC', rest', spent'', r', hNonZero', hown', htoken', hnpkOut', hmergedEq,
        hcommitOld, hcommitNew, _hroot', hremove', _hnullify', heq'⟩ := hmerge
      by_cases hasset : asset = tok
      · subst hasset
        have hmidlive : midPool.live asset = transactAllOutputs w ++ rest := by
          rw [heq]; show (if asset = w.token then _ else _) = _; rw [if_pos htoken.symm]
        have hs'live : s'.pool.live asset = ownedNewNotes w' ++ rest' := by
          rw [heq']; show (if asset = asset then _ else _) = _; rw [if_pos rfl]
        have hcntDep := removeAll_count hRemove pre
        rw [htoken] at hcntDep
        have hcntMerge := removeAll_count hremove' pre
        have houts' : hashCommitment (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) =
            pub'.commitmentsOut 0 := (hC'.outputs 0).symm
        obtain ⟨preOld, hpreOld, hvalOld, hconsistOld⟩ := hnz asset channelId0 oldHolding hh
        have hpreOldEq : preOld = (⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token,
            w'.valueIn 0⟩ : CommitmentPreimage) := hashCommitment_inj (hconsistOld.trans hcommitOld.symm)
        have hw'0 : w'.valueIn 0 ≠ 0 := by rw [hpreOldEq] at hvalOld; exact hvalOld
        have hvaleq : w'.valueIn 1 = amount := by
          have heq2 : commitment (npk (Term.val pub'.ownerField) (w'.randomIn 1)) w'.token
              (w'.valueIn 1) = commitment (w.npkOut idx) asset amount := hcommitNew.trans hcommit
          exact Term.val.inj (Term.hash3_inj heq2).2.2
        have hbalance := transactOwned_value_conserved w' pub' (by decide) (by decide) hC'
        have hsumeq : w'.valueIn 0 + (w'.valueIn 1 + 0) = w'.valueOut 0 + 0 := hbalance
        rw [hvaleq] at hsumeq
        have hmergedNeOld : merged ≠ oldHolding := by
          intro heqmo
          rw [hmergedEq, ← houts'] at heqmo
          unfold hashCommitment at heqmo
          dsimp only at heqmo
          rw [← hcommitOld] at heqmo
          have hthis := Term.val.inj (Term.hash3_inj heqmo).2.2
          omega
        have hmergedNeNew : merged ≠ pub.commitmentsOut idx := by
          intro heqmn
          rw [hmergedEq, ← houts'] at heqmn
          unfold hashCommitment at heqmn
          dsimp only at heqmn
          rw [← hcommitNew] at heqmn
          have hthis := Term.val.inj (Term.hash3_inj heqmn).2.2
          omega
        by_cases hcid : channelId0 ∈ L
        · have hL'notin : channelId0 ∉ L.erase channelId0 := hnodup.not_mem_erase
          have hLlen : (L.erase channelId0).length + 1 = L.length := by
            have hl := (List.perm_cons_erase hcid).length_eq
            simp only [List.length_cons] at hl; omega
          have hqc : hashCommitment pre = merged := by
            have hm := hmem channelId0 hcid
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_pos rfl] at hm
            exact (Option.some.inj hm).symm
          have hpreeq : pre = (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) :=
            hashCommitment_inj (hqc.trans (hmergedEq.trans houts'.symm))
          have hL'mem : ∀ cid ∈ L.erase channelId0, s.holdings asset cid = some (hashCommitment pre) := by
            intro cid hcidL'
            have hcidL : cid ∈ L := List.mem_of_mem_erase hcidL'
            have hne : cid ≠ channelId0 := fun heqc => hL'notin (heqc ▸ hcidL')
            have hm := hmem cid hcidL
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_neg hne] at hm
            exact hm
          have hown2 : pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r :=
            Or.inr ⟨r', by rw [hpreeq]; exact hnpkOut'⟩
          refine ⟨fun _ => hown2, ?_⟩
          have hspmerge0 : pre ∉ ownedSpentNotes pub' w' := by
            intro hmemspent
            obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
            have hhc := congrArg hashCommitment hj
            rw [hqc] at hhc
            match j with
            | 0 =>
              unfold hashCommitment at hhc
              rw [hcommitOld] at hhc
              exact hmergedNeOld hhc.symm
            | 1 =>
              unfold hashCommitment at hhc
              rw [hcommitNew] at hhc
              exact hmergedNeNew hhc.symm
          have hsp0 : pre ∉ transactSpentNotes w := by
            intro hmemspent
            obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
            exact userDisjoint pre hown2 w.publicKey w.nullifyingKey (w.randomIn j)
              (congrArg CommitmentPreimage.npk hj).symm
          rw [List.count_eq_zero_of_not_mem hsp0] at hcntDep
          rw [List.count_eq_zero_of_not_mem hspmerge0] at hcntMerge
          have hmintcount : 0 < List.count pre (ownedNewNotes w') := by
            rw [hpreeq]
            exact List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨0, rfl⟩)
          have hmidcount : List.count pre (midPool.live asset) ≥ List.count pre (s.pool.live asset) := by
            rw [hmidlive, List.count_append, hcntDep]; omega
          have hL'nodup : (L.erase channelId0).Nodup := hnodup.erase channelId0
          have hL'bound := (hinv asset pre (L.erase channelId0) hL'nodup hL'mem).2
          rw [hs'live, List.count_append]
          omega
        · have hLmem : ∀ cid ∈ L, s.holdings asset cid = some (hashCommitment pre) := by
            intro cid hcidL
            have hne : cid ≠ channelId0 := fun heqc => hcid (heqc ▸ hcidL)
            have hm := hmem cid hcidL
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_neg hne] at hm
            exact hm
          have hLbound := hinv asset pre L hnodup hLmem
          obtain ⟨hownres, hcntres⟩ := hLbound
          refine ⟨hownres, ?_⟩
          rw [hs'live, List.count_append]
          by_cases hpreOldHolding : hashCommitment pre = oldHolding
          · have hLplusMem : ∀ cid ∈ channelId0 :: L, s.holdings asset cid = some (hashCommitment pre) := by
              intro cid hcidmem
              rcases List.mem_cons.mp hcidmem with hcideq | hcidL
              · subst hcideq; rw [hpreOldHolding]; exact hh
              · exact hLmem cid hcidL
            have hLplusNodup : (channelId0 :: L).Nodup := List.nodup_cons.mpr ⟨hcid, hnodup⟩
            have hLplusBound := (hinv asset pre (channelId0 :: L) hLplusNodup hLplusMem).2
            simp only [List.length_cons] at hLplusBound
            have hpreval : pre = (⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token,
                w'.valueIn 0⟩ : CommitmentPreimage) :=
              hashCommitment_inj (hpreOldHolding.trans hcommitOld.symm)
            have hsp0 : pre ∉ transactSpentNotes w := by
              intro hmemspent
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
              have hnpkeq : npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j) =
                  pre.npk := congrArg CommitmentPreimage.npk hj
              rw [hpreval] at hnpkeq
              exact user_npk_ne_contract_npk hnpkeq
            rw [List.count_eq_zero_of_not_mem hsp0] at hcntDep
            have houtsIdx : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ :
                CommitmentPreimage) = pub.commitmentsOut idx := (hC.outputs idx).symm
            have hboth : ownedSpentNotes pub' w' =
                [(⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token, w'.valueIn 0⟩ :
                    CommitmentPreimage),
                 (⟨npk (Term.val pub'.ownerField) (w'.randomIn 1), w'.token, w'.valueIn 1⟩ :
                    CommitmentPreimage)] := by
              unfold ownedSpentNotes
              simp [List.ofFn_succ, List.ofFn_zero]
            by_cases hpreFresh : hashCommitment pre = pub.commitmentsOut idx
            · have hfreshEq : pre = (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) :=
                hashCommitment_inj (hpreFresh.trans houtsIdx.symm)
              have hmintAtLeast : 1 ≤ List.count pre (transactAllOutputs w) := by
                rw [hfreshEq]
                exact List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨idx, rfl⟩)
              have hmergeAtMost : List.count pre (ownedSpentNotes pub' w') ≤ 2 := by
                rw [hboth]
                have hle := List.count_le_length (a := pre)
                  (l := [(⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token, w'.valueIn 0⟩ :
                      CommitmentPreimage),
                    (⟨npk (Term.val pub'.ownerField) (w'.randomIn 1), w'.token, w'.valueIn 1⟩ :
                      CommitmentPreimage)])
                simpa using hle
              have hmidcount3 : List.count pre (midPool.live asset) ≥
                  1 + List.count pre (s.pool.live asset) := by
                rw [hmidlive, List.count_append]; omega
              omega
            · have hspCount : List.count pre (ownedSpentNotes pub' w') ≤ 1 := by
                rw [hboth, hpreval, List.count_cons, List.count_cons, List.count_nil]
                have hne12 : (⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token,
                    w'.valueIn 0⟩ : CommitmentPreimage) ≠
                    (⟨npk (Term.val pub'.ownerField) (w'.randomIn 1), w'.token, w'.valueIn 1⟩ :
                      CommitmentPreimage) := by
                  intro hcontra
                  apply hpreFresh
                  rw [hpreOldHolding]
                  have hthis : hashCommitment (⟨npk (Term.val pub'.ownerField) (w'.randomIn 0),
                      w'.token, w'.valueIn 0⟩ : CommitmentPreimage) = oldHolding := by
                    unfold hashCommitment; exact hcommitOld
                  rw [← hthis, hcontra]
                  unfold hashCommitment
                  exact hcommitNew
                simp [hne12, Ne.symm hne12]
              have hmidcount2 : List.count pre (midPool.live asset) ≥ List.count pre (s.pool.live asset) := by
                rw [hmidlive, List.count_append]; omega
              omega
          · by_cases hLempty : L.length = 0
            · omega
            · have hownpre := hownres (Nat.pos_of_ne_zero hLempty)
              have hsp0 : pre ∉ transactSpentNotes w := by
                intro hmemspent
                obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
                exact userDisjoint pre hownpre w.publicKey w.nullifyingKey (w.randomIn j)
                  (congrArg CommitmentPreimage.npk hj).symm
              rw [List.count_eq_zero_of_not_mem hsp0] at hcntDep
              have houtsIdx : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ :
                  CommitmentPreimage) = pub.commitmentsOut idx := (hC.outputs idx).symm
              have hboth : ownedSpentNotes pub' w' =
                  [(⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token, w'.valueIn 0⟩ :
                      CommitmentPreimage),
                   (⟨npk (Term.val pub'.ownerField) (w'.randomIn 1), w'.token, w'.valueIn 1⟩ :
                      CommitmentPreimage)] := by
                unfold ownedSpentNotes
                simp [List.ofFn_succ, List.ofFn_zero]
              by_cases hpreFresh : hashCommitment pre = pub.commitmentsOut idx
              · have hfreshEq : pre = (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) :=
                  hashCommitment_inj (hpreFresh.trans houtsIdx.symm)
                have hmintAtLeast : 1 ≤ List.count pre (transactAllOutputs w) := by
                  rw [hfreshEq]
                  exact List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨idx, rfl⟩)
                have hne0 : pre ≠ (⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token,
                    w'.valueIn 0⟩ : CommitmentPreimage) := by
                  intro hcontra
                  apply hpreOldHolding
                  rw [hcontra]; unfold hashCommitment; exact hcommitOld
                have hmergeAtMost : List.count pre (ownedSpentNotes pub' w') ≤ 1 := by
                  rw [hboth, List.count_cons, List.count_cons, List.count_nil]
                  simp only [hne0, Ne.symm hne0, beq_iff_eq, if_false]
                  split <;> omega
                have hmidcount3 : List.count pre (midPool.live asset) ≥
                    1 + List.count pre (s.pool.live asset) := by
                  rw [hmidlive, List.count_append, hcntDep]; omega
                omega
              · have hspmerge2 : List.count pre (ownedSpentNotes pub' w') = 0 := by
                  rw [hboth, List.count_cons, List.count_cons, List.count_nil]
                  have hne0 : pre ≠ (⟨npk (Term.val pub'.ownerField) (w'.randomIn 0), w'.token,
                      w'.valueIn 0⟩ : CommitmentPreimage) := by
                    intro hcontra
                    apply hpreOldHolding
                    rw [hcontra]; unfold hashCommitment; exact hcommitOld
                  have hne1 : pre ≠ (⟨npk (Term.val pub'.ownerField) (w'.randomIn 1), w'.token,
                      w'.valueIn 1⟩ : CommitmentPreimage) := by
                    intro hcontra
                    apply hpreFresh
                    rw [hcontra]; unfold hashCommitment; exact hcommitNew
                  simp [hne0, Ne.symm hne0, hne1, Ne.symm hne1]
                rw [hspmerge2] at hcntMerge
                have hmidcount2b : List.count pre (midPool.live asset) ≥ List.count pre (s.pool.live asset) := by
                  rw [hmidlive, List.count_append]; omega
                omega
      · have hholdeq : s'.holdings asset = s.holdings asset := by
          rw [hholdseq]; unfold update; funext cid; rw [if_neg hasset]
        have hliveeq : s'.pool.live asset = s.pool.live asset := by
          rw [heq']
          show (if asset = tok then _ else midPool.live asset) = s.pool.live asset
          rw [if_neg hasset]
          rw [heq]
          show (if asset = w.token then _ else s.pool.live asset) = s.pool.live asset
          rw [if_neg (htoken ▸ hasset)]
        rw [hliveeq]
        apply hinv asset pre L hnodup
        intro cid hcid
        have hm := hmem cid hcid
        rw [hholdeq] at hm
        exact hm
  | transfer assetIndex cid0 claimedStateHash outcome indices =>
    have hstep0 := hstep
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep0
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨hmatch, hholdseq, _hchanseq⟩ := hrest
    change PoolOwnedSpendStep s.pool s.self (outcome.get ⟨assetIndex, hidx⟩).asset
      (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid0)
      ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices).2.1.filterMap (fun a =>
        if a.amount = 0 then none
        else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ : CommitmentPreimage)) ++
        (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0 -
            (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices).2.2 = 0
         then []
         else [(⟨Term.val s.self, (outcome.get ⟨assetIndex, hidx⟩).asset,
           heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0 -
             (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices).2.2⟩ : CommitmentPreimage)]))
      s'.pool at hmatch
    change s'.holdings = update s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset
      (update (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset) cid0
        (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0 -
            (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
              (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices).2.2 = 0
         then none
         else some (commitment (Term.val s.self) (outcome.get ⟨assetIndex, hidx⟩).asset
           (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0 -
             (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid0) indices).2.2)))) at hholdseq
    intro asset pre L hnodup hmem
    generalize hAO : outcome.get ⟨assetIndex, hidx⟩ = assetOutcome at hmatch hholdseq
    generalize htok : assetOutcome.asset = tok at hmatch hholdseq
    generalize hRemDef : heldValue s tok cid0 -
      (transferEffects assetOutcome.allocations (heldValue s tok cid0) indices).2.2 =
      remainder at hmatch hholdseq
    by_cases hasset : asset = tok
    · subst hasset
      rcases hc0 : s.holdings asset cid0 with _ | c0
      · simp only [hc0] at hmatch
        obtain ⟨w, pub, _hM, hC, _spent', _newRoot, hNonZero, _hown, htoken, hnewnotes, _hroot, _hmark,
          heq⟩ := hmatch
        have hheldzero : heldValue s asset cid0 = 0 := by unfold heldValue; rw [hc0]
        have hrem0 : remainder = 0 := by rw [← hRemDef, hheldzero]; omega
        have hcid0notin : cid0 ∉ L := fun hcid0L => by
          have hm := hmem cid0 hcid0L
          rw [hholdseq] at hm; unfold update at hm
          rw [if_pos rfl, if_pos rfl, hrem0, if_pos rfl] at hm
          exact absurd hm (by simp)
        have hLmem : ∀ cid ∈ L, s.holdings asset cid = some (hashCommitment pre) := by
          intro cid hcidL
          have hm := hmem cid hcidL
          rw [hholdseq] at hm; unfold update at hm
          rw [if_pos rfl, if_neg (fun (heqc : cid = cid0) => hcid0notin (heqc ▸ hcidL))] at hm
          exact hm
        have hLbound := hinv asset pre L hnodup hLmem
        refine ⟨hLbound.1, ?_⟩
        rw [heq]
        show L.length ≤ List.count pre
            (if asset = asset then _ ++ s.pool.live asset else s.pool.live asset)
        rw [if_pos rfl, List.count_append]
        have := hLbound.2
        omega
      · simp only [hc0] at hmatch
        obtain ⟨w, pub, _hM, hC, rest, _spent', _newRoot, hNonZero, _hown, htoken, hnewnotes, hccommit,
          _hroot, hremove, _hmark, heq⟩ := hmatch
        have hcntDep := removeAll_count hremove pre
        by_cases hcid : cid0 ∈ L
        · have hL'notin : cid0 ∉ L.erase cid0 := hnodup.not_mem_erase
          have hLlen : (L.erase cid0).length + 1 = L.length := by
            have hl := (List.perm_cons_erase hcid).length_eq
            simp only [List.length_cons] at hl; omega
          have hrem0 : remainder ≠ 0 := by
            intro hrem0
            have hm := hmem cid0 hcid
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_pos rfl, hrem0, if_pos rfl] at hm
            exact absurd hm (by simp)
          have hqc : hashCommitment pre = commitment (Term.val s.self) asset remainder := by
            have hm := hmem cid0 hcid
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_pos rfl, if_neg hrem0] at hm
            exact (Option.some.inj hm).symm
          have hpreeq : pre = (⟨Term.val s.self, asset, remainder⟩ : CommitmentPreimage) :=
            hashCommitment_inj hqc
          have hL'mem : ∀ cid ∈ L.erase cid0, s.holdings asset cid = some (hashCommitment pre) := by
            intro cid hcidL'
            have hcidL : cid ∈ L := List.mem_of_mem_erase hcidL'
            have hne : cid ≠ cid0 := fun heqc => hL'notin (heqc ▸ hcidL')
            have hm := hmem cid hcidL
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_neg hne] at hm
            exact hm
          have hL'nodup : (L.erase cid0).Nodup := hnodup.erase cid0
          have hL'bound := (hinv asset pre (L.erase cid0) hL'nodup hL'mem).2
          have hownpre : pre.npk = Term.val s.self ∨ ∃ r, pre.npk = npk (Term.val s.self) r :=
            Or.inl (by rw [hpreeq])
          refine ⟨fun _ => hownpre, ?_⟩
          have hc0preeq : pre.npk ≠
              (⟨npk (Term.val pub.ownerField) (w.randomIn 0), w.token, w.valueIn 0⟩ :
                CommitmentPreimage).npk := by
            rw [hpreeq]
            exact fun hcontra => Term.val_ne_hash s.self _ hcontra
          have hsp0 : pre ∉ ownedSpentNotes pub w := by
            intro hmemspent
            obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
            have hj0 : j = 0 := Subsingleton.elim j 0
            rw [hj0] at hj
            exact hc0preeq (congrArg CommitmentPreimage.npk hj).symm
          rw [List.count_eq_zero_of_not_mem hsp0] at hcntDep
          have hmintcount : 0 < List.count pre
              ((transferEffects assetOutcome.allocations (heldValue s asset cid0)
                indices).2.1.filterMap (fun a => if a.amount = 0 then none
                  else some (⟨a.destination, asset, a.amount⟩ : CommitmentPreimage)) ++
                (if remainder = 0 then [] else [(⟨Term.val s.self, asset, remainder⟩ :
                  CommitmentPreimage)])) := by
            rw [List.count_pos_iff]
            apply List.mem_append.mpr
            right
            rw [hpreeq, if_neg hrem0]
            exact List.mem_singleton_self _
          rw [heq]
          show L.length ≤ List.count pre
              (if asset = asset then _ else s.pool.live asset)
          rw [if_pos rfl, List.count_append]
          omega
        · have hLmem : ∀ cid ∈ L, s.holdings asset cid = some (hashCommitment pre) := by
            intro cid hcidL
            have hne : cid ≠ cid0 := fun heqc => hcid (heqc ▸ hcidL)
            have hm := hmem cid hcidL
            rw [hholdseq] at hm; unfold update at hm
            rw [if_pos rfl, if_neg hne] at hm
            exact hm
          have hLbound := hinv asset pre L hnodup hLmem
          refine ⟨hLbound.1, ?_⟩
          rw [heq]
          show L.length ≤ List.count pre
              (if asset = asset then _ else s.pool.live asset)
          rw [if_pos rfl, List.count_append]
          by_cases hpreC0 : hashCommitment pre = c0
          · have hc0preeq : pre = (⟨npk (Term.val pub.ownerField) (w.randomIn 0), w.token,
                w.valueIn 0⟩ : CommitmentPreimage) := hashCommitment_inj (hpreC0.trans hccommit.symm)
            have hsp1 : List.count pre (ownedSpentNotes pub w) = 1 := by
              have heqlist : ownedSpentNotes pub w =
                  [(⟨npk (Term.val pub.ownerField) (w.randomIn 0), w.token, w.valueIn 0⟩ :
                    CommitmentPreimage)] := by
                unfold ownedSpentNotes
                simp
              rw [heqlist, hc0preeq, List.count_cons, List.count_nil]
              simp
            have hLplusnodup : (cid0 :: L).Nodup := List.nodup_cons.mpr ⟨hcid, hnodup⟩
            have hLplusmem : ∀ cid ∈ cid0 :: L, s.holdings asset cid = some (hashCommitment pre) := by
              intro cid hcidL
              rcases List.mem_cons.mp hcidL with heqc | hcidL'
              · rw [heqc, hc0, hpreC0]
              · exact hLmem cid hcidL'
            have hLplusbound := (hinv asset pre (cid0 :: L) hLplusnodup hLplusmem).2
            simp only [List.length_cons] at hLplusbound
            omega
          · have hsp0 : pre ∉ ownedSpentNotes pub w := by
              intro hmemspent
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
              have hj0 : j = 0 := Subsingleton.elim j 0
              rw [hj0] at hj
              apply hpreC0
              rw [← hj]
              unfold hashCommitment
              exact hccommit
            rw [List.count_eq_zero_of_not_mem hsp0] at hcntDep
            omega
    · have hholdeq : s'.holdings asset = s.holdings asset := by
        rw [hholdseq]
        unfold update
        funext cid
        rw [if_neg hasset]
      have hliveeq : s'.pool.live asset = s.pool.live asset := by
        rcases hc0 : s.holdings tok cid0 with _ | c0
        · simp only [hc0] at hmatch
          obtain ⟨w, _pub, _hM, _hC, _spent', _newRoot, _hNonZero, _hown, _htoken, _hnewnotes, _hroot,
            _hmark, heq⟩ := hmatch
          rw [heq]
          show (if asset = tok then _ else s.pool.live asset) = s.pool.live asset
          rw [if_neg hasset]
        · simp only [hc0] at hmatch
          obtain ⟨w, _pub, _hM, _hC, _rest, _spent', _newRoot, _hNonZero, _hown, _htoken, _hnewnotes,
            _hccommit, _hroot, _hremove, _hmark, heq⟩ := hmatch
          rw [heq]
          show (if asset = tok then _ else s.pool.live asset) = s.pool.live asset
          rw [if_neg hasset]
      rw [hliveeq]
      apply hinv asset pre L hnodup
      intro cid hcid
      have hm := hmem cid hcid
      rw [hholdeq] at hm
      exact hm

end ArmadaLean.Adjudicator
