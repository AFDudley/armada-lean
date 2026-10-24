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

/-- Marking a single nullifier spent: it fails iff the nullifier is already
    spent, and otherwise prepends it (`ArmadaLean.markSpent`, `PoolOwned.lean`). -/
theorem markSpent_single (spent : NullifierSet) (n : Nat) :
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
        (if remainder = 0 then [] else [(⟨self, asset, remainder⟩ : CommitmentPreimage)]),
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
(`ArmadaLean.hashCommitment`) is injective (`ArmadaLean.Poseidon.
poseidon3_inj`), so two VALID entries (`hvalid`'s own hypothesis) sharing
one commitment key must carry the SAME preimage — a batch can never
silently overwrite a known holding's registry entry with a different
value, honest or not. -/

/-- `hashCommitment` is injective: two preimages hashing to the same
    commitment are the same preimage (`ArmadaLean.Poseidon.poseidon3_inj`,
    the Poseidon collision-resistance axiom already used by `Transact.lean`
    and `TransactOwned.lean`). -/
theorem hashCommitment_inj {p q : CommitmentPreimage} (h : hashCommitment p = hashCommitment q) :
    p = q := by
  unfold hashCommitment commitment at h
  obtain ⟨h1, h2, h3⟩ := poseidon3_inj h
  cases p; cases q
  simp_all

/-- Applying a valid record batch to a registry that already reads `pre` at
    `c` (consistently, `hashCommitment pre = c`) still reads `pre` at `c`
    afterward: any entry in the batch sharing key `c` must, by `hvalid` and
    `hashCommitment_inj`, carry the value `pre` itself, so whether or not
    the batch touches `c`, the final value there is unchanged. -/
theorem applyRecords_preserves_known {records : List (Nat × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    (reg : PreimageRegistry) (c : Nat) (pre : CommitmentPreimage)
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
theorem applyRecords_reads {records : List (Nat × CommitmentPreimage)}
    (hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1)
    (reg : PreimageRegistry) (c : Nat) (p : CommitmentPreimage)
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
    obtain ⟨N, M, w, pub, idx, hdstep, hholdseq⟩ := hinner
    obtain ⟨_hown, hcommit, htoken, _hN, _hM, hC, _rest, _spent', _newRoot, records,
      _hEmergency, _hWithdrawOnly, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
      fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
    intro qasset qcid qc hc
    rw [hholdseq] at hc
    unfold update at hc
    by_cases ha : qasset = asset
    · subst ha
      by_cases hcid : qcid = channelId
      · subst hcid
        rw [if_pos rfl, if_pos rfl] at hc
        have hqc : pub.commitmentsOut idx = qc := Option.some.inj hc
        have hval : w.valueOut idx = amount := by
          have hout := hC.outputs idx
          rw [htoken, hcommit] at hout
          exact (poseidon3_inj hout).2.2.symm
        have hnz : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
          unfold isZeroPreimage
          intro ⟨_, hv, _⟩
          rw [hval] at hv
          have hcheck : amount = 0 := hv
          omega
        have hread := applyRecords_reads hvalid s.pool.preimageOf (pub.commitmentsOut idx)
          ⟨w.npkOut idx, w.token, w.valueOut idx⟩ hidxrec hnz
        rw [hqc] at hread
        refine ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, ?_, ?_, ?_⟩
        · rw [heq]; exact hread
        · rw [hval]
          intro hz; have hcheck2 : amount = 0 := hz; omega
        · exact (hC.outputs idx).symm.trans hqc
      · rw [if_pos rfl, if_neg hcid] at hc
        obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qc hc
        refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
        rw [heq]
        exact applyRecords_preserves_known hvalid s.pool.preimageOf qc pre_old hpre_old hconsist_old
    · rw [if_neg ha] at hc
      obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qc hc
      refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
      rw [heq]
      exact applyRecords_preserves_known hvalid s.pool.preimageOf qc pre_old hpre_old hconsist_old
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
         else [(⟨s.self, (outcome.get ⟨assetIndex, hidx⟩).asset,
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
         else some (commitment s.self (outcome.get ⟨assetIndex, hidx⟩).asset
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
        (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
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
          (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)))),
        remainder ≠ 0 → commitment s.self assetOutcome.asset remainder = qc →
        ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
      intro hpre hrem hqc
      have hnz : ¬ isZeroPreimage (⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage) :=
        fun hz => hrem hz.2.1
      have hmemout : (⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage) ∈
          ((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])) := by
        rw [if_neg hrem]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      have hmemout2 : (qc, (⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)) ∈
          ((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)) := by
        rw [← hqc]
        exact List.mem_map.mpr ⟨_, hmemout, rfl⟩
      refine ⟨⟨s.self, assetOutcome.asset, remainder⟩, ?_, hrem, hqc⟩
      rw [hpre]
      exact applyRecords_reads hvalid_outputs s.pool.preimageOf qc
        (⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage) hmemout2 hnz
    have hunrelated : ∀ (hpre : s'.pool.preimageOf = applyRecords s.pool.preimageOf
        (((transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk assetOutcome.asset pre.value, pre)))),
        s.holdings qasset qcid = some qc →
        ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
      intro hpre hc'
      obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qc hc'
      refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
      rw [hpre]
      exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre_old hpre_old hconsist_old
    rcases hc0 : s.holdings assetOutcome.asset cid with _ | c0
    · rw [hc0] at hmatch
      obtain ⟨w, pub, _, hC, _, _, hNonZero, _, htoken, hnewnotes, _, _, _, _, heq⟩ := hmatch
      have hrecordseq : ownedOutputRecords w pub = ((transferEffects assetOutcome.allocations
          (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
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
            (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
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
    · rw [hc0] at hmatch
      obtain ⟨w, pub, _, hC, _, _, _, hNonZero, _, htoken, hnewnotes, _, _, _, _, heq⟩ := hmatch
      have hrecordseq : ownedOutputRecords w pub = ((transferEffects assetOutcome.allocations
          (heldValue s assetOutcome.asset cid) indices).2.1.filterMap
            (fun a => if a.amount = 0 then none
              else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) ++
          (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
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
            (if remainder = 0 then [] else [(⟨s.self, assetOutcome.asset, remainder⟩ : CommitmentPreimage)])).map
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

/-! ## `payout_can_happen`'s own prerequisites: an internal channel id
    exists, and a deposit sets `heldValue` to exactly its own `amount` -/

/-- A list with more than `N` pairwise-distinct members cannot have every
    member below `N` — the pigeonhole principle, stated directly over
    `List.Nodup` since this project carries no further combinatorics
    library. Proved by strong induction on `N`: either `N` itself is a
    member (remove it, recurse at `N - 1`) or it is not (every member
    is already below `N - 1`, recurse without removing anything). -/
theorem no_long_nodup_bounded_list :
    ∀ (N : Nat) (l : List Nat), l.Nodup → N < l.length → (∀ x ∈ l, x < N) → False := by
  intro N
  induction N with
  | zero =>
    intro l _ hlen hbound
    match l, hlen with
    | x :: _, _ => exact absurd (hbound x List.mem_cons_self) (by omega)
  | succ N ih =>
    intro l hnodup hlen hbound
    by_cases hmem : N ∈ l
    · have hnodup' : (l.erase N).Nodup := List.Nodup.erase N hnodup
      have hlen' : (l.erase N).length = l.length - 1 := List.length_erase_of_mem hmem
      have hbound' : ∀ x ∈ l.erase N, x < N := by
        intro x hx
        have := (List.Nodup.mem_erase_iff hnodup).mp hx
        have hlt : x < N + 1 := hbound x this.2
        have hne : x ≠ N := this.1
        omega
      exact ih (l.erase N) hnodup' (by omega) hbound'
    · have hbound' : ∀ x ∈ l, x < N := by
        intro x hx
        have hlt : x < N + 1 := hbound x hx
        by_cases hxN : x = N
        · exact absurd (hxN ▸ hx) hmem
        · omega
      exact ih l hnodup (by omega) hbound'

/-- A channel id that is not an external (address-sized) destination
    exists: `channelIdOf`'s own injectivity (`HashAssumptions.
    channelIdOf_inj`) forces its range over `channelNonce ∈ [0, 2^160]`
    (2^160+1 pairwise-distinct values) to escape `[0, 2^160)` (only
    2^160 slots), by `no_long_nodup_bounded_list`. `payout_can_happen`
    needs this to fund a channel by `.deposit` (which requires `¬
    isExternal channelId`) and later finalize that SAME channel by
    `.conclude`/`.challenge` (whose own index is `channelId fp`, for
    whichever `fp` the call names) — the two requirements can only
    meet at a channel id neither `channelIdOf`'s nor `isExternal`'s own
    definition otherwise guarantees. -/
theorem exists_internal_channelId (hashA : HashAssumptions) :
    ∃ n : Nat, ¬ isExternal (channelIdOf [] n 0 0) := by
  apply Classical.byContradiction
  intro hcon
  have hf : Function.Injective (fun n => channelIdOf [] n 0 0) := by
    intro a b hab
    exact (hashA.channelIdOf_inj hab).2.1
  have hbound : ∀ n, channelIdOf [] n 0 0 < 2 ^ 160 := by
    intro n
    apply Classical.byContradiction
    intro hn
    exact hcon ⟨n, hn⟩
  apply no_long_nodup_bounded_list (2 ^ 160)
    ((List.range (2 ^ 160 + 1)).map (fun n => channelIdOf [] n 0 0))
  · exact List.Pairwise.map _ (fun _ _ hab heq => hab (hf heq)) (List.nodup_range)
  · rw [List.length_map, List.length_range]
    omega
  · intro x hx
    obtain ⟨n, _, hn⟩ := List.mem_map.mp hx
    rw [← hn]
    exact hbound n

/-- A successful `.deposit` sets `heldValue` to exactly its own `amount`
    argument — never the prior `heldValue` plus `amount` (`DepositStep`'s
    own mechanics mint a note worth `amount` directly, with no arithmetic
    tying it to the prior holding beyond the `expectedHeld` equality
    GATE, which only checks a value, never adds to one). The same
    `applyRecords_reads` read-back `holdings_preimage_nonzero_step`'s own
    `.deposit` case already uses. -/
theorem deposit_sets_heldValue
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (channelId expectedHeld asset amount : Nat)
    (hstep : Step sig appRel actor s (.deposit channelId expectedHeld asset amount) s') :
    heldValue s' asset channelId = amount := by
  obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨N, M, w, pub, idx, hdstep, hholdseq⟩ := hinner
  obtain ⟨_hown, hcommit, htoken, _hN, _hM, hC, _rest, _spent', _newRoot, records,
    _hEmergency, _hWithdrawOnly, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have hval : w.valueOut idx = amount := by
    have hout := hC.outputs idx
    rw [htoken, hcommit] at hout
    exact (poseidon3_inj hout).2.2.symm
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
  rw [heq]
  dsimp only
  rw [hread]
  simp [hval]

end ArmadaLean.Adjudicator
