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

/-- `afford`'s own payout at a GIVEN index never goes DOWN as surplus
    goes UP: priority order means more funds can only help a later
    entry, never hurt one (S2 §5.2's Turbo Value Algorithm is monotone
    in its own starting surplus). What the `unbeatable_pays`/
    `unbeatable_pays_after_timeout` interleaving invariant needs: a
    `.deposit` raising `heldValue` while the channel is still
    unfinalized can only keep `x`'s own affordability, never break it. -/
theorem afford_mono (allocs : List Allocation) {surplus1 surplus2 : Nat} (hle : surplus1 ≤ surplus2)
    (k : Nat) : (afford allocs surplus1).getD k 0 ≤ (afford allocs surplus2).getD k 0 := by
  induction allocs generalizing surplus1 surplus2 k with
  | nil => simp [afford]
  | cons a as ih =>
    cases k with
    | zero =>
      show min a.amount surplus1 ≤ min a.amount surplus2
      omega
    | succ k' =>
      show (afford as (surplus1 - min a.amount surplus1)).getD k' 0 ≤
        (afford as (surplus2 - min a.amount surplus2)).getD k' 0
      exact ih (by omega) k'


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

/-- `afford_le`, per index: `afford`'s own payout at `k` never exceeds
    allocation `k`'s own recorded amount — for `k` past the list's own
    end, both sides read `0` by `getD`'s own default. What A-14 needs to
    turn `transferEffects`'s own subtraction into a running total that
    never goes negative. -/
theorem afford_le_getD (allocs : List Allocation) (surplus : Nat) (k : Nat) :
    (afford allocs surplus).getD k 0 ≤ (allocs.getD k Allocation.default).amount := by
  by_cases hk : k < allocs.length
  · have hlen : (afford allocs surplus).length = allocs.length := afford_length allocs surplus
    have h1 : allocs[k]? = some (allocs.getD k Allocation.default) := by
      rw [List.getD_eq_getElem?_getD]
      cases h : allocs[k]? with
      | none => rw [List.getElem?_eq_none_iff] at h; omega
      | some a => simp
    have h2 : (afford allocs surplus)[k]? = some ((afford allocs surplus).getD k 0) := by
      rw [List.getD_eq_getElem?_getD]
      cases h : (afford allocs surplus)[k]? with
      | none => rw [List.getElem?_eq_none_iff] at h; omega
      | some p => simp
    have hzip := (List.getElem?_zip_eq_some
      (z := (allocs.getD k Allocation.default, (afford allocs surplus).getD k 0))).mpr ⟨h1, h2⟩
    have hmem : (allocs.getD k Allocation.default, (afford allocs surplus).getD k 0) ∈
        allocs.zip (afford allocs surplus) := List.mem_iff_getElem?.mpr ⟨k, hzip⟩
    exact afford_le allocs surplus _ hmem
  ·
    have h1 : allocs.getD k Allocation.default = Allocation.default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h2 : (afford allocs surplus).getD k 0 = 0 := by
      have hlen := afford_length allocs surplus
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h1, h2]
    exact Nat.zero_le _


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

/-- Splitting `(indexed, allocation, paid)` triples into a "kept" record
    (amount reduced by `paid` when selected) and an "exited" record
    (amount `paid`, only when selected) conserves the total amount —
    PROVIDED every selected triple's own `paid` never exceeds its own
    allocation's amount (so the `Nat` subtraction never underflows). The
    generic shape behind `transferEffects`'s own `(newAllocations,
    exitAllocations, totalPayouts)` split. -/
theorem indexed_conservation {α : Type} (l : List (α × Allocation × Nat)) (sel : α → Bool)
    (hle : ∀ p ∈ l, p.2.2 ≤ p.2.1.amount) :
    listSum ((l.map fun p => if sel p.1 then { p.2.1 with amount := p.2.1.amount - p.2.2 }
        else p.2.1).map Allocation.amount) +
      listSum ((l.filterMap fun p =>
        if sel p.1 then some ({ p.2.1 with amount := p.2.2 } : Allocation) else none).map
        Allocation.amount) =
      listSum (l.map fun p => p.2.1.amount) := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    have hxle : x.2.2 ≤ x.2.1.amount := hle x List.mem_cons_self
    have hxsle : ∀ p ∈ xs, p.2.2 ≤ p.2.1.amount := fun p hp => hle p (List.mem_cons_of_mem x hp)
    by_cases hsel : sel x.1 = true
    · simp only [List.map_cons, List.filterMap_cons, if_pos hsel, listSum]
      have := ih hxsle
      dsimp only at this ⊢
      omega
    · simp only [List.map_cons, List.filterMap_cons, if_neg hsel, listSum]
      have := ih hxsle
      dsimp only at this ⊢
      omega

/-- `transferEffects`'s own split (`newAllocations`, `exitAllocations`,
    `totalPayouts`) conserves the total amount: `instantiate
    `indexed_conservation` on `transferEffects`'s own `indexed` list,
    using `afford_le` for the "paid never exceeds amount" side
    condition. -/
theorem transferEffects_conservation (allocs : List Allocation) (surplus : Nat)
    (indices : List Nat) :
    listSum ((transferEffects allocs surplus indices).1.map Allocation.amount) +
      (transferEffects allocs surplus indices).2.2 =
      listSum (allocs.map Allocation.amount) := by
  have hconv := indexed_conservation
    ((List.range allocs.length).zip (allocs.zip (afford allocs surplus)))
    (fun i => indices.isEmpty || i ∈ indices)
    (fun p hp => afford_le allocs surplus p.2 (List.of_mem_zip hp).2)
  have hmap : ((List.range allocs.length).zip (allocs.zip (afford allocs surplus))).map
      (fun (p : Nat × Allocation × Nat) => p.2.1) = allocs := by
    have h1 : ((List.range allocs.length).zip (allocs.zip (afford allocs surplus))).map
        (fun (p : Nat × Allocation × Nat) => p.2) = allocs.zip (afford allocs surplus) := by
      apply List.map_snd_zip
      rw [List.length_zip, afford_length]
      simp
    calc ((List.range allocs.length).zip (allocs.zip (afford allocs surplus))).map
          (fun (p : Nat × Allocation × Nat) => p.2.1)
        = (((List.range allocs.length).zip (allocs.zip (afford allocs surplus))).map
            (fun (p : Nat × Allocation × Nat) => p.2)).map Prod.fst := by
          rw [List.map_map]; rfl
      _ = (allocs.zip (afford allocs surplus)).map Prod.fst := by rw [h1]
      _ = allocs := by
        apply List.map_fst_zip
        rw [afford_length]
        exact Nat.le_refl _
  have hmap2 : ((List.range allocs.length).zip (allocs.zip (afford allocs surplus))).map
      (fun (p : Nat × Allocation × Nat) => p.2.1.amount) = allocs.map Allocation.amount := by
    have hc := congrArg (List.map Allocation.amount) hmap
    rwa [List.map_map] at hc
  exact hconv.trans (congrArg listSum hmap2)





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

/-- `transferEffects`'s `newAllocations` (`.1`) at a SELECTED index is the
    old amount minus `afford`'s own payout there; at an UNSELECTED index
    it is the old amount, unchanged — `transfer_pays_only_the_finalized_
    outcome` (A-01, `Safety.lean`) made explicit per index. -/
theorem transferEffects_newAllocations_getD (allocs : List Allocation) (surplus : Nat)
    (indices : List Nat) (i : Nat) (hi : i < allocs.length) :
    ((transferEffects allocs surplus indices).1.getD i Allocation.default).amount =
      if indices.isEmpty || i ∈ indices then
        (allocs.getD i Allocation.default).amount - (afford allocs surplus).getD i 0
      else (allocs.getD i Allocation.default).amount := by
  have hlen : (afford allocs surplus).length = allocs.length := afford_length allocs surplus
  have hrange : (List.range allocs.length)[i]? = some i := List.getElem?_range hi
  have halloc : allocs[i]? = some (allocs.getD i Allocation.default) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : allocs[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some a => simp
  have hpaid : (afford allocs surplus)[i]? = some ((afford allocs surplus).getD i 0) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (afford allocs surplus)[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some p => simp
  have hzip1 := (List.getElem?_zip_eq_some
    (z := (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0))).mpr ⟨halloc, hpaid⟩
  have hzip2 := (List.getElem?_zip_eq_some
    (z := (i, (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0)))).mpr
    ⟨hrange, hzip1⟩
  unfold transferEffects
  dsimp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hzip2]
  simp only [Option.map_some, Option.getD_some]
  split <;> rfl

/-- `transferEffects`'s `newAllocations` (`.1`) carries one entry per
    input allocation — `List.range`/`.zip`/`.map` all preserve length,
    and `afford_length` keeps the zipped `paidAt` list the same length
    as `allocs`. Lets A-14 handle an index past the list's own end
    uniformly with `transferEffects_newAllocations_getD`. -/
theorem transferEffects_newAllocations_length (allocs : List Allocation) (surplus : Nat)
    (indices : List Nat) :
    (transferEffects allocs surplus indices).1.length = allocs.length := by
  unfold transferEffects
  dsimp only
  rw [List.length_map, List.length_zip, List.length_zip, List.length_range,
    afford_length allocs surplus]
  omega

/-- `transferEffects_newAllocations_getD`, for the WHOLE allocation, not
    just its own `.amount`: at a selected index, destination/type/
    metadata survive unchanged too (only `.amount` moves). What
    `afford_exchange` (below) needs to recover `transferEffects`'s own
    `newAllocations` LIST, not just one of its own fields. -/
theorem transferEffects_newAllocations_getD_full (allocs : List Allocation) (surplus : Nat)
    (indices : List Nat) (i : Nat) (hi : i < allocs.length) :
    (transferEffects allocs surplus indices).1.getD i Allocation.default =
      { allocs.getD i Allocation.default with
        amount := if indices.isEmpty || i ∈ indices then
          (allocs.getD i Allocation.default).amount - (afford allocs surplus).getD i 0
        else (allocs.getD i Allocation.default).amount } := by
  have hlen : (afford allocs surplus).length = allocs.length := afford_length allocs surplus
  have hrange : (List.range allocs.length)[i]? = some i := List.getElem?_range hi
  have halloc : allocs[i]? = some (allocs.getD i Allocation.default) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : allocs[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some a => simp
  have hpaid : (afford allocs surplus)[i]? = some ((afford allocs surplus).getD i 0) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (afford allocs surplus)[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some p => simp
  have hzip1 := (List.getElem?_zip_eq_some
    (z := (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0))).mpr ⟨halloc, hpaid⟩
  have hzip2 := (List.getElem?_zip_eq_some
    (z := (i, (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0)))).mpr
    ⟨hrange, hzip1⟩
  unfold transferEffects
  dsimp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hzip2]
  simp only [Option.map_some, Option.getD_some]
  split <;> rfl

/-- `transferEffects`'s own `newAllocations`, selecting only index `0`:
    the head's amount drops by its own `afford` payout, the tail is
    untouched (no other index is selected). What `afford_exchange`
    (below) needs to unfold `transferEffects (a :: as) surplus [0]`
    without re-deriving `List.range`/`.zip`/`.map`'s own interplay each
    time. -/
theorem transferEffects_newAllocations_cons_zero (a : Allocation) (as : List Allocation)
    (surplus : Nat) :
    (transferEffects (a :: as) surplus [0]).1 =
      { a with amount := a.amount - min a.amount surplus } :: as := by
  have hlen1 : (transferEffects (a :: as) surplus [0]).1.length = (a :: as).length :=
    transferEffects_newAllocations_length (a :: as) surplus [0]
  have hlen2 : (({ a with amount := a.amount - min a.amount surplus } :: as) :
      List Allocation).length = (a :: as).length := by simp
  apply List.ext_get (hlen1.trans hlen2.symm)
  intro n h1 h2
  have hfull := transferEffects_newAllocations_getD_full (a :: as) surplus [0] n (by simpa using h2)
  have hget1 : (transferEffects (a :: as) surplus [0]).1.get ⟨n, h1⟩ =
      (transferEffects (a :: as) surplus [0]).1.getD n Allocation.default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  have hget2 : (({ a with amount := a.amount - min a.amount surplus } :: as) :
      List Allocation).get ⟨n, h2⟩ =
      (({ a with amount := a.amount - min a.amount surplus } :: as) :
      List Allocation).getD n Allocation.default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
  rw [hget1, hget2, hfull]
  cases n with
  | zero => simp [afford]
  | succ n' => simp


/-- `transferEffects`'s own `newAllocations`, selecting a SUCCESSOR
    index: the head is untouched (index `0` is never `i' + 1`), and the
    tail recurses as `transferEffects`'s own call on `as`, one index
    lower, over the surplus `as`'s own run actually sees (`afford`'s
    own head payout already subtracted). -/
theorem transferEffects_newAllocations_cons_succ (a : Allocation) (as : List Allocation)
    (surplus i' : Nat) :
    (transferEffects (a :: as) surplus [i' + 1]).1 =
      a :: (transferEffects as (surplus - min a.amount surplus) [i']).1 := by
  have hlen1 : (transferEffects (a :: as) surplus [i' + 1]).1.length = (a :: as).length :=
    transferEffects_newAllocations_length (a :: as) surplus [i' + 1]
  have hlen2 : (a :: (transferEffects as (surplus - min a.amount surplus) [i']).1).length =
      (a :: as).length := by
    simp [transferEffects_newAllocations_length as (surplus - min a.amount surplus) [i']]
  apply List.ext_get (hlen1.trans hlen2.symm)
  intro n h1 h2
  have hfull := transferEffects_newAllocations_getD_full (a :: as) surplus [i' + 1] n
    (by rw [← hlen2]; exact h2)
  have hget1 : (transferEffects (a :: as) surplus [i' + 1]).1.get ⟨n, h1⟩ =
      (transferEffects (a :: as) surplus [i' + 1]).1.getD n Allocation.default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  have hget2 : (a :: (transferEffects as (surplus - min a.amount surplus) [i']).1).get
      ⟨n, h2⟩ = (a :: (transferEffects as (surplus - min a.amount surplus) [i']).1).getD
      n Allocation.default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
  rw [hget1, hget2, hfull]
  cases n with
  | zero => simp
  | succ n' =>
    have hn'range : n' < as.length := by
      rw [hlen1] at h1
      simp only [List.length_cons] at h1
      omega
    have hafforD : (afford (a :: as) surplus).getD (n' + 1) 0 =
        (afford as (surplus - min a.amount surplus)).getD n' 0 := by
      simp [afford]
    have hfull2 := transferEffects_newAllocations_getD_full as (surplus - min a.amount surplus)
      [i'] n' hn'range
    simp only [List.getD_cons_succ, hafforD, List.mem_singleton] at *
    rw [hfull2]
    by_cases hsel : n' = i'
    · simp [hsel]
    · have : (n' + 1 = i' + 1) = False := by simp [hsel]
      simp [this, hsel]

/-- `transferEffects`'s own total payout, selecting a SINGLE index, is
    exactly `afford`'s own computed amount there — A-02's own two
    `.transfer [i]`/`.transfer [j]` calls each select one index, so
    their own `.2.2` reduces to a plain `afford` lookup `afford_exchange`
    can reason about directly. -/
theorem transferEffects_totalPayouts_single (allocs : List Allocation) (surplus idx : Nat) :
    (transferEffects allocs surplus [idx]).2.2 = (afford allocs surplus).getD idx 0 := by
  induction allocs generalizing surplus idx with
  | nil => simp [transferEffects, afford, listSum]
  | cons a as ih =>
    have hcons := transferEffects_conservation (a :: as) surplus [idx]
    cases idx with
    | zero =>
      rw [transferEffects_newAllocations_cons_zero] at hcons
      simp only [listSum, List.map_cons] at hcons
      simp only [afford, List.getD_cons_zero]
      have hle : min a.amount surplus ≤ a.amount := Nat.min_le_left _ _
      omega
    | succ i' =>
      rw [transferEffects_newAllocations_cons_succ] at hcons
      have hih := ih (surplus - min a.amount surplus) i'
      have hcons2 := transferEffects_conservation as (surplus - min a.amount surplus) [i']
      simp only [listSum, List.map_cons] at hcons
      simp only [afford, List.getD_cons_succ]
      omega

/-- `afford`'s own payout at ANY index never exceeds the surplus it
    started with — stronger than `afford_le` (which bounds a payout by
    its OWN allocation's amount): this bounds it by the surplus
    instead, what `afford_exchange` needs to show subtracting a LATER
    payout from an EARLIER-reduced surplus never underflows. -/
theorem afford_getD_le_surplus (allocs : List Allocation) (surplus i : Nat) :
    (afford allocs surplus).getD i 0 ≤ surplus := by
  induction allocs generalizing surplus i with
  | nil => simp [afford]
  | cons a as ih =>
    cases i with
    | zero =>
      show min a.amount surplus ≤ surplus
      omega
    | succ i' =>
      show (afford as (surplus - min a.amount surplus)).getD i' 0 ≤ surplus
      have := ih (surplus - min a.amount surplus) i'
      omega

/-- Paying out exactly index `i`'s own `afford`-computed amount, THEN
    recomputing `afford` on the updated list and the surplus that
    leaves, gives the SAME value at every OTHER index `k` as the
    ORIGINAL `afford` run did. The two-call case A-02 needs: paying `i`
    first never changes what `j` would have been afforded, and vice
    versa. -/
theorem afford_exchange (allocs : List Allocation) (surplus : Nat) (i k : Nat) (hik : i ≠ k) :
    (afford ((transferEffects allocs surplus [i]).1)
        (surplus - (afford allocs surplus).getD i 0)).getD k 0 =
      (afford allocs surplus).getD k 0 := by
  induction allocs generalizing surplus i k with
  | nil => simp [afford, transferEffects]
  | cons a as ih =>
    cases i with
    | zero =>
      rw [transferEffects_newAllocations_cons_zero]
      cases k with
      | zero => exact absurd rfl hik
      | succ k' =>
        have hafford0 : (afford (a :: as) surplus).getD 0 0 = min a.amount surplus := by
          simp [afford]
        rw [hafford0]
        show (afford ({ a with amount := a.amount - min a.amount surplus } :: as)
          (surplus - min a.amount surplus)).getD (k' + 1) 0 =
          (afford (a :: as) surplus).getD (k' + 1) 0
        have hmin0 : min (a.amount - min a.amount surplus) (surplus - min a.amount surplus) = 0 := by
          omega
        simp only [afford, hmin0, Nat.sub_zero, List.getD_cons_succ]
    | succ i' =>
      rw [transferEffects_newAllocations_cons_succ]
      have hgeti : (afford (a :: as) surplus).getD (i' + 1) 0 =
          (afford as (surplus - min a.amount surplus)).getD i' 0 := by
        simp [afford]
      cases k with
      | zero =>
        rw [hgeti]
        show min a.amount (surplus - (afford as (surplus - min a.amount surplus)).getD i' 0) =
          min a.amount surplus
        have hle := afford_getD_le_surplus as (surplus - min a.amount surplus) i'
        omega
      | succ k' =>
        have hik' : i' ≠ k' := fun h => hik (congrArg Nat.succ h)
        rw [hgeti]
        simp only [afford, List.getD_cons_succ]
        have hle := afford_getD_le_surplus as (surplus - min a.amount surplus) i'
        have hminEq : min a.amount (surplus -
            (afford as (surplus - min a.amount surplus)).getD i' 0) = min a.amount surplus := by
          omega
        rw [hminEq]
        have hswap : (surplus - (afford as (surplus - min a.amount surplus)).getD i' 0) -
            min a.amount surplus =
            (surplus - min a.amount surplus) -
              (afford as (surplus - min a.amount surplus)).getD i' 0 := by omega
        rw [hswap]
        exact ih (surplus - min a.amount surplus) i' k' hik'

/-- `transferEffects`, restated with an arbitrary `Bool`-valued selection
    predicate instead of an `indices` list: the SAME computation,
    unfolded directly (not a new definition — `transferEffects`'s own
    `selected` local is exactly this shape). What the batch-selection
    generalization of `afford_exchange` below needs: a selection
    predicate SHIFTS cleanly as `fun j => sel (j+1)` on the tail, where
    an `indices : List Nat` does not (`indices.isEmpty` flips meaning
    after stripping a head element — `[0]`'s tail `[]` would wrongly
    read as "select all" under the list convention). -/
def transferEffectsSel (allocations : List Allocation) (surplus : Nat) (sel : Nat → Bool) :
    List Allocation × List Allocation × Nat :=
  let paidAt := afford allocations surplus
  let indexed := (List.range allocations.length).zip (allocations.zip paidAt)
  let newAllocations := indexed.map fun (i, a, paid) =>
    if sel i then { a with amount := a.amount - paid } else a
  let exitAllocations := indexed.filterMap fun (i, a, paid) =>
    if sel i then some { a with amount := paid } else none
  (newAllocations, exitAllocations, listSum (exitAllocations.map Allocation.amount))

/-- `transferEffects` IS `transferEffectsSel` under `indices`'s own
    selection rule — same definition, unfolded. -/
theorem transferEffects_eq_sel (allocs : List Allocation) (surplus : Nat) (indices : List Nat) :
    transferEffects allocs surplus indices =
      transferEffectsSel allocs surplus (fun i => indices.isEmpty || i ∈ indices) := rfl

/-- `transferEffectsSel`'s own `newAllocations` (`.1`) at index `i`:
    the SAME per-index characterization `transferEffects_newAllocations_
    getD_full` gives for `indices`, restated for an arbitrary `sel`.
    Same proof technique (`List.getElem?_zip_eq_some`), since
    `transferEffectsSel` is the SAME `List.range`/`.zip`/`.map` shape
    `transferEffects` unfolds to. -/
theorem transferEffectsSel_getD_full (allocs : List Allocation) (surplus : Nat)
    (sel : Nat → Bool) (i : Nat) (hi : i < allocs.length) :
    (transferEffectsSel allocs surplus sel).1.getD i Allocation.default =
      { allocs.getD i Allocation.default with
        amount := if sel i then
          (allocs.getD i Allocation.default).amount - (afford allocs surplus).getD i 0
        else (allocs.getD i Allocation.default).amount } := by
  have hlen : (afford allocs surplus).length = allocs.length := afford_length allocs surplus
  have hrange : (List.range allocs.length)[i]? = some i := List.getElem?_range hi
  have halloc : allocs[i]? = some (allocs.getD i Allocation.default) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : allocs[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some a => simp
  have hpaid : (afford allocs surplus)[i]? = some ((afford allocs surplus).getD i 0) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (afford allocs surplus)[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some p => simp
  have hzip1 := (List.getElem?_zip_eq_some
    (z := (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0))).mpr ⟨halloc, hpaid⟩
  have hzip2 := (List.getElem?_zip_eq_some
    (z := (i, (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0)))).mpr
    ⟨hrange, hzip1⟩
  unfold transferEffectsSel
  dsimp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hzip2]
  simp only [Option.map_some, Option.getD_some]
  split <;> rfl

/-- A SELECTED index's own entry is a member of `transferEffectsSel`'s
    `exitAllocations` (`.2.1`), carrying `afford`'s own paid amount as
    its `.amount`, everything else unchanged. What the `unbeatable_pays`/
    `unbeatable_pays_after_timeout` invariant needs to tie a selected
    `destIdx`'s own affordability bound to an ACTUAL minted payout
    output: `transferEffectsSel_getD_full` gives `newAllocations`'s own
    SHRUNK entry; this gives `exitAllocations`'s own PAID entry, the one
    `.transfer`'s own `payoutOutputs` mints a note from. -/
theorem transferEffectsSel_exit_mem (allocs : List Allocation) (surplus : Nat) (sel : Nat → Bool)
    (i : Nat) (hi : i < allocs.length) (hsel : sel i = true) :
    { allocs.getD i Allocation.default with
        amount := (afford allocs surplus).getD i 0 } ∈
      (transferEffectsSel allocs surplus sel).2.1 := by
  have hlen : (afford allocs surplus).length = allocs.length := afford_length allocs surplus
  have hrange : (List.range allocs.length)[i]? = some i := List.getElem?_range hi
  have halloc : allocs[i]? = some (allocs.getD i Allocation.default) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : allocs[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some a => simp
  have hpaid : (afford allocs surplus)[i]? = some ((afford allocs surplus).getD i 0) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (afford allocs surplus)[i]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some p => simp
  have hzip1 := (List.getElem?_zip_eq_some
    (z := (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0))).mpr ⟨halloc, hpaid⟩
  have hzip2 := (List.getElem?_zip_eq_some
    (z := (i, (allocs.getD i Allocation.default, (afford allocs surplus).getD i 0)))).mpr
    ⟨hrange, hzip1⟩
  have hmemIndexed : (i, allocs.getD i Allocation.default, (afford allocs surplus).getD i 0) ∈
      (List.range allocs.length).zip (allocs.zip (afford allocs surplus)) :=
    List.mem_iff_getElem?.mpr ⟨_, hzip2⟩
  unfold transferEffectsSel
  dsimp only
  exact List.mem_filterMap.mpr ⟨_, hmemIndexed, by rw [if_pos hsel]⟩


/-- `transferEffectsSel`'s own `newAllocations`, decomposed one entry at
    a time: the head is paid out (or not) by `sel 0` alone, and the
    tail recurses as `transferEffectsSel`'s own call on `as`, with `sel`
    SHIFTED by one position and the surplus `afford`'s own head payout
    already subtracted — the list-indexed counterpart of
    `transferEffects_newAllocations_cons_zero`/`_cons_succ`, generalized
    from a single selected index to an arbitrary predicate. Same proof
    technique (`List.ext_get`), reading each side off
    `transferEffectsSel_getD_full`. -/
theorem transferEffectsSel_cons (a : Allocation) (as : List Allocation) (surplus : Nat)
    (sel : Nat → Bool) :
    (transferEffectsSel (a :: as) surplus sel).1 =
      (if sel 0 then { a with amount := a.amount - min a.amount surplus } else a) ::
        (transferEffectsSel as (surplus - min a.amount surplus) (fun j => sel (j + 1))).1 := by
  have hlen1 : (transferEffectsSel (a :: as) surplus sel).1.length = (a :: as).length := by
    unfold transferEffectsSel
    simp [afford_length]
  have hlen2 : ((if sel 0 then { a with amount := a.amount - min a.amount surplus } else a) ::
      (transferEffectsSel as (surplus - min a.amount surplus) (fun j => sel (j + 1))).1).length =
      (a :: as).length := by
    have : (transferEffectsSel as (surplus - min a.amount surplus) (fun j => sel (j + 1))).1.length
        = as.length := by
      unfold transferEffectsSel
      simp [afford_length]
    simp [this]
  apply List.ext_get (hlen1.trans hlen2.symm)
  intro n h1 h2
  have hfull := transferEffectsSel_getD_full (a :: as) surplus sel n (by rw [hlen1] at h1; exact h1)
  have hget1 : (transferEffectsSel (a :: as) surplus sel).1.get ⟨n, h1⟩ =
      (transferEffectsSel (a :: as) surplus sel).1.getD n Allocation.default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  have hget2 : ((if sel 0 then { a with amount := a.amount - min a.amount surplus } else a) ::
      (transferEffectsSel as (surplus - min a.amount surplus) (fun j => sel (j + 1))).1).get
      ⟨n, h2⟩ = ((if sel 0 then { a with amount := a.amount - min a.amount surplus } else a) ::
      (transferEffectsSel as (surplus - min a.amount surplus) (fun j => sel (j + 1))).1).getD
      n Allocation.default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
  rw [hget1, hget2, hfull]
  cases n with
  | zero => by_cases h0 : sel 0 <;> simp [h0, afford]
  | succ n' =>
    have hn'range : n' < as.length := by
      rw [hlen1] at h1; simp only [List.length_cons] at h1; omega
    have hafforD : (afford (a :: as) surplus).getD (n' + 1) 0 =
        (afford as (surplus - min a.amount surplus)).getD n' 0 := by simp [afford]
    have hfull2 := transferEffectsSel_getD_full as (surplus - min a.amount surplus)
      (fun j => sel (j + 1)) n' hn'range
    simp only [List.getD_cons_succ, hafforD]
    rw [hfull2]

/-- `transferEffectsSel`'s own total payout, decomposed the same way:
    the head's own share, if selected, plus the tail's own total. -/
theorem transferEffectsSel_cons_payout (a : Allocation) (as : List Allocation) (surplus : Nat)
    (sel : Nat → Bool) :
    (transferEffectsSel (a :: as) surplus sel).2.2 =
      (if sel 0 then min a.amount surplus else 0) +
        (transferEffectsSel as (surplus - min a.amount surplus) (fun j => sel (j + 1))).2.2 := by
  have haffcons : afford (a :: as) surplus =
      min a.amount surplus :: afford as (surplus - min a.amount surplus) := rfl
  by_cases h0 : sel 0
  · simp only [if_pos h0]
    unfold transferEffectsSel
    simp only [List.length_cons, List.range_succ_eq_map, haffcons, List.zip_cons_cons,
      List.map_cons, List.filterMap_cons, if_pos h0, listSum,
      List.zip_map_left, List.filterMap_map]
    congr 2
  · simp only [if_neg h0]
    unfold transferEffectsSel
    simp only [List.length_cons, List.range_succ_eq_map, haffcons, List.zip_cons_cons,
      List.filterMap_cons, if_neg h0,
      List.zip_map_left, List.filterMap_map, Nat.zero_add]
    congr 1


/-- `transferEffectsSel`'s own total payout never exceeds `afford`'s own
    total: every paid entry's amount IS one of `afford`'s own
    per-index values (`transferEffectsSel`'s `exitAllocations`, built by
    `filterMap`, keeps only SOME of `afford`'s own list), so their sum
    is at most the WHOLE list's sum. What `afford_exchange_sel` needs
    to bound its own carried deficit by `afford_sum_le`. -/
theorem transferEffectsSel_payout_le (allocs : List Allocation) :
    ∀ (surplus : Nat) (sel : Nat → Bool),
      (transferEffectsSel allocs surplus sel).2.2 ≤ listSum (afford allocs surplus) := by
  induction allocs with
  | nil => intro surplus sel; simp [transferEffectsSel, afford, listSum]
  | cons a as ih =>
    intro surplus sel
    rw [transferEffectsSel_cons_payout]
    simp only [afford, listSum]
    have hrec := ih (surplus - min a.amount surplus) (fun j => sel (j + 1))
    by_cases h0 : sel 0
    · rw [if_pos h0]; omega
    · rw [if_neg h0]; omega

/-- `afford_exchange` generalized from ONE paid-out index to an entire
    selection predicate at once (`.transfer`'s own batch semantics,
    via `transferEffectsSel`): paying out every SELECTED entry
    simultaneously, each at its OWN `afford`-computed share, leaves
    every UNSELECTED entry's OWN later-recomputed `afford` value
    exactly where `afford` originally put it. Structural induction on
    `allocs`, generalizing `afford_exchange`'s own `i≠k` case split to
    `sel k = false`, carrying the ACTUAL running payout total (not an
    abstract bound) so `afford_sum_le`/`transferEffectsSel_payout_le`
    discharge the one inequality each step needs directly. What the
    `unbeatable_pays`/`unbeatable_pays_after_timeout` interleaving
    argument needs: another actor's `.transfer`, selecting ANY set of
    OTHER allocations, never lowers what `h`'s own entry can still
    afford. -/
theorem afford_exchange_sel (allocs : List Allocation) :
    ∀ (surplus : Nat) (sel : Nat → Bool) (k : Nat), sel k = false →
      (afford (transferEffectsSel allocs surplus sel).1
          (surplus - (transferEffectsSel allocs surplus sel).2.2)).getD k 0 =
        (afford allocs surplus).getD k 0 := by
  induction allocs with
  | nil => intro surplus sel k _; simp [afford, transferEffectsSel]
  | cons a as ih =>
    intro surplus sel k hk
    rw [transferEffectsSel_cons, transferEffectsSel_cons_payout]
    have hpaid0le : min a.amount surplus ≤ surplus := Nat.min_le_right _ _
    have hrestle : (transferEffectsSel as (surplus - min a.amount surplus)
        (fun j => sel (j + 1))).2.2 ≤ surplus - min a.amount surplus :=
      Nat.le_trans (transferEffectsSel_payout_le as _ _) (afford_sum_le as _)
    by_cases h0 : sel 0
    · simp only [if_pos h0]
      cases k with
      | zero => rw [h0] at hk; exact absurd hk (by decide)
      | succ k' =>
        have hswap : surplus - (min a.amount surplus +
            (transferEffectsSel as (surplus - min a.amount surplus)
              (fun j => sel (j + 1))).2.2) =
            (surplus - min a.amount surplus) -
              (transferEffectsSel as (surplus - min a.amount surplus)
                (fun j => sel (j + 1))).2.2 := by omega
        rw [hswap]
        have hgetD1 : (afford (a :: as) surplus).getD (k' + 1) 0 =
            (afford as (surplus - min a.amount surplus)).getD k' 0 := by simp [afford]
        rw [hgetD1]
        have hminzero : min (a.amount - min a.amount surplus)
            ((surplus - min a.amount surplus) -
              (transferEffectsSel as (surplus - min a.amount surplus)
                (fun j => sel (j + 1))).2.2) = 0 := by omega
        simp only [afford, List.getD_cons_succ, hminzero, Nat.sub_zero]
        show (afford ((transferEffectsSel as (surplus - min a.amount surplus)
            (fun j => sel (j + 1))).1) ((surplus - min a.amount surplus) -
            (transferEffectsSel as (surplus - min a.amount surplus)
              (fun j => sel (j + 1))).2.2)).getD k' 0 =
          (afford as (surplus - min a.amount surplus)).getD k' 0
        exact ih (surplus - min a.amount surplus) (fun j => sel (j + 1)) k' hk
    · simp only [if_neg h0]
      cases k with
      | zero =>
        have hminEq0 : min a.amount (surplus -
            (transferEffectsSel as (surplus - min a.amount surplus)
              (fun j => sel (j + 1))).2.2) = min a.amount surplus := by omega
        simp only [afford, hminEq0, Nat.zero_add, List.getD_cons_zero]
      | succ k' =>
        have hgetD1 : (afford (a :: as) surplus).getD (k' + 1) 0 =
            (afford as (surplus - min a.amount surplus)).getD k' 0 := by simp [afford]
        rw [hgetD1]
        have hminEq : min a.amount (surplus -
            (transferEffectsSel as (surplus - min a.amount surplus)
              (fun j => sel (j + 1))).2.2) = min a.amount surplus := by omega
        have hsub : surplus -
            (transferEffectsSel as (surplus - min a.amount surplus)
              (fun j => sel (j + 1))).2.2 - min a.amount surplus =
            (surplus - min a.amount surplus) -
              (transferEffectsSel as (surplus - min a.amount surplus)
                (fun j => sel (j + 1))).2.2 := by omega
        simp only [afford, Nat.zero_add, hminEq, List.getD_cons_succ]
        rw [hsub]
        show (afford ((transferEffectsSel as (surplus - min a.amount surplus)
            (fun j => sel (j + 1))).1) ((surplus - min a.amount surplus) -
            (transferEffectsSel as (surplus - min a.amount surplus)
              (fun j => sel (j + 1))).2.2)).getD k' 0 =
          (afford as (surplus - min a.amount surplus)).getD k' 0
        exact ih (surplus - min a.amount surplus) (fun j => sel (j + 1)) k' hk




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

/-- Bridges `_root_.Step.transactOwned`'s own `rest` (a constant list, baked
    into its `if t = token then ... ++ rest else ...` shape) against
    `PoolOwnedSpendStep`'s own "none"-nullified `live` field, which instead
    writes `before.live t` inside the same `then` branch — syntactically
    different even though `t = token` there makes them equal. -/
theorem transactOwned_none_live_eq (token : Nat) (live : Nat → List (Nat × CommitmentPreimage))
    (X : List CommitmentPreimage) (n : Nat) :
    (fun t => if t = token then withPositionsFrom n X ++ live token else live t) =
    (fun t => if t = token then withPositionsFrom n X ++ live t else live t) := by
  funext t
  by_cases ht : t = token <;> simp [ht]

/-- `bulkTransferFold`'s own pool-level lift: `_root_.Reachable` carries
    forward across the WHOLE fold, one asset's own `PoolOwnedSpendStep` —
    itself `_root_.Step.transactOwned` — at a time. What
    `adjudicator_pool_step` needs for its own two bulk `Call` cases. -/
theorem bulkTransferFold_pool_reachable (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    _root_.Reachable pool → _root_.Reachable poolF := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold hreach
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, _hholdEq⟩ := hfold
      rw [hpoolEq]; exact hreach
    | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hreach
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, r0, midPool, hmatch, hrec⟩ := hfold
      refine ih newRest midPool poolF _ holdingsF hrec ?_
      rcases hh : holdings exit.asset cid with _ | c0
      · rw [hh] at hmatch
        obtain ⟨w, pub, hM, hC, spent', randomOut, hNonZero, hCapacity, hown, htoken, hnewnotes,
          hroot, hmark, hRandomOut, heq⟩ := hmatch
        rw [heq]
        have hstepw := _root_.Step.transactOwned w pub (by decide) hM hC self hown
          (pool.live w.token) spent'
          (List.ofFn fun j => (Fin.natAdd _ j, (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure)))
          hroot (by simp [ownedSpentPositions, removeAll]) hmark hNonZero
          (fun x hx => by
            obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
            exact hj ▸ hRandomOut j)
          hCapacity
        rw [htoken, hnewnotes] at hstepw
        rw [transactOwned_none_live_eq] at hstepw
        simp only [List.map_ofFn] at hstepw
        exact _root_.Reachable.step hreach hstepw
      · obtain ⟨pos0, c1⟩ := c0
        rw [hh] at hmatch
        obtain ⟨w, pub, hM, hC, rest', spent', randomOut, hNonZero, hCapacity, hown, htoken,
          hnewnotes, hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
        rw [heq]
        have hstepw := _root_.Step.transactOwned w pub (by decide) hM hC self hown rest' spent'
          (List.ofFn fun j => (Fin.natAdd _ j, (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure)))
          hroot (by rw [htoken]; exact hremove) hmark hNonZero
          (fun x hx => by
            obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
            exact hj ▸ hRandomOut j)
          hCapacity
        rw [htoken, hnewnotes] at hstepw
        simp only [List.map_ofFn] at hstepw
        exact _root_.Reachable.step hreach hstepw


/-- One adjudicator `Step`'s own pool-level effect is exactly a pool-model
    `_root_.Step`, so `_root_.Reachable` carries forward across it:
    trivially for every `Call` case that leaves `s.pool` unchanged;
    `.deposit`'s own `DepositStep` is `_root_.Step.transact` with
    `unshieldTail := []` (the adjudicator never unshields its own
    deposit), `newNotes := transactAllOutputs w` (the whole output batch
    stays live, matching `DepositStep`'s own `live` field exactly);
    `.deposit`'s own merge (`DepositMergeStep`) is a SECOND
    `_root_.Step.transactOwned`, chained after the first; `.transfer`
    and both bulk calls are `PoolOwnedSpendStep`, itself
    `_root_.Step.transactOwned` (same `live`/`spent`/`leaves`/`roots`/
    `preimageOf`/`ownedRandomOf` shape, `caller := addressOf pub
    .ownerField` matching `self = addressOf pub.ownerField`). What lets
    `unbeatable_pays`'s own strategy invoke `leaf_has_merkle_witness`/
    `owned_spend_witness_exists` at an ARBITRARY reachable `mid`, not
    only at the deployment pool. -/
theorem adjudicator_pool_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s')
    (hreach : _root_.Reachable s.pool) : _root_.Reachable s'.pool := by
  cases call with
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
    obtain ⟨r0, ownerField, hself, hown, hcommit, htoken, hposition, hN, hM, hC, rest, spent',
      records, hCapacity, hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hmidReach : _root_.Reachable midPool := by
      rw [heq]
      have hstepw := _root_.Step.transact w pub hN hM hC (transactAllOutputs w) [] rest spent'
        records [(pub.commitmentsOut idx, (⟨ownerField, r0⟩ : OwnedDisclosure))]
        hRoot (by simp) (by simp) hRemove hNullify hSublist
        (fun cd hcd => by
          rw [List.mem_singleton] at hcd
          exact hcd ▸ ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hidxrec, hown.symm⟩)
        (by unfold transactAllOutputs; rw [List.length_ofFn]; exact hCapacity)
      have heldEq : (fun t => if t = w.token
          then s.pool.held t - listSum (([] : List CommitmentPreimage).map CommitmentPreimage.value)
          else s.pool.held t) = s.pool.held := by
        funext t
        by_cases ht : t = w.token
        · simp [ht, listSum]
        · simp [ht]
      rw [heldEq] at hstepw
      exact _root_.Reachable.step hreach hstepw
    rcases hh : s.holdings asset channelId with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, _hholdseq⟩ := hmatch
      rw [hpoolEq]; exact hmidReach
    · obtain ⟨oldPos, oldHoldingVal⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergedPos, hmerge, _hholdseq⟩ := hmatch
      obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity',
        hown', htoken', hnpkOut', hmergedEq, _hleaf0, _hleaf1, hcommitOld, hcommitNew, hroot',
        hremove', hnullify', hrandomOut', heq'⟩ := hmerge
      rw [heq']
      have hstepw := _root_.Step.transactOwned w' pub' (by decide) (by decide) hC' s.self hown' rest'
        spent'' [(0, (⟨pub'.ownerField, randomOut'⟩ : OwnedDisclosure))]
        hroot' (by rw [htoken']; exact hremove') hnullify'
        (fun j => by have : j = 0 := Fin.ext (by omega); rw [this]; exact hNonZero')
        (fun x hx => by
          rw [List.mem_singleton] at hx
          exact hx ▸ hrandomOut') hCapacity'
      rw [htoken'] at hstepw
      simp only [List.map] at hstepw
      exact _root_.Reachable.step hmidReach hstepw
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, _hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, _hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, _hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨r0, hmatch, _hholdseq, _hchanseq⟩ := hrest
    rcases hh : s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with _ | c0
    · rw [hh] at hmatch
      obtain ⟨w, pub, hM, hC, spent', randomOut, hNonZero, hCapacity, hown, htoken, hnewnotes,
        hroot, hmark, hRandomOut, heq⟩ := hmatch
      rw [heq]
      have hstepw := _root_.Step.transactOwned w pub (by decide) hM hC s.self hown
        (s.pool.live w.token) spent'
        (List.ofFn fun j => (Fin.natAdd _ j, (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure)))
        hroot (by simp [ownedSpentPositions, removeAll]) hmark hNonZero
        (fun x hx => by
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
          exact hj ▸ hRandomOut j)
        hCapacity
      rw [htoken, hnewnotes] at hstepw
      rw [transactOwned_none_live_eq] at hstepw
      simp only [List.map_ofFn] at hstepw
      exact _root_.Reachable.step hreach hstepw
    · obtain ⟨pos0, c1⟩ := c0
      rw [hh] at hmatch
      obtain ⟨w, pub, hM, hC, rest, spent', randomOut, hNonZero, hCapacity, hown, htoken,
        hnewnotes, hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
      rw [heq]
      have hstepw := _root_.Step.transactOwned w pub (by decide) hM hC s.self hown rest spent'
        (List.ofFn fun j => (Fin.natAdd _ j, (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure)))
        hroot (by rw [htoken]; exact hremove) hmark hNonZero
        (fun x hx => by
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
          exact hj ▸ hRandomOut j)
        hCapacity
      rw [htoken, hnewnotes] at hstepw
      simp only [List.map_ofFn] at hstepw
      exact _root_.Reachable.step hreach hstepw
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _hsa, _hidx1, _h5, _h6, hpoolEq, _hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_pool_reachable s.self channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold hreach
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_pool_reachable s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold hreach
  | tick newNow =>
    obtain ⟨_, _, hpoolEq, _hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, _hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | signNote pk msgHash =>
    obtain ⟨_, _, hpoolEq, _, _hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach

/-- The reachable-set form of `adjudicator_pool_step`: the pool component
    of every adjudicator-reachable state is itself pool-reachable from
    `pool0`. -/
theorem adjudicator_pool_reachable (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0) (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets self pool0) s) :
    _root_.Reachable s.pool :=
  reachable_preserves (P := fun s'' => _root_.Reachable s''.pool) hReachPool
    (fun actor call s1 s2 hP hstep => adjudicator_pool_step sig appRel actor s1 s2 call hstep hP)
    hreach


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
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, _, _, _, h, _, _, _, _⟩ := hstep
    exact h
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, _, _, _, h, _, _, _, _⟩ := hstep
    exact h
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
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact h
  | tick newNow =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | sign p d =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
/-- `bulkTransferFold`'s own non-empty call always opens a
    `PoolOwnedSpendStep`, whose own `self = addressOf pub.ownerField`
    conjunct (both nullified cases) bounds `self` regardless of which
    asset or channel is being processed. What `holding_implies_self_is_
    address` needs for its own `.bulkTransferAllAssets`/
    `.bulkConcludeAndTransferAllAssets` cases. -/
theorem bulkTransferFold_self_bound (self : Nat) (cid : Term) (exit : SingleAssetExit)
    (rest : List SingleAssetExit) (pool poolF : PoolState)
    (holdings holdingsF : Nat → Term → Option (Nat × Term)) (newOutcome : Outcome) :
    bulkTransferFold self cid (exit :: rest) pool holdings newOutcome poolF holdingsF →
    self < 2 ^ 160 := by
  cases newOutcome with
  | nil => intro hfold; unfold bulkTransferFold at hfold; exact hfold.elim
  | cons newExit newRest =>
    intro hfold
    unfold bulkTransferFold at hfold
    obtain ⟨_hguarantee, _hnewExit, r0, midPool, hmatch, _hrec⟩ := hfold
    rcases hh : holdings exit.asset cid with _ | c0
    · rw [hh] at hmatch
      obtain ⟨_w, _pub, _hM, _hC, _spent', _randomOut, _hNonZero, _hCapacity, hown, _htoken,
        _hnewnotes, _hroot, _hmark, _hRandomOut, _heq⟩ := hmatch
      rw [hown]; unfold addressOf; exact Nat.mod_lt _ (by decide)
    · rw [hh] at hmatch
      obtain ⟨_w, _pub, _hM, _hC, _rest', _spent', _randomOut, _hNonZero, _hCapacity, hown,
        _htoken, _hnewnotes, _hleavesIdx, _hcommit, _hroot, _hremove, _hmark, _hRandomOut,
        _heq⟩ := hmatch
      rw [hown]; unfold addressOf; exact Nat.mod_lt _ (by decide)

/-- **A channel can hold a note only when the adjudicator's own `self` is a
    real 20-byte address.** `self = addressOf ownerField` (`addressOf x =
    x % 2^160`, so always `< 2^160`) gates every step that ever WRITES a
    non-`none` `holdings` entry — `.deposit` (both the first-deposit and
    the merge case), `.transfer`'s own remainder, and both bulk calls' own
    remainder, all via `DepositStep`/`PoolOwnedSpendStep`/
    `DepositMergeStep`. No step ever reads this bound from an EXISTING
    entry, so the invariant threads through every OTHER call case for
    free (`holdings` unchanged). What lets `unbeatable_pays`'s own
    strategy derive `self < 2 ^ 160` from `haffordable`/`hxpos` alone,
    with no extra hypothesis. -/
theorem holding_implies_self_is_address (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (self : Nat) (pool0 : PoolState) (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets self pool0) s)
    (asset : Nat) (cid : Term) (hh : s.holdings asset cid ≠ none) :
    self < 2 ^ 160 := by
  have hP : s.self = self ∧ ((∃ a c, s.holdings a c ≠ none) → self < 2 ^ 160) := by
    refine reachable_preserves
      (P := fun s'' => s''.self = self ∧ ((∃ a c, s''.holdings a c ≠ none) → self < 2 ^ 160))
      ⟨rfl, fun hex => by obtain ⟨a, c, hac⟩ := hex; simp [genesis] at hac⟩ ?_ hreach
    intro actor call s1 s2 hP1 hstep
    have hselfeq := (step_self sig appRel actor s1 s2 call hstep).trans hP1.1
    refine ⟨hselfeq, ?_⟩
    intro hex
    cases call with
    | deposit channelId expectedHeld asset' amount =>
      obtain ⟨_hcfg, _hheld, _hext, _hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
      obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, _hmatch⟩ := hinner
      obtain ⟨_r0, _ownerField, hself, _hown, _hcommit, _htoken, _hposition, _hN, _hM, _hC,
        _rest, _spent', _records, _hCapacity, _hRoot, _hRemove, _hNullify, _hSublist, _hidxrec,
        _heq⟩ := hdstep
      rw [← hP1.1, hself]; unfold addressOf; exact Nat.mod_lt _ (by decide)
    | challenge fp proof candidate challenger =>
      obtain ⟨_, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
      exact hP1.2 (hholdEq ▸ hex)
    | checkpoint fp proof candidate =>
      obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
      exact hP1.2 (hholdEq ▸ hex)
    | conclude fp candidate =>
      obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
      exact hP1.2 (hholdEq ▸ hex)
    | transfer assetIndex cid' claimedStateHash outcome indices =>
      obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
      obtain ⟨_hguarantee, hrest⟩ := hinner
      obtain ⟨_r0, hmatch, _hholdseq, _hchanseq⟩ := hrest
      rcases hh' : s1.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid' with _ | c0
      · rw [hh'] at hmatch
        obtain ⟨_w, _pub, _hM, _hC, _spent', _randomOut, _hNonZero, _hCapacity, hown, _htoken,
          _hnewnotes, _hroot, _hmark, _hRandomOut, _heq⟩ := hmatch
        rw [← hP1.1, hown]; unfold addressOf; exact Nat.mod_lt _ (by decide)
      · rw [hh'] at hmatch
        obtain ⟨_w, _pub, _hM, _hC, _rest, _spent', _randomOut, _hNonZero, _hCapacity, hown,
          _htoken, _hnewnotes, _hleavesIdx, _hcommit, _hroot, _hremove, _hmark, _hRandomOut,
          _heq⟩ := hmatch
        rw [← hP1.1, hown]; unfold addressOf; exact Nat.mod_lt _ (by decide)
    | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
        targetAssetIndex claimedTargetStateHash =>
      obtain ⟨_, _, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
      exact hP1.2 (hholdEq ▸ hex)
    | bulkTransferAllAssets channelId outcome claimedStateHash =>
      obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
      cases outcome with
      | nil =>
        cases newOutcome with
        | nil =>
          unfold bulkTransferFold at hfold
          obtain ⟨_hpoolEq, hholdEq⟩ := hfold
          exact hP1.2 (hholdEq ▸ hex)
        | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
      | cons exit rest =>
        rw [← hP1.1]
        exact bulkTransferFold_self_bound s1.self channelId exit rest s1.pool s2.pool s1.holdings
          s2.holdings newOutcome hfold
    | bulkConcludeAndTransferAllAssets fp candidate =>
      obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
      generalize hco : candidate.outcome = co at hfold
      cases co with
      | nil =>
        cases newOutcome with
        | nil =>
          unfold bulkTransferFold at hfold
          obtain ⟨_hpoolEq, hholdEq⟩ := hfold
          exact hP1.2 (hholdEq ▸ hex)
        | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
      | cons exit rest =>
        rw [← hP1.1]
        exact bulkTransferFold_self_bound s1.self (channelId fp) exit rest s1.pool s2.pool
          s1.holdings s2.holdings newOutcome hfold
    | tick newNow =>
      obtain ⟨_, _, hpoolEq, hholdEq, _⟩ := hstep
      exact hP1.2 (hholdEq ▸ hex)
    | sign p d =>
      obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
      exact hP1.2 (hholdEq ▸ hex)
    | signNote pk msgHash =>
      obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
      exact hP1.2 (hholdEq ▸ hex)
  exact hP.2 ⟨asset, cid, hh⟩

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
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _⟩ := hstep
    rw [h]; exact fun p d hp => hp
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _⟩ := hstep
    rw [h]; exact fun p d hp => hp
  | tick newNow =>
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]; exact fun p d hp => hp
  | sign p d =>
    obtain ⟨_, h⟩ := hstep
    rw [h.1]; exact fun p' d' hp => Or.inr hp
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h]; exact fun p d hp => hp

/-- `signedBy` at one participant's OWN row is untouched by a `Step`
    taken under any OTHER identity: only `.sign q d` by actor `.nitro q`
    itself ever adds to row `q`, and every other call leaves `signedBy`
    unchanged entirely (`step_signedBy_mono`'s own case list). What
    `unbeatable_pays`/`unbeatable_pays_after_timeout` need to carry `h`'s
    own `AuthorizedBy` fact across an `interleaved` sequence that never
    acts as `h`. -/
theorem step_signedBy_frame (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s') (q : Nat) (hactor : actor ≠ Actor.nitro q) :
    s'.signedBy q = s.signedBy q := by
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _⟩ := hstep
    rw [h]
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _⟩ := hstep
    rw [h]
  | tick newNow =>
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hstep
    rw [h.1]
  | sign p d =>
    obtain ⟨hp, h⟩ := hstep
    rw [h.1]
    funext d'
    dsimp only
    have hpneq : p ≠ q := fun heq => hactor (heq ▸ hp)
    have hiff : (q = p ∧ d' = d ∨ s.signedBy q d') ↔ s.signedBy q d' := by
      constructor
      · rintro (⟨heq, _⟩ | hsb)
        · exact absurd heq (fun h => hpneq h.symm)
        · exact hsb
      · exact Or.inr
    exact propext hiff
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h]

/-- `step_signedBy_frame` across a whole `interleaved` sequence: if no
    step in it ever acts as `.nitro q`, `q`'s own `signedBy` row is
    exactly what it was before the sequence ran. -/
theorem appliesAll_signedBy_frame (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (q : Nat) :
    ∀ {calls : List (Actor × Call)} {s s' : AdjudicatorState},
      AppliesAll sig appRel s calls s' →
      (∀ actor call, (actor, call) ∈ calls → actor ≠ Actor.nitro q) →
      s'.signedBy q = s.signedBy q
  | [], s, s', happ, _ => by rw [show s' = s from happ]
  | (actor, call) :: rest, s, s', happ, hexcl => by
    obtain ⟨mid, hstep, hrest⟩ := happ
    have h1 : mid.signedBy q = s.signedBy q :=
      step_signedBy_frame sig appRel actor s mid call hstep q
        (hexcl actor call (List.mem_cons_self ..))
    have h2 : s'.signedBy q = mid.signedBy q :=
      appliesAll_signedBy_frame sig appRel q hrest
        (fun actor' call' hc => hexcl actor' call' (List.mem_cons_of_mem _ hc))
    rw [h2, h1]


/-- `poolSignedBy` at one public key's OWN row is untouched by a `Step`
    taken under any OTHER identity: only `.signNote pk msgHash` by actor
    `.pool pk` itself ever adds to row `pk` (`Operations.lean`'s own
    module comment on `.sign`/`.signNote`, the pool-layer counterpart);
    every other call leaves `poolSignedBy` unchanged entirely
    (`step_signedBy_mono`'s own case list, `poolSignedBy` side). What
    `unbeatable_pays`/`unbeatable_pays_after_timeout` need to carry the
    MODEL FIX's `s.poolSignedBy w.publicKey (msgHashOf pub)` gate
    (`Operations.lean`'s `.deposit` case) across an `interleaved`
    sequence that never acts as `.pool pk`: no step in it can newly
    authorize a `.deposit` spend under `pk`. -/
theorem poolSignedBy_frame (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s') (pk : Nat × Nat)
    (hactor : actor ≠ Actor.pool pk) :
    s'.poolSignedBy pk = s.poolSignedBy pk := by
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.2]
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.2]
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.2]
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.2]
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.2]
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h.2]
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h]
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h]
  | tick newNow =>
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hstep
    rw [h.2]
  | sign p d =>
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hstep
    rw [h]
  | signNote pk' msgHash =>
    obtain ⟨hp, h⟩ := hstep
    rw [h.1]
    funext m'
    dsimp only
    have hpneq : pk' ≠ pk := fun heq => hactor (heq ▸ hp)
    have hiff : (pk = pk' ∧ m' = msgHash ∨ s.poolSignedBy pk m') ↔ s.poolSignedBy pk m' := by
      constructor
      · rintro (⟨heq, _⟩ | hsb)
        · exact absurd heq (fun h => hpneq h.symm)
        · exact hsb
      · exact Or.inr
    exact propext hiff

/-- `poolSignedBy_frame` across a whole `interleaved` sequence: if no
    step in it ever acts as `.pool pk`, `pk`'s own `poolSignedBy` row is
    exactly what it was before the sequence ran. -/
theorem appliesAll_poolSignedBy_frame (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (pk : Nat × Nat) :
    ∀ {calls : List (Actor × Call)} {s s' : AdjudicatorState},
      AppliesAll sig appRel s calls s' →
      (∀ actor call, (actor, call) ∈ calls → actor ≠ Actor.pool pk) →
      s'.poolSignedBy pk = s.poolSignedBy pk
  | [], s, s', happ, _ => by rw [show s' = s from happ]
  | (actor, call) :: rest, s, s', happ, hexcl => by
    obtain ⟨mid, hstep, hrest⟩ := happ
    have h1 : mid.poolSignedBy pk = s.poolSignedBy pk :=
      poolSignedBy_frame sig appRel actor s mid call hstep pk
        (hexcl actor call (List.mem_cons_self ..))
    have h2 : s'.poolSignedBy pk = mid.poolSignedBy pk :=
      appliesAll_poolSignedBy_frame sig appRel pk hrest
        (fun actor' call' hc => hexcl actor' call' (List.mem_cons_of_mem _ hc))
    rw [h2, h1]

/-- A live note keyed to a USER's own master public key is spent by a
    `.deposit` step ONLY if the witness signs under THAT SAME key:
    `transactSpentPositions` claims, for each input it names, a preimage
    keyed to `npk (masterPublicKey w.publicKey w.nullifyingKey) _`
    (`Pool.lean`); `removeAll`'s own list-permutation semantics
    (`removeAll_perm`) means a position the witness does NOT name
    survives untouched into `rest`, and one it DOES name forces its
    EXACT claimed preimage onto the real one (`removeAll`'s `elem`
    check is `DecidableEq`-exact), hence (`npk`/`masterPublicKey`'s own
    Poseidon injectivity) the SAME public key. What the MODEL FIX's
    `poolSignedBy` gate (`Operations.lean`'s `.deposit` case) and
    `poolSignedBy_frame` need together, for `unbeatable_pays`/
    `unbeatable_pays_after_timeout`: a note only `h` holds the key for
    cannot be spent by a DIFFERENT key holder's deposit at all, so
    excluding that OTHER key's `.pool` actor from `interleaved` is
    moot for THIS note — it was never spendable by anyone else in the
    first place; the exclusion only matters for `poolSignedBy_frame`
    keeping `h`'s OWN key's authorization row from growing BY SOMEONE
    ELSE first. -/
theorem deposit_spend_requires_signer {N M : Nat}
    (before : PoolState) (token pos : Nat) (pre : CommitmentPreimage)
    (pk : Nat × Nat) (nk r : Nat) (hnpk : pre.npk = npk (masterPublicKey pk nk) r)
    (hmem : (pos, pre) ∈ before.live token)
    (w : TransactWitness N M) (htoken : w.token = token) (hpk : w.publicKey ≠ pk)
    {rest : List (Nat × CommitmentPreimage)}
    (hRemove : removeAll (before.live w.token) (transactSpentPositions w) = some rest) :
    (pos, pre) ∈ rest := by
  have hmemperm : (pos, pre) ∈ transactSpentPositions w ++ rest :=
    (removeAll_perm hRemove).mem_iff.mp (htoken ▸ hmem)
  refine (List.mem_append.mp hmemperm).resolve_left ?_
  intro hsp
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hsp
  have hpreeq : pre = (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j),
      w.token, w.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
  have hnpkeq2 : npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j) =
      npk (masterPublicKey pk nk) r :=
    (congrArg CommitmentPreimage.npk hpreeq).symm.trans hnpk
  have hmpkeq : masterPublicKey w.publicKey w.nullifyingKey = masterPublicKey pk nk :=
    (Term.hash2_inj hnpkeq2).1
  obtain ⟨h1, h2, h3⟩ := Term.hash3_inj hmpkeq
  exact hpk (Prod.ext (Term.val.inj h1) (Term.val.inj h2))



/-- `SignedByAll` carries forward across one more `Step`: `AuthorizedBy`
    is `s.signedBy p d ∨ sig.contractAuthorizes p d` (`State.lean`), and
    only the FIRST disjunct can depend on `s` at all — `step_signedBy_mono`
    gives that one, the second survives unchanged. What
    `finalized_outcome_was_concluded_or_challenged` needs to carry a
    `SignedByAll` fact, established at one `.conclude` call, forward to
    the state actually queried. -/
theorem SignedByAll_mono (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s')
    (fp : FixedPart) (vp : VariablePart) (h : SignedByAll sig s fp vp) :
    SignedByAll sig s' fp vp := by
  intro p hp
  rcases h p hp with hsb | hca
  · exact Or.inl (step_signedBy_mono sig appRel actor s s' call hstep p (stateHash fp vp) hsb)
  · exact Or.inr hca

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
theorem payout_outputs_nonzero (exitAllocs : List Allocation) (remainder asset self r : Nat) :
    ∀ pre ∈ (exitAllocs.filterMap (fun a =>
        if a.amount = 0 then none else some (⟨a.destination, asset, a.amount⟩ : CommitmentPreimage))) ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]),
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

/-- One `PoolOwnedSpendStep`-backed holdings update, the shape `.transfer`
    and `bulkTransferFold` both use: spend channel `cid`'s own holding of
    `asset`, pay `payoutOutputs` out, and record at most one `remainder`
    note back to `cid`. If every known holding reads back a nonzero,
    consistent preimage before this update, the same holds after — the
    fresh remainder note this update writes, and every OTHER holding,
    touched by this update or not. Generalizes `.transfer`'s own
    reasoning (`Operations.lean`) so `bulkTransferFold`'s induction can
    reuse it once per asset instead of re-deriving it. -/
theorem PoolOwnedSpend_update_preimage_nonzero
    (pool pool' : PoolState) (self asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option (Nat × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some (pool.leaves.length +
               (payoutOutputs ++ (if remainder = 0 then [] else
                 [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length - 1,
             commitment (npk (Term.val self) r) asset remainder)))) qasset qcid = some (qpos, qc) →
      ∃ pre, pool'.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
  intro qasset qcid qpos qc hc
  unfold update at hc
  have hvalid_outputs : ∀ cp ∈ (payoutOutputs ++
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)])).map
      (fun pre => (commitment pre.npk asset pre.value, pre)), hashCommitment cp.2 = cp.1 := by
    intro cp hcp
    obtain ⟨pre, hmem, hcpeq⟩ := List.mem_map.mp hcp
    have htok : pre.token = asset := by
      rcases List.mem_append.mp hmem with hc1 | hc2
      · exact htokPayout pre hc1
      · by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc2; exact absurd hc2 (List.not_mem_nil)
        · rw [if_neg hrem] at hc2
          rw [List.mem_singleton] at hc2
          exact hc2 ▸ rfl
    rw [← hcpeq]
    show hashCommitment pre = commitment pre.npk asset pre.value
    rw [← htok]
    rfl
  have hrelated : ∀ (hpre : pool'.preimageOf = applyRecords pool.preimageOf
      ((payoutOutputs ++ (if remainder = 0 then [] else
        [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)))),
      remainder ≠ 0 → commitment (npk (Term.val self) r) asset remainder = qc →
      ∃ pre, pool'.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro hpre hrem hqc
    have hnz : ¬ isZeroPreimage (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) :=
      fun hz => hrem hz.2.1
    have hmemout : (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])) := by
      rw [if_neg hrem]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    have hmemout2 : (qc, (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      rw [← hqc]
      exact List.mem_map.mpr ⟨_, hmemout, rfl⟩
    refine ⟨⟨npk (Term.val self) r, asset, remainder⟩, ?_, hrem, hqc⟩
    rw [hpre]
    exact applyRecords_reads hvalid_outputs pool.preimageOf qc
      (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) hmemout2 hnz
  have hunrelated : ∀ (hpre : pool'.preimageOf = applyRecords pool.preimageOf
      ((payoutOutputs ++ (if remainder = 0 then [] else
        [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)))),
      holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool'.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro hpre hc'
    obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qpos qc hc'
    refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
    rw [hpre]
    exact applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre_old hpre_old hconsist_old
  rcases hc0 : holdings asset cid with _ | c0
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _spent', _randomOut, hNonZero, _hCapacity, _hown, htoken, hnewnotes,
      _hroot, _hmark, _hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    have hpre0 : pool'.preimageOf = applyRecords pool.preimageOf
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk asset pre.value, pre))) := by
      rw [← hrecordseq]
      exact congrArg PoolState.preimageOf heq
    by_cases heqch : qasset = asset ∧ qcid = cid
    · obtain ⟨ha, hcid⟩ := heqch
      subst ha; subst hcid
      rw [if_pos rfl, if_pos rfl] at hc
      by_cases hrem : remainder = 0
      · rw [if_pos hrem] at hc; exact absurd hc (by simp)
      · rw [if_neg hrem] at hc
        exact hrelated hpre0 hrem (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hc).2
    · have hc' : holdings qasset qcid = some (qpos, qc) := by
        by_cases ha : qasset = asset
        · subst ha
          by_cases hcid : qcid = cid
          · exact absurd ⟨rfl, hcid⟩ heqch
          · rw [if_pos rfl, if_neg hcid] at hc; exact hc
        · rw [if_neg ha] at hc; exact hc
      exact hunrelated hpre0 hc'
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _, hC, _, _, _, hNonZero, _, _, htoken, hnewnotes, _, _, _, _, _, _, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    have hpre0 : pool'.preimageOf = applyRecords pool.preimageOf
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk asset pre.value, pre))) := by
      rw [← hrecordseq]
      exact congrArg PoolState.preimageOf heq
    by_cases heqch : qasset = asset ∧ qcid = cid
    · obtain ⟨ha, hcid⟩ := heqch
      subst ha; subst hcid
      rw [if_pos rfl, if_pos rfl] at hc
      by_cases hrem : remainder = 0
      · rw [if_pos hrem] at hc; exact absurd hc (by simp)
      · rw [if_neg hrem] at hc
        exact hrelated hpre0 hrem (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hc).2
    · have hc' : holdings qasset qcid = some (qpos, qc) := by
        by_cases ha : qasset = asset
        · subst ha
          by_cases hcid : qcid = cid
          · exact absurd ⟨rfl, hcid⟩ heqch
          · rw [if_pos rfl, if_neg hcid] at hc; exact hc
        · rw [if_neg ha] at hc; exact hc
      exact hunrelated hpre0 hc'


/-- `PoolOwnedSpendStep`'s own `ownedRandomOf` update, the `ownedRandomOf`
    sibling of `PoolOwnedSpend_update_preimage_nonzero`: an already-known
    adjudicator-owned disclosure survives the step (`applyOwnedRecords_
    preserves_known`, since the step's own disclosure batch is valid
    against `pool.preimageOf`, `htokPayout`/`hC.outputs` giving every
    batch entry's own commitment), and — when `remainder ≠ 0` — the FRESH
    remainder note is disclosed directly (`hRandomOut`, the step's own
    mandatory owned-output disclosure, combined with `npk_inj` to pin the
    random back to `r`). What `unbeatable_pays`'s own strategy needs to
    carry a channel's held note's own disclosure across the `.transfer`
    call that spends it, and to name the fresh remainder note's own
    disclosure directly. -/
theorem PoolOwnedSpendStep_ownedRandom_known
    (pool pool' : PoolState) (self asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option (Nat × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])
      pool') :
    (∀ qc pre' r', pool.preimageOf qc = some pre' → hashCommitment pre' = qc →
      pre'.npk = npk (Term.val self) r' →
      pool.ownedRandomOf qc = some ⟨self, r'⟩ →
      pool'.ownedRandomOf qc = some ⟨self, r'⟩) ∧
    (remainder ≠ 0 →
      pool'.ownedRandomOf (commitment (npk (Term.val self) r) asset remainder) =
        some ⟨self, r⟩) := by
  have hvalid_outputs : ∀ cp ∈ (payoutOutputs ++
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)])).map
      (fun pre => (commitment pre.npk asset pre.value, pre)), hashCommitment cp.2 = cp.1 := by
    intro cp hcp
    obtain ⟨pre, hmem, hcpeq⟩ := List.mem_map.mp hcp
    have htok : pre.token = asset := by
      rcases List.mem_append.mp hmem with hc1 | hc2
      · exact htokPayout pre hc1
      · by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc2; exact absurd hc2 (List.not_mem_nil)
        · rw [if_neg hrem] at hc2
          rw [List.mem_singleton] at hc2
          exact hc2 ▸ rfl
    rw [← hcpeq]
    show hashCommitment pre = commitment pre.npk asset pre.value
    rw [← htok]
    rfl
  rcases hc0 : holdings asset cid with _ | c0
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, hM, hC, spent', randomOut, hNonZero, hCapacity, hown, htoken, hnewnotes,
      hroot, hmark, hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    have hvalid_owned : ∀ cd ∈ (List.ofFn fun j : Fin (if remainder = 0 then ([] :
        List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)]).length => ((pub.commitmentsOut (Fin.natAdd payoutOutputs.length j) :
        Term), (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure))),
        ∃ pre, pool'.preimageOf cd.1 = some pre ∧ npk (Term.val cd.2.ownerField) cd.2.random = pre.npk := by
      intro cd hcd
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcd
      refine ⟨⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
        w.valueOut (Fin.natAdd payoutOutputs.length j)⟩, ?_, ?_⟩
      · have hmemrec : (pub.commitmentsOut (Fin.natAdd payoutOutputs.length j),
            (⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
              w.valueOut (Fin.natAdd payoutOutputs.length j)⟩ : CommitmentPreimage)) ∈
            ownedOutputRecords w pub := by
          unfold ownedOutputRecords
          exact List.mem_ofFn.mpr ⟨_, rfl⟩
        rw [hrecordseq] at hmemrec
        have hnzj : ¬ isZeroPreimage (⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
            w.valueOut (Fin.natAdd payoutOutputs.length j)⟩ : CommitmentPreimage) :=
          npk_preimage_not_zero (hRandomOut j)
        rw [← congrArg Prod.fst hj]
        rw [heq]; dsimp only; rw [hrecordseq]
        exact applyRecords_reads hvalid_outputs pool.preimageOf _ _ hmemrec hnzj
      · dsimp only
        rw [← hj]
        exact hRandomOut j
    constructor
    · intro qc pre' r' hpre' hconsist hnpk' hknown
      have hpre'_at_pool' : pool'.preimageOf qc = some pre' := by
        rw [heq]; dsimp only; rw [hrecordseq]
        exact applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre' hpre' hconsist
      rw [heq]
      show applyOwnedRecords pool.ownedRandomOf (List.ofFn fun j : Fin (if remainder = 0 then
        ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)]).length => ((pub.commitmentsOut (Fin.natAdd payoutOutputs.length j) :
        Term), (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure))) qc = some ⟨self, r'⟩
      exact applyOwnedRecords_preserves_known hvalid_owned pool.ownedRandomOf qc self r' pre'
        hknown hpre'_at_pool' hnpk'
    · intro hrem
      rw [heq]
      show applyOwnedRecords pool.ownedRandomOf (List.ofFn fun j : Fin (if remainder = 0 then
        ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)]).length => ((pub.commitmentsOut (Fin.natAdd payoutOutputs.length j) :
        Term), (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure)))
        (commitment (npk (Term.val self) r) asset remainder) = some ⟨self, r⟩
      have hlt : payoutOutputs.length < (payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length := by
        rw [if_neg hrem, List.length_append]; simp
      have hltM : payoutOutputs.length < (ownedNewNotes w).length := by
        rw [congrArg List.length hnewnotes]; exact hlt
      have hget : (ownedNewNotes w)[payoutOutputs.length]? =
          (payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]))[payoutOutputs.length]? :=
        congrArg (·[payoutOutputs.length]?) hnewnotes
      have hrhs : (payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]))[payoutOutputs.length]? =
          some (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) := by
        rw [if_neg hrem, List.getElem?_append_right (Nat.le_refl _)]
        simp
      rw [hrhs] at hget
      have hltM' : payoutOutputs.length < payoutOutputs.length + (if remainder = 0 then
          ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)]).length := by rw [if_neg hrem]; simp
      unfold ownedNewNotes at hget
      rw [List.getElem?_ofFn, dif_pos hltM'] at hget
      have hpreeq : (⟨w.npkOut ⟨payoutOutputs.length, hltM'⟩, w.token,
          w.valueOut ⟨payoutOutputs.length, hltM'⟩⟩ : CommitmentPreimage) =
          ⟨npk (Term.val self) r, asset, remainder⟩ := Option.some.inj hget
      have hnpkeq : w.npkOut ⟨payoutOutputs.length, hltM'⟩ = npk (Term.val self) r :=
        congrArg CommitmentPreimage.npk hpreeq
      have htokeq : w.token = asset := congrArg CommitmentPreimage.token hpreeq
      have hvaleq : w.valueOut ⟨payoutOutputs.length, hltM'⟩ = remainder :=
        congrArg CommitmentPreimage.value hpreeq
      have hcommiteq : pub.commitmentsOut ⟨payoutOutputs.length, hltM'⟩ =
          commitment (npk (Term.val self) r) asset remainder := by
        rw [hC.outputs ⟨payoutOutputs.length, hltM'⟩, hnpkeq, htokeq, hvaleq]
      have hnataddeq : Fin.natAdd payoutOutputs.length (⟨0, by rw [if_neg hrem]; simp⟩ : Fin
          (if remainder = 0 then ([] : List CommitmentPreimage) else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]).length) =
          (⟨payoutOutputs.length, hltM'⟩ : Fin (payoutOutputs.length + (if remainder = 0 then
          ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)]).length)) := by
        apply Fin.ext
        show payoutOutputs.length + 0 = payoutOutputs.length
        omega
      have hrandomeq : npk (Term.val pub.ownerField) (randomOut (⟨0, by rw [if_neg hrem]; simp⟩ : Fin
          (if remainder = 0 then ([] : List CommitmentPreimage) else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]).length)) =
          npk (Term.val self) r := by
        rw [hRandomOut, hnataddeq]; exact hnpkeq
      obtain ⟨hmpk, hrand⟩ := npk_inj hrandomeq
      have hof : pub.ownerField = self := Term.val.inj hmpk
      refine applyOwnedRecords_reads hvalid_owned pool.ownedRandomOf _ _ ?_
      apply List.mem_ofFn.mpr
      refine ⟨⟨0, by rw [if_neg hrem]; simp⟩, ?_⟩
      rw [hnataddeq, hcommiteq, hof, hrand]
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, hM, hC, rest, spent', randomOut, hNonZero, hCapacity, hown, htoken, hnewnotes,
      hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    have hvalid_owned : ∀ cd ∈ (List.ofFn fun j : Fin (if remainder = 0 then ([] :
        List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)]).length => ((pub.commitmentsOut (Fin.natAdd payoutOutputs.length j) :
        Term), (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure))),
        ∃ pre, pool'.preimageOf cd.1 = some pre ∧ npk (Term.val cd.2.ownerField) cd.2.random = pre.npk := by
      intro cd hcd
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcd
      refine ⟨⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
        w.valueOut (Fin.natAdd payoutOutputs.length j)⟩, ?_, ?_⟩
      · have hmemrec : (pub.commitmentsOut (Fin.natAdd payoutOutputs.length j),
            (⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
              w.valueOut (Fin.natAdd payoutOutputs.length j)⟩ : CommitmentPreimage)) ∈
            ownedOutputRecords w pub := by
          unfold ownedOutputRecords
          exact List.mem_ofFn.mpr ⟨_, rfl⟩
        rw [hrecordseq] at hmemrec
        have hnzj : ¬ isZeroPreimage (⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
            w.valueOut (Fin.natAdd payoutOutputs.length j)⟩ : CommitmentPreimage) :=
          npk_preimage_not_zero (hRandomOut j)
        rw [← congrArg Prod.fst hj]
        rw [heq]; dsimp only; rw [hrecordseq]
        exact applyRecords_reads hvalid_outputs pool.preimageOf _ _ hmemrec hnzj
      · dsimp only
        rw [← hj]
        exact hRandomOut j
    constructor
    · intro qc pre' r' hpre' hconsist hnpk' hknown
      have hpre'_at_pool' : pool'.preimageOf qc = some pre' := by
        rw [heq]; dsimp only; rw [hrecordseq]
        exact applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre' hpre' hconsist
      rw [heq]
      show applyOwnedRecords pool.ownedRandomOf (List.ofFn fun j : Fin (if remainder = 0 then
        ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)]).length => ((pub.commitmentsOut (Fin.natAdd payoutOutputs.length j) :
        Term), (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure))) qc = some ⟨self, r'⟩
      exact applyOwnedRecords_preserves_known hvalid_owned pool.ownedRandomOf qc self r' pre'
        hknown hpre'_at_pool' hnpk'
    · intro hrem
      rw [heq]
      show applyOwnedRecords pool.ownedRandomOf (List.ofFn fun j : Fin (if remainder = 0 then
        ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)]).length => ((pub.commitmentsOut (Fin.natAdd payoutOutputs.length j) :
        Term), (⟨pub.ownerField, randomOut j⟩ : OwnedDisclosure)))
        (commitment (npk (Term.val self) r) asset remainder) = some ⟨self, r⟩
      have hlt : payoutOutputs.length < (payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length := by
        rw [if_neg hrem, List.length_append]; simp
      have hltM : payoutOutputs.length < (ownedNewNotes w).length := by
        rw [congrArg List.length hnewnotes]; exact hlt
      have hget : (ownedNewNotes w)[payoutOutputs.length]? =
          (payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]))[payoutOutputs.length]? :=
        congrArg (·[payoutOutputs.length]?) hnewnotes
      have hrhs : (payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]))[payoutOutputs.length]? =
          some (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) := by
        rw [if_neg hrem, List.getElem?_append_right (Nat.le_refl _)]
        simp
      rw [hrhs] at hget
      have hltM' : payoutOutputs.length < payoutOutputs.length + (if remainder = 0 then
          ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)]).length := by rw [if_neg hrem]; simp
      unfold ownedNewNotes at hget
      rw [List.getElem?_ofFn, dif_pos hltM'] at hget
      have hpreeq : (⟨w.npkOut ⟨payoutOutputs.length, hltM'⟩, w.token,
          w.valueOut ⟨payoutOutputs.length, hltM'⟩⟩ : CommitmentPreimage) =
          ⟨npk (Term.val self) r, asset, remainder⟩ := Option.some.inj hget
      have hnpkeq : w.npkOut ⟨payoutOutputs.length, hltM'⟩ = npk (Term.val self) r :=
        congrArg CommitmentPreimage.npk hpreeq
      have htokeq : w.token = asset := congrArg CommitmentPreimage.token hpreeq
      have hvaleq : w.valueOut ⟨payoutOutputs.length, hltM'⟩ = remainder :=
        congrArg CommitmentPreimage.value hpreeq
      have hcommiteq : pub.commitmentsOut ⟨payoutOutputs.length, hltM'⟩ =
          commitment (npk (Term.val self) r) asset remainder := by
        rw [hC.outputs ⟨payoutOutputs.length, hltM'⟩, hnpkeq, htokeq, hvaleq]
      have hnataddeq : Fin.natAdd payoutOutputs.length (⟨0, by rw [if_neg hrem]; simp⟩ : Fin
          (if remainder = 0 then ([] : List CommitmentPreimage) else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]).length) =
          (⟨payoutOutputs.length, hltM'⟩ : Fin (payoutOutputs.length + (if remainder = 0 then
          ([] : List CommitmentPreimage) else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)]).length)) := by
        apply Fin.ext
        show payoutOutputs.length + 0 = payoutOutputs.length
        omega
      have hrandomeq : npk (Term.val pub.ownerField) (randomOut (⟨0, by rw [if_neg hrem]; simp⟩ : Fin
          (if remainder = 0 then ([] : List CommitmentPreimage) else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)]).length)) =
          npk (Term.val self) r := by
        rw [hRandomOut, hnataddeq]; exact hnpkeq
      obtain ⟨hmpk, hrand⟩ := npk_inj hrandomeq
      have hof : pub.ownerField = self := Term.val.inj hmpk
      refine applyOwnedRecords_reads hvalid_owned pool.ownedRandomOf _ _ ?_
      apply List.mem_ofFn.mpr
      refine ⟨⟨0, by rw [if_neg hrem]; simp⟩, ?_⟩
      rw [hnataddeq, hcommiteq, hof, hrand]


/-- One `PoolOwnedSpendStep`-backed holdings update (the shape `.transfer`
    and `bulkTransferFold` both use) leaves every OTHER `(asset, cid)`
    pair's own held value UNCHANGED: `update`/`update` only ever touch
    the ONE pair this step names, and `applyRecords_preserves_known`
    carries an already-known preimage through the payout batch
    unscathed. The `PoolOwnedSpendStep`-backed sibling of
    `deposit_frame`, what A-13 needs to rule out `.transfer`/bulk calls
    on a DIFFERENT channel from lowering `heldValue` at the named one. -/
theorem PoolOwnedSpendStep_frame
    (pool pool' : PoolState) (self asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option (Nat × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (qasset : Nat) (qcid : Term) (hne : (qasset, qcid) ≠ (asset, cid)) :
    (match (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some (pool.leaves.length +
               (payoutOutputs ++ (if remainder = 0 then [] else
                 [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length - 1,
             commitment (npk (Term.val self) r) asset remainder)))) qasset qcid with
      | none => (0 : Nat)
      | some (_, c) => ((pool'.preimageOf c).map CommitmentPreimage.value).getD 0) =
    (match holdings qasset qcid with
      | none => 0
      | some (_, c) => ((pool.preimageOf c).map CommitmentPreimage.value).getD 0) := by
  have hvalid_outputs : ∀ cp ∈ (payoutOutputs ++
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)])).map
      (fun pre => (commitment pre.npk asset pre.value, pre)), hashCommitment cp.2 = cp.1 := by
    intro cp hcp
    obtain ⟨pre, hmem, hcpeq⟩ := List.mem_map.mp hcp
    have htok : pre.token = asset := by
      rcases List.mem_append.mp hmem with hc1 | hc2
      · exact htokPayout pre hc1
      · by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc2; exact absurd hc2 (List.not_mem_nil)
        · rw [if_neg hrem] at hc2
          rw [List.mem_singleton] at hc2
          exact hc2 ▸ rfl
    rw [← hcpeq]
    show hashCommitment pre = commitment pre.npk asset pre.value
    rw [← htok]
    rfl
  have hupd : (update holdings asset
      (update (holdings asset) cid
        (if remainder = 0 then none
         else some (pool.leaves.length +
             (payoutOutputs ++ (if remainder = 0 then [] else
               [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length - 1,
           commitment (npk (Term.val self) r) asset remainder)))) qasset qcid = holdings qasset qcid := by
    unfold update
    by_cases ha : qasset = asset
    · subst ha
      rw [if_pos rfl]
      by_cases hcid : qcid = cid
      · exact absurd (by rw [hcid]) hne
      · rw [if_neg hcid]
    · rw [if_neg ha]
  rw [hupd]
  rcases hc0 : holdings asset cid with _ | c0
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _spent', _randomOut, hNonZero, _hCapacity, _hown, htoken, hnewnotes,
      _hroot, _hmark, _hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    have hpre0 : pool'.preimageOf = applyRecords pool.preimageOf
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk asset pre.value, pre))) := by
      rw [← hrecordseq]
      exact congrArg PoolState.preimageOf heq
    rcases hq : holdings qasset qcid with _ | qpair
    · rfl
    · obtain ⟨qpos, qc⟩ := qpair
      obtain ⟨pre_old, hpre_old, _hval_old, hconsist_old⟩ := hinv qasset qcid qpos qc hq
      dsimp only
      rw [hpre0, applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre_old hpre_old
        hconsist_old, hpre_old]
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _, hC, _, _, _, hNonZero, _, _, htoken, hnewnotes, _, _, _, _, _, _, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    have hpre0 : pool'.preimageOf = applyRecords pool.preimageOf
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk asset pre.value, pre))) := by
      rw [← hrecordseq]
      exact congrArg PoolState.preimageOf heq
    rcases hq : holdings qasset qcid with _ | qpair
    · rfl
    · obtain ⟨qpos, qc⟩ := qpair
      obtain ⟨pre_old, hpre_old, _hval_old, hconsist_old⟩ := hinv qasset qcid qpos qc hq
      dsimp only
      rw [hpre0, applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre_old hpre_old
        hconsist_old, hpre_old]

/-- One `PoolOwnedSpendStep`-backed holdings update (the shape `.transfer`
    and `bulkTransferFold` both use) sets the TOUCHED pair's own held
    value to EXACTLY `remainder` — the fresh remainder note this update
    writes reads back at its own face value, the same
    `applyRecords_reads` read-back `PoolOwnedSpendStep_frame`'s own
    `hrelated` case uses. What A-02 needs: `heldValue` after a
    `.transfer` call is exactly the surplus that call's own
    `transferEffects` left behind. -/
theorem PoolOwnedSpendStep_sets_heldValue
    (pool pool' : PoolState) (self asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option (Nat × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])
      pool') :
    (match (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some (pool.leaves.length +
               (payoutOutputs ++ (if remainder = 0 then [] else
                 [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length - 1,
             commitment (npk (Term.val self) r) asset remainder)))) asset cid with
      | none => (0 : Nat)
      | some (_, c) => ((pool'.preimageOf c).map CommitmentPreimage.value).getD 0) = remainder := by
  by_cases hrem : remainder = 0
  · unfold update
    simp [hrem]
  · have hvalid_outputs : ∀ cp ∈ (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)), hashCommitment cp.2 = cp.1 := by
      intro cp hcp
      obtain ⟨pre, hmem, hcpeq⟩ := List.mem_map.mp hcp
      have htok : pre.token = asset := by
        rcases List.mem_append.mp hmem with hc1 | hc2
        · exact htokPayout pre hc1
        · rw [if_neg hrem] at hc2
          rw [List.mem_singleton] at hc2
          exact hc2 ▸ rfl
      rw [← hcpeq]
      show hashCommitment pre = commitment pre.npk asset pre.value
      rw [← htok]
      rfl
    have hnz : ¬ isZeroPreimage (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) :=
      fun hz => hrem hz.2.1
    have hmemout : (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])) := by
      rw [if_neg hrem]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    have hmemout2 : (commitment (npk (Term.val self) r) asset remainder,
        (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) :=
      List.mem_map.mpr ⟨_, hmemout, rfl⟩
    rcases hc0 : holdings asset cid with _ | c0
    · simp only [hc0] at hmatch
      obtain ⟨w, pub, _hM, hC, _spent', _randomOut, hNonZero, _hCapacity, _hown, htoken, hnewnotes,
        _hroot, _hmark, _hRandomOut, heq⟩ := hmatch
      have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
          (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
            CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk asset pre.value, pre)) := by
        have hstep1 := congrArg
          (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
        rw [← hstep1]
        unfold ownedOutputRecords ownedNewNotes
        rw [List.map_ofFn]
        congr 1
        funext j
        congr 1
        exact (hC.outputs j).trans (by rw [htoken])
      have hpre0 : pool'.preimageOf = applyRecords pool.preimageOf
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
            (fun pre => (commitment pre.npk asset pre.value, pre))) := by
        rw [← hrecordseq]
        exact congrArg PoolState.preimageOf heq
      unfold update
      rw [if_pos rfl, if_pos rfl]
      rw [if_neg hrem]
      dsimp only
      rw [hpre0]
      rw [applyRecords_reads hvalid_outputs pool.preimageOf (commitment (npk (Term.val self) r) asset
        remainder) (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) hmemout2 hnz]
      simp
    · simp only [hc0] at hmatch
      obtain ⟨w, pub, _, hC, _, _, _, hNonZero, _, _, htoken, hnewnotes, _, _, _, _, _, _, heq⟩ := hmatch
      have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
          (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
            CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk asset pre.value, pre)) := by
        have hstep1 := congrArg
          (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
        rw [← hstep1]
        unfold ownedOutputRecords ownedNewNotes
        rw [List.map_ofFn]
        congr 1
        funext j
        congr 1
        exact (hC.outputs j).trans (by rw [htoken])
      have hpre0 : pool'.preimageOf = applyRecords pool.preimageOf
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).map
            (fun pre => (commitment pre.npk asset pre.value, pre))) := by
        rw [← hrecordseq]
        exact congrArg PoolState.preimageOf heq
      unfold update
      rw [if_pos rfl, if_pos rfl]
      rw [if_neg hrem]
      dsimp only
      rw [hpre0]
      rw [applyRecords_reads hvalid_outputs pool.preimageOf (commitment (npk (Term.val self) r) asset
        remainder) (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage) hmemout2 hnz]
      simp




/-- A successful `.transfer` sets `heldValue` to EXACTLY the surplus its
    own `transferEffects` left behind — the remainder note
    `PoolOwnedSpendStep_sets_heldValue` already shows reads back at its
    own face value. What A-02 needs to thread `heldValue` across its own
    two `.transfer` calls. -/
theorem transfer_sets_heldValue
    (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (assetIndex : Nat) (cid claimedStateHash : Term)
    (outcome : Outcome) (indices : List Nat)
    (hstep : Step sig appRel actor s (.transfer assetIndex cid claimedStateHash outcome indices) s')
    (h : assetIndex < outcome.length) :
    heldValue s' (outcome.get ⟨assetIndex, h⟩).asset cid =
      heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid -
        (transferEffects (outcome.get ⟨assetIndex, h⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, h⟩).asset cid) indices).2.2 := by
  obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _, _, _, _⟩ := hstep
  obtain ⟨_hexit, hrest⟩ := hinner
  obtain ⟨r, hospend, hholdseq, _hchan⟩ := hrest
  unfold heldValue
  rw [hholdseq]
  exact PoolOwnedSpendStep_sets_heldValue s.pool s'.pool s.self (outcome.get ⟨assetIndex, h⟩).asset cid
    _ r _ s.holdings
    (fun pre hpre => by
      obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
      by_cases hamt : a.amount = 0
      · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
      · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
    hospend

/-- `bulkTransferFold`'s own invariant: if every known holding reads back
    a nonzero, consistent preimage before the fold, the same holds after
    -- one application of `PoolOwnedSpend_update_preimage_nonzero` per
    asset in the fold's own list, carried forward by induction. -/
theorem bulkTransferFold_preimage_nonzero (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) →
    ∀ qasset qcid qpos qc, holdingsF qasset qcid = some (qpos, qc) →
      ∃ pre, poolF.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, hholdEq⟩ := hfold
      rw [hholdEq, hpoolEq]
      exact hinv
    | cons _ _ =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, r, midPool, hmatch, hrec⟩ := hfold
      refine ih newRest midPool poolF _ holdingsF hrec ?_
      exact PoolOwnedSpend_update_preimage_nonzero pool midPool self exit.asset cid _ r _
        holdings
        (fun pre hpre => by
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
        hmatch hinv

/-- `bulkTransferFold`'s own frame fact: every channel OTHER than `cid`
    (the one the whole fold pays out) keeps every asset's own held value
    UNCHANGED — one application of `PoolOwnedSpendStep_frame` per asset
    in the fold's own list, carried forward by induction, paired with
    `PoolOwnedSpend_update_preimage_nonzero` to keep the invariant alive
    across the recursion. What A-13 needs for the two bulk calls. -/
theorem bulkTransferFold_frame (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) →
    ∀ qasset qcid, qcid ≠ cid →
    (match holdingsF qasset qcid with
      | none => (0 : Nat)
      | some (_, c) => ((poolF.preimageOf c).map CommitmentPreimage.value).getD 0) =
    (match holdings qasset qcid with
      | none => 0
      | some (_, c) => ((pool.preimageOf c).map CommitmentPreimage.value).getD 0) := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold _hinv qasset qcid _hne
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, hholdEq⟩ := hfold
      rw [hholdEq, hpoolEq]
    | cons _ _ =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv qasset qcid hne
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, r, midPool, hmatch, hrec⟩ := hfold
      have hframe1 := PoolOwnedSpendStep_frame pool midPool self exit.asset cid _ r _
        holdings
        (fun pre hpre => by
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
        hmatch hinv qasset qcid (fun h => hne (congrArg Prod.snd h))
      have hinvMid := PoolOwnedSpend_update_preimage_nonzero pool midPool self exit.asset cid _ r _
        holdings
        (fun pre hpre => by
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
        hmatch hinv
      have hframe2 := ih newRest midPool poolF _ holdingsF hrec hinvMid qasset qcid hne
      exact hframe2.trans hframe1



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
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
    obtain ⟨_r, _ownerField, _hself, _hown, hcommit, htoken, hposition, hN, hM, hC, rest, spent',
      records, hCapacity, hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
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
    obtain ⟨r, hmatch, hholdseq, _hchanseq⟩ := hrest
    change PoolOwnedSpendStep s.pool s.self (outcome.get ⟨assetIndex, hidx⟩).asset
      (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid)
      ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
        if a.amount = 0 then none
        else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ : CommitmentPreimage)))
      (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
          (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
            (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
       then []
       else [(⟨npk (Term.val s.self) r, (outcome.get ⟨assetIndex, hidx⟩).asset,
         heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
           (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
             (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ : CommitmentPreimage)])
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
                else [(⟨npk (Term.val s.self) r, (outcome.get ⟨assetIndex, hidx⟩).asset,
                  heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                    (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ :
                    CommitmentPreimage)])).length - 1,
           commitment (npk (Term.val s.self) r) (outcome.get ⟨assetIndex, hidx⟩).asset
             (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
               (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2)))) at hholdseq
    generalize hAO : outcome.get ⟨assetIndex, hidx⟩ = assetOutcome at hmatch hholdseq
    generalize hPayoutDef : (transferEffects assetOutcome.allocations
        (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
          if a.amount = 0 then none
          else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) =
      payoutOutputs at hmatch hholdseq
    generalize hRemDef : heldValue s assetOutcome.asset cid -
      (transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.2 =
      remainder at hmatch hholdseq
    rw [hholdseq]
    exact PoolOwnedSpend_update_preimage_nonzero s.pool s'.pool s.self assetOutcome.asset cid
      remainder r payoutOutputs s.holdings
      (fun pre hpre => by
        rw [← hPayoutDef] at hpre
        obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
        by_cases hamt : a.amount = 0
        · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
        · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
      hmatch hinv
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _hsa, _hidx1, _h5, _h6, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, hpre, hval, hconsist⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, hpoolEq ▸ hpre, hval, hconsist⟩
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_preimage_nonzero s.self channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold hinv
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_preimage_nonzero s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold hinv
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

/-- Converse of `withPositionsFrom_mem_snd`: anything already IN the
    underlying list gets SOME position once tagged — what the
    `unbeatable_pays`/`unbeatable_pays_after_timeout` invariant needs to
    turn "this output is one of `.transfer`'s own `payoutOutputs`" into
    an ACTUAL `(pos, pre) ∈ s'.pool.live token` fact. -/
theorem withPositionsFrom_mem_fwd {α : Type} {start : Nat} {l : List α} {a : α}
    (h : a ∈ l) : ∃ pos, (pos, a) ∈ withPositionsFrom start l := by
  induction l generalizing start with
  | nil => exact absurd h (by simp)
  | cons b rest ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · exact ⟨start, by rw [heq]; exact List.mem_cons_self ..⟩
    · obtain ⟨pos, hpos⟩ := ih hmem (start := start + 1)
      exact ⟨pos, List.mem_cons_of_mem _ hpos⟩


/-- One `PoolOwnedSpendStep`-backed holdings update's effect on the
    `holdings_position_live_step` invariant — the position-live sibling
    of `PoolOwnedSpend_update_preimage_nonzero`, generalizing `.transfer`'s
    own reasoning so `bulkTransferFold`'s induction can reuse it once per
    asset instead of re-deriving it. -/
theorem PoolOwnedSpend_update_position_live
    (pool pool' : PoolState) (self asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option (Nat × Term))
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
          ∃ r, pre.npk = npk (Term.val self) r)) ∧
      qpos < pool.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some (pool.leaves.length + (payoutOutputs ++ (if remainder = 0 then [] else
             [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length - 1,
             commitment (npk (Term.val self) r) asset remainder)))) qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool'.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
          ∃ r, pre.npk = npk (Term.val self) r)) ∧
      qpos < pool'.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', (update holdings asset
          (update (holdings asset) cid
            (if remainder = 0 then none
             else some (pool.leaves.length + (payoutOutputs ++ (if remainder = 0 then [] else
               [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])).length - 1,
               commitment (npk (Term.val self) r) asset remainder)))) qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  intro qasset qcid qpos qc hc
  unfold update at hc
  unfold PoolOwnedSpendStep at hmatch
  generalize hOutDef : (payoutOutputs ++ (if remainder = 0 then [] else
      [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])) = outputs at hmatch hc ⊢
  rcases hh : holdings asset cid with _ | ⟨oldPos, oldC⟩
  · rw [hh] at hmatch
    obtain ⟨w, pub, hM, hC, spent', randomOut, hNonZero, hCapacity, hself0, htoken, houtpre,
      hroot, hmarkspent, hrandomOut, heq⟩ := hmatch
    by_cases ha : qasset = asset
    · rw [if_pos ha] at hc
      rw [ha]
      by_cases hcid : qcid = cid
      · rw [if_pos hcid] at hc
        rw [hcid]
        by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc; exact absurd hc (by simp)
        · rw [if_neg hrem] at hc
          have hqc : (pool.leaves.length + outputs.length - 1,
              commitment (npk (Term.val self) r) asset remainder) = (qpos, qc) :=
            Option.some.inj hc
          have hpeq : pool.leaves.length + outputs.length - 1 = qpos := (Prod.ext_iff.mp hqc).1
          have hceq : commitment (npk (Term.val self) r) asset remainder = qc :=
            (Prod.ext_iff.mp hqc).2
          have hsplit : outputs = payoutOutputs ++
              [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)] := by
            rw [← hOutDef, if_neg hrem]
          have hlen : outputs.length = payoutOutputs.length + 1 := by
            rw [hsplit, List.length_append, List.length_singleton]
          refine ⟨⟨⟨npk (Term.val self) r, asset, remainder⟩, ?_, ?_, Or.inr ⟨r, rfl⟩⟩, ?_, ?_⟩
          · rw [heq]
            show (qpos, (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)) ∈
                (if asset = asset then
                    withPositionsFrom pool.leaves.length outputs ++ pool.live asset
                  else pool.live asset)
            have hposeq : pool.leaves.length + outputs.length - 1 =
                pool.leaves.length + payoutOutputs.length := by omega
            rw [if_pos rfl, ← hpeq, hposeq, hsplit, withPositionsFrom_append]
            apply List.mem_append.mpr
            left
            apply List.mem_append.mpr
            right
            simp [withPositionsFrom]
          · exact hceq
          · rw [heq]
            show qpos < (pool.leaves ++ outputs.map hashCommitment).length
            rw [List.length_append, List.length_map]
            omega
          · intro qasset' qcid' qpos' qc' hc'
            unfold update at hc'
            intro hne
            by_cases ha' : qasset' = asset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = cid
              · exact absurd (show (qasset', qcid') = (asset, cid) by
                  rw [ha', hcid']) hne
              · rw [if_neg hcid'] at hc'
                obtain ⟨_, hbound_old2, _⟩ := hinv asset qcid' qpos' qc' hc'
                omega
            · rw [if_neg ha'] at hc'
              obtain ⟨_, hbound_old2, _⟩ := hinv qasset' qcid' qpos' qc' hc'
              omega
      · rw [if_neg hcid] at hc
        have hc2 : holdings qasset qcid = some (qpos, qc) := ha ▸ hc
        obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
          hinv qasset qcid qpos qc hc2
        refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
        · rw [heq]
          show (qpos, pre_old) ∈
              (if asset = asset then
                  withPositionsFrom pool.leaves.length outputs ++ pool.live asset
                else pool.live asset)
          rw [if_pos rfl]
          exact List.mem_append.mpr (Or.inr (ha ▸ hpre_old))
        · rw [heq]
          show qpos < (pool.leaves ++ outputs.map hashCommitment).length
          rw [List.length_append]
          omega
        · intro qasset' qcid' qpos' qc' hc'
          unfold update at hc'
          intro hne
          by_cases ha' : qasset' = asset
          · rw [if_pos ha'] at hc'
            by_cases hcid' : qcid' = cid
            · rw [if_pos hcid'] at hc'
              by_cases hrem : remainder = 0
              · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
              · rw [if_neg hrem] at hc'
                have hqc' : (pool.leaves.length + outputs.length - 1,
                    commitment (npk (Term.val self) r) asset remainder) = (qpos', qc') :=
                  Option.some.inj hc'
                have hpeq' : pool.leaves.length + outputs.length - 1 = qpos' :=
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
    · have hc2 : holdings qasset qcid = some (qpos, qc) := by
        rw [if_neg ha] at hc; exact hc
      obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
        hinv qasset qcid qpos qc hc2
      refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
      · rw [heq]
        show (qpos, pre_old) ∈
            (if qasset = asset then
                withPositionsFrom pool.leaves.length outputs ++ pool.live qasset
              else pool.live qasset)
        rw [if_neg ha]
        exact hpre_old
      · rw [heq]
        show qpos < (pool.leaves ++ outputs.map hashCommitment).length
        rw [List.length_append]
        omega
      · intro qasset' qcid' qpos' qc' hc'
        unfold update at hc'
        intro hne
        by_cases ha' : qasset' = asset
        · rw [if_pos ha'] at hc'
          by_cases hcid' : qcid' = cid
          · rw [if_pos hcid'] at hc'
            by_cases hrem : remainder = 0
            · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
            · rw [if_neg hrem] at hc'
              have hqc' : (pool.leaves.length + outputs.length - 1,
                  commitment (npk (Term.val self) r) asset remainder) = (qpos', qc') :=
                Option.some.inj hc'
              have hpeq' : pool.leaves.length + outputs.length - 1 = qpos' :=
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
      hinv asset cid oldPos oldC hh
    have hsurvivesSpend : ∀ (pos : Nat) (pre : CommitmentPreimage),
        pos ≠ oldPos →
        (pos, pre) ∈ pool.live asset → (pos, pre) ∈ pool'.live asset := by
      intro pos pre hnepos hmem
      rw [heq]
      show (pos, pre) ∈
          (if asset = asset then
              withPositionsFrom pool.leaves.length outputs ++ rest
            else pool.live asset)
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
    by_cases ha : qasset = asset
    · rw [if_pos ha] at hc
      rw [ha]
      by_cases hcid : qcid = cid
      · rw [if_pos hcid] at hc
        rw [hcid]
        by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc; exact absurd hc (by simp)
        · rw [if_neg hrem] at hc
          have hqc : (pool.leaves.length + outputs.length - 1,
              commitment (npk (Term.val self) r) asset remainder) = (qpos, qc) :=
            Option.some.inj hc
          have hpeq : pool.leaves.length + outputs.length - 1 = qpos := (Prod.ext_iff.mp hqc).1
          have hceq : commitment (npk (Term.val self) r) asset remainder = qc :=
            (Prod.ext_iff.mp hqc).2
          have hsplit : outputs = payoutOutputs ++
              [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)] := by
            rw [← hOutDef, if_neg hrem]
          have hlen : outputs.length = payoutOutputs.length + 1 := by
            rw [hsplit, List.length_append, List.length_singleton]
          refine ⟨⟨⟨npk (Term.val self) r, asset, remainder⟩, ?_, ?_, Or.inr ⟨r, rfl⟩⟩, ?_, ?_⟩
          · rw [heq]
            show (qpos, (⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)) ∈
                (if asset = asset then
                    withPositionsFrom pool.leaves.length outputs ++ rest
                  else pool.live asset)
            have hposeq : pool.leaves.length + outputs.length - 1 =
                pool.leaves.length + payoutOutputs.length := by omega
            rw [if_pos rfl, ← hpeq, hposeq, hsplit, withPositionsFrom_append]
            apply List.mem_append.mpr
            left
            apply List.mem_append.mpr
            right
            simp [withPositionsFrom]
          · exact hceq
          · rw [heq]
            show qpos < (pool.leaves ++ outputs.map hashCommitment).length
            rw [List.length_append, List.length_map]
            omega
          · intro qasset' qcid' qpos' qc' hc'
            unfold update at hc'
            intro hne
            by_cases ha' : qasset' = asset
            · rw [if_pos ha'] at hc'
              by_cases hcid' : qcid' = cid
              · exact absurd (show (qasset', qcid') = (asset, cid) by
                  rw [ha', hcid']) hne
              · rw [if_neg hcid'] at hc'
                obtain ⟨_, hbound_old2, _⟩ := hinv asset qcid' qpos' qc' hc'
                omega
            · rw [if_neg ha'] at hc'
              obtain ⟨_, hbound_old2, _⟩ := hinv qasset' qcid' qpos' qc' hc'
              omega
      · rw [if_neg hcid] at hc
        have hc2 : holdings qasset qcid = some (qpos, qc) := ha ▸ hc
        obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
          hinv qasset qcid qpos qc hc2
        have hqposneold : qpos ≠ oldPos :=
          hdistOld qasset qcid qpos qc hc2 (fun h => hcid (congrArg Prod.snd h))
        refine ⟨⟨pre_old, hsurvivesSpend qpos pre_old hqposneold (ha ▸ hpre_old), hval_old,
          hown_old⟩, ?_, ?_⟩
        · rw [heq]
          show qpos < (pool.leaves ++ outputs.map hashCommitment).length
          rw [List.length_append]
          omega
        · intro qasset' qcid' qpos' qc' hc'
          unfold update at hc'
          intro hne
          by_cases ha' : qasset' = asset
          · rw [if_pos ha'] at hc'
            by_cases hcid' : qcid' = cid
            · rw [if_pos hcid'] at hc'
              by_cases hrem : remainder = 0
              · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
              · rw [if_neg hrem] at hc'
                have hqc' : (pool.leaves.length + outputs.length - 1,
                    commitment (npk (Term.val self) r) asset remainder) = (qpos', qc') :=
                  Option.some.inj hc'
                have hpeq' : pool.leaves.length + outputs.length - 1 = qpos' :=
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
    · have hc2 : holdings qasset qcid = some (qpos, qc) := by
        rw [if_neg ha] at hc; exact hc
      obtain ⟨⟨pre_old, hpre_old, hval_old, hown_old⟩, hbound_old, hdist_old⟩ :=
        hinv qasset qcid qpos qc hc2
      refine ⟨⟨pre_old, ?_, hval_old, hown_old⟩, ?_, ?_⟩
      · rw [heq]
        show (qpos, pre_old) ∈
            (if qasset = asset then
                withPositionsFrom pool.leaves.length outputs ++ rest
              else pool.live qasset)
        rw [if_neg ha]
        exact hpre_old
      · rw [heq]
        show qpos < (pool.leaves ++ outputs.map hashCommitment).length
        rw [List.length_append]
        omega
      · intro qasset' qcid' qpos' qc' hc'
        unfold update at hc'
        intro hne
        by_cases ha' : qasset' = asset
        · rw [if_pos ha'] at hc'
          by_cases hcid' : qcid' = cid
          · rw [if_pos hcid'] at hc'
            by_cases hrem : remainder = 0
            · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
            · rw [if_neg hrem] at hc'
              have hqc' : (pool.leaves.length + outputs.length - 1,
                  commitment (npk (Term.val self) r) asset remainder) = (qpos', qc') :=
                Option.some.inj hc'
              have hpeq' : pool.leaves.length + outputs.length - 1 = qpos' :=
                (Prod.ext_iff.mp hqc').1
              have houtlen1 : outputs.length ≥ 1 := by
                rw [← hOutDef, if_neg hrem, List.length_append, List.length_singleton]
                omega
              omega
          · rw [if_neg hcid'] at hc'
            exact hdist_old qasset' qcid' qpos' qc' (ha' ▸ hc') hne
        · rw [if_neg ha'] at hc'
          exact hdist_old qasset' qcid' qpos' qc' hc' hne

/-- `bulkTransferFold`'s own invariant for `holdings_position_live_step` —
    the position-live sibling of `bulkTransferFold_preimage_nonzero`: one
    application of `PoolOwnedSpend_update_position_live` per asset in the
    fold's own list, carried forward by induction. -/
theorem bulkTransferFold_position_live (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
          ∃ r, pre.npk = npk (Term.val self) r)) ∧
      qpos < pool.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) →
    ∀ qasset qcid qpos qc, holdingsF qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ poolF.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
          ∃ r, pre.npk = npk (Term.val self) r)) ∧
      qpos < poolF.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', holdingsF qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, hholdEq⟩ := hfold
      rw [hholdEq, hpoolEq]
      exact hinv
    | cons _ _ =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, r, midPool, hmatch, hrec⟩ := hfold
      refine ih newRest midPool poolF _ holdingsF hrec ?_
      exact PoolOwnedSpend_update_position_live pool midPool self exit.asset cid _ r _
        holdings hmatch hinv

/-- One `PoolOwnedSpendStep`'s effect on `PoolState.notedValue`: spending
    one channel's holding and paying it out never changes the pool's own
    per-token noted total — generalizes `notedValue_conserved`'s own
    `.transfer`/`.deposit` reasoning (`Safety.lean`) so `bulkTransferFold`'s
    induction can reuse it once per asset instead of re-deriving it. -/
theorem PoolOwnedSpendStep_notedValue_conserved
    (pool pool' : PoolState) (self asset : Nat) (nullified : Option (Nat × Term))
    (payoutOutputs ownedPreimages : List CommitmentPreimage)
    (hmatch : PoolOwnedSpendStep pool self asset nullified payoutOutputs ownedPreimages pool') :
    ∀ token, pool'.notedValue token = pool.notedValue token := by
  intro token
  unfold PoolState.notedValue
  by_cases ht : token = asset
  · rcases nullified with _ | ⟨pos, c⟩
    · obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
        hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hmatch
      have hbal := transactOwned_balance (Nat.zero_le 8) hM hC
      have hspent0 : listSum ((ownedSpentPositions pub w).map (fun p => p.2.value)) = 0 := by
        have hnil : ownedSpentPositions pub w = [] := by
          apply List.eq_nil_of_length_eq_zero
          unfold ownedSpentPositions
          simp
        rw [hnil]; rfl
      rw [hspent0] at hbal
      rw [heq]
      dsimp only
      rw [← hnewnotes]
      rw [if_pos ht, ht]
      simp only [List.map_append, listSum_append, withPositionsFrom_map]
      omega
    · obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
        hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hmatch
      have hbal := transactOwned_balance (by decide) hM hC
      have hsum := removeAll_sum (fun p => p.2.value) hremove
      rw [heq]
      dsimp only
      rw [← hnewnotes]
      rw [if_pos ht, ht]
      simp only [List.map_append, listSum_append, withPositionsFrom_map] at hsum ⊢
      omega
  · rcases nullified with _ | ⟨pos, c⟩
    · obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
        hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hmatch
      rw [heq]
      show listSum ((if token = asset then _
          else pool.live token).map (fun p => p.2.value)) =
        listSum ((pool.live token).map (fun p => p.2.value))
      rw [if_neg ht]
    · obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
        hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hmatch
      rw [heq]
      show listSum ((if token = asset then _
          else pool.live token).map (fun p => p.2.value)) =
        listSum ((pool.live token).map (fun p => p.2.value))
      rw [if_neg ht]

/-- A `PoolOwnedSpendStep` never touches a USER-keyed note: its own
    nullification (the "some" case) only ever claims a position keyed
    `npk (Term.val pub.ownerField) _` (`ownedSpentPositions`'s own
    definition, `Pool.lean`), and `self = addressOf pub.ownerField`
    ties that to the CONTRACT's own identity — `user_npk_ne_contract_
    npk` (`TransactOwned.lean`) then rules out a user-keyed preimage
    ever matching. The "none" case nullifies nothing at all. What
    `unbeatable_pays`/`unbeatable_pays_after_timeout` need: `.transfer`/
    the bulk calls (both built on this one step) can never spend `h`'s
    own payout note, so once minted it survives every later one. -/
theorem PoolOwnedSpendStep_preserves_user_note {pool pool' : PoolState} (self token : Nat)
    (nullified : Option (Nat × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage)
    (hstep : PoolOwnedSpendStep pool self token nullified payoutPreimages ownedPreimages pool')
    (t pos : Nat) (pre : CommitmentPreimage) (pk : Nat × Nat) (nk r : Nat)
    (hnpk : pre.npk = npk (masterPublicKey pk nk) r)
    (hmem : (pos, pre) ∈ pool.live t) :
    (pos, pre) ∈ pool'.live t := by
  unfold PoolOwnedSpendStep at hstep
  rcases nullified with _ | ⟨npos, c⟩
  · obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
      hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hstep
    rw [heq]
    dsimp only
    by_cases ht : t = token
    · rw [ht, if_pos rfl]
      show (pos, pre) ∈ withPositionsFrom pool.leaves.length (payoutPreimages ++ ownedPreimages) ++
        pool.live token
      exact List.mem_append.mpr (Or.inr (ht ▸ hmem))
    · show (pos, pre) ∈ (if t = token then _ else pool.live t)
      rw [if_neg ht]; exact hmem
  · obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
      hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hstep
    rw [heq]
    dsimp only
    by_cases ht : t = token
    · rw [ht, if_pos rfl]
      show (pos, pre) ∈ withPositionsFrom pool.leaves.length (payoutPreimages ++ ownedPreimages) ++ rest
      apply List.mem_append.mpr
      right
      have hmemperm : (pos, pre) ∈ ownedSpentPositions pub w ++ rest :=
        (removeAll_perm hremove).mem_iff.mp (ht ▸ hmem)
      refine (List.mem_append.mp hmemperm).resolve_left ?_
      intro hsp
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hsp
      have hpreeq : pre = (⟨npk (Term.val pub.ownerField) (w.randomIn j), w.token,
          w.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
      rw [hpreeq] at hnpk
      exact user_npk_ne_contract_npk hnpk.symm
    · show (pos, pre) ∈ (if t = token then _ else pool.live t)
      rw [if_neg ht]; exact hmem


/-- A `PoolOwnedSpendStep` touches `.live` ONLY at its own `token`: ANY
    note already live at a DIFFERENT token stays live, regardless of
    who owns it. The token-disjoint sibling of
    `PoolOwnedSpendStep_preserves_user_note` (that one additionally
    handles `t = token` for a user-keyed note specifically); this one
    needs no ownership fact at all. What `bulkTransferFold_index_
    payout` (`unbeatable_pays`/`unbeatable_pays_after_timeout`) needs
    to carry a just-minted note at ONE asset's own token through every
    LATER asset's own spend in the same bulk call. -/
theorem PoolOwnedSpendStep_live_frame {pool pool' : PoolState} (self token : Nat)
    (nullified : Option (Nat × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage)
    (hstep : PoolOwnedSpendStep pool self token nullified payoutPreimages ownedPreimages pool')
    (t pos : Nat) (pre : CommitmentPreimage) (ht : t ≠ token)
    (hmem : (pos, pre) ∈ pool.live t) :
    (pos, pre) ∈ pool'.live t := by
  unfold PoolOwnedSpendStep at hstep
  rcases nullified with _ | ⟨npos, c⟩
  · obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
      hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hstep
    rw [heq]
    dsimp only
    show (pos, pre) ∈ (if t = token then _ else pool.live t)
    rw [if_neg ht]; exact hmem
  · obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hCapacity, _hself2, _htoken,
      hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hstep
    rw [heq]
    dsimp only
    show (pos, pre) ∈ (if t = token then _ else pool.live t)
    rw [if_neg ht]; exact hmem

/-- `bulkTransferFold`'s own invariant for `PoolOwnedSpendStep_preserves_
    user_note`: one application per asset in the fold's own list,
    carried forward by induction — the user-note-liveness sibling of
    `bulkTransferFold_position_live`. -/
theorem bulkTransferFold_preserves_user_note (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    ∀ t pos pre pk nk r, pre.npk = npk (masterPublicKey pk nk) r →
      (pos, pre) ∈ pool.live t → (pos, pre) ∈ poolF.live t := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold t pos pre pk nk r hnpk hmem
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, _hholdEq⟩ := hfold
      rw [hpoolEq]; exact hmem
    | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold t pos pre pk nk r hnpk hmem
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, rr, midPool, hmatch, hrec⟩ := hfold
      refine ih newRest midPool poolF _ _ hrec t pos pre pk nk r hnpk ?_
      exact PoolOwnedSpendStep_preserves_user_note self exit.asset _ _ _ hmatch t pos pre pk nk r
        hnpk hmem

/-- `bulkTransferFold`'s own invariant for `PoolOwnedSpendStep_live_
    frame`: one application per asset in the fold's own list, carried
    forward by induction — the token-disjoint sibling of
    `bulkTransferFold_preserves_user_note` (that one needs the note to
    be user-keyed; this one needs its OWN token absent from the rest
    of the fold's own asset list, no ownership fact at all). What
    `bulkTransferFold_index_payout` needs to carry a just-minted note
    at ONE asset's own token through every LATER asset's own spend. -/
theorem bulkTransferFold_live_frame (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    ∀ t pos pre, t ∉ outcome.map SingleAssetExit.asset →
      (pos, pre) ∈ pool.live t → (pos, pre) ∈ poolF.live t := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold t pos pre _ht hmem
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, _hholdEq⟩ := hfold
      rw [hpoolEq]; exact hmem
    | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold t pos pre ht hmem
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, rr, midPool, hmatch, hrec⟩ := hfold
      have htne : t ≠ exit.asset := by
        intro heq; exact ht (heq ▸ List.mem_cons_self ..)
      have htrest : t ∉ rest.map SingleAssetExit.asset := by
        intro hc; exact ht (List.mem_cons_of_mem _ hc)
      refine ih newRest midPool poolF _ _ hrec t pos pre htrest ?_
      exact PoolOwnedSpendStep_live_frame self exit.asset _ _ _ hmatch t pos pre htne hmem



/-- `bulkTransferFold`'s own invariant for `notedValue_conserved`: one
    application of `PoolOwnedSpendStep_notedValue_conserved` per asset in
    the fold's own list, carried forward by induction. -/
theorem bulkTransferFold_notedValue_conserved (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    ∀ token, poolF.notedValue token = pool.notedValue token := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold token
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, _⟩ := hfold
      rw [hpoolEq]
    | cons _ _ =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold token
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, _r, midPool, hmatch, hrec⟩ := hfold
      rw [ih newRest midPool poolF _ holdingsF hrec token]
      exact PoolOwnedSpendStep_notedValue_conserved pool midPool self exit.asset _ _ _ hmatch token

/-- A user-keyed note survives ANY `Step` taken by an actor OTHER than
    its own key's pool identity, PROVIDED that key had not already
    signed a spend of it: `.transfer`/the bulk calls can never touch it
    at all (`PoolOwnedSpendStep_preserves_user_note`/`bulkTransferFold_
    preserves_user_note` — contract-owned spends only); every OTHER
    call but `.deposit` does not touch `.pool`; `.deposit` needs the
    full argument — `deposit_spend_requires_signer` when the witness
    signs under a DIFFERENT key, `hhonestPool` (relative to the anchor
    `s0`, carried forward unchanged by `hsrow0`) when it signs under
    THIS key, since the model fix (`Operations.lean`'s `.deposit` case)
    requires `s.poolSignedBy w.publicKey (msgHashOf pub)` to hold, and
    that row is exactly `s0`'s own (`poolSignedBy_frame`, applied
    through `hsrow0` by the caller) — `hhonestPool` then rules out every
    message it could cover ever nullifying this note. What
    `unbeatable_pays`/`unbeatable_pays_after_timeout` need: once `h`'s
    own payout note is minted, no later step in `interleaved` removes
    it. -/
theorem note_survives_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (pk : Nat × Nat) (nk r : Nat) (s0 : AdjudicatorState)
    (hhonestPool : ∀ m, s0.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ npk (masterPublicKey pk nk) r)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hstep : Step sig appRel actor s call s') (hactor : actor ≠ Actor.pool pk)
    (hsrow0 : s.poolSignedBy pk = s0.poolSignedBy pk)
    (t pos : Nat) (pre : CommitmentPreimage) (hnpk : pre.npk = npk (masterPublicKey pk nk) r)
    (hmem : (pos, pre) ∈ s.pool.live t) :
    (pos, pre) ∈ s'.pool.live t := by
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_, _, _, _, hinner, _, _, _, _, hsb⟩ := hstep
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, hpoolsigned, hmatch⟩ := hinner
    obtain ⟨_r, _ownerField, _hself, _hown, hcommit, htoken, hposition, hN, hM, hC, rest, spent',
      records, hCapacity, hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hmid : (pos, pre) ∈ midPool.live t := by
      rw [heq]
      by_cases ht : t = w.token
      · subst ht
        have hmemw : (pos, pre) ∈ s.pool.live w.token := hmem
        have hnotmem : (pos, pre) ∉ transactSpentPositions w := by
          intro hsp
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hsp
          have hpreeq : pre = (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j),
              w.token, w.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
          have hclaimnpk : (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j),
              w.token, w.valueIn j⟩ : CommitmentPreimage).npk = npk (masterPublicKey pk nk) r :=
            (congrArg CommitmentPreimage.npk hpreeq).symm.trans hnpk
          by_cases hwpk : w.publicKey = pk
          · have step1 : s.poolSignedBy pk (msgHashOf pub) := hwpk ▸ hpoolsigned
            have hsigned0' : s0.poolSignedBy pk (msgHashOf pub) := hsrow0 ▸ step1
            exact hhonestPool (msgHashOf pub) hsigned0' w pub rfl hC hwpk j hclaimnpk
          · have hnpkeq2 : npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j) =
                npk (masterPublicKey pk nk) r := hclaimnpk
            have hmpkeq : masterPublicKey w.publicKey w.nullifyingKey = masterPublicKey pk nk :=
              (Term.hash2_inj hnpkeq2).1
            obtain ⟨h1, h2, _⟩ := Term.hash3_inj hmpkeq
            exact hwpk (Prod.ext (Term.val.inj h1) (Term.val.inj h2))
        have hmemperm : (pos, pre) ∈ transactSpentPositions w ++ rest :=
          (removeAll_perm hRemove).mem_iff.mp (htoken ▸ hmemw)
        have hinrest := (List.mem_append.mp hmemperm).resolve_left hnotmem
        show (pos, pre) ∈ (if w.token = w.token then
            withPositionsFrom s.pool.leaves.length (transactAllOutputs w) ++ rest else s.pool.live w.token)
        rw [if_pos rfl]
        exact List.mem_append.mpr (Or.inr hinrest)
      · show (pos, pre) ∈ (if t = w.token then _ else s.pool.live t)
        rw [if_neg ht]
        exact hmem
    match s.holdings asset cid, hmatch with
    | none, ⟨hspool, _⟩ => rw [hspool]; exact hmid
    | some (oldPos, oldHolding), ⟨merged, mergedPos, hmerge, _hholdseq⟩ =>
      obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r'', randomOut', hNonZero', hCapacity',
        hself', htoken', hnpkOut', hmergedEq, hleaf0', hleaf1', hcommitOld, hcommitNew, hRoot',
        hRemove', hNullify', hRandomOut', heq'⟩ := hmerge
      have hnotmem' : (pos, pre) ∉ ownedSpentPositions pub' w' := by
        intro hsp
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hsp
        have hpreeq' : pre = (⟨npk (Term.val pub'.ownerField) (w'.randomIn j), w'.token,
            w'.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
        rw [hpreeq'] at hnpk
        exact user_npk_ne_contract_npk hnpk.symm
      rw [heq']
      by_cases ht' : t = asset
      · rw [ht']
        show (pos, pre) ∈ (if asset = asset then
            withPositionsFrom midPool.leaves.length (ownedNewNotes w') ++ rest' else midPool.live asset)
        rw [if_pos rfl]
        apply List.mem_append.mpr
        right
        have hmidasset : (pos, pre) ∈ midPool.live asset := ht' ▸ hmid
        have hmemperm' : (pos, pre) ∈ ownedSpentPositions pub' w' ++ rest' :=
          (removeAll_perm hRemove').mem_iff.mp (htoken'.symm ▸ hmidasset)
        exact (List.mem_append.mp hmemperm').resolve_left hnotmem'
      · show (pos, pre) ∈ (if t = asset then _ else midPool.live t)
        rw [if_neg ht']
        exact hmid
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, hchan, hspool, _, _, _, _, _⟩ := hstep
    rw [hspool]; exact hmem
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, hchan, hspool, _, _, _, _, _⟩ := hstep
    rw [hspool]; exact hmem
  | conclude fp candidate =>
    obtain ⟨_, _, _, hchan, hspool, _, _, _, _, _⟩ := hstep
    rw [hspool]; exact hmem
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _, _, _, _, hinner, _, _, _, _⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨r', hospend, _hholdseq, _hchan⟩ := hrest
    exact PoolOwnedSpendStep_preserves_user_note s.self (outcome.get ⟨assetIndex, hidx⟩).asset
      _ _ _ hospend t pos pre pk nk r hnpk hmem
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, hspool, _, _, _, _, _⟩ := hstep
    rw [hspool]; exact hmem
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, newOutcome, hfold, _, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_preserves_user_note s.self cid outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold t pos pre pk nk r hnpk hmem
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, newOutcome, hfold, _, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_preserves_user_note s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold t pos pre pk nk r hnpk hmem
  | tick newNow =>
    obtain ⟨_, _, hspool, _, _, _, _, _⟩ := hstep
    rw [hspool]; exact hmem
  | sign p d =>
    obtain ⟨_, hsb⟩ := hstep
    obtain ⟨_, hspool, _⟩ := hsb
    rw [hspool]; exact hmem
  | signNote pk' msgHash =>
    obtain ⟨_, _, hspool, _, _, _, _, _, _⟩ := hstep
    rw [hspool]; exact hmem

/-- `note_survives_step` across a whole `interleaved` sequence: if no
    step in it ever acts as `.pool pk`, `h`'s own payout note — once
    live at the start — stays live throughout, using `poolSignedBy_
    frame` to keep `hsrow0` true at every intermediate state. -/
theorem appliesAll_note_survives (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (pk : Nat × Nat) (nk r : Nat) (s0 : AdjudicatorState)
    (hhonestPool : ∀ m, s0.poolSignedBy pk m →
      ∀ {N M : Nat} (w : TransactWitness N M) (pub : TransactPublic N M),
      msgHashOf pub = m → Constrained w pub → w.publicKey = pk →
      ∀ i : Fin N, (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn i),
        w.token, w.valueIn i⟩ : CommitmentPreimage).npk ≠ npk (masterPublicKey pk nk) r)
    (t pos : Nat) (pre : CommitmentPreimage) (hnpk : pre.npk = npk (masterPublicKey pk nk) r) :
    ∀ {calls : List (Actor × Call)} {s s' : AdjudicatorState},
      AppliesAll sig appRel s calls s' →
      (∀ actor call, (actor, call) ∈ calls → actor ≠ Actor.pool pk) →
      s.poolSignedBy pk = s0.poolSignedBy pk →
      (pos, pre) ∈ s.pool.live t → (pos, pre) ∈ s'.pool.live t
  | [], s, s', happ, _, _, hmem => by rw [show s' = s from happ]; exact hmem
  | (actor, call) :: rest, s, s', happ, hexcl, hsrow0, hmem => by
    obtain ⟨mid, hstep, hrest⟩ := happ
    have hactor : actor ≠ Actor.pool pk := hexcl actor call (List.mem_cons_self ..)
    have hmem_mid := note_survives_step sig appRel pk nk r s0 hhonestPool actor s mid call hstep
      hactor hsrow0 t pos pre hnpk hmem
    have hsrow0_mid : mid.poolSignedBy pk = s0.poolSignedBy pk :=
      (poolSignedBy_frame sig appRel actor s mid call hstep pk hactor).trans hsrow0
    exact appliesAll_note_survives sig appRel pk nk r s0 hhonestPool t pos pre hnpk hrest
      (fun actor' call' hc => hexcl actor' call' (List.mem_cons_of_mem _ hc)) hsrow0_mid hmem_mid



/-- `bulkTransferFold`'s own effect on an outcome is `OutcomeDerivedFrom`
    its starting outcome: each asset's own `transferEffects`-rewrite,
    chained down the list via `OutcomeDerivedFrom_cons` (`Outcome.lean`)
    for the entries not yet reached, then one more `.transferStep` at
    the list's own head index. What `finalized_outcome_was_concluded_or_challenged`
    needs for the bulk-call cases, mirroring `.transfer`'s own single-asset
    `OutcomeDerivedFrom.transferStep` use. -/
theorem bulkTransferFold_outcomeDerivedFrom (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    OutcomeDerivedFrom outcome newOutcome := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold
    cases newOutcome with
    | nil => exact OutcomeDerivedFrom.refl []
    | cons _ _ =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, hnewExit, _r, midPool, hmatch, hrec⟩ := hfold
      have hrestDerived := ih newRest midPool poolF _ holdingsF hrec
      have hconsDerived := OutcomeDerivedFrom_cons exit hrestDerived
      rw [hnewExit]
      have hid : newRest.mapIdx (fun (i : Nat) (e : SingleAssetExit) => e) = newRest := by
        rw [List.mapIdx_eq_iff]
        intro i
        simp
      have hstep := OutcomeDerivedFrom.transferStep (o := exit :: rest) 0 (by simp)
        (match holdings exit.asset cid with
          | none => 0
          | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0)
        [] hconsDerived
      rw [List.mapIdx_cons] at hstep
      simp only [List.get_cons_zero, ne_eq, not_true_eq_false, if_false,
        Nat.succ_ne_zero, not_false_eq_true, if_true] at hstep
      rwa [hid] at hstep

/-- `bulkTransferFold`'s own per-index payout: at a GIVEN `assetIndex`
    whose own TOKEN appears NOWHERE ELSE in `outcome` (`hunique`,
    `unbeatable_pays`/`unbeatable_pays_after_timeout`'s own
    `hassetunique` restated per-list), the fold's own `newOutcome`
    entry there is exactly `.transfer`'s OWN per-asset rewrite (pay-all,
    `indices := []`), and — once paid — the resulting note is live in
    `poolF`, carried there unharmed by EVERY LATER asset's own spend
    (`bulkTransferFold_live_frame`, since no later entry shares this
    index's own token). The combined fact `unbeatable_pays`/
    `unbeatable_pays_after_timeout` need for a bulk call: `.transfer`'s
    own single-asset reasoning, applied to ONE position in the fold's
    own per-asset list, with everything AFTER it shown not to touch it
    again. -/
theorem bulkTransferFold_index_payout (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) →
    ∀ (assetIndex : Nat) (hidx : assetIndex < outcome.length)
      (hunique : ∀ j (hj : j < outcome.length), j ≠ assetIndex →
        (outcome.get ⟨j, hj⟩).asset ≠ (outcome.get ⟨assetIndex, hidx⟩).asset)
      (hidxN : assetIndex < newOutcome.length),
    newOutcome.get ⟨assetIndex, hidxN⟩ =
      { outcome.get ⟨assetIndex, hidx⟩ with
        allocations := (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (match holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).1 } ∧
    ∀ k : Nat, (afford (outcome.get ⟨assetIndex, hidx⟩).allocations
        (match holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with
          | none => 0
          | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0)).getD k 0 ≠ 0 →
      ∃ pos, (pos, (⟨((outcome.get ⟨assetIndex, hidx⟩).allocations.getD k
          Allocation.default).destination, (outcome.get ⟨assetIndex, hidx⟩).asset,
        (afford (outcome.get ⟨assetIndex, hidx⟩).allocations
          (match holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0)).getD k 0⟩ :
        CommitmentPreimage)) ∈ poolF.live (outcome.get ⟨assetIndex, hidx⟩).asset := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv assetIndex hidx
    exact absurd hidx (by simp)
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv assetIndex hidx hunique hidxN
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨hguarantee, hnewExit, r, midPool, hmatch, hrec⟩ := hfold
      cases assetIndex with
      | zero =>
        refine ⟨hnewExit, ?_⟩
        intro k hk
        let surplus := match holdings exit.asset cid with
          | none => 0
          | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0
        have htokPayout : ∀ pre ∈ (transferEffects exit.allocations surplus []).2.1
            |>.filterMap (fun a => if a.amount = 0 then none else
              some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)),
            pre.token = exit.asset := by
          intro pre hpre
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl
        have hkrange : k < exit.allocations.length := by
          by_cases hkr : k < exit.allocations.length
          · exact hkr
          · exfalso
            have hge : exit.allocations.length ≤ k := Nat.le_of_not_lt hkr
            have hgeA : (afford exit.allocations surplus).length ≤ k := by
              rw [afford_length]; exact hge
            have : (afford exit.allocations surplus).getD k 0 = 0 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hgeA]; rfl
            exact hk this
        have hexitmem : { exit.allocations.getD k Allocation.default with
            amount := (afford exit.allocations surplus).getD k 0 } ∈
            (transferEffects exit.allocations surplus []).2.1 :=
          transferEffectsSel_exit_mem exit.allocations surplus (fun _ => true) k hkrange rfl
        have hpayoutmem : (⟨(exit.allocations.getD k Allocation.default).destination, exit.asset,
            (afford exit.allocations surplus).getD k 0⟩ : CommitmentPreimage) ∈
            ((transferEffects exit.allocations surplus []).2.1.filterMap (fun a =>
              if a.amount = 0 then none else
                some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage))) := by
          apply List.mem_filterMap.mpr
          refine ⟨{ exit.allocations.getD k Allocation.default with
            amount := (afford exit.allocations surplus).getD k 0 }, hexitmem, ?_⟩
          dsimp only
          split
          · next h => exact absurd h hk
          · rfl
        have hlivemem : ∃ pos, (pos, (⟨(exit.allocations.getD k Allocation.default).destination,
            exit.asset, (afford exit.allocations surplus).getD k 0⟩ : CommitmentPreimage)) ∈
            midPool.live exit.asset := by
          rcases hh : holdings exit.asset cid with _ | ⟨pos0, c0⟩
          · rw [hh] at hmatch
            have hsurplusEq : surplus = 0 := by
              show (match holdings exit.asset cid with
                | none => 0
                | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) = 0
              rw [hh]
            rw [hsurplusEq] at hpayoutmem
            rw [hsurplusEq]
            obtain ⟨w, pub, hM, hC, spent', randomOut, hNonZero, hCapacity, hbody⟩ := hmatch
            have heq := hbody.2.2.2.2.2.2
            obtain ⟨pos, hposmem⟩ := withPositionsFrom_mem_fwd (start := pool.leaves.length)
              (List.mem_append_left
                (if (0 : Nat) - (transferEffects exit.allocations 0 []).2.2 = 0 then []
                 else [(⟨npk (Term.val self) r, exit.asset,
                   (0 : Nat) - (transferEffects exit.allocations 0 []).2.2⟩ :
                   CommitmentPreimage)])
                hpayoutmem)
            refine ⟨pos, ?_⟩
            rw [heq]
            show (pos, _) ∈ (if exit.asset = exit.asset then
              withPositionsFrom pool.leaves.length _ ++ pool.live _ else pool.live _)
            rw [if_pos rfl]
            apply List.mem_append_left _ hposmem
          · rw [hh] at hmatch
            have hsurplusEq : surplus = ((pool.preimageOf c0).map CommitmentPreimage.value |>.getD 0) := by
              show (match holdings exit.asset cid with
                | none => 0
                | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) = _
              rw [hh]
            rw [hsurplusEq] at hpayoutmem
            rw [hsurplusEq]
            obtain ⟨w, pub, hM, hC, rest', spent', randomOut, hNonZero, hCapacity, hbody⟩ := hmatch
            have heq := hbody.2.2.2.2.2.2.2.2.2
            obtain ⟨pos, hposmem⟩ := withPositionsFrom_mem_fwd (start := pool.leaves.length)
              (List.mem_append_left
                (if ((pool.preimageOf c0).map CommitmentPreimage.value |>.getD 0) -
                    (transferEffects exit.allocations
                      ((pool.preimageOf c0).map CommitmentPreimage.value |>.getD 0) []).2.2 = 0 then []
                 else [(⟨npk (Term.val self) r, exit.asset,
                   ((pool.preimageOf c0).map CommitmentPreimage.value |>.getD 0) -
                     (transferEffects exit.allocations
                       ((pool.preimageOf c0).map CommitmentPreimage.value |>.getD 0) []).2.2⟩ :
                   CommitmentPreimage)])
                hpayoutmem)
            refine ⟨pos, ?_⟩
            rw [heq]
            show (pos, _) ∈ (if exit.asset = exit.asset then
              withPositionsFrom pool.leaves.length _ ++ rest' else pool.live _)
            rw [if_pos rfl]
            apply List.mem_append_left _ hposmem
        obtain ⟨pos, hlivemem⟩ := hlivemem
        refine ⟨pos, ?_⟩
        have hunique0 : exit.asset ∉ rest.map SingleAssetExit.asset := by
          intro hc
          obtain ⟨j, hjmem, hjeq⟩ := List.mem_map.mp hc
          obtain ⟨j', hj'lt, hj'eq⟩ := List.mem_iff_getElem.mp hjmem
          have hj'lt' : j' + 1 < (exit :: rest).length := by simpa using hj'lt
          have := hunique (j' + 1) hj'lt' (by omega)
          simp only [List.get_cons_succ] at this
          apply this
          rw [show rest.get ⟨j', hj'lt⟩ = j from by
            rw [← hj'eq]; rfl]
          simpa using hjeq
        exact bulkTransferFold_live_frame self cid rest newRest midPool poolF _ holdingsF hrec
          exit.asset pos _ hunique0 hlivemem
      | succ n =>
        have hidx' : n < rest.length := by simpa using hidx
        have hidxN' : n < newRest.length := by simpa using hidxN
        have hunique' : ∀ j (hj : j < rest.length), j ≠ n →
            (rest.get ⟨j, hj⟩).asset ≠ (rest.get ⟨n, hidx'⟩).asset := by
          intro j hj hjn
          have := hunique (j + 1) (by simpa using hj) (by omega)
          simpa using this
        have htokNe : (rest.get ⟨n, hidx'⟩).asset ≠ exit.asset := by
          have hne0 := hunique 0 (by omega) (by omega)
          simp only [List.get_cons_succ, List.get_cons_zero] at hne0
          exact fun hc => hne0 hc.symm
        have htokPayout : ∀ pre ∈ (transferEffects exit.allocations (match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1
            |>.filterMap (fun a => if a.amount = 0 then none else
              some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)),
            pre.token = exit.asset := by
          intro pre hpre
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl
        have hinv' := PoolOwnedSpend_update_preimage_nonzero pool midPool self exit.asset cid
          ((match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) -
            (transferEffects exit.allocations (match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.2) r
          ((transferEffects exit.allocations (match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1.filterMap
            (fun a => if a.amount = 0 then none else
              some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)))
          holdings htokPayout hmatch hinv
        have hframe := PoolOwnedSpendStep_frame pool midPool self exit.asset cid
          ((match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) -
            (transferEffects exit.allocations (match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.2) r
          ((transferEffects exit.allocations (match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1.filterMap
            (fun a => if a.amount = 0 then none else
              some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)))
          holdings htokPayout hmatch hinv (rest.get ⟨n, hidx'⟩).asset cid
          (by simp only [ne_eq, Prod.mk.injEq, not_and]; intro hc; exact absurd hc htokNe)
        obtain ⟨heq1, heq2⟩ := ih newRest midPool poolF _ holdingsF hrec hinv' n hidx' hunique' hidxN'
        have hvalEq := congrArg (afford (rest.get ⟨n, hidx'⟩).allocations) hframe
        refine ⟨?_, ?_⟩
        · show newRest.get ⟨n, hidxN'⟩ = _
          simp only [List.get_cons_succ]
          exact heq1.trans (congrArg (fun v => { rest.get ⟨n, hidx'⟩ with
            allocations := (transferEffects (rest.get ⟨n, hidx'⟩).allocations v []).1 }) hframe)
        · intro k hk
          simp only [List.get_cons_succ] at hk
          obtain ⟨pos, hposmem⟩ := heq2 k (congrArg (fun l => List.getD l k 0) hvalEq ▸ hk)
          simp only [List.get_cons_succ]
          exact ⟨pos, (congrArg (fun l => List.getD l k 0) hvalEq) ▸ hposmem⟩

/-- `bulkTransferFold` pairs `outcome` and `newOutcome` one entry per
    recursive step (its own `cons exit rest, cons newExit newRest` match
    arm; any length mismatch hits its own `False` arm instead) — so the
    two always share a length. What lets `unbeatablePaysInv_step`'s own
    bulk `Call` cases carry `assetIndex`'s own bound from `outcome` to
    `newOutcome`. -/
theorem bulkTransferFold_length (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    newOutcome.length = outcome.length := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold
    cases newOutcome with
    | nil => rfl
    | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, _r, midPool, _hmatch, hrec⟩ := hfold
      simpa using ih newRest midPool poolF _ _ hrec

/-- `bulkTransferFold`'s own holdings touch exactly ONE channel — `cid`,
    threaded unchanged through every asset's own recursive step. A
    DIFFERENT channel's holding of any asset survives the whole fold
    unscathed. What `unbeatablePaysInv_step`'s own bulk `Call` cases need
    to carry B's `heldValue` fact across a bulk call on a DIFFERENT
    channel from the one the invariant names. -/
theorem bulkTransferFold_holdings_frame_cid (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    ∀ qasset qcid, qcid ≠ cid → holdingsF qasset qcid = holdings qasset qcid := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold qasset qcid hne
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hpoolEq, hholdEq⟩ := hfold
      rw [hholdEq]
    | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold qasset qcid hne
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, r, midPool, hmatch, hrec⟩ := hfold
      rw [ih newRest midPool poolF _ holdingsF hrec qasset qcid hne]
      unfold update
      by_cases hqa : qasset = exit.asset
      · subst hqa
        rw [if_pos rfl, if_neg hne]
      · rw [if_neg hqa]

/-- `bulkTransferFold`'s own held value, read at ANY asset and a DIFFERENT
    channel from the one `cid` the whole fold spends, survives the whole
    fold unscathed — both halves: the channel's own holding
    (`bulkTransferFold_holdings_frame_cid`) and the pool's own preimage
    read-back for whatever commitment that holding names
    (`PoolOwnedSpendStep_frame`, lifted by induction). Needs the
    preimage-nonzero invariant threaded through, the same way
    `bulkTransferFold_index_payout`'s own induction does. What
    `unbeatablePaysInv_step`'s own bulk `Call` cases need to carry B's
    `heldValue` fact across a bulk call on a channel OTHER than the one
    the invariant names. -/
theorem bulkTransferFold_heldValue_frame_cid (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) →
    ∀ qasset qcid, qcid ≠ cid →
      (match holdingsF qasset qcid with
        | none => 0
        | some (_, c) => (poolF.preimageOf c).map CommitmentPreimage.value |>.getD 0) =
      (match holdings qasset qcid with
        | none => 0
        | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold _hinv qasset qcid _hne
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, hholdEq⟩ := hfold
      rw [hpoolEq, hholdEq]
    | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv qasset qcid hne
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, r, midPool, hmatch, hrec⟩ := hfold
      have htokPayout : ∀ pre ∈ (transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1
          |>.filterMap (fun a => if a.amount = 0 then none else
            some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)),
          pre.token = exit.asset := by
        intro pre hpre
        obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
        by_cases hamt : a.amount = 0
        · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
        · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl
      have hinv' := PoolOwnedSpend_update_preimage_nonzero pool midPool self exit.asset cid
        ((match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) -
          (transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.2) r
        ((transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1.filterMap
          (fun a => if a.amount = 0 then none else
            some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)))
        holdings htokPayout hmatch hinv
      have hframe := PoolOwnedSpendStep_frame pool midPool self exit.asset cid
        ((match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) -
          (transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.2) r
        ((transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1.filterMap
          (fun a => if a.amount = 0 then none else
            some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)))
        holdings htokPayout hmatch hinv qasset qcid (fun heq => hne (congrArg Prod.snd heq))
      exact (ih newRest midPool poolF _ holdingsF hrec hinv' qasset qcid hne).trans hframe


/-- `PoolOwnedSpendStep`'s own `preimageOf` update, stated without any
    `holdings` indexing (the bare registry fact `PoolOwnedSpend_update_
    preimage_nonzero`'s own internal `hrelated`/`hunrelated` case split
    already establishes, exposed here on its own): an already-known,
    consistent preimage survives the step. What chains a `bulkTransferFold`
    induction's own `ih` call forward across each asset's own spend,
    alongside `PoolOwnedSpendStep_ownedRandom_known`. -/
theorem PoolOwnedSpendStep_preimageOf_known
    (pool pool' : PoolState) (self asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option (Nat × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (qc : Term) (pre : CommitmentPreimage) (hpre : pool.preimageOf qc = some pre)
    (hconsist : hashCommitment pre = qc) :
    pool'.preimageOf qc = some pre := by
  have hvalid_outputs : ∀ cp ∈ (payoutOutputs ++
      (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
        CommitmentPreimage)])).map
      (fun pre => (commitment pre.npk asset pre.value, pre)), hashCommitment cp.2 = cp.1 := by
    intro cp hcp
    obtain ⟨pre0, hmem, hcpeq⟩ := List.mem_map.mp hcp
    have htok : pre0.token = asset := by
      rcases List.mem_append.mp hmem with hc1 | hc2
      · exact htokPayout pre0 hc1
      · by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc2; exact absurd hc2 (List.not_mem_nil)
        · rw [if_neg hrem] at hc2
          rw [List.mem_singleton] at hc2
          exact hc2 ▸ rfl
    rw [← hcpeq]
    show hashCommitment pre0 = commitment pre0.npk asset pre0.value
    rw [← htok]
    rfl
  rcases hc0 : holdings asset cid with _ | c0
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _spent', _randomOut, _hNonZero, _hCapacity, _hown, htoken, hnewnotes,
      _hroot, _hmark, _hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    rw [heq]; dsimp only; rw [hrecordseq]
    exact applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre hpre hconsist
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _rest, _spent', _randomOut, _hNonZero, _hCapacity, _hown, htoken,
      hnewnotes, _hleavesIdx, _hcommit, _hroot, _hremove, _hmark, _hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk (Term.val self) r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      have hstep1 := congrArg
        (List.map (fun pre => (commitment pre.npk asset pre.value, pre))) hnewnotes
      rw [← hstep1]
      unfold ownedOutputRecords ownedNewNotes
      rw [List.map_ofFn]
      congr 1
      funext j
      congr 1
      exact (hC.outputs j).trans (by rw [htoken])
    rw [heq]; dsimp only; rw [hrecordseq]
    exact applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre hpre hconsist


/-- `bulkTransferFold`'s own `ownedRandomOf` update, the `bulkTransferFold`
    lift of `PoolOwnedSpendStep_ownedRandom_known`'s own first half: an
    already-known adjudicator-owned disclosure survives the WHOLE fold,
    one asset's own spend at a time, the same way
    `bulkTransferFold_heldValue_frame_cid` lifts `PoolOwnedSpendStep_
    frame`. What `unbeatable_pays`'s own strategy needs to carry the
    channel's held note's own disclosure across a bulk call elsewhere in
    `interleaved`. -/
theorem bulkTransferFold_ownedRandom_known (self : Nat) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option (Nat × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) →
    ∀ qc pre r, pool.preimageOf qc = some pre → hashCommitment pre = qc →
      pre.npk = npk (Term.val self) r → pool.ownedRandomOf qc = some ⟨self, r⟩ →
      poolF.ownedRandomOf qc = some ⟨self, r⟩ := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold _hinv qc pre r _hpre _hconsist _hnpk hknown
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, _hholdEq⟩ := hfold
      rw [hpoolEq]; exact hknown
    | cons _ _ => unfold bulkTransferFold at hfold; exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv qc pre r hpre hconsist hnpk hknown
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, _hnewExit, r0, midPool, hmatch, hrec⟩ := hfold
      have htokPayout : ∀ pre ∈ (transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1
          |>.filterMap (fun a => if a.amount = 0 then none else
            some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)),
          pre.token = exit.asset := by
        intro pre hpre
        obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
        by_cases hamt : a.amount = 0
        · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
        · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl
      have hinv' := PoolOwnedSpend_update_preimage_nonzero pool midPool self exit.asset cid
        ((match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) -
          (transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.2) r0
        ((transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1.filterMap
          (fun a => if a.amount = 0 then none else
            some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)))
        holdings htokPayout hmatch hinv
      have hOwnedKnown := (PoolOwnedSpendStep_ownedRandom_known pool midPool self exit.asset cid
        ((match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) -
          (transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.2) r0
        ((transferEffects exit.allocations (match holdings exit.asset cid with
            | none => 0
            | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1.filterMap
          (fun a => if a.amount = 0 then none else
            some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)))
        holdings htokPayout hmatch).1 qc pre r hpre hconsist hnpk hknown
      have hpre_mid : midPool.preimageOf qc = some pre :=
        PoolOwnedSpendStep_preimageOf_known pool midPool self exit.asset cid
          ((match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) -
            (transferEffects exit.allocations (match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.2) r0
          ((transferEffects exit.allocations (match holdings exit.asset cid with
              | none => 0
              | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0) []).2.1.filterMap
            (fun a => if a.amount = 0 then none else
              some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)))
          holdings htokPayout hmatch qc pre hpre hconsist
      exact ih newRest midPool poolF _ holdingsF hrec hinv' qc pre r hpre_mid hconsist hnpk hOwnedKnown





/-- The reachability-level lift of `PoolOwnedSpendStep_ownedRandom_known`'s
    own "already known survives" half, one `Step` at a time, bundled with
    the preimage-nonzero invariant it needs at every intermediate state
    (`holdings_preimage_nonzero_step`'s own fact, threaded alongside since
    this lemma's own `.transfer`/bulk cases need it too): an already-
    known, consistent, adjudicator-owned commitment's own `ownedRandomOf`
    disclosure survives EVERY `Call` — trivially for every case that
    leaves `s.pool` unchanged, via `PoolOwnedSpendStep_ownedRandom_known`
    for `.transfer`, via `bulkTransferFold_ownedRandom_known` for the two
    bulk calls. What `unbeatable_pays`'s own strategy needs to carry the
    channel's held note's own disclosure from the anchor `s` to an
    ARBITRARY reachable `mid`, so `owned_spend_witness_exists`'s own
    `hOwned` hypothesis can be built there. -/
theorem ownedRandom_known_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hinv : (∀ qc pre r, s.pool.preimageOf qc = some pre → hashCommitment pre = qc →
        pre.npk = npk (Term.val s.self) r → s.pool.ownedRandomOf qc = some ⟨s.self, r⟩) ∧
      (∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
        ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc))
    (hstep : Step sig appRel actor s call s') :
    (∀ qc pre r, s.pool.preimageOf qc = some pre → hashCommitment pre = qc →
        pre.npk = npk (Term.val s.self) r → s'.pool.ownedRandomOf qc = some ⟨s.self, r⟩) ∧
      (∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
        ∃ pre, s'.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) := by
  obtain ⟨hinvOwned, hinvPre⟩ := hinv
  have hinvPre' := holdings_preimage_nonzero_step sig appRel actor s s' call hinvPre hstep
  refine ⟨?_, hinvPre'⟩
  cases call with
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
    rcases hh : s.holdings asset channelId with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, _hholdseq⟩ := hmatch
      obtain ⟨r0, ownerField, hself, hown, hcommit, htoken, _hposition, _hN, _hM, hC, _rest,
        _spent', records, _hCapacity, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
      have hvalid_outputs : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
        fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
      intro qc pre r hpre hconsist hnpk
      have h1 := hinvOwned qc pre r hpre hconsist hnpk
      have hpre_mid : applyRecords s.pool.preimageOf records qc = some pre :=
        applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre hpre hconsist
      rw [hpoolEq]
      have hnz0 : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
        rw [htoken]; exact npk_preimage_not_zero hown.symm
      have hread0 := applyRecords_reads hvalid_outputs s.pool.preimageOf _ _ hidxrec hnz0
      rw [heq]; dsimp only
      show applyOwnedRecords s.pool.ownedRandomOf
        [(pub.commitmentsOut idx, (⟨ownerField, r0⟩ : OwnedDisclosure))] qc = some ⟨s.self, r⟩
      exact applyOwnedRecords_preserves_known (reg := applyRecords s.pool.preimageOf records)
        (fun cd hcd => by
          rw [List.mem_singleton] at hcd
          refine hcd ▸ ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, ?_⟩
          rw [htoken]; exact hown.symm) s.pool.ownedRandomOf qc s.self r pre h1 hpre_mid hnpk
    · obtain ⟨oldPos, oldHoldingVal⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergedPos, hmerge, _hholdseq⟩ := hmatch
      obtain ⟨r0, ownerField, hself, hown, hcommit, htoken, _hposition, _hN, _hM, hC, _rest,
        _spent', records, _hCapacity, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
      have hvalid_outputs : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
        fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
      intro qc pre r hpre hconsist hnpk
      have hpre_mid : midPool.preimageOf qc = some pre := by
        rw [heq]; dsimp only
        exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre hpre hconsist
      have h1 := hinvOwned qc pre r hpre hconsist hnpk
      have hnz0' : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
        rw [htoken]; exact npk_preimage_not_zero hown.symm
      have hread0 := applyRecords_reads hvalid_outputs s.pool.preimageOf _ _ hidxrec hnz0'
      have hpre_s_applied : applyRecords s.pool.preimageOf records qc = some pre :=
        applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre hpre hconsist
      have h1mid : midPool.ownedRandomOf qc = some ⟨s.self, r⟩ := by
        rw [heq]; dsimp only
        exact applyOwnedRecords_preserves_known (reg := applyRecords s.pool.preimageOf records)
          (fun cd hcd => by
          rw [List.mem_singleton] at hcd
          refine hcd ▸ ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, ?_⟩
          rw [htoken]; exact hown.symm) s.pool.ownedRandomOf qc s.self r pre h1 hpre_s_applied hnpk
      obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity',
        hown', htoken', hnpkOut', hmergedEq, _hleaf0, _hleaf1, hcommitOld, hcommitNew, hroot',
        hremove', hnullify', hrandomOut', heq'⟩ := hmerge
      have hvalid_outputs' : ∀ cp ∈ ownedOutputRecords w' pub', hashCommitment cp.2 = cp.1 :=
        ownedOutputRecords_valid hC'
      have hmemrec : (pub'.commitmentsOut (0 : Fin 1),
          (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage)) ∈
          ownedOutputRecords w' pub' := by
        unfold ownedOutputRecords
        exact List.mem_ofFn.mpr ⟨0, rfl⟩
      have hnz0 : ¬ isZeroPreimage (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) :=
        npk_preimage_not_zero hnpkOut'.symm
      have hread' := applyRecords_reads hvalid_outputs' midPool.preimageOf _ _ hmemrec hnz0
      have hvalid' : applyRecords midPool.preimageOf (ownedOutputRecords w' pub')
          (pub'.commitmentsOut (0 : Fin 1)) =
          some (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) := hread'
      rw [heq']
      show applyOwnedRecords midPool.ownedRandomOf
        [(pub'.commitmentsOut (0 : Fin 1), (⟨pub'.ownerField, randomOut'⟩ : OwnedDisclosure))] qc =
        some ⟨s.self, r⟩
      have hpre_mid_applied : applyRecords midPool.preimageOf (ownedOutputRecords w' pub') qc =
          some pre := applyRecords_preserves_known hvalid_outputs' midPool.preimageOf qc pre
        hpre_mid hconsist
      exact applyOwnedRecords_preserves_known (reg := applyRecords midPool.preimageOf
        (ownedOutputRecords w' pub')) (fun cd hcd => by
        rw [List.mem_singleton] at hcd
        exact hcd ▸ ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, hvalid', hrandomOut'⟩)
        midPool.ownedRandomOf qc s.self r pre h1mid hpre_mid_applied hnpk
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, _hholdEq, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    rw [hpoolEq]; exact hinvOwned qc pre r hpre hconsist hnpk
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, _hholdEq, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    rw [hpoolEq]; exact hinvOwned qc pre r hpre hconsist hnpk
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, _hholdEq, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    rw [hpoolEq]; exact hinvOwned qc pre r hpre hconsist hnpk
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨r0, hmatch, _hholdseq, _hchanseq⟩ := hrest
    change PoolOwnedSpendStep s.pool s.self (outcome.get ⟨assetIndex, hidx⟩).asset
      (s.holdings (outcome.get ⟨assetIndex, hidx⟩).asset cid)
      ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
          (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
        if a.amount = 0 then none
        else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ : CommitmentPreimage)))
      (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
          (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
            (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
       then []
       else [(⟨npk (Term.val s.self) r0, (outcome.get ⟨assetIndex, hidx⟩).asset,
         heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
           (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
             (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ : CommitmentPreimage)])
      s'.pool at hmatch
    generalize hAO : outcome.get ⟨assetIndex, hidx⟩ = assetOutcome at hmatch
    generalize hPayoutDef : (transferEffects assetOutcome.allocations
        (heldValue s assetOutcome.asset cid) indices).2.1.filterMap (fun a =>
          if a.amount = 0 then none
          else some (⟨a.destination, assetOutcome.asset, a.amount⟩ : CommitmentPreimage)) =
      payoutOutputs at hmatch
    generalize hRemDef : heldValue s assetOutcome.asset cid -
      (transferEffects assetOutcome.allocations (heldValue s assetOutcome.asset cid) indices).2.2 =
      remainder at hmatch
    intro qc pre r hpre hconsist hnpk
    exact (PoolOwnedSpendStep_ownedRandom_known s.pool s'.pool s.self assetOutcome.asset cid
      remainder r0 payoutOutputs s.holdings
      (fun pre hpre => by
        rw [← hPayoutDef] at hpre
        obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
        by_cases hamt : a.amount = 0
        · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
        · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
      hmatch).1 qc pre r hpre hconsist hnpk (hinvOwned qc pre r hpre hconsist hnpk)
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _hsa, _hidx1, _h5, _h6, hpoolEq, _hholdEq, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    rw [hpoolEq]; exact hinvOwned qc pre r hpre hconsist hnpk
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    exact bulkTransferFold_ownedRandom_known s.self channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold hinvPre qc pre r hpre hconsist hnpk (hinvOwned qc pre r hpre hconsist hnpk)
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    exact bulkTransferFold_ownedRandom_known s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold hinvPre qc pre r hpre hconsist hnpk
      (hinvOwned qc pre r hpre hconsist hnpk)
  | tick newNow =>
    obtain ⟨_, _, hpoolEq, _hholdEq, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    rw [hpoolEq]; exact hinvOwned qc pre r hpre hconsist hnpk
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, _hholdEq, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    rw [hpoolEq]; exact hinvOwned qc pre r hpre hconsist hnpk
  | signNote pk msgHash =>
    obtain ⟨_, _, hpoolEq, _, _hholdEq, _⟩ := hstep
    intro qc pre r hpre hconsist hnpk
    rw [hpoolEq]; exact hinvOwned qc pre r hpre hconsist hnpk


/-- **Every held note's own preimage has a known owned disclosure, for
    some `ownerField` with `self = addressOf ownerField`.** One `Step` at
    a time. What `unbeatable_pays`'s own strategy needs to build
    `owned_spend_witness_exists`'s own `hOwned` hypothesis for the
    channel's held note, at an ARBITRARY reachable state. -/
theorem held_note_owned_disclosure_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre ownerField r, s.pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        s.self = addressOf ownerField ∧ s.pool.ownedRandomOf qc = some ⟨ownerField, r⟩ ∧
        npk (Term.val ownerField) r = pre.npk)
    (hstep : Step sig appRel actor s call s') :
    ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
      ∃ pre ownerField r, s'.pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        s.self = addressOf ownerField ∧ s'.pool.ownedRandomOf qc = some ⟨ownerField, r⟩ ∧
        npk (Term.val ownerField) r = pre.npk := by
  cases call with
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_hcfg, _hheld, _hext, _hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
    obtain ⟨r0, ownerField, hself, hown, hcommit, htoken, _hposition, _hN, _hM, hC, _rest,
      _spent', records, _hCapacity, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hvalid_outputs : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
      fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
    have hnz0 : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
      rw [htoken]; exact npk_preimage_not_zero hown.symm
    have hread0 := applyRecords_reads hvalid_outputs s.pool.preimageOf _ _ hidxrec hnz0
    rcases hh : s.holdings asset channelId with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, hholdseq⟩ := hmatch
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc; unfold update at hc
      by_cases ha : qasset = asset
      · subst ha
        by_cases hcid : qcid = channelId
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          obtain ⟨hpeq, hceq⟩ := Prod.mk.injEq .. ▸ Option.some.inj hc
          refine ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, ownerField, r0, ?_, ?_, hself, ?_, ?_⟩
          · rw [hpoolEq, heq, ← hceq]; dsimp only; exact hread0
          · exact (hC.outputs idx).symm.trans hceq
          · rw [hpoolEq, heq, ← hceq]; dsimp only
            exact applyOwnedRecords_reads (reg := applyRecords s.pool.preimageOf records)
              (fun cd hcd => by
                rw [List.mem_singleton] at hcd
                rw [hcd]
                exact ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, hown.symm⟩)
              s.pool.ownedRandomOf (pub.commitmentsOut idx) (⟨ownerField, r0⟩ : OwnedDisclosure)
              (List.mem_singleton_self _)
          · exact hown.symm
        · rw [if_pos rfl, if_neg hcid] at hc
          obtain ⟨pre, ownerField', r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
          refine ⟨pre, ownerField', r, ?_, h2, h3, ?_, h5⟩
          · rw [hpoolEq, heq]; dsimp only
            exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2
          · rw [hpoolEq, heq]; dsimp only
            exact applyOwnedRecords_preserves_known (reg := applyRecords s.pool.preimageOf records)
              (fun cd hcd => by
                rw [List.mem_singleton] at hcd
                rw [hcd]
                exact ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, by
                  rw [htoken]; exact hown.symm⟩) s.pool.ownedRandomOf qc ownerField' r pre h4
              (applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2) h5.symm
      · rw [if_neg ha] at hc
        obtain ⟨pre, ownerField', r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
        refine ⟨pre, ownerField', r, ?_, h2, h3, ?_, h5⟩
        · rw [hpoolEq, heq]; dsimp only
          exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2
        · rw [hpoolEq, heq]; dsimp only
          exact applyOwnedRecords_preserves_known (reg := applyRecords s.pool.preimageOf records)
            (fun cd hcd => by
              rw [List.mem_singleton] at hcd
              rw [hcd]
              exact ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, by
                rw [htoken]; exact hown.symm⟩) s.pool.ownedRandomOf qc ownerField' r pre h4
            (applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2) h5.symm
    · obtain ⟨oldPos, oldHoldingVal⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergedPos, hmerge, hholdseq⟩ := hmatch
      obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity',
        hown', htoken', hnpkOut', hmergedEq, _hleaf0, _hleaf1, hcommitOld, hcommitNew, hroot',
        hremove', hnullify', hrandomOut', heq'⟩ := hmerge
      intro qasset qcid qpos qc hc
      rw [hholdseq] at hc; unfold update at hc
      by_cases ha : qasset = asset
      · subst ha
        by_cases hcid : qcid = channelId
        · subst hcid
          rw [if_pos rfl, if_pos rfl] at hc
          obtain ⟨hpeq, hceq⟩ := Prod.mk.injEq .. ▸ Option.some.inj hc
          have hvalid_outputs' : ∀ cp ∈ ownedOutputRecords w' pub', hashCommitment cp.2 = cp.1 :=
            ownedOutputRecords_valid hC'
          have hmemrec : (pub'.commitmentsOut (0 : Fin 1),
              (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage)) ∈
              ownedOutputRecords w' pub' := by
            unfold ownedOutputRecords; exact List.mem_ofFn.mpr ⟨0, rfl⟩
          have hnz0' : ¬ isZeroPreimage (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) :=
            npk_preimage_not_zero hnpkOut'.symm
          have hread' := applyRecords_reads hvalid_outputs' midPool.preimageOf _ _ hmemrec hnz0'
          refine ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, pub'.ownerField, randomOut', ?_, ?_,
            hown', ?_, ?_⟩
          · rw [heq', hceq.symm.trans hmergedEq]; dsimp only; exact hread'
          · exact (hC'.outputs 0).symm.trans (hmergedEq.symm.trans hceq)
          · rw [heq', hceq.symm.trans hmergedEq]; dsimp only
            exact applyOwnedRecords_reads
              (reg := applyRecords midPool.preimageOf (ownedOutputRecords w' pub')) (fun cd hcd => by
                rw [List.mem_singleton] at hcd
                rw [hcd]
                exact ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, hread', hrandomOut'⟩)
              midPool.ownedRandomOf (pub'.commitmentsOut (0 : Fin 1))
              (⟨pub'.ownerField, randomOut'⟩ : OwnedDisclosure) (List.mem_singleton_self _)
          · exact hrandomOut'
        · rw [if_pos rfl, if_neg hcid] at hc
          obtain ⟨pre, ownerField', r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
          have hvalid_outputs' : ∀ cp ∈ ownedOutputRecords w' pub', hashCommitment cp.2 = cp.1 :=
            ownedOutputRecords_valid hC'
          have h1mid : midPool.preimageOf qc = some pre := by
            rw [heq]; dsimp only
            exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2
          have h4mid : midPool.ownedRandomOf qc = some ⟨ownerField', r⟩ := by
            rw [heq]; dsimp only
            exact applyOwnedRecords_preserves_known (reg := applyRecords s.pool.preimageOf records)
              (fun cd hcd => by
                rw [List.mem_singleton] at hcd
                rw [hcd]
                exact ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, by
                  rw [htoken]; exact hown.symm⟩) s.pool.ownedRandomOf qc ownerField' r pre h4
              (applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2) h5.symm
          refine ⟨pre, ownerField', r, ?_, h2, h3, ?_, h5⟩
          · rw [heq']; dsimp only
            exact applyRecords_preserves_known hvalid_outputs' midPool.preimageOf qc pre h1mid h2
          · rw [heq']; dsimp only
            exact applyOwnedRecords_preserves_known
              (reg := applyRecords midPool.preimageOf (ownedOutputRecords w' pub')) (fun cd hcd => by
              rw [List.mem_singleton] at hcd
              exact hcd ▸ ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩,
                applyRecords_reads hvalid_outputs' midPool.preimageOf _ _
                  (by unfold ownedOutputRecords; exact List.mem_ofFn.mpr ⟨0, rfl⟩)
                  (npk_preimage_not_zero hnpkOut'.symm), hrandomOut'⟩)
              midPool.ownedRandomOf qc ownerField' r pre h4mid
              (applyRecords_preserves_known hvalid_outputs' midPool.preimageOf qc pre h1mid h2) h5.symm
      · rw [if_neg ha] at hc
        obtain ⟨pre, ownerField', r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
        have hvalid_outputs' : ∀ cp ∈ ownedOutputRecords w' pub', hashCommitment cp.2 = cp.1 :=
          ownedOutputRecords_valid hC'
        have h1mid : midPool.preimageOf qc = some pre := by
          rw [heq]; dsimp only
          exact applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2
        have h4mid : midPool.ownedRandomOf qc = some ⟨ownerField', r⟩ := by
          rw [heq]; dsimp only
          exact applyOwnedRecords_preserves_known (reg := applyRecords s.pool.preimageOf records)
            (fun cd hcd => by
              rw [List.mem_singleton] at hcd
              rw [hcd]
              exact ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, by
                rw [htoken]; exact hown.symm⟩) s.pool.ownedRandomOf qc ownerField' r pre h4
            (applyRecords_preserves_known hvalid_outputs s.pool.preimageOf qc pre h1 h2) h5.symm
        refine ⟨pre, ownerField', r, ?_, h2, h3, ?_, h5⟩
        · rw [heq']; dsimp only
          exact applyRecords_preserves_known hvalid_outputs' midPool.preimageOf qc pre h1mid h2
        · rw [heq']; dsimp only
          exact applyOwnedRecords_preserves_known
            (reg := applyRecords midPool.preimageOf (ownedOutputRecords w' pub')) (fun cd hcd => by
            rw [List.mem_singleton] at hcd
            exact hcd ▸ ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩,
              applyRecords_reads hvalid_outputs' midPool.preimageOf _ _
                (by unfold ownedOutputRecords; exact List.mem_ofFn.mpr ⟨0, rfl⟩)
                (npk_preimage_not_zero hnpkOut'.symm), hrandomOut'⟩)
            midPool.ownedRandomOf qc ownerField' r pre h4mid
            (applyRecords_preserves_known hvalid_outputs' midPool.preimageOf qc pre h1mid h2) h5.symm
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, ownerField, r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, ownerField, r, hpoolEq ▸ h1, h2, h3, hpoolEq ▸ h4, h5⟩
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, ownerField, r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, ownerField, r, hpoolEq ▸ h1, h2, h3, hpoolEq ▸ h4, h5⟩
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, ownerField, r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, ownerField, r, hpoolEq ▸ h1, h2, h3, hpoolEq ▸ h4, h5⟩
  | transfer assetIndex cid claimedStateHash outcome indices => sorry
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, ownerField, r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, ownerField, r, hpoolEq ▸ h1, h2, h3, hpoolEq ▸ h4, h5⟩
  | bulkTransferAllAssets channelId outcome claimedStateHash => sorry
  | bulkConcludeAndTransferAllAssets fp candidate => sorry
  | tick newNow =>
    obtain ⟨_, _, hpoolEq, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, ownerField, r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, ownerField, r, hpoolEq ▸ h1, h2, h3, hpoolEq ▸ h4, h5⟩
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, ownerField, r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, ownerField, r, hpoolEq ▸ h1, h2, h3, hpoolEq ▸ h4, h5⟩
  | signNote pk msgHash =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    intro qasset qcid qpos qc hc
    rw [hholdEq] at hc
    obtain ⟨pre, ownerField, r, h1, h2, h3, h4, h5⟩ := hinv qasset qcid qpos qc hc
    exact ⟨pre, ownerField, r, hpoolEq ▸ h1, h2, h3, hpoolEq ▸ h4, h5⟩

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
    not commitments: two different channels' notes CAN carry the identical commitment
    (two deposits, or two `.transfer` remainders, that reuse the same caller-chosen
    random `r` — nothing in the model forces two different calls' own `r` apart), but
    they can never share a leaf position — `Pool.lean`'s module comment. -/


theorem holdings_position_live_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ s.pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, s.self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
          ∃ r, pre.npk = npk (Term.val s.self) r)) ∧
      qpos < s.pool.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', s.holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos))
    (hstep : Step sig appRel actor s call s') :
    ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ s'.pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, s.self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
          ∃ r, pre.npk = npk (Term.val s.self) r)) ∧
      qpos < s'.pool.leaves.length ∧
      (∀ qasset' qcid' qpos' qc', s'.holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  have userDisjoint : ∀ (pre : CommitmentPreimage),
      ((∃ ownerField r, s.self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
        ∃ r, pre.npk = npk (Term.val s.self) r) →
      ∀ pk' nk' r', pre.npk ≠ npk (masterPublicKey pk' nk') r' := by
    intro pre hown pk' nk' r' hcontra
    rcases hown with ⟨ownerField, r, _hself, h2⟩ | ⟨r, h2⟩
    · rw [h2] at hcontra
      exact user_npk_ne_contract_npk hcontra.symm
    · rw [h2] at hcontra
      exact user_npk_ne_contract_npk hcontra.symm
  have trivial : s'.pool = s.pool → s'.holdings = s.holdings →
      ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
        (∃ pre, (qpos, pre) ∈ s'.pool.live qasset ∧ hashCommitment pre = qc ∧
          ((∃ ownerField r, s.self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
            ∃ r, pre.npk = npk (Term.val s.self) r)) ∧
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
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_position_live s.self channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold hinv
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_position_live s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold hinv
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
    obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
    obtain ⟨r, ownerField, hself, hown, hcommit, htoken, hposition, hN, hM, hC, rest, spent',
      records, hCapacity, hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
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
          refine ⟨⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, ?_, ?_,
            Or.inl ⟨ownerField, r, hself, hown⟩⟩, ?_, ?_⟩
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
          ((∃ ownerField r, s.self = addressOf ownerField ∧ pre.npk = npk (Term.val ownerField) r) ∨
            ∃ r'', pre.npk = npk (Term.val s.self) r'') →
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
          refine ⟨⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, ?_, ?_, Or.inr ⟨r', hnpkOut'⟩⟩, ?_, ?_⟩
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
    obtain ⟨r, hmatch, hholdseq, _hchanseq⟩ := hrest
    intro qasset qcid qpos qc hc
    rw [hholdseq] at hc ⊢
    exact PoolOwnedSpend_update_position_live s.pool s'.pool s.self
      (outcome.get ⟨assetIndex, hidx⟩).asset cid _ r _ s.holdings hmatch hinv qasset qcid qpos qc hc

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
  obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
  obtain ⟨_r, _ownerField, _hself, _hown, hcommit, htoken, _hposition, _hN, _hM, hC, _rest,
    _spent', records, _hCapacity, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
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
  obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
  obtain ⟨_r, _ownerField, _hself, _hown, hcommit, htoken, _hposition, _hN, _hM, hC, _rest,
    _spent', records, _hCapacity, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
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


/-- A successful `.deposit` leaves `heldValue` UNCHANGED at every OTHER
    `(asset, channelId)` pair: `update` only ever touches the ONE pair
    the call names, and `applyRecords_preserves_known` carries any
    OTHER already-known preimage through the deposit's own disclosure
    batch unscathed. The frame half of `deposit_effect` (`Safety.lean`,
    A-08), paired with `deposit_sets_heldValue`/
    `deposit_merge_sets_heldValue` for the touched pair itself. -/
theorem deposit_frame (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (channelId : Term) (expectedHeld asset amount : Nat)
    (hstep : Step sig appRel actor s (.deposit channelId expectedHeld asset amount) s')
    (hinv : ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre, s.pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (asset' : Nat) (cid' : Term) (hne : (asset', cid') ≠ (asset, channelId)) :
    heldValue s' asset' cid' = heldValue s asset' cid' := by
  obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨N, M, w, pub, idx, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
  obtain ⟨_r, _ownerField, _hself, _hown, hcommit, htoken, hposition, hN, hM, hC, rest, spent',
    records, hCapacity, hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have hchain : ∀ qc pre, s.pool.preimageOf qc = some pre → hashCommitment pre = qc →
      midPool.preimageOf qc = some pre := fun qc pre hpre hconsist => by
    rw [heq]; exact applyRecords_preserves_known hvalid s.pool.preimageOf qc pre hpre hconsist
  unfold heldValue
  rcases hh : s.holdings asset channelId with _ | oldHolding
  · rw [hh] at hmatch
    obtain ⟨hpoolEq, hholdseq⟩ := hmatch
    rw [hholdseq]
    unfold update
    by_cases ha : asset' = asset
    · subst ha
      by_cases hcid : cid' = channelId
      · subst hcid; exact absurd rfl hne
      · rw [if_pos rfl, if_neg hcid]
        rcases hh' : s.holdings asset' cid' with _ | hpair
        · rfl
        · obtain ⟨qpos, qc⟩ := hpair
          obtain ⟨pre_old, hpre_old, _hval_old, hconsist_old⟩ := hinv asset' cid' qpos qc hh'
          dsimp only; rw [hpoolEq, hchain qc pre_old hpre_old hconsist_old, hpre_old]
    · rw [if_neg ha]
      rcases hh' : s.holdings asset' cid' with _ | hpair
      · rfl
      · obtain ⟨qpos, qc⟩ := hpair
        obtain ⟨pre_old, hpre_old, _hval_old, hconsist_old⟩ := hinv asset' cid' qpos qc hh'
        dsimp only; rw [hpoolEq, hchain qc pre_old hpre_old hconsist_old, hpre_old]
  · obtain ⟨oldPos, oldHoldingVal⟩ := oldHolding
    rw [hh] at hmatch
    obtain ⟨merged, mergedPos, hmerge, hholdseq⟩ := hmatch
    obtain ⟨_hmergedPos, w', pub', hC', rest', spent'', r', randomOut', hNonZero', hCapacity',
      hown', htoken', hnpkOut', hmergedEq, _hleaf0, _hleaf1, hcommitOld, hcommitNew, hroot',
      hremove', hnullify', _hrandomOut', heq'⟩ := hmerge
    have hchain2 : ∀ qc pre, s.pool.preimageOf qc = some pre → hashCommitment pre = qc →
        s'.pool.preimageOf qc = some pre := fun qc pre hpre hconsist => by
      rw [heq']
      exact applyRecords_preserves_known (ownedOutputRecords_valid hC') midPool.preimageOf qc pre
        (hchain qc pre hpre hconsist) hconsist
    rw [hholdseq]
    unfold update
    by_cases ha : asset' = asset
    · subst ha
      by_cases hcid : cid' = channelId
      · subst hcid; exact absurd rfl hne
      · rw [if_pos rfl, if_neg hcid]
        rcases hh' : s.holdings asset' cid' with _ | hpair
        · rfl
        · obtain ⟨qpos, qc⟩ := hpair
          obtain ⟨pre_old2, hpre_old2, _hval_old2, hconsist_old2⟩ := hinv asset' cid' qpos qc hh'
          dsimp only; rw [hchain2 qc pre_old2 hpre_old2 hconsist_old2, hpre_old2]
    · rw [if_neg ha]
      rcases hh' : s.holdings asset' cid' with _ | hpair
      · rfl
      · obtain ⟨qpos, qc⟩ := hpair
        obtain ⟨pre_old2, hpre_old2, _hval_old2, hconsist_old2⟩ := hinv asset' cid' qpos qc hh'
        dsimp only; rw [hchain2 qc pre_old2 hpre_old2 hconsist_old2, hpre_old2]

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
