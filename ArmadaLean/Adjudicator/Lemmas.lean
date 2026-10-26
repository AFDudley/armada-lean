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

/-- `afford` pays nothing out of a zero surplus, at any index: with no
    funds to distribute, every entry's own paid amount is `0`. What
    `unbeatable_pays`'s own strategy needs: a positive affordable amount
    (`haffordable`/`hxpos`) rules out a zero `heldValue`, so the
    channel's own held note actually exists. -/
theorem afford_zero_surplus (allocs : List Allocation) (k : Nat) :
    (afford allocs 0).getD k 0 = 0 := by
  induction allocs generalizing k with
  | nil => simp [afford]
  | cons a as ih =>
    cases k with
    | zero => show min a.amount 0 = 0; omega
    | succ k' =>
      show (afford as (0 - min a.amount 0)).getD k' 0 = 0
      simpa using ih k'

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

/-- The converse of `transferEffectsSel_exit_mem`: EVERY member of
    `exitAllocations` (`.2.1`) comes from some selected index `i`, equal
    to that index's own entry, `afford`'s own paid amount included.
    What `unbeatable_pays`'s `.transfer` witness needs to show
    `exitAllocs`'s own guarantee-type precondition (`Operations.lean`'s
    `.transfer`) from `curOutcome`'s own allocations alone, for a
    SINGLE selected `destIdx` (`sel = (· = destIdx)`): every exit entry
    is `destIdx`'s own allocation, so `hnoguarantee` (stated over every
    allocation) already covers it. -/
theorem transferEffectsSel_exit_forall (allocs : List Allocation) (surplus : Nat)
    (sel : Nat → Bool) :
    ∀ x ∈ (transferEffectsSel allocs surplus sel).2.1,
      ∃ i, i < allocs.length ∧ sel i = true ∧
        x = { allocs.getD i Allocation.default with
          amount := (afford allocs surplus).getD i 0 } := by
  intro x hx
  unfold transferEffectsSel at hx
  dsimp only at hx
  obtain ⟨⟨i, a, paid⟩, hmem, heq⟩ := List.mem_filterMap.mp hx
  by_cases hsel : sel i = true
  · rw [if_pos hsel] at heq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    rw [List.getElem?_zip_eq_some] at hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [List.getElem?_zip_eq_some] at hj2
    obtain ⟨hj2a, hj2b⟩ := hj2
    dsimp only at hj2a hj2b
    have hjlt : j < allocs.length := by
      have := List.getElem?_eq_some_iff.mp hj1
      simpa using this.1
    have hieq : i = j := by
      have := List.getElem?_eq_some_iff.mp hj1
      simpa using this.2.symm
    subst hieq
    have ha : a = allocs.getD i Allocation.default := by
      rw [List.getD_eq_getElem?_getD, hj2a]; rfl
    have hpaid : paid = (afford allocs surplus).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, hj2b]; rfl
    refine ⟨i, hjlt, hsel, ?_⟩
    have hxeq := Option.some.inj heq.symm
    rw [hxeq, ha, hpaid]
  · rw [if_neg hsel] at heq; exact absurd heq (by simp)

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


/-- `transferEffectsSel`'s own exit list, decomposed the same way as
    `transferEffectsSel_cons_payout`: the head's own payout, if
    selected, prepended to the tail's own exit list. What
    `transfer_step_exists` (`Safety.lean`) needs to pin a single-index
    selection's exit list down to exactly one entry. -/
theorem transferEffectsSel_cons_exit (a : Allocation) (as : List Allocation) (surplus : Nat)
    (sel : Nat → Bool) :
    (transferEffectsSel (a :: as) surplus sel).2.1 =
      (if sel 0 then [{ a with amount := min a.amount surplus }] else []) ++
        (transferEffectsSel as (surplus - min a.amount surplus) (fun j => sel (j + 1))).2.1 := by
  have haffcons : afford (a :: as) surplus =
      min a.amount surplus :: afford as (surplus - min a.amount surplus) := rfl
  by_cases h0 : sel 0
  · simp only [if_pos h0]
    unfold transferEffectsSel
    simp only [List.length_cons, List.range_succ_eq_map, haffcons, List.zip_cons_cons,
      List.filterMap_cons, if_pos h0,
      List.zip_map_left, List.filterMap_map, List.singleton_append]
    congr 1
  · simp only [if_neg h0, List.nil_append]
    unfold transferEffectsSel
    simp only [List.length_cons, List.range_succ_eq_map, haffcons, List.zip_cons_cons,
      List.filterMap_cons, if_neg h0,
      List.zip_map_left, List.filterMap_map]
    congr 1

/-- A single-index selection's own exit list is exactly one entry: the
    selected allocation's own share. What `transfer_step_exists`
    (`Safety.lean`) needs for `PoolOwnedSpendStep`'s own `hM` bound —
    without this, `payoutOutputs`'s own length is unbounded. -/
theorem transferEffects_exit_single (allocs : List Allocation) (surplus idx : Nat)
    (hidx : idx < allocs.length) :
    (transferEffects allocs surplus [idx]).2.1 =
      [{ allocs.getD idx Allocation.default with amount := (afford allocs surplus).getD idx 0 }] := by
  induction allocs generalizing surplus idx with
  | nil => simp at hidx
  | cons a as ih =>
    rw [transferEffects_eq_sel, transferEffectsSel_cons_exit]
    cases idx with
    | zero =>
      have hsel0 : ([0].isEmpty || (0:Nat) ∈ [0]) = true := by simp
      rw [hsel0]
      have hempty : (transferEffectsSel as (surplus - min a.amount surplus)
          (fun j => [0].isEmpty || j + 1 ∈ [0])).2.1 = [] := by
        have hsel' : ∀ j, ([0].isEmpty || j + 1 ∈ [0]) = false := by
          intro j; simp
        unfold transferEffectsSel
        simp only [hsel']
        simp
      rw [hempty]
      simp [afford]
    | succ i' =>
      have hidx' : i' < as.length := by simpa using hidx
      have hselshift : (fun j => [i' + 1].isEmpty || j + 1 ∈ [i' + 1]) =
          (fun j => [i'].isEmpty || j ∈ [i']) := by
        funext j; simp [Nat.succ_eq_add_one]
      rw [hselshift, ← transferEffects_eq_sel, ih (surplus - min a.amount surplus) i' hidx']
      have hsel0 : ([i' + 1].isEmpty || (0:Nat) ∈ [i' + 1]) = false := by simp
      rw [hsel0]
      simp only [List.getD_cons_succ, Bool.false_eq_true, if_false, List.nil_append]
      have hafforD : (afford (a :: as) surplus).getD (i' + 1) 0 =
          (afford as (surplus - min a.amount surplus)).getD i' 0 := by simp [afford]
      rw [hafforD]


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

/-- One `PoolOwnedSpendStep` call is exactly one `_root_.Step.transactOwned`
    instance (the "none"-nullified branch mints with no spend, the
    "some"-nullified branch nullifies the named position), so
    `_root_.Reachable` carries forward across it. What
    `bulkTransferFold_pool_reachable` needs, one asset at a time. -/
theorem PoolOwnedSpendStep_reachable
    (pool pool' : PoolState) (self : Term) (token : Nat)
    (nullified : Option ((Nat × Nat) × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage)
    (hmatch : PoolOwnedSpendStep pool self token nullified payoutPreimages ownedPreimages pool')
    (hreach : _root_.Reachable pool) : _root_.Reachable pool' := by
  unfold PoolOwnedSpendStep at hmatch
  rcases nullified with _ | ⟨npos, c⟩
  · obtain ⟨w, pub, hM, hC, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes,
      hroot, hmark, hRandomOut, heq⟩ := hmatch
    subst htoken
    have hcap : (ownedNewNotes w).length = payoutPreimages.length + ownedPreimages.length :=
      List.length_ofFn
    have hRemove0 : removeAll (pool.live w.token)
        (ownedSpentPositions (insertTreeNumber pool.closedTrees pool.leaves
          (payoutPreimages.length + ownedPreimages.length)) pub w) =
        some (pool.live w.token) := by
      simp [ownedSpentPositions, removeAll]
    refine Reachable.step hreach ?_
    rw [heq]
    have hterm := _root_.Step.transactOwned (s := pool) w pub
      (insertTreeNumber pool.closedTrees pool.leaves
        (payoutPreimages.length + ownedPreimages.length))
      (by omega) hM hC self hself (pool.live w.token) spent'
      ((List.finRange ownedPreimages.length).map fun j =>
        (Fin.natAdd payoutPreimages.length j, (⟨self, ownedRandom j⟩ : OwnedDisclosure)))
      hroot hRemove0 hmark hNonZero
      (by
        intro x hx
        obtain ⟨j, hjmem, hxeq⟩ := List.mem_map.mp hx
        rw [← hxeq]
        exact (hRandomOut j).symm)
    rw [hcap, hnewnotes, List.map_map] at hterm
    simp only [Function.comp] at hterm
    have hlive : (fun t => if t = w.token then
          withTreePositionsFrom
              (insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages.length + ownedPreimages.length))
              (insertStartPos pool.leaves (payoutPreimages.length + ownedPreimages.length))
              (payoutPreimages ++ ownedPreimages) ++ pool.live w.token
        else pool.live t) =
        (fun t => if t = w.token then
          withTreePositionsFrom
              (insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages.length + ownedPreimages.length))
              (insertStartPos pool.leaves (payoutPreimages.length + ownedPreimages.length))
              (payoutPreimages ++ ownedPreimages) ++ pool.live t
        else pool.live t) := by
      funext t
      by_cases h : t = w.token
      · rw [h]
      · simp [h]
    rw [hlive] at hterm
    exact hterm
  · obtain ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero, hself, htoken,
      hnewnotes, hleaf0, hceq, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
    subst htoken
    have hcap : (ownedNewNotes w).length = payoutPreimages.length + ownedPreimages.length :=
      List.length_ofFn
    refine Reachable.step hreach ?_
    rw [heq]
    have hterm := _root_.Step.transactOwned (s := pool) w pub npos.1
      (by omega) hM hC self hself rest spent'
      ((List.finRange ownedPreimages.length).map fun j =>
        (Fin.natAdd payoutPreimages.length j, (⟨self, ownedRandom j⟩ : OwnedDisclosure)))
      hroot hremove hmark hNonZero
      (by
        intro x hx
        obtain ⟨j, hjmem, hxeq⟩ := List.mem_map.mp hx
        rw [← hxeq]
        exact (hRandomOut j).symm)
    rw [hcap, hnewnotes, List.map_map] at hterm
    simp only [Function.comp] at hterm
    exact hterm


/-- `bulkTransferFold`'s own pool-level lift: `_root_.Reachable` carries
    forward across the WHOLE fold, one asset's own `PoolOwnedSpendStep` —
    itself `_root_.Step.transactOwned` — at a time. What
    `adjudicator_pool_step` needs for its own two bulk `Call` cases. -/
theorem bulkTransferFold_pool_reachable (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    _root_.Reachable pool → _root_.Reachable poolF := by
  intro outcome
  induction outcome with
  | nil =>
    intro newOutcome pool poolF holdings holdingsF hfold hreach
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      obtain ⟨hpoolEq, _⟩ := hfold
      rw [hpoolEq]; exact hreach
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hreach
    cases newOutcome with
    | nil =>
      unfold bulkTransferFold at hfold
      exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguard, _hnewExit, r, midPool, hspend, hfoldrest⟩ := hfold
      have hreachMid : _root_.Reachable midPool :=
        PoolOwnedSpendStep_reachable pool midPool self exit.asset _ _ _ hspend hreach
      exact ih newRest midPool poolF _ holdingsF hfoldrest hreachMid



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
    obtain ⟨_hcfg, _hheld, _hext, _hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, spendTreeNumber, treeNumber, position, midPool, hdstep,
      _hpoolsigned, hmatch⟩ := hinner
    obtain ⟨r, hown, hcommit, htoken, htreeNumber, _hposition, hN, hM, hC, rest, spent',
      records, hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hcap : (transactAllOutputs w).length = M := List.length_ofFn
    have hStepMid : _root_.Step s.pool midPool := by
      rw [heq]
      have hterm := _root_.Step.transact (s := s.pool) w pub spendTreeNumber hN hM hC
        (transactAllOutputs w) [] rest spent' records
        [(pub.commitmentsOut idx, (⟨s.self, r⟩ : OwnedDisclosure))]
        hRoot (by simp) (by simp) hRemove hNullify hSublist
        (by
          intro cd hcd
          rw [List.mem_singleton] at hcd
          subst hcd
          exact ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hidxrec, hown.symm⟩)
      rw [hcap, ← htreeNumber] at hterm
      simp only [List.map_nil, listSum, Nat.sub_zero, ite_self] at hterm
      exact hterm
    have hreachMid : _root_.Reachable midPool := Reachable.step hreach hStepMid
    rcases hh : s.holdings asset channelId with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, _hholdseq⟩ := hmatch
      rw [hpoolEq]; exact hreachMid
    · obtain ⟨_oldTreeNum, _oldPosNat⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergeSpendTreeNumber, mergedTreeNumber, mergedPos, hmergestep, _hholdseq⟩ :=
        hmatch
      obtain ⟨hmergedTN, hmergedPosEq, w', pub', hC', rest', spent'', r', randomOut', hNonZero',
        hself', htoken', hnpkOut0', hmergedEq, hleaf0', hleaf1', hcommitOld', hcommitNew',
        holdTN', newTN', hroot', hremove', hnullify', hrandomOut', heq'⟩ := hmergestep
      subst htoken'
      have hcap' : (ownedNewNotes w').length = 1 := List.length_ofFn
      have hStepFinal : _root_.Step midPool s'.pool := by
        rw [heq']
        have hterm := _root_.Step.transactOwned (s := midPool) w' pub' mergeSpendTreeNumber
          (by omega) (by omega) hC' s.self hself' rest' spent''
          [((0 : Fin 1), (⟨pub'.ownerField, randomOut'⟩ : OwnedDisclosure))]
          hroot' hremove' hnullify' (fun j => (Subsingleton.elim j 0) ▸ hNonZero')
          (by
            intro x hx
            rw [List.mem_singleton] at hx
            subst hx
            exact hrandomOut')
        rw [hcap', ← hmergedTN, ← hmergedPosEq] at hterm
        exact hterm
      exact Reachable.step hreachMid hStepFinal
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨r, hmatch, _hholdseq, _hchanseq⟩ := hrest
    exact PoolOwnedSpendStep_reachable s.pool s'.pool s.self _ _ _ _ hmatch hreach
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _hsa, _hidx1, _h5, _h6, hpoolEq, hholdEq, _⟩ := hstep
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
    obtain ⟨_, _, hpoolEq, hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach
  | signNote pk msgHash =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    rw [hpoolEq]; exact hreach


/-- The reachable-set form of `adjudicator_pool_step`: the pool component
    of every adjudicator-reachable state is itself pool-reachable from
    `pool0`. -/
theorem adjudicator_pool_reachable (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState)
    (hReachPool : _root_.Reachable pool0) (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
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
    exact congrArg Term.keccak h
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, h, _, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | tick newNow =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | sign p d =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact congrArg Term.keccak h
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, _, h, _, _⟩ := hstep
    exact congrArg Term.keccak h

/-- Every `Step` case OTHER than `.tick` leaves `now` untouched
    (`Operations.lean`): `.tick` is the one call whose own job is to
    advance the clock; every other case states `s'.now = s.now`
    directly. What `unbeatable_pays`'s own strategy needs: `interleaved`
    (which excludes `.tick`, `hexclTick`) never changes `mid.now` away
    from `s.now`, so `s`'s own `hnowpos : 0 < s.now` still holds at
    `mid`. -/
theorem step_now_frame (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hnotick : ∀ newNow, call ≠ Call.tick newNow)
    (hstep : Step sig appRel actor s call s') :
    s'.now = s.now := by
  cases call with
  | deposit cid expectedHeld asset amount =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := hstep
    exact h
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := hstep
    exact h
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := hstep
    exact h
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | bulkTransferAllAssets cid outcome claimedStateHash =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _, _⟩ := hstep
    exact h
  | tick newNow => exact absurd rfl (hnotick newNow)
  | sign p d =>
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := hstep
    exact h
  | signNote pk msgHash =>
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := hstep
    exact h

/-- `AppliesAll`'s own lift of `step_now_frame`: a call sequence that
    never includes `.tick` leaves `now` exactly where it started, one
    `Step` at a time. -/
theorem appliesAll_now_frame (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (s s' : AdjudicatorState) (calls : List (Actor × Call))
    (happ : AppliesAll sig appRel s calls s')
    (hnotick : ∀ actor newNow, (actor, Call.tick newNow) ∉ calls) :
    s'.now = s.now := by
  induction calls generalizing s with
  | nil => rw [happ]
  | cons hd rest ih =>
    obtain ⟨actor, call⟩ := hd
    obtain ⟨mid, hstep, hrest⟩ := happ
    have hnotickcall : ∀ newNow, call ≠ Call.tick newNow := by
      intro newNow heq
      exact hnotick actor newNow (heq ▸ List.mem_cons_self)
    have hnotickrest : ∀ actor' newNow, (actor', Call.tick newNow) ∉ rest :=
      fun actor' newNow hc => hnotick actor' newNow (List.mem_cons_of_mem _ hc)
    rw [ih mid hrest hnotickrest, step_now_frame sig appRel actor s mid call hnotickcall hstep]

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
    (before : PoolState) (token : Nat) (pos : Nat × Nat) (pre : CommitmentPreimage)
    (pk : Nat × Nat) (nk r : Nat) (hnpk : pre.npk = npk (masterPublicKey pk nk) r)
    (hmem : (pos, pre) ∈ before.live token)
    (w : TransactWitness N M) (htoken : w.token = token) (hpk : w.publicKey ≠ pk)
    (spendTreeNumber : Nat)
    {rest : List ((Nat × Nat) × CommitmentPreimage)}
    (hRemove : removeAll (before.live w.token) (transactSpentPositions spendTreeNumber w) = some rest) :
    (pos, pre) ∈ rest := by
  have hmemperm : (pos, pre) ∈ transactSpentPositions spendTreeNumber w ++ rest :=
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
theorem payout_outputs_nonzero (exitAllocs : List Allocation) (remainder asset : Nat) (self : Term) (r : Nat) :
    ∀ pre ∈ (exitAllocs.filterMap (fun a =>
        if a.amount = 0 then none else some (⟨a.destination, asset, a.amount⟩ : CommitmentPreimage))) ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]),
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

/-- **The one destructuring of a `PoolOwnedSpendStep`** every
    `preimageOf`-shaped fact about it starts from: the payout-plus-
    remainder batch is valid against `hashCommitment`, and `pool'.
    preimageOf` is `pool.preimageOf` with that batch applied.
    `PoolOwnedSpend_update_preimage_nonzero`, `PoolOwnedSpendStep_frame`,
    `PoolOwnedSpendStep_sets_heldValue`, and `PoolOwnedSpendStep_
    preimageOf_known` each built their own copy of this case split
    (fresh `cid` vs. already-held `cid`) and its own `hrecordseq`; this
    is the ONE copy they now share. -/
theorem PoolOwnedSpendStep_preimageOf_eq
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool') :
    (∀ cp ∈ (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)), hashCommitment cp.2 = cp.1) ∧
    pool'.preimageOf = applyRecords pool.preimageOf
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map
          (fun pre => (commitment pre.npk asset pre.value, pre))) := by
  have hvalid_outputs : ∀ cp ∈ (payoutOutputs ++
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
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
  refine ⟨hvalid_outputs, ?_⟩
  rcases hc0 : holdings asset cid with _ | c0
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _spent', _randomOut, _hNonZero, _hown, htoken, hnewnotes,
      _hroot, _hmark, _hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
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
    rw [← hrecordseq]
    exact congrArg PoolState.preimageOf heq
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _rest, _spent', _randomOut, _hNonZero, _hown, htoken,
      hnewnotes, _hleavesIdx, _hcommit, _hroot, _hremove, _hmark, _hRandomOut, heq⟩ := hmatch
    have hrecordseq : ownedOutputRecords w pub = (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
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
    rw [← hrecordseq]
    exact congrArg PoolState.preimageOf heq

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
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some ((insertTreeNumber pool.closedTrees pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
               insertStartPos pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
             commitment (npk self r) asset remainder)))) qasset qcid = some (qpos, qc) →
      ∃ pre, pool'.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
  intro qasset qcid qpos qc hc
  unfold update at hc
  obtain ⟨hvalid_outputs, hpre0⟩ := PoolOwnedSpendStep_preimageOf_eq pool pool' self asset cid
    remainder r payoutOutputs holdings htokPayout hmatch
  have hrelated : remainder ≠ 0 → commitment (npk self r) asset remainder = qc →
      ∃ pre, pool'.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro hrem hqc
    have hnz : ¬ isZeroPreimage (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) :=
      fun hz => hrem hz.2.1
    have hmemout : (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
          CommitmentPreimage)])) := by
      rw [if_neg hrem]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    have hmemout2 : (qc, (⟨npk self r, asset, remainder⟩ : CommitmentPreimage)) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) := by
      rw [← hqc]
      exact List.mem_map.mpr ⟨_, hmemout, rfl⟩
    refine ⟨⟨npk self r, asset, remainder⟩, ?_, hrem, hqc⟩
    rw [hpre0]
    exact applyRecords_reads hvalid_outputs pool.preimageOf qc
      (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) hmemout2 hnz
  have hunrelated : holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool'.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc := by
    intro hc'
    obtain ⟨pre_old, hpre_old, hval_old, hconsist_old⟩ := hinv qasset qcid qpos qc hc'
    refine ⟨pre_old, ?_, hval_old, hconsist_old⟩
    rw [hpre0]
    exact applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre_old hpre_old hconsist_old
  by_cases heqch : qasset = asset ∧ qcid = cid
  · obtain ⟨ha, hcid⟩ := heqch
    subst ha; subst hcid
    rw [if_pos rfl, if_pos rfl] at hc
    by_cases hrem : remainder = 0
    · rw [if_pos hrem] at hc; exact absurd hc (by simp)
    · rw [if_neg hrem] at hc
      exact hrelated hrem (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hc).2
  · have hc' : holdings qasset qcid = some (qpos, qc) := by
      by_cases ha : qasset = asset
      · subst ha
        by_cases hcid : qcid = cid
        · exact absurd ⟨rfl, hcid⟩ heqch
        · rw [if_pos rfl, if_neg hcid] at hc; exact hc
      · rw [if_neg ha] at hc; exact hc
    exact hunrelated hc'


/-- **The one tail every `PoolOwnedSpendStep_ownedRandom_known` branch
    shares**: once the step's own witness `w`/`pub` are in hand (`N = 0`
    for a fresh `cid`, `N = 1` for an already-held one — the only thing
    that differs between the two call-site branches), both conjuncts
    follow the same way. `PoolOwnedSpendStep_ownedRandom_known` now
    supplies `w`/`pub`/`heqPre`/`heqOR` once per branch and calls this
    ONE proof instead of repeating it. -/
private theorem PoolOwnedSpendStep_ownedRandom_tail {N : Nat}
    (pool pool' : PoolState) (self : Term) (asset : Nat) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (w : TransactOwnedWitness N (payoutOutputs.length + (if remainder = 0 then
      ([] : List CommitmentPreimage) else
        [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length))
    (pub : TransactOwnedPublic N (payoutOutputs.length + (if remainder = 0 then
      ([] : List CommitmentPreimage) else
        [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length))
    (hC : OwnedConstrained w pub)
    (hNonZero : ∀ j, ¬ isZeroPreimage (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage))
    (htoken : w.token = asset)
    (ownedRandom : Fin (if remainder = 0 then ([] : List CommitmentPreimage) else
      [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length → Nat)
    (hnewnotes : ownedNewNotes w = payoutOutputs ++
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]))
    (hdisclose : ∀ j, w.npkOut (Fin.natAdd payoutOutputs.length j) = npk self (ownedRandom j))
    (heqPre : pool'.preimageOf = applyRecords pool.preimageOf (ownedOutputRecords w pub))
    (heqOR : pool'.ownedRandomOf = applyOwnedRecords pool.ownedRandomOf
      ((List.finRange (if remainder = 0 then ([] : List CommitmentPreimage) else
        [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length).map fun j =>
          (pub.commitmentsOut (Fin.natAdd payoutOutputs.length j),
            (⟨self, ownedRandom j⟩ : OwnedDisclosure)))) :
    (∀ qc pre' r', pool.preimageOf qc = some pre' → hashCommitment pre' = qc →
      pre'.npk = npk self r' →
      pool.ownedRandomOf qc = some ⟨self, r'⟩ →
      pool'.ownedRandomOf qc = some ⟨self, r'⟩) ∧
    (remainder ≠ 0 →
      pool'.ownedRandomOf (commitment (npk self r) asset remainder) =
        some ⟨self, r⟩) := by
  have hvalid_oor : ∀ cp ∈ ownedOutputRecords w pub, hashCommitment cp.2 = cp.1 := by
    intro cp hcp
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hcp
    rw [← hj]
    show hashCommitment (⟨w.npkOut j, w.token, w.valueOut j⟩ : CommitmentPreimage) =
      pub.commitmentsOut j
    rw [hC.outputs j]
    rfl
  refine ⟨?_, ?_⟩
  · intro qc pre' r' hpre hconsist hnpk hknown
    have hpre' : pool'.preimageOf qc = some pre' := by
      rw [heqPre]
      exact applyRecords_preserves_known hvalid_oor pool.preimageOf qc pre' hpre hconsist
    rw [heqOR]
    exact applyOwnedRecords_preserves_known (reg := pool'.preimageOf)
      (fun cd hcd => by
        obtain ⟨j, _hjmem, hjeq⟩ := List.mem_map.mp hcd
        refine ⟨⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
          w.valueOut (Fin.natAdd payoutOutputs.length j)⟩, ?_, ?_⟩
        · rw [← hjeq, heqPre]
          exact applyRecords_returns hvalid_oor (List.mem_ofFn.mpr ⟨_, rfl⟩) (hNonZero _)
        · rw [← hjeq]
          exact (hdisclose j).symm)
      pool.ownedRandomOf qc self r' pre' hknown hpre' hnpk
  · intro hrem
    let j0 : Fin (if remainder = 0 then ([] : List CommitmentPreimage) else
        [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length :=
      ⟨0, by simp [if_neg hrem]⟩
    have hj0val : (Fin.natAdd payoutOutputs.length j0).val = payoutOutputs.length := by
      simp [j0]
    have hl2 : (if remainder = 0 then ([] : List CommitmentPreimage) else
        [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])[0]? =
        some (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) := by
      rw [if_neg hrem]; rfl
    have hstep1 : (payoutOutputs ++ (if remainder = 0 then ([] : List CommitmentPreimage) else
        [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]))[payoutOutputs.length]? =
        (if remainder = 0 then ([] : List CommitmentPreimage) else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])[0]? := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hg0 : (ownedNewNotes w)[payoutOutputs.length]? =
        (payoutOutputs ++
          (if remainder = 0 then ([] : List CommitmentPreimage) else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]))[payoutOutputs.length]? :=
      congrArg (fun l => l[payoutOutputs.length]?) hnewnotes
    have hg : (ownedNewNotes w)[payoutOutputs.length]? =
        some (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) :=
      hg0.trans (hstep1.trans hl2)
    have hg2 : (ownedNewNotes w)[payoutOutputs.length]? =
        some (⟨w.npkOut (Fin.natAdd payoutOutputs.length j0), w.token,
          w.valueOut (Fin.natAdd payoutOutputs.length j0)⟩ : CommitmentPreimage) := by
      unfold ownedNewNotes
      rw [List.getElem?_ofFn, dif_pos (hj0val ▸ (Fin.natAdd payoutOutputs.length j0).isLt)]
      congr 2
    rw [hg2] at hg
    have hidx0eq : (⟨w.npkOut (Fin.natAdd payoutOutputs.length j0), w.token,
        w.valueOut (Fin.natAdd payoutOutputs.length j0)⟩ : CommitmentPreimage) =
        (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) := Option.some.inj hg
    have hnpkeq : w.npkOut (Fin.natAdd payoutOutputs.length j0) = npk self r :=
      congrArg CommitmentPreimage.npk hidx0eq
    have hvaleq : w.valueOut (Fin.natAdd payoutOutputs.length j0) = remainder :=
      congrArg CommitmentPreimage.value hidx0eq
    have hdisc0 := hdisclose j0
    rw [hnpkeq] at hdisc0
    obtain ⟨_hselfeq, hrandeq⟩ := npk_inj hdisc0
    have hcOut : pub.commitmentsOut (Fin.natAdd payoutOutputs.length j0) =
        commitment (npk self r) asset remainder := by
      rw [hC.outputs (Fin.natAdd payoutOutputs.length j0), hnpkeq, htoken, hvaleq]
    rw [heqOR]
    exact applyOwnedRecords_reads (reg := pool'.preimageOf)
      (fun cd hcd => by
        obtain ⟨j, _hjmem, hjeq⟩ := List.mem_map.mp hcd
        refine ⟨⟨w.npkOut (Fin.natAdd payoutOutputs.length j), w.token,
          w.valueOut (Fin.natAdd payoutOutputs.length j)⟩, ?_, ?_⟩
        · rw [← hjeq, heqPre]
          exact applyRecords_returns hvalid_oor (List.mem_ofFn.mpr ⟨_, rfl⟩) (hNonZero _)
        · rw [← hjeq]
          exact (hdisclose j).symm)
      pool.ownedRandomOf (commitment (npk self r) asset remainder) ⟨self, r⟩
      (List.mem_map.mpr ⟨j0, List.mem_finRange _, by rw [hcOut, hrandeq]⟩)

/-- `PoolOwnedSpendStep`'s own `ownedRandomOf` update, the `ownedRandomOf`
    sibling of `PoolOwnedSpend_update_preimage_nonzero`: an already-known
    adjudicator-owned disclosure survives the step, and — when
    `remainder ≠ 0` — the FRESH remainder note is disclosed directly.
    What `unbeatable_pays`'s own strategy needs to carry a channel's
    held note's own disclosure across the `.transfer` call that spends
    it, and to name the fresh remainder note's own disclosure directly.
    Both branches (fresh `cid` vs. already-held `cid`) share ONE proof,
    `PoolOwnedSpendStep_ownedRandom_tail`. -/

theorem PoolOwnedSpendStep_ownedRandom_known
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool') :
    (∀ qc pre' r', pool.preimageOf qc = some pre' → hashCommitment pre' = qc →
      pre'.npk = npk self r' →
      pool.ownedRandomOf qc = some ⟨self, r'⟩ →
      pool'.ownedRandomOf qc = some ⟨self, r'⟩) ∧
    (remainder ≠ 0 →
      pool'.ownedRandomOf (commitment (npk self r) asset remainder) =
        some ⟨self, r⟩) := by
  rcases hc0 : holdings asset cid with _ | c0
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _spent', ownedRandom, hNonZero, _hown, htoken, hnewnotes,
      _hroot, _hmark, hdisclose, heq⟩ := hmatch
    exact PoolOwnedSpendStep_ownedRandom_tail pool pool' self asset remainder r payoutOutputs
      w pub hC hNonZero htoken ownedRandom hnewnotes hdisclose
      (congrArg PoolState.preimageOf heq) (congrArg PoolState.ownedRandomOf heq)
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, hC, _rest, _spent', ownedRandom, hNonZero, _hown, htoken, hnewnotes,
      _hleavesIdx, _hcommit, _hroot, _hremove, _hmark, hdisclose, heq⟩ := hmatch
    exact PoolOwnedSpendStep_ownedRandom_tail pool pool' self asset remainder r payoutOutputs
      w pub hC hNonZero htoken ownedRandom hnewnotes hdisclose
      (congrArg PoolState.preimageOf heq) (congrArg PoolState.ownedRandomOf heq)

/-- One `PoolOwnedSpendStep`-backed holdings update (the shape `.transfer`
    and `bulkTransferFold` both use) leaves every OTHER `(asset, cid)`
    pair's own held value UNCHANGED: `update`/`update` only ever touch
    the ONE pair this step names, and `applyRecords_preserves_known`
    carries an already-known preimage through the payout batch
    unscathed. The `PoolOwnedSpendStep`-backed sibling of
    `deposit_frame`, what A-13 needs to rule out `.transfer`/bulk calls
    on a DIFFERENT channel from lowering `heldValue` at the named one. -/
theorem PoolOwnedSpendStep_frame
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc)
    (qasset : Nat) (qcid : Term) (hne : (qasset, qcid) ≠ (asset, cid)) :
    (match (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some ((insertTreeNumber pool.closedTrees pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
               insertStartPos pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
             commitment (npk self r) asset remainder)))) qasset qcid with
      | none => (0 : Nat)
      | some (_, c) => ((pool'.preimageOf c).map CommitmentPreimage.value).getD 0) =
    (match holdings qasset qcid with
      | none => 0
      | some (_, c) => ((pool.preimageOf c).map CommitmentPreimage.value).getD 0) := by
  obtain ⟨hvalid_outputs, hpre0⟩ := PoolOwnedSpendStep_preimageOf_eq pool pool' self asset cid
    remainder r payoutOutputs holdings htokPayout hmatch
  have hupd : (update holdings asset
      (update (holdings asset) cid
         (if remainder = 0 then none
         else some ((insertTreeNumber pool.closedTrees pool.leaves
               (payoutOutputs ++ (if remainder = 0 then [] else
                 [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
             insertStartPos pool.leaves
               (payoutOutputs ++ (if remainder = 0 then [] else
                 [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
               (payoutOutputs ++ (if remainder = 0 then [] else
                 [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
           commitment (npk self r) asset remainder)))) qasset qcid = holdings qasset qcid := by
    unfold update
    by_cases ha : qasset = asset
    · subst ha
      rw [if_pos rfl]
      by_cases hcid : qcid = cid
      · exact absurd (by rw [hcid]) hne
      · rw [if_neg hcid]
    · rw [if_neg ha]
  rw [hupd]
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
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool') :
    (match (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some ((insertTreeNumber pool.closedTrees pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
               insertStartPos pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
             commitment (npk self r) asset remainder)))) asset cid with
      | none => (0 : Nat)
      | some (_, c) => ((pool'.preimageOf c).map CommitmentPreimage.value).getD 0) = remainder := by
  by_cases hrem : remainder = 0
  · unfold update
    simp [hrem]
  · obtain ⟨hvalid_outputs, hpre0⟩ := PoolOwnedSpendStep_preimageOf_eq pool pool' self asset cid
      remainder r payoutOutputs holdings htokPayout hmatch
    have hnz : ¬ isZeroPreimage (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) :=
      fun hz => hrem hz.2.1
    have hmemout : (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
          CommitmentPreimage)])) := by
      rw [if_neg hrem]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    have hmemout2 : (commitment (npk self r) asset remainder,
        (⟨npk self r, asset, remainder⟩ : CommitmentPreimage)) ∈
        (payoutOutputs ++
        (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ :
          CommitmentPreimage)])).map
        (fun pre => (commitment pre.npk asset pre.value, pre)) :=
      List.mem_map.mpr ⟨_, hmemout, rfl⟩
    unfold update
    rw [if_pos rfl, if_pos rfl]
    rw [if_neg hrem]
    dsimp only
    rw [hpre0]
    rw [applyRecords_reads hvalid_outputs pool.preimageOf (commitment (npk self r) asset
      remainder) (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) hmemout2 hnz]
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

/-- `bulkTransferFold`'s own frame fact: every channel OTHER than `cid`
    (the one the whole fold pays out) keeps every asset's own held value
    UNCHANGED — one application of `PoolOwnedSpendStep_frame` per asset
    in the fold's own list, carried forward by induction, paired with
    `PoolOwnedSpend_update_preimage_nonzero` to keep the invariant alive
    across the recursion. What A-13 needs for the two bulk calls. -/
theorem bulkTransferFold_frame (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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

/-- `withTreePositionsFrom` splits across `++`, the tree-tagged counterpart of
    `withPositionsFrom_append`, composing it with the tag-preserving `map`. -/
theorem withTreePositionsFrom_append {α : Type} (treeNumber start : Nat) (l1 l2 : List α) :
    withTreePositionsFrom treeNumber start (l1 ++ l2) =
      withTreePositionsFrom treeNumber start l1 ++
        withTreePositionsFrom treeNumber (start + l1.length) l2 := by
  unfold withTreePositionsFrom
  rw [withPositionsFrom_append, List.map_append]

/-- `withTreePositionsFrom` of a one-element list tags that element with `start`
    directly — the base case `withTreePositionsFrom_append` needs to pin a batch's
    LAST element to its exact landing key. -/
theorem withTreePositionsFrom_singleton {α : Type} (treeNumber start : Nat) (a : α) :
    withTreePositionsFrom treeNumber start [a] = [((treeNumber, start), a)] := by
  unfold withTreePositionsFrom withPositionsFrom
  rfl

/-- A freshly-inserted batch's own tree, read off BEFORE the insertion, already has
    exactly `insertStartPos` many leaves (`insertStartPos_eq_leavesAt_length`); read off
    AFTER the insertion, it has `insertStartPos + outputs.length` many
    (`insertResult_leavesAt_target_length`, composed with `List.length_map` since the
    batch pushed is `outputs.map hashCommitment`, not `outputs` itself). The two bounds
    `PoolOwnedSpend_update_position_live` needs to place a batch's own positions past
    every position any earlier holding could have named, and within the tree's own new
    length. -/
theorem PoolOwnedSpendStep_fresh_position_bounds
    (closedTrees : List TreeState) (curLeaves curRoots : List Term)
    (outputs : List CommitmentPreimage) :
    (PoolState.leavesAt
        (insertResult closedTrees curLeaves curRoots (outputs.map hashCommitment)).1
        (insertResult closedTrees curLeaves curRoots (outputs.map hashCommitment)).2.1
        (insertResult closedTrees curLeaves curRoots (outputs.map hashCommitment)).2.2
        (insertTreeNumber closedTrees curLeaves outputs.length)).length
      = insertStartPos curLeaves outputs.length + outputs.length ∧
    (PoolState.leavesAt closedTrees curLeaves curRoots
        (insertTreeNumber closedTrees curLeaves outputs.length)).length
      = insertStartPos curLeaves outputs.length := by
  constructor
  · have h := insertResult_leavesAt_target_length closedTrees curLeaves curRoots
      (outputs.map hashCommitment)
    rw [List.length_map] at h
    exact h
  · exact (insertStartPos_eq_leavesAt_length closedTrees curLeaves curRoots outputs.length).symm


/-- The branch-independent core of `PoolOwnedSpend_update_position_live`: given the
    `.live`/tree-length facts common to BOTH `PoolOwnedSpendStep`'s "none" and "some"
    branches (`hliveT`/`hge`/`hlevA'`), plus a proof that an untouched key's OLD live
    entry survives into whichever `baseline` list that branch actually appends onto
    (`hbaseline` — trivial for "none", a `removeAll` argument for "some"), the
    position-live update fact holds uniformly. Lets the two branches of
    `PoolOwnedSpend_update_position_live` share one proof of the touched-key and
    bound/uniqueness reasoning, which never depends on which branch produced
    `pool'`. -/
theorem PoolOwnedSpend_update_position_live_core
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = ownerField ∧ pre.npk = npk ownerField r) ∨
          ∃ r, pre.npk = npk self r)) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos))
    (baseline : List ((Nat × Nat) × CommitmentPreimage))
    (hliveT : ∀ t, pool'.live t = if t = asset
        then withTreePositionsFrom (insertTreeNumber pool.closedTrees pool.leaves
              (payoutOutputs ++ (if remainder = 0 then [] else
                [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length)
            (insertStartPos pool.leaves
              (payoutOutputs ++ (if remainder = 0 then [] else
                [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length)
            (payoutOutputs ++ (if remainder = 0 then [] else
              [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])) ++ baseline
        else pool.live t)
    (hge : ∀ tn, (pool.leavesAt' tn).length ≤ (pool'.leavesAt' tn).length)
    (hlevA' : ∀ tn, pool'.leavesAt' tn = PoolState.leavesAt
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).1
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.1
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.2 tn)
    (hbaseline : ∀ qasset'' qcid'' qpos qc'', holdings qasset'' qcid'' = some (qpos, qc'') →
      (qasset'', qcid'') ≠ (asset, cid) → ∀ qpre, (qpos, qpre) ∈ pool.live asset →
      (qpos, qpre) ∈ baseline) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some ((insertTreeNumber pool.closedTrees pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
               insertStartPos pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
             commitment (npk self r) asset remainder)))) qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool'.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = ownerField ∧ pre.npk = npk ownerField r) ∨
          ∃ r, pre.npk = npk self r)) ∧
      qpos.2 < (pool'.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', (update holdings asset
          (update (holdings asset) cid
            (if remainder = 0 then none
             else some ((insertTreeNumber pool.closedTrees pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                 insertStartPos pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
               commitment (npk self r) asset remainder)))) qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  intro qasset qcid qpos qc hc
  unfold update at hc
  by_cases heqch : qasset = asset ∧ qcid = cid
  · obtain ⟨ha, hcidEq⟩ := heqch
    rw [ha, hcidEq] at hc ⊢
    rw [if_pos rfl, if_pos rfl] at hc
    by_cases hrem : remainder = 0
    · rw [if_pos hrem] at hc; exact absurd hc (by simp)
    · simp only [if_neg hrem] at hc
      rw [if_neg hrem] at hliveT hlevA'
      injection hc with hc1
      injection hc1 with hqpos hqcEq
      subst hqpos; subst hqcEq
      have hlen1 : 1 ≤ (payoutOutputs ++
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length := by simp
      have hb1 : (pool'.leavesAt' (insertTreeNumber pool.closedTrees pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length)).length
          = insertStartPos pool.leaves
              (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length +
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length := by
        rw [hlevA']
        have h := insertResult_leavesAt_target_length pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).map
            hashCommitment)
        rw [List.length_map] at h
        exact h
      have hb2 : (pool.leavesAt' (insertTreeNumber pool.closedTrees pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length)).length
          = insertStartPos pool.leaves
              (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length := by
        unfold PoolState.leavesAt'
        exact (insertStartPos_eq_leavesAt_length pool.closedTrees pool.leaves pool.roots
          (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length).symm
      refine ⟨⟨(⟨npk self r, asset, remainder⟩ : CommitmentPreimage), ?_, rfl, Or.inr ⟨r, rfl⟩⟩,
        ?_, ?_⟩
      · rw [hliveT, if_pos rfl]
        apply List.mem_append_left
        have hsplit := withTreePositionsFrom_append
          (insertTreeNumber pool.closedTrees pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length)
          (insertStartPos pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length)
          payoutOutputs [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]
        rw [hsplit, withTreePositionsFrom_singleton]
        have hposeq : insertStartPos pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length +
            payoutOutputs.length
            = insertStartPos pool.leaves
              (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length +
              (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length - 1 := by
          simp
        rw [hposeq]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · rw [hb1]; omega
      · intro qasset' qcid' qpos' qc' hc' hne'
        have hc'' : holdings qasset' qcid' = some (qpos', qc') := by
          unfold update at hc'
          by_cases ha2 : qasset' = asset
          · subst ha2
            rw [if_pos rfl] at hc'
            by_cases hcid2 : qcid' = cid
            · exact absurd (by rw [hcid2]) hne'
            · rwa [if_neg hcid2] at hc'
          · rwa [if_neg ha2] at hc'
        have h2 := (hinv qasset' qcid' qpos' qc' hc'').2.1
        intro hcontra
        rw [hcontra] at h2
        rw [hb2] at h2
        omega
  · have hc'' : holdings qasset qcid = some (qpos, qc) := by
      by_cases ha : qasset = asset
      · subst ha
        rw [if_pos rfl] at hc
        by_cases hcid : qcid = cid
        · exact absurd ⟨rfl, hcid⟩ heqch
        · rwa [if_neg hcid] at hc
      · rwa [if_neg ha] at hc
    have hne_prod : (qasset, qcid) ≠ (asset, cid) :=
      fun h => heqch ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    obtain ⟨⟨pre, hmemOld, hhashOld, hownOld⟩, hboundOld, huniqOld⟩ := hinv qasset qcid qpos qc hc''
    have hboundNew : qpos.2 < (pool'.leavesAt' qpos.1).length := by
      have h := hge qpos.1
      omega
    have hneFresh : qpos ≠ (insertTreeNumber pool.closedTrees pool.leaves
          (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length,
        insertStartPos pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length +
          (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length - 1) := by
      intro hcontra
      have hqp1 : qpos.1 = insertTreeNumber pool.closedTrees pool.leaves
          (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length :=
        congrArg Prod.fst hcontra
      have hqp2 : qpos.2 = insertStartPos pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length +
          (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length - 1 :=
        congrArg Prod.snd hcontra
      rw [hqp1] at hboundOld
      have hb2 : (pool.leavesAt' (insertTreeNumber pool.closedTrees pool.leaves
            (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length)).length
          = insertStartPos pool.leaves
              (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length := by
        unfold PoolState.leavesAt'
        exact (insertStartPos_eq_leavesAt_length pool.closedTrees pool.leaves pool.roots
          (payoutOutputs ++ [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length).symm
      rw [hb2] at hboundOld
      have hlen1 : 1 ≤ (payoutOutputs ++
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)]).length := by simp
      omega
    have huniqNew : ∀ qasset' qcid' qpos' qc', (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some ((insertTreeNumber pool.closedTrees pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
               insertStartPos pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
             commitment (npk self r) asset remainder)))) qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos := by
      intro qasset' qcid' qpos' qc' hc' hne'
      by_cases hother : (qasset', qcid') = (asset, cid)
      · injection hother with ha2 hcid2
        rw [ha2, hcid2] at hc'
        unfold update at hc'
        rw [if_pos rfl, if_pos rfl] at hc'
        by_cases hrem : remainder = 0
        · rw [if_pos hrem] at hc'; exact absurd hc' (by simp)
        · simp only [if_neg hrem] at hc'
          injection hc' with hc'1
          injection hc'1 with hqp' _hqc'
          rw [← hqp']
          exact hneFresh.symm
      · have hc2 : holdings qasset' qcid' = some (qpos', qc') := by
          unfold update at hc'
          by_cases ha2 : qasset' = asset
          · subst ha2
            rw [if_pos rfl] at hc'
            by_cases hcid2 : qcid' = cid
            · exact absurd (by rw [hcid2]) hother
            · rwa [if_neg hcid2] at hc'
          · rwa [if_neg ha2] at hc'
        exact huniqOld qasset' qcid' qpos' qc' hc2 hne'
    by_cases hqa : qasset = asset
    · refine ⟨⟨pre, ?_, hhashOld, hownOld⟩, hboundNew, huniqNew⟩
      rw [hliveT, hqa, if_pos rfl]
      exact List.mem_append_right _
        (hbaseline asset qcid qpos qc (hqa ▸ hc'') (hqa ▸ hne_prod) pre (hqa ▸ hmemOld))
    · exact ⟨⟨pre, by rw [hliveT, if_neg hqa]; exact hmemOld, hhashOld, hownOld⟩, hboundNew, huniqNew⟩

/-- One `PoolOwnedSpendStep`-backed holdings update's effect on the
    `holdings_position_live_step` invariant — the position-live sibling
    of `PoolOwnedSpend_update_preimage_nonzero`, generalizing `.transfer`'s
    own reasoning so `bulkTransferFold`'s induction can reuse it once per
    asset instead of re-deriving it. -/
theorem PoolOwnedSpend_update_position_live
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = ownerField ∧ pre.npk = npk ownerField r) ∨
          ∃ r, pre.npk = npk self r)) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some ((insertTreeNumber pool.closedTrees pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
               insertStartPos pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
             commitment (npk self r) asset remainder)))) qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool'.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, self = ownerField ∧ pre.npk = npk ownerField r) ∨
          ∃ r, pre.npk = npk self r)) ∧
      qpos.2 < (pool'.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', (update holdings asset
          (update (holdings asset) cid
            (if remainder = 0 then none
             else some ((insertTreeNumber pool.closedTrees pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                 insertStartPos pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
               commitment (npk self r) asset remainder)))) qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  rcases hc0 : holdings asset cid with _ | c0
  · simp only [hc0] at hmatch
    obtain ⟨_w, _pub, _hM, _hC, _spent', _ownedOutputs, _hNonZero, _hself, _htoken, _hnewnotes,
      _hroot, _hmark, _hRandomOut, heq⟩ := hmatch
    have hliveT : ∀ t, pool'.live t = if t = asset
        then withTreePositionsFrom (insertTreeNumber pool.closedTrees pool.leaves
              (payoutOutputs ++ (if remainder = 0 then [] else
                [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length)
            (insertStartPos pool.leaves
              (payoutOutputs ++ (if remainder = 0 then [] else
                [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length)
            (payoutOutputs ++ (if remainder = 0 then [] else
              [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])) ++ pool.live asset
        else pool.live t := fun t => by
          rw [heq]
          by_cases ht : t = asset <;> simp [ht, List.length_append]
    have hclosed : pool'.closedTrees = (insertResult pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).1 := by
      rw [heq]
    have hleaves : pool'.leaves = (insertResult pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.1 := by
      rw [heq]
    have hroots : pool'.roots = (insertResult pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.2 := by
      rw [heq]
    have hlevA' : ∀ tn, pool'.leavesAt' tn = PoolState.leavesAt
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).1
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.1
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.2 tn := by
      intro tn
      unfold PoolState.leavesAt'
      rw [hclosed, hleaves, hroots]
    have hge : ∀ tn, (pool.leavesAt' tn).length ≤ (pool'.leavesAt' tn).length := by
      intro tn
      rw [hlevA']
      exact insertResult_leavesAt_length_ge pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment) tn
    exact PoolOwnedSpend_update_position_live_core pool pool' self asset cid remainder r
      payoutOutputs holdings hinv (pool.live asset) hliveT hge hlevA'
      (fun _ _ _ _ _ _ qpre hmem => hmem)
  · simp only [hc0] at hmatch
    obtain ⟨w, pub, _hM, _hC, rest, _spent', _ownedOutputs, _hNonZero, _hself, _htoken,
      _hnewnotes, hleavesIdx, _hcommit, _hroot, hremove, _hmark, _hRandomOut, heq⟩ := hmatch
    have hliveT : ∀ t, pool'.live t = if t = asset
        then withTreePositionsFrom (insertTreeNumber pool.closedTrees pool.leaves
              (payoutOutputs ++ (if remainder = 0 then [] else
                [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length)
            (insertStartPos pool.leaves
              (payoutOutputs ++ (if remainder = 0 then [] else
                [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length)
            (payoutOutputs ++ (if remainder = 0 then [] else
              [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])) ++ rest
        else pool.live t := fun t => by rw [heq]; simp only [List.length_append]
    have hclosed : pool'.closedTrees = (insertResult pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).1 := by
      rw [heq]
    have hleaves : pool'.leaves = (insertResult pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.1 := by
      rw [heq]
    have hroots : pool'.roots = (insertResult pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.2 := by
      rw [heq]
    have hlevA' : ∀ tn, pool'.leavesAt' tn = PoolState.leavesAt
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).1
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.1
        (insertResult pool.closedTrees pool.leaves pool.roots
          ((payoutOutputs ++ (if remainder = 0 then [] else
            [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment)).2.2 tn := by
      intro tn
      unfold PoolState.leavesAt'
      rw [hclosed, hleaves, hroots]
    have hge : ∀ tn, (pool.leavesAt' tn).length ≤ (pool'.leavesAt' tn).length := by
      intro tn
      rw [hlevA']
      exact insertResult_leavesAt_length_ge pool.closedTrees pool.leaves pool.roots
        ((payoutOutputs ++ (if remainder = 0 then [] else
          [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).map hashCommitment) tn
    have hwanted1 : ∀ y ∈ ownedSpentPositions c0.1.1 pub w, y.1 = c0.1 := by
      intro y hy
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hy
      have hi0 : i = 0 := by omega
      rw [← hi, hi0]
      show (c0.1.1, w.leavesIndices 0) = c0.1
      rw [hleavesIdx]
    exact PoolOwnedSpend_update_position_live_core pool pool' self asset cid remainder r
      payoutOutputs holdings hinv rest hliveT hge hlevA'
      (fun qasset'' qcid'' qpos qc'' hcall hne'' qpre hmem => by
        have hqposNe : qpos ≠ c0.1 := by
          have h3 := (hinv asset cid c0.1 c0.2 hc0).2.2
          exact h3 qasset'' qcid'' qpos qc'' hcall hne''
        have hnotwanted : (qpos, qpre) ∉ ownedSpentPositions c0.1.1 pub w := by
          intro hbad
          exact hqposNe (hwanted1 _ hbad)
        rcases List.mem_append.mp ((removeAll_perm hremove).mem_iff.mp hmem) with hin | hin
        · exact absurd hin hnotwanted
        · exact hin)

/-- One `PoolOwnedSpendStep`'s effect on `PoolState.notedValue`: spending
    one channel's holding and paying it out never changes the pool's own
    per-token noted total — generalizes `notedValue_conserved`'s own
    `.transfer`/`.deposit` reasoning (`Safety.lean`) so `bulkTransferFold`'s
    induction can reuse it once per asset instead of re-deriving it. -/
theorem PoolOwnedSpendStep_notedValue_conserved
    (pool pool' : PoolState) (self : Term) (asset : Nat) (nullified : Option ((Nat × Nat) × Term))
    (payoutOutputs ownedPreimages : List CommitmentPreimage)
    (hmatch : PoolOwnedSpendStep pool self asset nullified payoutOutputs ownedPreimages pool') :
    ∀ token, pool'.notedValue token = pool.notedValue token := by
  intro token
  unfold PoolOwnedSpendStep at hmatch
  unfold PoolState.notedValue
  rcases nullified with _ | c0
  · obtain ⟨w, pub, hM, hC, spent', ownedOutputs, hNonZero, hself, htoken, hnewnotes,
      hroot, hmark, hRandomOut, heq⟩ := hmatch
    rw [heq]
    dsimp only
    simp only [← List.length_append]
    by_cases ht : token = asset
    · rw [ht]
      rw [if_pos rfl]
      have hbal := transactOwned_value_conserved w pub (by omega) hM hC
      have hvalin0 : List.ofFn w.valueIn = ([] : List Nat) := by simp
      rw [hvalin0] at hbal
      simp only [listSum] at hbal
      have hvoeq : (ownedNewNotes w).map CommitmentPreimage.value = List.ofFn w.valueOut := by
        unfold ownedNewNotes
        rw [List.map_ofFn]
        rfl
      have hpos := withTreePositionsFrom_map CommitmentPreimage.value
        (insertTreeNumber pool.closedTrees pool.leaves
          (payoutOutputs ++ ownedPreimages).length)
        (insertStartPos pool.leaves (payoutOutputs ++ ownedPreimages).length)
        (payoutOutputs ++ ownedPreimages)
      rw [List.map_append, listSum_append, hpos, ← hnewnotes, hvoeq]
      omega
    · rw [if_neg ht]
  · obtain ⟨w, pub, hM, hC, rest, spent', ownedOutputs, hNonZero, hself, htoken,
      hnewnotes, hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hmatch
    rw [heq]
    dsimp only
    simp only [← List.length_append]
    by_cases ht : token = asset
    · rw [ht]
      rw [if_pos rfl]
      have hsum := removeAll_sum (fun p => p.2.value) hremove
      have hbal : listSum ((ownedSpentPositions c0.1.fst pub w).map (fun p => p.2.value)) =
          listSum ((ownedNewNotes w).map CommitmentPreimage.value) :=
        transactOwned_balance c0.1.fst (by omega) hM hC
      have hpos := withTreePositionsFrom_map CommitmentPreimage.value
        (insertTreeNumber pool.closedTrees pool.leaves
          (payoutOutputs ++ ownedPreimages).length)
        (insertStartPos pool.leaves (payoutOutputs ++ ownedPreimages).length)
        (payoutOutputs ++ ownedPreimages)
      rw [List.map_append, listSum_append, hpos, ← hnewnotes]
      rw [← hbal]
      exact hsum.symm
    · rw [if_neg ht]

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
theorem PoolOwnedSpendStep_preserves_user_note {pool pool' : PoolState} (selfInputs : List Term)
    (token : Nat) (nullified : Option ((Nat × Nat) × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage)
    (hstep : PoolOwnedSpendStep pool (Term.keccak selfInputs) token nullified payoutPreimages
      ownedPreimages pool')
    (t : Nat) (pos : Nat × Nat) (pre : CommitmentPreimage) (pk : Nat × Nat) (nk r : Nat)
    (hnpk : pre.npk = npk (masterPublicKey pk nk) r)
    (hmem : (pos, pre) ∈ pool.live t) :
    (pos, pre) ∈ pool'.live t := by
  unfold PoolOwnedSpendStep at hstep
  by_cases ht : t = token
  · rcases nullified with _ | c0
    · obtain ⟨w, pub, hM, hC, spent', ownedOutputs, hNonZero, hself, htoken,
        hnewnotes, hroot, hmark, hRandomOut, heq⟩ := hstep
      rw [heq]
      dsimp only
      show (pos, pre) ∈ (if t = token then _ else pool.live t)
      rw [if_pos ht]
      exact List.mem_append_right _ hmem
    · obtain ⟨w, pub, hM, hC, rest, spent', ownedOutputs, hNonZero, hself, htoken,
        hnewnotes, hleavesIdx, hcommit, hroot, hremove, hmark, hRandomOut, heq⟩ := hstep
      rw [heq]
      dsimp only
      show (pos, pre) ∈ (if t = token then _ else pool.live t)
      rw [if_pos ht]
      apply List.mem_append_right
      have hnotwanted : (pos, pre) ∉ ownedSpentPositions c0.1.fst pub w := by
        intro hbad
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hbad
        have hi0 : i = 0 := by omega
        rw [hi0] at hi
        have hpre_eq : pre = (⟨npk pub.ownerField (w.randomIn 0), w.token, w.valueIn 0⟩ :
            CommitmentPreimage) := (congrArg Prod.snd hi).symm
        have hnpk2 : pre.npk = npk pub.ownerField (w.randomIn 0) := by rw [hpre_eq]
        rw [← hself] at hnpk2
        rw [hnpk] at hnpk2
        exact user_npk_ne_contract_npk hnpk2
      rcases List.mem_append.mp ((removeAll_perm hremove).mem_iff.mp (ht ▸ hmem)) with hin | hin
      · exact absurd hin hnotwanted
      · exact hin
  · rcases nullified with _ | ⟨npos, c⟩
    · obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hself2, _htoken,
        hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hstep
      rw [heq]
      dsimp only
      show (pos, pre) ∈ (if t = token then _ else pool.live t)
      rw [if_neg ht]; exact hmem
    · obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hself2, _htoken,
        hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hstep
      rw [heq]
      dsimp only
      show (pos, pre) ∈ (if t = token then _ else pool.live t)
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
theorem PoolOwnedSpendStep_live_frame {pool pool' : PoolState} (self : Term) (token : Nat)
    (nullified : Option ((Nat × Nat) × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage)
    (hstep : PoolOwnedSpendStep pool self token nullified payoutPreimages ownedPreimages pool')
    (t : Nat) (pos : Nat × Nat) (pre : CommitmentPreimage) (ht : t ≠ token)
    (hmem : (pos, pre) ∈ pool.live t) :
    (pos, pre) ∈ pool'.live t := by
  unfold PoolOwnedSpendStep at hstep
  rcases nullified with _ | ⟨npos, c⟩
  · obtain ⟨w, pub, hM, hC, spent', _randomOut, _hNonZero, _hself2, _htoken,
      hnewnotes, _hroot, _hmarkspent, _hRandomOut, heq⟩ := hstep
    rw [heq]
    dsimp only
    show (pos, pre) ∈ (if t = token then _ else pool.live t)
    rw [if_neg ht]; exact hmem
  · obtain ⟨w, pub, hM, hC, rest, spent', _randomOut, _hNonZero, _hself2, _htoken,
      hnewnotes, _hleaf0, _hceq, _hroot, hremove, _hmarkspent, _hRandomOut, heq⟩ := hstep
    rw [heq]
    dsimp only
    show (pos, pre) ∈ (if t = token then _ else pool.live t)
    rw [if_neg ht]; exact hmem

/-- `bulkTransferFold`'s own invariant for `PoolOwnedSpendStep_preserves_
    user_note`: one application per asset in the fold's own list,
    carried forward by induction — the user-note-liveness sibling of
    `bulkTransferFold_position_live`. -/
theorem bulkTransferFold_preserves_user_note (selfInputs : List Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
    bulkTransferFold (Term.keccak selfInputs) cid outcome pool holdings newOutcome poolF holdingsF →
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
      exact PoolOwnedSpendStep_preserves_user_note selfInputs exit.asset _ _ _ hmatch t pos pre pk nk r
        hnpk hmem

/-- `bulkTransferFold`'s own invariant for `PoolOwnedSpendStep_live_
    frame`: one application per asset in the fold's own list, carried
    forward by induction — the token-disjoint sibling of
    `bulkTransferFold_preserves_user_note` (that one needs the note to
    be user-keyed; this one needs its OWN token absent from the rest
    of the fold's own asset list, no ownership fact at all). What
    `bulkTransferFold_index_payout` needs to carry a just-minted note
    at ONE asset's own token through every LATER asset's own spend. -/
theorem bulkTransferFold_live_frame (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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
theorem bulkTransferFold_notedValue_conserved (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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
    (t : Nat) (pos : Nat × Nat) (pre : CommitmentPreimage) (hnpk : pre.npk = npk (masterPublicKey pk nk) r)
    (hmem : (pos, pre) ∈ s.pool.live t) :
    (pos, pre) ∈ s'.pool.live t := by
  cases call with
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_hcfg, _hheld, _hext, _hpos', hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, spendTreeNumber, treeNumber, position, midPool, hdstep, hpoolsigned,
      hmatch⟩ := hinner
    obtain ⟨r0, hown, hcommit, htoken, htreeNumber, hposition, hN, hM, hC, rest, spent', records,
      hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
    have hnotspent : (pos, pre) ∉ transactSpentPositions spendTreeNumber w := by
      intro hsp
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hsp
      have hpreeq : pre = (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j),
          w.token, w.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
      have hnpkeq2 : npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j) =
          npk (masterPublicKey pk nk) r :=
        (congrArg CommitmentPreimage.npk hpreeq).symm.trans hnpk
      have hmpkeq : masterPublicKey w.publicKey w.nullifyingKey = masterPublicKey pk nk :=
        (Term.hash2_inj hnpkeq2).1
      obtain ⟨h1, h2, _h3⟩ := Term.hash3_inj hmpkeq
      have hwpk : w.publicKey = pk := Prod.ext (Term.val.inj h1) (Term.val.inj h2)
      have hsigned : s0.poolSignedBy pk (msgHashOf pub) := by
        rw [← hsrow0, ← hwpk]; exact hpoolsigned
      exact hhonestPool (msgHashOf pub) hsigned w pub rfl hC hwpk j hnpkeq2
    rcases hh : s.holdings asset channelId with _ | oldHolding
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, _hholdseq⟩ := hmatch
      rw [hpoolEq, heq]
      dsimp only
      by_cases ht : t = w.token
      · subst ht
        rw [if_pos rfl]
        have hmemperm : (pos, pre) ∈ transactSpentPositions spendTreeNumber w ++ rest :=
          (removeAll_perm hRemove).mem_iff.mp hmem
        have hmemrest : (pos, pre) ∈ rest := (List.mem_append.mp hmemperm).resolve_left hnotspent
        exact List.mem_append_right _ hmemrest
      · rw [if_neg ht]; exact hmem
    · obtain ⟨⟨_oldTreeNum, _oldPosNat⟩, oldHoldingVal⟩ := oldHolding
      rw [hh] at hmatch
      obtain ⟨merged, mergeSpendTreeNumber, mergedTreeNumber, mergedPos, hmergestep, _hholdseq⟩ := hmatch
      obtain ⟨_hmergedTN, _hmergedPosEq, w', pub', hC', rest', _spent'', _r', randomOut', _hNonZero',
        hself', _htoken', _hnpkOut0', _hmergedEq, _hleaf0', _hleaf1', _hcommitOld', _hcommitNew',
        _holdTN', _hnewTN', _hroot', hremove', _hnullify', _hrandomOut', heq'⟩ := hmergestep
      have hmidlive : (pos, pre) ∈ midPool.live t := by
        rw [heq]
        dsimp only
        by_cases ht : t = w.token
        · subst ht
          rw [if_pos rfl]
          have hmemperm : (pos, pre) ∈ transactSpentPositions spendTreeNumber w ++ rest :=
            (removeAll_perm hRemove).mem_iff.mp hmem
          exact List.mem_append_right _ ((List.mem_append.mp hmemperm).resolve_left hnotspent)
        · rw [if_neg ht]; exact hmem
      have hnotspent' : (pos, pre) ∉ ownedSpentPositions mergeSpendTreeNumber pub' w' := by
        intro hbad
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hbad
        have hpreeq' : pre = (⟨npk pub'.ownerField (w'.randomIn j), w'.token, w'.valueIn j⟩ :
            CommitmentPreimage) := (congrArg Prod.snd hj).symm
        have hnpk2 : pre.npk = npk pub'.ownerField (w'.randomIn j) := by rw [hpreeq']
        rw [← hself'] at hnpk2
        exact user_npk_ne_contract_npk (addrInputs := s.selfInputs) (hnpk.symm.trans hnpk2)
      rw [heq']
      dsimp only
      by_cases ht : t = asset
      · subst ht
        rw [if_pos rfl]
        have hmemperm' : (pos, pre) ∈ ownedSpentPositions mergeSpendTreeNumber pub' w' ++ rest' :=
          (removeAll_perm hremove').mem_iff.mp hmidlive
        exact List.mem_append_right _ ((List.mem_append.mp hmemperm').resolve_left hnotspent')
      · rw [if_neg ht]; exact hmidlive
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, _, _⟩ := hstep
    rw [hpoolEq]; exact hmem
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, _, _⟩ := hstep
    rw [hpoolEq]; exact hmem
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, _, _⟩ := hstep
    rw [hpoolEq]; exact hmem
  | transfer assetIndex cid claimedStateHash outcome indices =>
    obtain ⟨hidx, _hmode, _hsh, _hoh, _hstrict, hinner, _hcfg, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨_hguarantee, hrest⟩ := hinner
    obtain ⟨r0, hmatch, _hholdseq, _hchanseq⟩ := hrest
    exact PoolOwnedSpendStep_preserves_user_note s.selfInputs (outcome.get ⟨assetIndex, hidx⟩).asset _ _ _
      hmatch t pos pre pk nk r hnpk hmem
  | reclaim sourceChannelId sourceOutcome sourceAssetIndex indexOfTargetInSource targetOutcome
      targetAssetIndex claimedTargetStateHash =>
    obtain ⟨_, _, _, _, _, _, hpoolEq, _, _⟩ := hstep
    rw [hpoolEq]; exact hmem
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_preserves_user_note s.selfInputs channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold t pos pre pk nk r hnpk hmem
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_preserves_user_note s.selfInputs (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold t pos pre pk nk r hnpk hmem
  | tick newNow =>
    obtain ⟨_, _, hpoolEq, _, _⟩ := hstep
    rw [hpoolEq]; exact hmem
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, _⟩ := hstep
    rw [hpoolEq]; exact hmem
  | signNote pk' msgHash =>
    obtain ⟨_, _, hpoolEq, _, _⟩ := hstep
    rw [hpoolEq]; exact hmem

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
    (t : Nat) (pos : Nat × Nat) (pre : CommitmentPreimage) (hnpk : pre.npk = npk (masterPublicKey pk nk) r) :
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
theorem bulkTransferFold_outcomeDerivedFrom (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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

/-- The tree-tagged counterpart of `withPositionsFrom_mem_fwd`: anything
    already IN the underlying list gets SOME `(treeNumber, position)` key
    once tagged. What `bulkTransferFold_index_payout` needs to turn "this
    output is one of the fold's own `payoutOutputs`" into an ACTUAL
    `(pos, pre) ∈ midPool.live token` fact, against the real tree-tagged
    `withTreePositionsFrom` shape. -/
theorem withTreePositionsFrom_mem_fwd {α : Type} {treeNumber start : Nat} {l : List α} {a : α}
    (h : a ∈ l) : ∃ pos, ((treeNumber, pos), a) ∈ withTreePositionsFrom treeNumber start l := by
  obtain ⟨pos, hpos⟩ := withPositionsFrom_mem_fwd (start := start) h
  exact ⟨pos, List.mem_map.mpr ⟨(pos, a), hpos, rfl⟩⟩

/-- `PoolOwnedSpendStep`'s own per-payout liveness fact, generic over
    `payoutPreimages`/`ownedPreimages`, proved BEFORE `bulkTransferFold`
    is unfolded: any entry of `payoutPreimages` lands live in `after` at
    SOME position, regardless of which branch (`nullified = none` or
    `some _`) produced `after` — both branches write the SAME `live`
    update shape (`Notes.lean`'s `PoolOwnedSpendStep`), the fold's own
    `withTreePositionsFrom`-prefixed list over `payoutPreimages ++
    ownedPreimages`. What `bulkTransferFold_index_payout` needs to turn
    "this output is one of the fold's own `payoutOutputs`" into an
    ACTUAL `(pos, pre) ∈ midPool.live token` fact, without unfolding
    `transferEffects`/`afford` first. -/
theorem PoolOwnedSpendStep_payout_live
    (pool pool' : PoolState) (self : Term) (token : Nat)
    (nullified : Option ((Nat × Nat) × Term))
    (payoutPreimages ownedPreimages : List CommitmentPreimage)
    (hmatch : PoolOwnedSpendStep pool self token nullified payoutPreimages ownedPreimages pool') :
    ∀ a ∈ payoutPreimages, ∃ pos, (pos, a) ∈ pool'.live token := by
  intro a ha
  have hmemOut : a ∈ payoutPreimages ++ ownedPreimages := List.mem_append_left _ ha
  cases nullified with
  | none =>
    obtain ⟨w, pub, hM, hC, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes, hroot, hmark,
      hrandomOut, heq⟩ := hmatch
    have hliveT : pool'.live token =
        withTreePositionsFrom
          (insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages ++ ownedPreimages).length)
          (insertStartPos pool.leaves (payoutPreimages ++ ownedPreimages).length)
          (payoutPreimages ++ ownedPreimages) ++ pool.live token := by
      rw [heq]
      by_cases ht : token = token <;> simp [ht, List.length_append]
    obtain ⟨pos, hpos⟩ := withTreePositionsFrom_mem_fwd
      (treeNumber := insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages ++ ownedPreimages).length)
      (start := insertStartPos pool.leaves (payoutPreimages ++ ownedPreimages).length) hmemOut
    exact ⟨(insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages ++ ownedPreimages).length, pos),
      by rw [hliveT]; exact List.mem_append_left _ hpos⟩
  | some v =>
    obtain ⟨pt, c⟩ := v
    obtain ⟨w, pub, hM, hC, rest, spent', ownedRandom, hNonZero, hself, htoken, hnewnotes, hleavesIdx,
      hcommit, hroot, hremove, hmark, hrandomOut, heq⟩ := hmatch
    have hliveT : pool'.live token =
        withTreePositionsFrom
          (insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages ++ ownedPreimages).length)
          (insertStartPos pool.leaves (payoutPreimages ++ ownedPreimages).length)
          (payoutPreimages ++ ownedPreimages) ++ rest := by
      rw [heq]
      by_cases ht : token = token <;> simp [ht, List.length_append]
    obtain ⟨pos, hpos⟩ := withTreePositionsFrom_mem_fwd
      (treeNumber := insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages ++ ownedPreimages).length)
      (start := insertStartPos pool.leaves (payoutPreimages ++ ownedPreimages).length) hmemOut
    exact ⟨(insertTreeNumber pool.closedTrees pool.leaves (payoutPreimages ++ ownedPreimages).length, pos),
      by rw [hliveT]; exact List.mem_append_left _ hpos⟩


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
theorem bulkTransferFold_index_payout (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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
    intro newOutcome pool poolF holdings holdingsF hfold hinv assetIndex hidx hunique hidxN
    exact absurd hidx (by simp)
  | cons exit rest ih =>
    intro newOutcome pool poolF holdings holdingsF hfold hinv assetIndex hidx hunique hidxN
    cases newOutcome with
    | nil => unfold bulkTransferFold at hfold; exact hfold.elim
    | cons newExit newRest =>
      unfold bulkTransferFold at hfold
      obtain ⟨_hguarantee, hnewExit, r, midPool, hmatch, hrec⟩ := hfold
      cases assetIndex with
      | zero =>
        refine ⟨hnewExit, ?_⟩
        intro k hk
        let held := (match holdings exit.asset cid with
          | none => 0
          | some (_, c) => (pool.preimageOf c).map CommitmentPreimage.value |>.getD 0)
        have hklt : k < exit.allocations.length := by
          by_cases hc : k < exit.allocations.length
          · exact hc
          · exfalso
            have hlen := afford_length exit.allocations held
            have h0 : (afford exit.allocations held).getD k 0 = 0 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            exact hk h0
        have hexiteq : (transferEffects exit.allocations held []).2.1 =
            (transferEffectsSel exit.allocations held
              (fun i => ([] : List Nat).isEmpty || i ∈ ([] : List Nat))).2.1 := by
          rw [transferEffects_eq_sel]
        have hmemExit : { exit.allocations.getD k Allocation.default with
            amount := (afford exit.allocations held).getD k 0 } ∈
            (transferEffects exit.allocations held []).2.1 := by
          rw [hexiteq]
          exact transferEffectsSel_exit_mem exit.allocations held _ k hklt (by simp)
        have hk' : (afford exit.allocations held).getD k 0 ≠ 0 := hk
        rw [List.getD_eq_getElem?_getD] at hk'
        have hpayoutMem : (⟨(exit.allocations.getD k Allocation.default).destination, exit.asset,
            (afford exit.allocations held).getD k 0⟩ : CommitmentPreimage) ∈
            (transferEffects exit.allocations held []).2.1.filterMap (fun a =>
              if a.amount = 0 then none else
                some (⟨a.destination, exit.asset, a.amount⟩ : CommitmentPreimage)) :=
          List.mem_filterMap.mpr ⟨_, hmemExit, by simp [hk']⟩
        obtain ⟨pos, hpos⟩ := PoolOwnedSpendStep_payout_live pool midPool self exit.asset
          (holdings exit.asset cid) _ _ hmatch _ hpayoutMem
        have htne : exit.asset ∉ rest.map SingleAssetExit.asset := by
          intro hc
          obtain ⟨y, hyMem, hyEq⟩ := List.mem_map.mp hc
          obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hyMem
          have hcons2 : (exit :: rest)[n + 1]? = some y := by simpa using hn
          obtain ⟨hconsLt, hyget⟩ := List.getElem?_eq_some_iff.mp hcons2
          have hyget2 : (exit :: rest).get ⟨n + 1, hconsLt⟩ = y := hyget
          have hne := hunique (n + 1) hconsLt (by omega)
          rw [hyget2] at hne
          have hexitget : (exit :: rest).get ⟨0, hidx⟩ = exit := rfl
          rw [hexitget] at hne
          exact hne hyEq
        exact ⟨pos, bulkTransferFold_live_frame self cid rest newRest midPool poolF _ holdingsF hrec
          exit.asset pos _ htne hpos⟩
      | succ j =>
        have hjlt : j < rest.length := by simpa using hidx
        have hjltN : j < newRest.length := by simpa using hidxN
        have hunique' : ∀ j' (hj' : j' < rest.length), j' ≠ j →
            (rest.get ⟨j', hj'⟩).asset ≠ (rest.get ⟨j, hjlt⟩).asset := by
          intro j' hj' hne'
          have hcLt : j' + 1 < (exit :: rest).length := by simp; omega
          have := hunique (j' + 1) hcLt (by omega)
          have hget1 : (exit :: rest).get ⟨j' + 1, hcLt⟩ = rest.get ⟨j', hj'⟩ := rfl
          have hget2 : (exit :: rest).get ⟨j + 1, hidx⟩ = rest.get ⟨j, hjlt⟩ := rfl
          rw [hget1, hget2] at this
          exact this
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
        have hres := ih newRest midPool poolF _ holdingsF hrec hinv' j hjlt hunique' hjltN
        have hassetne : (rest.get ⟨j, hjlt⟩).asset ≠ exit.asset := by
          have h0lt : 0 < (exit :: rest).length := by simp
          have hh := hunique 0 h0lt (by omega)
          have hg0 : (exit :: rest).get ⟨0, h0lt⟩ = exit := rfl
          have hg1 : (exit :: rest).get ⟨j + 1, hidx⟩ = rest.get ⟨j, hjlt⟩ := rfl
          rw [hg0, hg1] at hh
          exact hh.symm
        have hassetne' : ((rest.get ⟨j, hjlt⟩).asset, cid) ≠ (exit.asset, cid) :=
          fun heq => hassetne (congrArg Prod.fst heq)
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
          holdings htokPayout hmatch hinv (rest.get ⟨j, hjlt⟩).asset cid hassetne'
        simp only [update, if_neg hassetne] at hframe hres
        rw [hframe] at hres
        have hget1 : (exit :: rest).get ⟨j + 1, hidx⟩ = rest.get ⟨j, hjlt⟩ := rfl
        have hget2 : (newExit :: newRest).get ⟨j + 1, hidxN⟩ = newRest.get ⟨j, hjltN⟩ := rfl
        rw [hget1, hget2]
        exact hres



/-- `bulkTransferFold` pairs `outcome` and `newOutcome` one entry per
    recursive step (its own `cons exit rest, cons newExit newRest` match
    arm; any length mismatch hits its own `False` arm instead) — so the
    two always share a length. What lets `unbeatablePaysInv_step`'s own
    bulk `Call` cases carry `assetIndex`'s own bound from `outcome` to
    `newOutcome`. -/
theorem bulkTransferFold_length (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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
theorem bulkTransferFold_holdings_frame_cid (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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
theorem bulkTransferFold_heldValue_frame_cid (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
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
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (qc : Term) (pre : CommitmentPreimage) (hpre : pool.preimageOf qc = some pre)
    (hconsist : hashCommitment pre = qc) :
    pool'.preimageOf qc = some pre := by
  obtain ⟨hvalid_outputs, hpre0⟩ := PoolOwnedSpendStep_preimageOf_eq pool pool' self asset cid
    remainder r payoutOutputs holdings htokPayout hmatch
  rw [hpre0]
  exact applyRecords_preserves_known hvalid_outputs pool.preimageOf qc pre hpre hconsist

/-- One `PoolOwnedSpendStep`-backed holdings update's COMPLETE effect: the
    six facts `PoolOwnedSpendStep_frame`, `PoolOwnedSpendStep_sets_
    heldValue`, `PoolOwnedSpendStep_ownedRandom_known`,
    `PoolOwnedSpendStep_preimageOf_known`, `PoolOwnedSpend_update_
    preimage_nonzero`, and `PoolOwnedSpend_update_position_live`, in one
    conjunction. The theorem's own hypothesis is the WEAKEST one every
    conjunct needs: the step itself, `hmatch`. `htokPayout` (needed by
    five of the six) and the two different holdings invariants
    `PoolOwnedSpendStep_frame`/`PoolOwnedSpend_update_preimage_nonzero`
    share and `PoolOwnedSpend_update_position_live` alone needs are NOT
    global hypotheses here — each stays a premise of its OWN conjunct,
    matching exactly what each original lemma took, so a caller who
    only needs `PoolOwnedSpend_update_position_live`'s own fact never
    has to supply `htokPayout` either. -/
theorem PoolOwnedSpendStep_effects
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool') :
    -- `PoolOwnedSpendStep_frame`, gated by `htokPayout` and its own holdings
    -- invariant.
    ((∀ pre ∈ payoutOutputs, pre.token = asset) →
      (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
        ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) →
      ∀ qasset qcid, (qasset, qcid) ≠ (asset, cid) →
        (match (update holdings asset
            (update (holdings asset) cid
              (if remainder = 0 then none
               else some ((insertTreeNumber pool.closedTrees pool.leaves
                     (payoutOutputs ++ (if remainder = 0 then [] else
                       [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                   insertStartPos pool.leaves
                     (payoutOutputs ++ (if remainder = 0 then [] else
                       [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                     (payoutOutputs ++ (if remainder = 0 then [] else
                       [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
                 commitment (npk self r) asset remainder)))) qasset qcid with
          | none => (0 : Nat)
          | some (_, c) => ((pool'.preimageOf c).map CommitmentPreimage.value).getD 0) =
        (match holdings qasset qcid with
          | none => 0
          | some (_, c) => ((pool.preimageOf c).map CommitmentPreimage.value).getD 0)) ∧
    -- `PoolOwnedSpendStep_sets_heldValue`, gated by `htokPayout`.
    ((∀ pre ∈ payoutOutputs, pre.token = asset) →
      (match (update holdings asset
          (update (holdings asset) cid
            (if remainder = 0 then none
             else some ((insertTreeNumber pool.closedTrees pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                 insertStartPos pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
               commitment (npk self r) asset remainder)))) asset cid with
        | none => (0 : Nat)
        | some (_, c) => ((pool'.preimageOf c).map CommitmentPreimage.value).getD 0) = remainder) ∧
    -- `PoolOwnedSpendStep_ownedRandom_known`, gated by `htokPayout`.
    ((∀ pre ∈ payoutOutputs, pre.token = asset) →
      (∀ qc pre' r', pool.preimageOf qc = some pre' → hashCommitment pre' = qc →
        pre'.npk = npk self r' → pool.ownedRandomOf qc = some ⟨self, r'⟩ →
        pool'.ownedRandomOf qc = some ⟨self, r'⟩) ∧
      (remainder ≠ 0 →
        pool'.ownedRandomOf (commitment (npk self r) asset remainder) = some ⟨self, r⟩)) ∧
    -- `PoolOwnedSpendStep_preimageOf_known`, gated by `htokPayout`.
    ((∀ pre ∈ payoutOutputs, pre.token = asset) →
      ∀ qc pre, pool.preimageOf qc = some pre → hashCommitment pre = qc →
        pool'.preimageOf qc = some pre) ∧
    -- `PoolOwnedSpend_update_preimage_nonzero`, gated by `htokPayout` and the
    -- SAME holdings invariant as `PoolOwnedSpendStep_frame`'s own conjunct.
    ((∀ pre ∈ payoutOutputs, pre.token = asset) →
      (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
        ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) →
      ∀ qasset qcid qpos qc, (update holdings asset
          (update (holdings asset) cid
            (if remainder = 0 then none
             else some ((insertTreeNumber pool.closedTrees pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                 insertStartPos pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
               commitment (npk self r) asset remainder)))) qasset qcid = some (qpos, qc) →
        ∃ pre, pool'.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc) ∧
    -- `PoolOwnedSpend_update_position_live`, gated ONLY by its OWN
    -- position-live holdings invariant — no `htokPayout`, matching its
    -- own (narrower) hypothesis set.
    ((∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
        (∃ pre, (qpos, pre) ∈ pool.live qasset ∧ hashCommitment pre = qc ∧
          ((∃ ownerField r, self = ownerField ∧ pre.npk = npk ownerField r) ∨
            ∃ r, pre.npk = npk self r)) ∧
        qpos.2 < (pool.leavesAt' qpos.1).length ∧
        (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
          (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) →
      ∀ qasset qcid qpos qc, (update holdings asset
          (update (holdings asset) cid
            (if remainder = 0 then none
             else some ((insertTreeNumber pool.closedTrees pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                 insertStartPos pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
               commitment (npk self r) asset remainder)))) qasset qcid = some (qpos, qc) →
        (∃ pre, (qpos, pre) ∈ pool'.live qasset ∧ hashCommitment pre = qc ∧
          ((∃ ownerField r, self = ownerField ∧ pre.npk = npk ownerField r) ∨
            ∃ r, pre.npk = npk self r)) ∧
        qpos.2 < (pool'.leavesAt' qpos.1).length ∧
        (∀ qasset' qcid' qpos' qc', (update holdings asset
            (update (holdings asset) cid
              (if remainder = 0 then none
               else some ((insertTreeNumber pool.closedTrees pool.leaves
                     (payoutOutputs ++ (if remainder = 0 then [] else
                       [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                   insertStartPos pool.leaves
                     (payoutOutputs ++ (if remainder = 0 then [] else
                       [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                     (payoutOutputs ++ (if remainder = 0 then [] else
                       [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
                 commitment (npk self r) asset remainder)))) qasset' qcid' = some (qpos', qc') →
          (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro htokPayout hinv qasset qcid hne
    exact PoolOwnedSpendStep_frame pool pool' self asset cid remainder r payoutOutputs holdings
      htokPayout hmatch hinv qasset qcid hne
  · intro htokPayout
    exact PoolOwnedSpendStep_sets_heldValue pool pool' self asset cid remainder r payoutOutputs
      holdings htokPayout hmatch
  · intro htokPayout
    exact PoolOwnedSpendStep_ownedRandom_known pool pool' self asset cid remainder r payoutOutputs
      holdings htokPayout hmatch
  · intro htokPayout qc pre hpre hconsist
    exact PoolOwnedSpendStep_preimageOf_known pool pool' self asset cid remainder r payoutOutputs
      holdings htokPayout hmatch qc pre hpre hconsist
  · intro htokPayout hinv
    exact PoolOwnedSpend_update_preimage_nonzero pool pool' self asset cid remainder r payoutOutputs
      holdings htokPayout hmatch hinv
  · intro hinv
    exact PoolOwnedSpend_update_position_live pool pool' self asset cid remainder r payoutOutputs
      holdings hmatch hinv




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
  obtain ⟨N, M, w, pub, idx, spendTreeNumber, treeNumber, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
  obtain ⟨_r, _hown, hcommit, htoken, _htreeNumber, _hposition, _hN, _hM, hC, _rest,
    _spent', records, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
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
    (oldPos : Nat × Nat) (oldHolding : Term) (hsome : s.holdings asset channelId = some (oldPos, oldHolding)) :
    heldValue s' asset channelId = heldValue s asset channelId + amount := by
  obtain ⟨_hcfg, _hheld, _hext, hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
  obtain ⟨N, M, w, pub, idx, spendTreeNumber, treeNumber, position, midPool, hdstep,
    _hpoolsigned, hmatch⟩ := hinner
  obtain ⟨oldTreeNumber, oldPosNat⟩ := oldPos
  obtain ⟨preOld, hpreOld, hvalOld, hconsOld⟩ := hinv asset channelId (oldTreeNumber, oldPosNat)
    oldHolding hsome
  rw [hsome] at hmatch
  obtain ⟨merged, mergeSpendTreeNumber, mergedTreeNumber, mergedPos, hmergestep, hholdseq⟩ := hmatch
  obtain ⟨r0, hown, hcommit, htoken, _htreeNumber, _hposition, _hN, _hM, hC, _rest, _spent',
    records, _hRoot, _hRemove, _hNullify, hSublist, hidxrec, heq⟩ := hdstep
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have hvalFresh : w.valueOut idx = amount := by
    have hout := hC.outputs idx
    rw [htoken, hcommit] at hout
    exact (Term.val.inj (Term.hash3_inj hout).2.2).symm
  obtain ⟨_hmergedTN, _hmergedPosEq, w', pub', hC', _rest', _spent'', r', randomOut', _hNonZero',
    hself', _htoken', hnpkOut0', hmergedEq, _hleaf0', _hleaf1', hcommitOld', hcommitNew',
    _holdTN', _hnewTN', _hroot', _hremove', _hnullify', _hrandomOut', heq'⟩ := hmergestep
  have hveq0 : preOld.value = w'.valueIn 0 := by
    have hcons'' : hashCommitment preOld = hashCommitment
        (⟨npk pub'.ownerField (w'.randomIn 0), w'.token, w'.valueIn 0⟩ : CommitmentPreimage) := by
      rw [hconsOld]; exact hcommitOld'.symm
    exact congrArg CommitmentPreimage.value (hashCommitment_inj hcons'')
  have hconsFresh : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) =
      pub.commitmentsOut idx := (hC.outputs idx).symm
  have hveq1 : w.valueOut idx = w'.valueIn 1 := by
    have hcons'' : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) =
        hashCommitment
          (⟨npk pub'.ownerField (w'.randomIn 1), w'.token, w'.valueIn 1⟩ : CommitmentPreimage) := by
      rw [hconsFresh]; exact hcommitNew'.symm
    exact congrArg CommitmentPreimage.value (hashCommitment_inj hcons'')
  have hbal := transactOwned_value_conserved w' pub' (by omega) (by omega) hC'
  simp only [listSum, List.ofFn_succ, List.ofFn_zero] at hbal
  have hvalid' : ∀ cp ∈ ownedOutputRecords w' pub', hashCommitment cp.2 = cp.1 :=
    ownedOutputRecords_valid hC'
  have hmemrec' : (pub'.commitmentsOut (0 : Fin 1),
      (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage)) ∈ ownedOutputRecords w' pub' := by
    unfold ownedOutputRecords; exact List.mem_ofFn.mpr ⟨0, rfl⟩
  have hnz0' : ¬ isZeroPreimage (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) :=
    npk_preimage_not_zero hnpkOut0'.symm
  have hread0' := applyRecords_reads hvalid' midPool.preimageOf _ _ hmemrec' hnz0'
  have hpre' : s'.pool.preimageOf (pub'.commitmentsOut (0 : Fin 1)) =
      some (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) := by
    rw [heq']; exact hread0'
  have hOld : heldValue s asset channelId = preOld.value := by
    unfold heldValue
    rw [hsome]
    simp [hpreOld]
  unfold heldValue
  rw [hholdseq]
  unfold update
  rw [if_pos rfl, if_pos rfl]
  show ((s'.pool.preimageOf merged).map CommitmentPreimage.value).getD 0 =
    heldValue s asset channelId + amount
  rw [hmergedEq, hpre', hOld]
  simp only [Option.map_some, Option.getD_some]
  simp only [Fin.succ_zero_eq_one, Nat.add_zero] at hbal
  omega


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
  obtain ⟨N, M, w, pub, idx, spendTreeNumber, treeNumber, position, midPool, hdstep, _hpoolsigned, hmatch⟩ := hinner
  obtain ⟨_r, _hown, hcommit, htoken, _htreeNumber, hposition, hN, hM, hC, rest, spent',
    records, hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
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
  · obtain ⟨⟨_oldTreeNum, _oldPosNat⟩, oldHoldingVal⟩ := oldHolding
    rw [hh] at hmatch
    obtain ⟨merged, mergeSpendTreeNumber, mergedTreeNumber, mergedPos, hmergestep, hholdseq⟩ := hmatch
    obtain ⟨_hmergedTN, _hmergedPosEq, w', pub', hC', _rest', _spent'', _r', randomOut', _hNonZero',
      _hself', _htoken', _hnpkOut0', _hmergedEq, _hleaf0', _hleaf1', _hcommitOld', _hcommitNew',
      _holdTN', _hnewTN', _hroot', _hremove', _hnullify', _hrandomOut', heq'⟩ := hmergestep
    have hvalid' : ∀ cp ∈ ownedOutputRecords w' pub', hashCommitment cp.2 = cp.1 :=
      ownedOutputRecords_valid hC'
    have hchain' : ∀ qc pre, midPool.preimageOf qc = some pre → hashCommitment pre = qc →
        s'.pool.preimageOf qc = some pre := fun qc pre hpre hconsist => by
      rw [heq']; exact applyRecords_preserves_known hvalid' midPool.preimageOf qc pre hpre hconsist
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
          dsimp only
          rw [hchain' qc pre_old (hchain qc pre_old hpre_old hconsist_old) hconsist_old, hpre_old]
    · rw [if_neg ha]
      rcases hh' : s.holdings asset' cid' with _ | hpair
      · rfl
      · obtain ⟨qpos, qc⟩ := hpair
        obtain ⟨pre_old, hpre_old, _hval_old, hconsist_old⟩ := hinv asset' cid' qpos qc hh'
        dsimp only
        rw [hchain' qc pre_old (hchain qc pre_old hpre_old hconsist_old) hconsist_old, hpre_old]

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
  exact Term.val_ne_hash a .keccak _ heq.symm


/-- **The one per-holding well-formedness invariant**, folding together what
    four separate step lemmas used to state piecewise: every holding names
    a commitment with a known, nonzero, self-consistent preimage of its own
    asset, that preimage's own leaf is live at the holding's own
    `(treeNumber, position)` key, that key is within the pool's own leaf
    range, no two DIFFERENT holdings ever share a key, and the preimage's
    own note key is the adjudicator's own, with the disclosure that proves
    it already on the public record. One shared `pre` witness ties every
    clause together — `hashCommitment_inj` always lets two separately
    obtained witnesses for the SAME commitment be unified, so no proof
    below ever needs to carry more than one `pre` per holding. -/
def HoldingWellFormed (s : AdjudicatorState) : Prop :=
  ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
    (∃ pre, s.pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
      pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ s.pool.live qasset ∧
      ∃ r, pre.npk = npk s.self r ∧ s.pool.ownedRandomOf qc = some ⟨s.self, r⟩) ∧
    qpos.2 < (s.pool.leavesAt' qpos.1).length ∧
    (∀ qasset' qcid' qpos' qc', s.holdings qasset' qcid' = some (qpos', qc') →
      (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)

/-- `HoldingWellFormed` holds trivially at `genesis`: no channel holds
    anything yet (`State.lean`'s `genesis`, `holdings := fun _ _ => none`),
    so the per-holding implication's own premise is never met. -/
theorem holdingWellFormed_genesis (assets : Nat → Prop) (selfInputs : List Term)
    (pool0 : PoolState) :
    HoldingWellFormed (genesis assets selfInputs pool0) := by
  intro qasset qcid qpos qc hc
  exact absurd hc (by simp [genesis])

/-- One `PoolOwnedSpendStep`-backed holdings update's effect on
    `HoldingWellFormed` — the shape `.transfer` and `bulkTransferFold`
    both use. Delegates every clause to an already-proved lemma
    (`PoolOwnedSpend_update_preimage_nonzero`, `PoolOwnedSpend_update_
    position_live`, `PoolOwnedSpendStep_ownedRandom_known`), unifying
    the two separately-obtained `pre` witnesses they each return via
    `hashCommitment_inj` — neither lemma's own conclusion carries
    `pre.token` or the disclosure, so this proof supplies both from
    `hinv` directly (the untouched case) or from the step's own
    construction (the touched case). -/
theorem PoolOwnedSpend_update_wellFormed
    (pool pool' : PoolState) (self : Term) (asset : Nat) (cid : Term) (remainder r : Nat)
    (payoutOutputs : List CommitmentPreimage)
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (htokPayout : ∀ pre ∈ payoutOutputs, pre.token = asset)
    (hmatch : PoolOwnedSpendStep pool self asset (holdings asset cid) payoutOutputs
      (if remainder = 0 then [] else [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])
      pool')
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool.live qasset ∧
        ∃ r', pre.npk = npk self r' ∧ pool.ownedRandomOf qc = some ⟨self, r'⟩) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) cid
          (if remainder = 0 then none
           else some ((insertTreeNumber pool.closedTrees pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
               insertStartPos pool.leaves
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                 (payoutOutputs ++ (if remainder = 0 then [] else
                   [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
             commitment (npk self r) asset remainder)))) qasset qcid = some (qpos, qc) →
      (∃ pre, pool'.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool'.live qasset ∧
        ∃ r', pre.npk = npk self r' ∧ pool'.ownedRandomOf qc = some ⟨self, r'⟩) ∧
      qpos.2 < (pool'.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', (update holdings asset
          (update (holdings asset) cid
            (if remainder = 0 then none
             else some ((insertTreeNumber pool.closedTrees pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length,
                 insertStartPos pool.leaves
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length +
                   (payoutOutputs ++ (if remainder = 0 then [] else
                     [(⟨npk self r, asset, remainder⟩ : CommitmentPreimage)])).length - 1),
               commitment (npk self r) asset remainder)))) qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  have hinvNZ : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      ∃ pre, pool.preimageOf qc = some pre ∧ pre.value ≠ 0 ∧ hashCommitment pre = qc :=
    fun qasset qcid qpos qc hc => by
      obtain ⟨⟨pre, h1, h2, h3, _h4, _h5, _r', _h6, _h7⟩, _, _⟩ := hinv qasset qcid qpos qc hc
      exact ⟨pre, h1, h3, h2⟩
  have hinvPL : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r', self = ownerField ∧ pre.npk = npk ownerField r') ∨
          ∃ r', pre.npk = npk self r')) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) :=
    fun qasset qcid qpos qc hc => by
      obtain ⟨⟨pre, _h1, h2, _h3, _h4, h5, r', hnpk, _h7⟩, hbound, huniq⟩ := hinv qasset qcid qpos qc hc
      exact ⟨⟨pre, h5, h2, Or.inr ⟨r', hnpk⟩⟩, hbound, huniq⟩
  have hpn := PoolOwnedSpend_update_preimage_nonzero pool pool' self asset cid remainder r
    payoutOutputs holdings htokPayout hmatch hinvNZ
  have hpl := PoolOwnedSpend_update_position_live pool pool' self asset cid remainder r
    payoutOutputs holdings hmatch hinvPL
  have hor := PoolOwnedSpendStep_ownedRandom_known pool pool' self asset cid remainder r
    payoutOutputs holdings htokPayout hmatch
  intro qasset qcid qpos qc hc
  obtain ⟨pre1, hpre1, hval1, hcons1⟩ := hpn qasset qcid qpos qc hc
  obtain ⟨⟨pre2, hmem2, hcons2, _hown2⟩, hbound2, huniq2⟩ := hpl qasset qcid qpos qc hc
  have hpeq : pre1 = pre2 := hashCommitment_inj (hcons1.trans hcons2.symm)
  have hmem1 : (qpos, pre1) ∈ pool'.live qasset := by rw [hpeq]; exact hmem2
  refine ⟨?_, hbound2, huniq2⟩
  by_cases heqch : qasset = asset ∧ qcid = cid
  · obtain ⟨ha, hcidEq⟩ := heqch
    rw [ha] at hc hmem1 ⊢
    rw [hcidEq] at hc
    by_cases hrem : remainder = 0
    · exfalso
      unfold update at hc
      rw [if_pos rfl, if_pos rfl, if_pos hrem] at hc
      exact absurd hc (by simp)
    · have hqceq : qc = commitment (npk self r) asset remainder := by
        unfold update at hc
        rw [if_pos rfl, if_pos rfl, if_neg hrem] at hc
        exact (congrArg Prod.snd (Option.some.inj hc)).symm
      have hpre1eq : pre1 = (⟨npk self r, asset, remainder⟩ : CommitmentPreimage) :=
        hashCommitment_inj (by rw [hcons1, hqceq]; rfl)
      have hdisc : pool'.ownedRandomOf qc = some ⟨self, r⟩ := by
        rw [hqceq]; exact hor.2 hrem
      exact ⟨pre1, hpre1, hcons1, hval1, by rw [hpre1eq], hmem1,
        ⟨r, by rw [hpre1eq], hdisc⟩⟩
  · have hc' : holdings qasset qcid = some (qpos, qc) := by
      unfold update at hc
      by_cases ha : qasset = asset
      · subst ha
        rw [if_pos rfl] at hc
        by_cases hcid : qcid = cid
        · exact absurd ⟨rfl, hcid⟩ heqch
        · rwa [if_neg hcid] at hc
      · rwa [if_neg ha] at hc
    obtain ⟨⟨pre0, hpre0, hcons0, _hval0, htok0, _hmem0, r0, hnpk0, hord0⟩, _, _⟩ :=
      hinv qasset qcid qpos qc hc'
    have hpeq0 : pre0 = pre1 := hashCommitment_inj (hcons0.trans hcons1.symm)
    have hordframe := hor.1 qc pre1 r0 (by rw [← hpeq0]; exact hpre0) (by rw [← hpeq0]; exact hcons0)
      (by rw [← hpeq0]; exact hnpk0) hord0
    exact ⟨pre1, hpre1, hcons1, hval1, (by rw [← hpeq0]; exact htok0), hmem1, ⟨r0, (by rw [← hpeq0]; exact hnpk0), hordframe⟩⟩

/-- `bulkTransferFold`'s own invariant for `HoldingWellFormed`: one
    application of `PoolOwnedSpend_update_wellFormed` per asset in the
    fold's own list, carried forward by induction — replaces the four
    separate `bulkTransferFold_preimage_nonzero`/`_ownedRandom_known`/
    `_owned_disclosure`/`_position_live` lemmas with one pass. -/
theorem bulkTransferFold_wellFormed (self : Term) (cid : Term) :
    ∀ (outcome newOutcome : Outcome) (pool poolF : PoolState)
      (holdings holdingsF : Nat → Term → Option ((Nat × Nat) × Term)),
    bulkTransferFold self cid outcome pool holdings newOutcome poolF holdingsF →
    (∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool.live qasset ∧
        ∃ r, pre.npk = npk self r ∧ pool.ownedRandomOf qc = some ⟨self, r⟩) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) →
    ∀ qasset qcid qpos qc, holdingsF qasset qcid = some (qpos, qc) →
      (∃ pre, poolF.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ poolF.live qasset ∧
        ∃ r, pre.npk = npk self r ∧ poolF.ownedRandomOf qc = some ⟨self, r⟩) ∧
      qpos.2 < (poolF.leavesAt' qpos.1).length ∧
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
      exact PoolOwnedSpend_update_wellFormed pool midPool self exit.asset cid _ r _
        holdings
        (fun pre hpre => by
          obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hpre
          by_cases hamt : a.amount = 0
          · rw [if_pos hamt] at hfa; exact absurd hfa (by simp)
          · rw [if_neg hamt] at hfa; exact (Option.some.inj hfa) ▸ rfl)
        hmatch hinv


/-- A `DepositStep`'s own frame fact for `HoldingWellFormed`: `DepositStep`
    never touches `AdjudicatorState.holdings` (only `Operations.lean`'s own
    `.deposit` Step case does, AFTER `DepositStep` fires), so EVERY existing
    holding's own invariant survives into the post-`DepositStep` pool
    unscathed — the depositor's own `N` spent inputs are USER-keyed
    (`user_npk_ne_contract_npk`), so they can never coincide with a
    contract-owned held note's own position. -/
theorem DepositStep_frame_wellFormed
    {N M : Nat} (pool pool' : PoolState) (selfInputs : List Term) (token amount : Nat)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (spendTreeNumber treeNumber position : Nat)
    (hdstep : DepositStep pool (Term.keccak selfInputs) token amount w pub idx
      spendTreeNumber treeNumber position pool')
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool.live qasset ∧
        ∃ r, pre.npk = npk (Term.keccak selfInputs) r ∧
          pool.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r⟩) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) :
    ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, pool'.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool'.live qasset ∧
        ∃ r, pre.npk = npk (Term.keccak selfInputs) r ∧
          pool'.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r⟩) ∧
      qpos.2 < (pool'.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  obtain ⟨r0, hown, hcommit, htoken, htreeNumber, hposition, hN, hM, hC, rest, spent', records,
    hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have userDisjoint : ∀ (pre : CommitmentPreimage) (r' : Nat), pre.npk = npk (Term.keccak selfInputs) r' →
      ∀ pk' nk' r'', pre.npk ≠ npk (masterPublicKey pk' nk') r'' := by
    intro pre r' hpre pk' nk' r'' hcontra
    rw [hpre] at hcontra
    exact user_npk_ne_contract_npk hcontra.symm
  have hliveT : ∀ t, pool'.live t = if t = w.token
      then withTreePositionsFrom treeNumber (insertStartPos pool.leaves M) (transactAllOutputs w) ++ rest
      else pool.live t := fun t => by rw [heq]
  have hpreEq : pool'.preimageOf = applyRecords pool.preimageOf records := by rw [heq]
  have hoRandEq : pool'.ownedRandomOf = applyOwnedRecords pool.ownedRandomOf
      [(pub.commitmentsOut idx, (⟨Term.keccak selfInputs, r0⟩ : OwnedDisclosure))] := by rw [heq]
  have hlevA' : ∀ tn, pool'.leavesAt' tn = PoolState.leavesAt
      (insertResult pool.closedTrees pool.leaves pool.roots ((transactAllOutputs w).map hashCommitment)).1
      (insertResult pool.closedTrees pool.leaves pool.roots ((transactAllOutputs w).map hashCommitment)).2.1
      (insertResult pool.closedTrees pool.leaves pool.roots ((transactAllOutputs w).map hashCommitment)).2.2
      tn := by
    intro tn; unfold PoolState.leavesAt'; rw [heq]
  have hge : ∀ tn, (pool.leavesAt' tn).length ≤ (pool'.leavesAt' tn).length := by
    intro tn
    rw [hlevA']
    exact insertResult_leavesAt_length_ge pool.closedTrees pool.leaves pool.roots
      ((transactAllOutputs w).map hashCommitment) tn
  have hnz0 : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
    rw [htoken]; exact npk_preimage_not_zero hown.symm
  have hread0 := applyRecords_reads hvalid pool.preimageOf _ _ hidxrec hnz0
  intro qasset qcid qpos qc hc
  obtain ⟨⟨pre, hpre, hcons, hval, htok, hmem, r, hnpk, hord⟩, hbound, huniq⟩ := hinv qasset qcid qpos qc hc
  have hpre' : pool'.preimageOf qc = some pre := by
    rw [hpreEq]; exact applyRecords_preserves_known hvalid pool.preimageOf qc pre hpre hcons
  have hord' : pool'.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r⟩ := by
    rw [hoRandEq]
    exact applyOwnedRecords_preserves_known (reg := applyRecords pool.preimageOf records)
      (fun cd hcd => by
        rw [List.mem_singleton] at hcd
        refine hcd ▸ ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, ?_⟩
        rw [htoken]; exact hown.symm)
      pool.ownedRandomOf qc (Term.keccak selfInputs) r pre hord
        (applyRecords_preserves_known hvalid pool.preimageOf qc pre hpre hcons) hnpk
  have hmem' : (qpos, pre) ∈ pool'.live qasset := by
    rw [hliveT]
    by_cases ht : qasset = w.token
    · rw [if_pos ht]
      apply List.mem_append.mpr
      right
      have hsp0 : (qpos, pre) ∉ transactSpentPositions spendTreeNumber w := by
        intro hmemspent
        obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmemspent
        have hpreeq : pre = (⟨npk (masterPublicKey w.publicKey w.nullifyingKey) (w.randomIn j),
            w.token, w.valueIn j⟩ : CommitmentPreimage) := (congrArg Prod.snd hj).symm
        exact userDisjoint pre r hnpk w.publicKey w.nullifyingKey (w.randomIn j) (by rw [hpreeq])
      have hmemperm : (qpos, pre) ∈ transactSpentPositions spendTreeNumber w ++ rest :=
        (removeAll_perm hRemove).mem_iff.mp (ht ▸ hmem)
      exact (List.mem_append.mp hmemperm).resolve_left hsp0
    · rw [if_neg ht]; exact hmem
  refine ⟨⟨pre, hpre', hcons, hval, htok, hmem', r, hnpk, hord'⟩, ?_, huniq⟩
  have h := hge qpos.1
  omega

/-- One `DepositStep`-backed first-deposit holdings update's effect on
    `HoldingWellFormed` — `.deposit`'s "none" (no prior holding) branch:
    the fresh note at `idx` becomes the new holding (`DepositStep_frame_
    wellFormed` carries every OTHER holding forward), landing fresh past
    every existing holding's own position bound (`insertResult_leavesAt_
    target_length`/`insertStartPos_eq_leavesAt_length`), so it can never
    collide with one. -/
theorem DepositStep_update_wellFormed
    {N M : Nat} (pool pool' : PoolState) (selfInputs : List Term) (asset amount : Nat)
    (channelId : Term) (hpos : 0 < amount)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (spendTreeNumber treeNumber position : Nat)
    (hdstep : DepositStep pool (Term.keccak selfInputs) asset amount w pub idx
      spendTreeNumber treeNumber position pool')
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (hnone : holdings asset channelId = none)
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool.live qasset ∧
        ∃ r, pre.npk = npk (Term.keccak selfInputs) r ∧
          pool.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r⟩) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) channelId (some ((treeNumber, position), pub.commitmentsOut idx))))
      qasset qcid = some (qpos, qc) →
      (∃ pre, pool'.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool'.live qasset ∧
        ∃ r, pre.npk = npk (Term.keccak selfInputs) r ∧
          pool'.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r⟩) ∧
      qpos.2 < (pool'.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', (update holdings asset
          (update (holdings asset) channelId (some ((treeNumber, position), pub.commitmentsOut idx))))
        qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  have hframe := DepositStep_frame_wellFormed pool pool' selfInputs asset amount w pub idx
    spendTreeNumber treeNumber position hdstep holdings hinv
  obtain ⟨r0, hown, hcommit, htoken, htreeNumber, hposition, hN, hM, hC, rest, spent', records,
    hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have hval : w.valueOut idx = amount := by
    have hout := hC.outputs idx
    rw [htoken, hcommit] at hout
    exact (Term.val.inj (Term.hash3_inj hout).2.2).symm
  have hnz0 : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
    unfold isZeroPreimage
    intro ⟨_, hv, _⟩
    rw [hval] at hv
    have hcheck : amount = 0 := hv
    omega
  have hread0 := applyRecords_reads hvalid pool.preimageOf _ _ hidxrec hnz0
  have hpreEq : pool'.preimageOf = applyRecords pool.preimageOf records := by rw [heq]
  have hoRandEq : pool'.ownedRandomOf = applyOwnedRecords pool.ownedRandomOf
      [(pub.commitmentsOut idx, (⟨Term.keccak selfInputs, r0⟩ : OwnedDisclosure))] := by rw [heq]
  have hliveT : ∀ t, pool'.live t = if t = w.token
      then withTreePositionsFrom treeNumber (insertStartPos pool.leaves M) (transactAllOutputs w) ++ rest
      else pool.live t := fun t => by rw [heq]
  have hlevA' : ∀ tn, pool'.leavesAt' tn = PoolState.leavesAt
      (insertResult pool.closedTrees pool.leaves pool.roots ((transactAllOutputs w).map hashCommitment)).1
      (insertResult pool.closedTrees pool.leaves pool.roots ((transactAllOutputs w).map hashCommitment)).2.1
      (insertResult pool.closedTrees pool.leaves pool.roots ((transactAllOutputs w).map hashCommitment)).2.2
      tn := by
    intro tn; unfold PoolState.leavesAt'; rw [heq]
  have hcap : (transactAllOutputs w).length = M := List.length_ofFn
  have hbounds := PoolOwnedSpendStep_fresh_position_bounds pool.closedTrees pool.leaves pool.roots
    (transactAllOutputs w)
  rw [hcap] at hbounds
  have hbTarget : (pool'.leavesAt' treeNumber).length = insertStartPos pool.leaves M + M := by
    rw [htreeNumber, hlevA']
    exact hbounds.1
  have hbOld : (pool.leavesAt' treeNumber).length = insertStartPos pool.leaves M := by
    rw [htreeNumber]
    exact hbounds.2
  have hidxmem : ((treeNumber, insertStartPos pool.leaves M + idx.val),
      (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage)) ∈
      withTreePositionsFrom treeNumber (insertStartPos pool.leaves M) (transactAllOutputs w) := by
    unfold withTreePositionsFrom transactAllOutputs
    rw [withPositionsFrom_ofFn, List.map_ofFn]
    exact List.mem_ofFn.mpr ⟨idx, rfl⟩
  intro qasset qcid qpos qc hc
  unfold update at hc
  by_cases heqch : qasset = asset ∧ qcid = channelId
  · obtain ⟨ha, hcidEq⟩ := heqch
    rw [ha, hcidEq] at hc ⊢
    rw [if_pos rfl, if_pos rfl] at hc
    obtain ⟨hqpos, hqc⟩ := Prod.mk.injEq .. ▸ Option.some.inj hc
    have hqceq : qc = pub.commitmentsOut idx := hqc.symm
    have hcons : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) = qc := by
      rw [hqceq]; exact (hC.outputs idx).symm
    have htok : (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage).token = asset := htoken
    have hpre' : pool'.preimageOf qc = some (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
      rw [hpreEq, hqceq]; exact hread0
    have hord' : pool'.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r0⟩ := by
      rw [hoRandEq]
      exact applyOwnedRecords_reads (reg := applyRecords pool.preimageOf records)
        (fun cd hcd => by
          rw [List.mem_singleton] at hcd
          exact hcd ▸ ⟨⟨w.npkOut idx, w.token, w.valueOut idx⟩, hread0, hown.symm⟩)
        pool.ownedRandomOf qc (⟨Term.keccak selfInputs, r0⟩ : OwnedDisclosure) (by
          rw [List.mem_singleton]; rw [hqceq])
    have hvnz : (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage).value ≠ 0 := by
      show w.valueOut idx ≠ 0
      rw [hval]
      omega
    have hmem' : (qpos, (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage)) ∈
        pool'.live asset := by
      rw [hliveT, if_pos htoken.symm, ← hqpos, hposition]
      exact List.mem_append_left _ hidxmem
    refine ⟨⟨(⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage), hpre', hcons,
        hvnz, htok, hmem', r0, hown, hord'⟩, ?_, ?_⟩
    · rw [← hqpos, hposition, hbTarget]; omega
    · intro qasset' qcid' qpos' qc' hc' hne
      unfold update at hc'
      have hqposEq : qpos = (treeNumber, position) := by rw [← hqpos]
      by_cases ha' : qasset' = asset
      · rw [if_pos ha'] at hc'
        by_cases hcid' : qcid' = channelId
        · exact absurd (Prod.ext ha' hcid' : (qasset', qcid') = (asset, channelId)) hne
        · rw [if_neg hcid'] at hc'
          obtain ⟨_, hb', _⟩ := hinv asset qcid' qpos' qc' hc'
          intro hcontra
          rw [hqposEq] at hcontra
          rw [hcontra, hbOld] at hb'
          omega
      · rw [if_neg ha'] at hc'
        obtain ⟨_, hb', _⟩ := hinv qasset' qcid' qpos' qc' hc'
        intro hcontra
        rw [hqposEq] at hcontra
        rw [hcontra, hbOld] at hb'
        omega
  · have hc' : holdings qasset qcid = some (qpos, qc) := by
      by_cases ha : qasset = asset
      · subst ha
        rw [if_pos rfl] at hc
        by_cases hcid : qcid = channelId
        · exact absurd ⟨rfl, hcid⟩ heqch
        · rwa [if_neg hcid] at hc
      · rwa [if_neg ha] at hc
    obtain ⟨hcore, hbound, _⟩ := hframe qasset qcid qpos qc hc'
    have hboundOld := (hinv qasset qcid qpos qc hc').2.1
    have huniq_old := (hinv qasset qcid qpos qc hc').2.2
    refine ⟨hcore, hbound, ?_⟩
    intro qasset' qcid' qpos' qc' hc2 hne
    unfold update at hc2
    by_cases ha' : qasset' = asset
    · subst ha'
      rw [if_pos rfl] at hc2
      by_cases hcid' : qcid' = channelId
      · subst hcid'
        rw [if_pos rfl] at hc2
        obtain ⟨hqpos', _⟩ := Prod.mk.injEq .. ▸ Option.some.inj hc2
        intro hcontra
        rw [hcontra] at hqpos'
        have hq1 : qpos.1 = treeNumber := congrArg Prod.fst hqpos'.symm
        have hq2 : qpos.2 = position := congrArg Prod.snd hqpos'.symm
        rw [hq1, hbOld, hq2, hposition] at hboundOld
        omega
      · rw [if_neg hcid'] at hc2
        exact huniq_old qasset' qcid' qpos' qc' hc2 hne
    · rw [if_neg ha'] at hc2
      exact huniq_old qasset' qcid' qpos' qc' hc2 hne


/-- One `DepositStep` followed by its own `DepositMergeStep`'s effect on
    `HoldingWellFormed` — `.deposit`'s "some" (prior holding) branch:
    `DepositStep_frame_wellFormed` lifts every holding's own invariant
    into `midPool` first (`DepositStep` never touches `holdings`), the
    channel's own old holding and `DepositStep`'s own fresh note (read
    off `midPool` directly, the same construction `DepositStep_update_
    wellFormed`'s touched case uses) are the merge's own two nullified
    inputs, and the merged note becomes the new holding. Every OTHER
    holding's own position is disjoint from both nullified ones — the
    old holding's by `holdings`'s own uniqueness clause, the fresh
    note's by the same freshness bound `DepositStep_update_wellFormed`
    uses — so it survives `removeAll` into `pool'`. -/
theorem DepositMergeStep_update_wellFormed
    {N M : Nat} (pool pool' midPool : PoolState) (selfInputs : List Term) (asset amount : Nat)
    (channelId : Term) (hpos : 0 < amount)
    (w : TransactWitness N M) (pub : TransactPublic N M) (idx : Fin M)
    (spendTreeNumber treeNumber position : Nat)
    (oldTreeNumber oldPos : Nat) (oldHoldingVal : Term)
    (merged : Term) (mergeSpendTreeNumber mergedTreeNumber mergedPos : Nat)
    (hdstep : DepositStep pool (Term.keccak selfInputs) asset amount w pub idx
      spendTreeNumber treeNumber position midPool)
    (hmergestep : DepositMergeStep midPool (Term.keccak selfInputs) asset oldTreeNumber oldPos
      oldHoldingVal treeNumber position (pub.commitmentsOut idx) merged mergeSpendTreeNumber
      mergedTreeNumber mergedPos pool')
    (holdings : Nat → Term → Option ((Nat × Nat) × Term))
    (hsome : holdings asset channelId = some ((oldTreeNumber, oldPos), oldHoldingVal))
    (hinv : ∀ qasset qcid qpos qc, holdings qasset qcid = some (qpos, qc) →
      (∃ pre, pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool.live qasset ∧
        ∃ r, pre.npk = npk (Term.keccak selfInputs) r ∧
          pool.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r⟩) ∧
      qpos.2 < (pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos)) :
    ∀ qasset qcid qpos qc, (update holdings asset
        (update (holdings asset) channelId (some ((mergedTreeNumber, mergedPos), merged))))
      qasset qcid = some (qpos, qc) →
      (∃ pre, pool'.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ pool'.live qasset ∧
        ∃ r, pre.npk = npk (Term.keccak selfInputs) r ∧
          pool'.ownedRandomOf qc = some ⟨Term.keccak selfInputs, r⟩) ∧
      qpos.2 < (pool'.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', (update holdings asset
          (update (holdings asset) channelId (some ((mergedTreeNumber, mergedPos), merged))))
        qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  have hframe1 := DepositStep_frame_wellFormed pool midPool selfInputs asset amount w pub idx
    spendTreeNumber treeNumber position hdstep holdings hinv
  -- The channel's own OLD holding, read off `midPool`.
  obtain ⟨⟨preOld, hpreOld, hconsOld, hvalOld, htokOld, hmemOld, rOld, hnpkOld, hordOld⟩,
    hboundOld, _huniqOld⟩ := hframe1 asset channelId (oldTreeNumber, oldPos) oldHoldingVal hsome
  -- `DepositStep`'s own fresh note, read off `midPool` directly.
  obtain ⟨r0, hown, hcommit, htoken, htreeNumber, hposition, hN, hM, hC, rest, spent', records,
    hRoot, hRemove, hNullify, hSublist, hidxrec, heq⟩ := hdstep
  have hvalid : ∀ cp ∈ records, hashCommitment cp.2 = cp.1 :=
    fun cp hcp => transactOutputRecords_valid hC cp (hSublist.subset hcp)
  have hvalFresh : w.valueOut idx = amount := by
    have hout := hC.outputs idx
    rw [htoken, hcommit] at hout
    exact (Term.val.inj (Term.hash3_inj hout).2.2).symm
  have hnz0 : ¬ isZeroPreimage (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by
    unfold isZeroPreimage
    intro ⟨_, hv, _⟩
    rw [hvalFresh] at hv
    have hcheck : amount = 0 := hv
    omega
  have hread0 := applyRecords_reads hvalid pool.preimageOf _ _ hidxrec hnz0
  have hpreFreshMid : midPool.preimageOf (pub.commitmentsOut idx) =
      some (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) := by rw [heq]; exact hread0
  have hconsFresh : hashCommitment (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) =
      pub.commitmentsOut idx := (hC.outputs idx).symm
  have hcap : (transactAllOutputs w).length = M := List.length_ofFn
  have hboundsFresh := PoolOwnedSpendStep_fresh_position_bounds pool.closedTrees pool.leaves
    pool.roots (transactAllOutputs w)
  rw [hcap] at hboundsFresh
  have hbOld : (pool.leavesAt' treeNumber).length = insertStartPos pool.leaves M := by
    rw [htreeNumber]; exact hboundsFresh.2
  -- The two nullified keys, after `oldTreeNumber`/`treeNumber` are tied to
  -- the merge's own single spend tree.
  obtain ⟨hmergedTN, hmergedPosEq, w', pub', hC', rest', spent'', r', randomOut', hNonZero',
    hself', htoken', hnpkOut0', hmergedEq, hleaf0', hleaf1', hcommitOld', hcommitNew',
    holdTN', hnewTN', hroot', hremove', hnullify', hrandomOut', heq'⟩ := hmergestep
  have hvalid' : ∀ cp ∈ ownedOutputRecords w' pub', hashCommitment cp.2 = cp.1 :=
    ownedOutputRecords_valid hC'
  have hmemrec' : (pub'.commitmentsOut (0 : Fin 1),
      (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage)) ∈ ownedOutputRecords w' pub' := by
    unfold ownedOutputRecords; exact List.mem_ofFn.mpr ⟨0, rfl⟩
  have hnz0' : ¬ isZeroPreimage (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) :=
    npk_preimage_not_zero hnpkOut0'.symm
  have hread0' := applyRecords_reads hvalid' midPool.preimageOf _ _ hmemrec' hnz0'
  have hpreEq' : pool'.preimageOf = applyRecords midPool.preimageOf (ownedOutputRecords w' pub') := by
    rw [heq']
  have hoRandEq' : pool'.ownedRandomOf = applyOwnedRecords midPool.ownedRandomOf
      [(pub'.commitmentsOut (0 : Fin 1), (⟨Term.keccak selfInputs, randomOut'⟩ : OwnedDisclosure))] := by
    rw [heq', hself']
  have hliveT' : ∀ t, pool'.live t = if t = asset
      then withTreePositionsFrom mergedTreeNumber mergedPos (ownedNewNotes w') ++ rest'
      else midPool.live t := fun t => by rw [heq']
  have hlevA'' : ∀ tn, pool'.leavesAt' tn = PoolState.leavesAt
      (insertResult midPool.closedTrees midPool.leaves midPool.roots
        ((ownedNewNotes w').map hashCommitment)).1
      (insertResult midPool.closedTrees midPool.leaves midPool.roots
        ((ownedNewNotes w').map hashCommitment)).2.1
      (insertResult midPool.closedTrees midPool.leaves midPool.roots
        ((ownedNewNotes w').map hashCommitment)).2.2 tn := by
    intro tn; unfold PoolState.leavesAt'; rw [heq']
  have hge' : ∀ tn, (midPool.leavesAt' tn).length ≤ (pool'.leavesAt' tn).length := by
    intro tn
    rw [hlevA'']
    exact insertResult_leavesAt_length_ge midPool.closedTrees midPool.leaves midPool.roots
      ((ownedNewNotes w').map hashCommitment) tn
  have hbOld' := PoolOwnedSpendStep_fresh_position_bounds midPool.closedTrees midPool.leaves
    midPool.roots (ownedNewNotes w')
  have hcap' : (ownedNewNotes w').length = 1 := List.length_ofFn
  rw [hcap'] at hbOld'
  have hbOld2 : (midPool.leavesAt' (insertTreeNumber midPool.closedTrees midPool.leaves 1)).length =
      insertStartPos midPool.leaves 1 := hbOld'.2
  have hmergedMem : ((mergedTreeNumber, mergedPos),
      (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage)) ∈
      withTreePositionsFrom mergedTreeNumber mergedPos (ownedNewNotes w') := by
    unfold withTreePositionsFrom ownedNewNotes
    rw [withPositionsFrom_ofFn, List.map_ofFn]
    exact List.mem_ofFn.mpr ⟨0, rfl⟩
  -- The two removed positions, tied to `(oldTreeNumber, oldPos)`/`(treeNumber, position)`.
  have hremovedKeys : ownedSpentPositions mergeSpendTreeNumber pub' w' =
      [((mergeSpendTreeNumber, oldPos), (⟨npk pub'.ownerField (w'.randomIn 0), w'.token,
          w'.valueIn 0⟩ : CommitmentPreimage)),
        ((mergeSpendTreeNumber, position), (⟨npk pub'.ownerField (w'.randomIn 1), w'.token,
          w'.valueIn 1⟩ : CommitmentPreimage))] := by
    have hraw : ownedSpentPositions mergeSpendTreeNumber pub' w' =
        [((mergeSpendTreeNumber, w'.leavesIndices 0), (⟨npk pub'.ownerField (w'.randomIn 0),
            w'.token, w'.valueIn 0⟩ : CommitmentPreimage)),
          ((mergeSpendTreeNumber, w'.leavesIndices 1), (⟨npk pub'.ownerField (w'.randomIn 1),
            w'.token, w'.valueIn 1⟩ : CommitmentPreimage))] := by
      unfold ownedSpentPositions; rfl
    rw [hraw, hleaf0', hleaf1']
  have hwanted : ∀ y ∈ ownedSpentPositions mergeSpendTreeNumber pub' w',
      y.1 = (oldTreeNumber, oldPos) ∨ y.1 = (treeNumber, position) := by
    intro y hy
    rw [hremovedKeys] at hy
    rcases List.mem_cons.mp hy with heqy | hy'
    · left; rw [heqy, ← holdTN']
    · rcases List.mem_cons.mp hy' with heqy | hy''
      · right; rw [heqy, ← hnewTN']
      · exact absurd hy'' (by simp)
  have hvIn0 : w'.valueIn 0 ≠ 0 := by
    have hpreq0 : preOld = (⟨npk pub'.ownerField (w'.randomIn 0), w'.token, w'.valueIn 0⟩ :
        CommitmentPreimage) := hashCommitment_inj (hconsOld.trans hcommitOld'.symm)
    have hveq0 : preOld.value = w'.valueIn 0 := congrArg CommitmentPreimage.value hpreq0
    rw [← hveq0]; exact hvalOld
  have hvIn1 : w'.valueIn 1 ≠ 0 := by
    have hnzFresh : w.valueOut idx ≠ 0 := by rw [hvalFresh]; omega
    have hpreq1 : (⟨w.npkOut idx, w.token, w.valueOut idx⟩ : CommitmentPreimage) =
        (⟨npk pub'.ownerField (w'.randomIn 1), w'.token, w'.valueIn 1⟩ : CommitmentPreimage) :=
      hashCommitment_inj (hconsFresh.trans hcommitNew'.symm)
    have hveq1 : w.valueOut idx = w'.valueIn 1 := congrArg CommitmentPreimage.value hpreq1
    rw [← hveq1]; exact hnzFresh
  have hvOut0 : w'.valueOut 0 ≠ 0 := by
    have hbal := transactOwned_value_conserved w' pub' (by omega) (by omega) hC'
    simp only [listSum, List.ofFn_succ, List.ofFn_zero] at hbal
    omega
  intro qasset qcid qpos qc hc
  unfold update at hc
  by_cases heqch : qasset = asset ∧ qcid = channelId
  · obtain ⟨ha, hcidEq⟩ := heqch
    rw [ha, hcidEq] at hc ⊢
    rw [if_pos rfl, if_pos rfl] at hc
    obtain ⟨hqpos, hqc⟩ := Prod.mk.injEq .. ▸ Option.some.inj hc
    have hqceq : qc = pub'.commitmentsOut (0 : Fin 1) := by rw [← hqc, hmergedEq]
    have hcons : hashCommitment (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) = qc := by
      rw [hqceq]; exact (hC'.outputs 0).symm
    have hpre' : pool'.preimageOf qc = some (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage) := by
      rw [hpreEq', hqceq]; exact hread0'
    have heqnpk : npk pub'.ownerField randomOut' = npk pub'.ownerField r' := by
      rw [hrandomOut', hnpkOut0', hself']
    have hreq : randomOut' = r' := (npk_inj heqnpk).2
    have hord' : pool'.ownedRandomOf qc = some ⟨Term.keccak selfInputs, randomOut'⟩ := by
      rw [hoRandEq']
      exact applyOwnedRecords_reads (reg := applyRecords midPool.preimageOf (ownedOutputRecords w' pub'))
        (fun cd hcd => by
          rw [List.mem_singleton] at hcd
          exact hcd ▸ ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, hread0', (by rw [hself']; exact hrandomOut')⟩)
        midPool.ownedRandomOf qc (⟨Term.keccak selfInputs, randomOut'⟩ : OwnedDisclosure)
        (by rw [List.mem_singleton]; rw [hqceq, hself'])
    have hmem' : (qpos, (⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage)) ∈ pool'.live asset := by
      rw [hliveT', if_pos rfl, ← hqpos]
      exact List.mem_append_left _ hmergedMem
    refine ⟨⟨(⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩ : CommitmentPreimage), hpre', hcons,
        hvOut0, htoken', hmem', randomOut',
        (by rw [hreq]; exact hnpkOut0'), hord'⟩, ?_, ?_⟩
    · rw [← hqpos, hlevA'' mergedTreeNumber, hmergedTN]
      have h := hbOld'.1
      omega
    · intro qasset' qcid' qpos' qc' hc' hne
      unfold update at hc'
      have hqposEq : qpos = (mergedTreeNumber, mergedPos) := by rw [← hqpos]
      by_cases ha' : qasset' = asset
      · rw [if_pos ha'] at hc'
        by_cases hcid' : qcid' = channelId
        · exact absurd (Prod.ext ha' hcid') hne
        · rw [if_neg hcid'] at hc'
          obtain ⟨_, hb'mid, _⟩ := hframe1 asset qcid' qpos' qc' hc'
          intro hcontra
          rw [hqposEq] at hcontra
          have hq1 : qpos'.1 = mergedTreeNumber := congrArg Prod.fst hcontra
          have hq2 : qpos'.2 = mergedPos := congrArg Prod.snd hcontra
          rw [hq1, hmergedTN] at hb'mid
          rw [hbOld2, hq2, hmergedPosEq] at hb'mid
          omega
      · rw [if_neg ha'] at hc'
        obtain ⟨_, hb'mid, _⟩ := hframe1 qasset' qcid' qpos' qc' hc'
        intro hcontra
        rw [hqposEq] at hcontra
        have hq1 : qpos'.1 = mergedTreeNumber := congrArg Prod.fst hcontra
        have hq2 : qpos'.2 = mergedPos := congrArg Prod.snd hcontra
        rw [hq1, hmergedTN] at hb'mid
        rw [hbOld2, hq2, hmergedPosEq] at hb'mid
        omega
  · have hc' : holdings qasset qcid = some (qpos, qc) := by
      by_cases ha : qasset = asset
      · subst ha
        rw [if_pos rfl] at hc
        by_cases hcid : qcid = channelId
        · exact absurd ⟨rfl, hcid⟩ heqch
        · rwa [if_neg hcid] at hc
      · rwa [if_neg ha] at hc
    obtain ⟨⟨preU, hpreU, hconsU, hvalU, htokU, hmemU, rU, hnpkU, hordU⟩, hboundU, huniqU⟩ :=
      hframe1 qasset qcid qpos qc hc'
    have hneOld : qpos ≠ (oldTreeNumber, oldPos) :=
      (huniqU asset channelId (oldTreeNumber, oldPos) oldHoldingVal hsome
        (fun h => heqch ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩)).symm
    have hqboundPool := (hinv qasset qcid qpos qc hc').2.1
    have hneFresh : qpos ≠ (treeNumber, position) := by
      intro hcontra
      have hq1 : qpos.1 = treeNumber := congrArg Prod.fst hcontra
      have hq2 : qpos.2 = position := congrArg Prod.snd hcontra
      rw [hq1, hbOld, hq2, hposition] at hqboundPool
      omega
    have hpre'' : pool'.preimageOf qc = some preU := by
      rw [hpreEq']
      exact applyRecords_preserves_known hvalid' midPool.preimageOf qc preU hpreU hconsU
    have hord'' : pool'.ownedRandomOf qc = some ⟨Term.keccak selfInputs, rU⟩ := by
      rw [hoRandEq']
      exact applyOwnedRecords_preserves_known
        (reg := applyRecords midPool.preimageOf (ownedOutputRecords w' pub'))
        (fun cd hcd => by
          rw [List.mem_singleton] at hcd
          exact hcd ▸ ⟨⟨w'.npkOut 0, w'.token, w'.valueOut 0⟩, hread0', (by rw [hself']; exact hrandomOut')⟩)
        midPool.ownedRandomOf qc (Term.keccak selfInputs) rU preU hordU
        (applyRecords_preserves_known hvalid' midPool.preimageOf qc preU hpreU hconsU) hnpkU
    have hmem'' : (qpos, preU) ∈ pool'.live qasset := by
      rw [hliveT']
      by_cases ht : qasset = asset
      · rw [if_pos ht]
        apply List.mem_append.mpr
        right
        have hnotwanted : (qpos, preU) ∉ ownedSpentPositions mergeSpendTreeNumber pub' w' := by
          intro hbad
          rcases hwanted _ hbad with h1 | h1
          · exact hneOld h1
          · exact hneFresh h1
        have hmemperm : (qpos, preU) ∈ ownedSpentPositions mergeSpendTreeNumber pub' w' ++ rest' :=
          (removeAll_perm hremove').mem_iff.mp (ht ▸ hmemU)
        exact (List.mem_append.mp hmemperm).resolve_left hnotwanted
      · rw [if_neg ht]; exact hmemU
    refine ⟨⟨preU, hpre'', hconsU, hvalU, htokU, hmem'', rU, hnpkU, hord''⟩, ?_, ?_⟩
    · have h := hge' qpos.1; omega
    · intro qasset' qcid' qpos' qc' hc2 hne
      unfold update at hc2
      by_cases ha' : qasset' = asset
      · subst ha'
        rw [if_pos rfl] at hc2
        by_cases hcid' : qcid' = channelId
        · subst hcid'
          rw [if_pos rfl] at hc2
          obtain ⟨hqpos', _⟩ := Prod.mk.injEq .. ▸ Option.some.inj hc2
          intro hcontra
          rw [hcontra] at hqpos'
          have hq1 : qpos.1 = mergedTreeNumber := congrArg Prod.fst hqpos'.symm
          have hq2 : qpos.2 = mergedPos := congrArg Prod.snd hqpos'.symm
          rw [hq1] at hboundU
          rw [hmergedTN] at hboundU
          rw [hbOld2, hq2, hmergedPosEq] at hboundU
          omega
        · rw [if_neg hcid'] at hc2
          exact huniqU qasset' qcid' qpos' qc' hc2 hne
      · rw [if_neg ha'] at hc2
        exact huniqU qasset' qcid' qpos' qc' hc2 hne


/-- **The one per-`Step` preservation lemma for `HoldingWellFormed`**,
    replacing `holdings_preimage_nonzero_step`, `ownedRandom_known_step`,
    `held_note_owned_disclosure_step`, and `holdings_position_live_step`'s
    own case analyses with ONE. `.transfer`/the two bulk calls delegate to
    `PoolOwnedSpend_update_wellFormed`/`bulkTransferFold_wellFormed`
    (built on `PoolOwnedSpendStep_effects`); `.deposit` delegates to
    `DepositStep_update_wellFormed`/`DepositMergeStep_update_wellFormed`;
    every other case leaves `s.pool`/`s.holdings` untouched. -/
theorem holdingWellFormed_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hinv : HoldingWellFormed s)
    (hstep : Step sig appRel actor s call s') :
    HoldingWellFormed s' := by
  have hselfEq : s'.self = s.self := step_self sig appRel actor s s' call hstep
  unfold HoldingWellFormed at hinv ⊢
  rw [hselfEq]
  have trivial : s'.pool = s.pool → s'.holdings = s.holdings →
      ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
        (∃ pre, s'.pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
          pre.value ≠ 0 ∧ pre.token = qasset ∧ (qpos, pre) ∈ s'.pool.live qasset ∧
          ∃ r, pre.npk = npk s.self r ∧ s'.pool.ownedRandomOf qc = some ⟨s.self, r⟩) ∧
        qpos.2 < (s'.pool.leavesAt' qpos.1).length ∧
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
  | deposit channelId expectedHeld asset amount =>
    obtain ⟨_hcfg, _hheld, _hext, _hpos, hinner, _hchan, _hcfg2, _hself, _hnow, _hsigned⟩ := hstep
    obtain ⟨N, M, w, pub, idx, spendTreeNumber, treeNumber, position, midPool, hdstep,
      _hpoolsigned, hmatch⟩ := hinner
    have hpos' : 0 < amount := _hpos
    rcases hh : s.holdings asset channelId with _ | ⟨⟨oldTreeNumber, oldPos⟩, oldHoldingVal⟩
    · rw [hh] at hmatch
      obtain ⟨hpoolEq, hholdseq⟩ := hmatch
      rw [hpoolEq, hholdseq]
      exact DepositStep_update_wellFormed s.pool midPool s.selfInputs asset amount channelId hpos'
        w pub idx spendTreeNumber treeNumber position hdstep s.holdings hh hinv
    · rw [hh] at hmatch
      obtain ⟨merged, mergeSpendTreeNumber, mergedTreeNumber, mergedPos, hmergestep, hholdseq⟩ :=
        hmatch
      rw [hholdseq]
      exact DepositMergeStep_update_wellFormed s.pool s'.pool midPool s.selfInputs asset amount
        channelId hpos' w pub idx spendTreeNumber treeNumber position oldTreeNumber oldPos oldHoldingVal
        merged mergeSpendTreeNumber mergedTreeNumber mergedPos hdstep hmergestep s.holdings
        hh hinv
  | challenge fp proof candidate challenger =>
    obtain ⟨_, _, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    exact trivial hpoolEq hholdEq
  | checkpoint fp proof candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    exact trivial hpoolEq hholdEq
  | conclude fp candidate =>
    obtain ⟨_, _, _, _, hpoolEq, hholdEq, _⟩ := hstep
    exact trivial hpoolEq hholdEq
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
      else [(⟨npk s.self r, (outcome.get ⟨assetIndex, hidx⟩).asset,
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
         else some ((insertTreeNumber s.pool.closedTrees s.pool.leaves
             ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
                 if a.amount = 0 then none
                 else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ :
                   CommitmentPreimage)) ++
               (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                   (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                     (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
                then []
                else [(⟨npk s.self r, (outcome.get ⟨assetIndex, hidx⟩).asset,
                  heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                    (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ :
                    CommitmentPreimage)])).length,
           insertStartPos s.pool.leaves
             ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
                 if a.amount = 0 then none
                 else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ :
                   CommitmentPreimage)) ++
               (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                   (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                     (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
                then []
                else [(⟨npk s.self r, (outcome.get ⟨assetIndex, hidx⟩).asset,
                  heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                    (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ :
                    CommitmentPreimage)])).length +
             ((transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
               (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.1.filterMap (fun a =>
                 if a.amount = 0 then none
                 else some (⟨a.destination, (outcome.get ⟨assetIndex, hidx⟩).asset, a.amount⟩ :
                   CommitmentPreimage)) ++
               (if heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                   (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                     (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2 = 0
                then []
                else [(⟨npk s.self r, (outcome.get ⟨assetIndex, hidx⟩).asset,
                  heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid -
                    (transferEffects (outcome.get ⟨assetIndex, hidx⟩).allocations
                      (heldValue s (outcome.get ⟨assetIndex, hidx⟩).asset cid) indices).2.2⟩ :
                    CommitmentPreimage)])).length - 1),
           commitment (npk s.self r) (outcome.get ⟨assetIndex, hidx⟩).asset
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
    exact PoolOwnedSpend_update_wellFormed s.pool s'.pool s.self assetOutcome.asset cid
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
    exact trivial hpoolEq hholdEq
  | bulkTransferAllAssets channelId outcome claimedStateHash =>
    obtain ⟨_hmode, _hsh, _hoh, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_wellFormed s.self channelId outcome newOutcome s.pool s'.pool
      s.holdings s'.holdings hfold hinv
  | bulkConcludeAndTransferAllAssets fp candidate =>
    obtain ⟨_hnotfinal, _hfinal, _hsigned, newOutcome, hfold, _hchanseq, _, _, _, _, _⟩ := hstep
    exact bulkTransferFold_wellFormed s.self (channelId fp) candidate.outcome newOutcome
      s.pool s'.pool s.holdings s'.holdings hfold hinv
  | tick newNow =>
    obtain ⟨_, _, hpoolEq, hholdEq, _⟩ := hstep
    exact trivial hpoolEq hholdEq
  | sign p d =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    exact trivial hpoolEq hholdEq
  | signNote pk msgHash =>
    obtain ⟨_, _, hpoolEq, _, hholdEq, _⟩ := hstep
    exact trivial hpoolEq hholdEq

/-- `HoldingWellFormed`, lifted to any reachable state. -/
theorem holdingWellFormed_reachable (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    HoldingWellFormed s :=
  reachable_preserves (P := HoldingWellFormed)
    (holdingWellFormed_genesis assets selfInputs pool0)
    (fun actor call s1 s2 hP hstep => holdingWellFormed_step sig appRel actor s1 s2 call hP hstep)
    hreach

/-- **Every held note's own preimage has a known owned disclosure, for
    some `ownerField` with `self = addressOf ownerField`.** One `Step` at
    a time. What `unbeatable_pays`'s own strategy needs to build
    `owned_spend_witness_exists`'s own `hOwned` hypothesis for the
    channel's held note, at an ARBITRARY reachable state. -/
theorem held_note_owned_disclosure_step (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (actor : Actor) (s s' : AdjudicatorState) (call : Call)
    (hinv : HoldingWellFormed s)
    (hstep : Step sig appRel actor s call s') :
    ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
      ∃ pre ownerField r, s'.pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.token = qasset ∧
        s.self = ownerField ∧ s'.pool.ownedRandomOf qc = some ⟨ownerField, r⟩ ∧
        npk ownerField r = pre.npk := by
  intro qasset qcid qpos qc hc
  obtain ⟨⟨pre, hpre, hconsist, _hval, htok, _hlive, r, hnpk, hown⟩, _, _⟩ :=
    holdingWellFormed_step sig appRel actor s s' call hinv hstep qasset qcid qpos qc hc
  have hselfEq : s'.self = s.self := step_self sig appRel actor s s' call hstep
  rw [hselfEq] at hnpk hown
  exact ⟨pre, s.self, r, hpre, hconsist, htok, rfl, hown, hnpk.symm⟩

/-- `held_note_owned_disclosure_step`'s own reachable-set lift: every held
    note's own preimage has a known owned disclosure, at ANY reachable
    state, not just one `Step` away from an already-established anchor —
    a direct projection of `HoldingWellFormed`'s own disclosure conjunct.
    What `unbeatable_pays`'s own strategy needs to build
    `owned_spend_witness_exists`'s own `hOwned` hypothesis for the
    channel's held note, at an ARBITRARY reachable `mid`. -/
theorem held_note_owned_disclosure_reachable (sig : SignatureAssumptions)
    (appRel : AdjudicatorState → FixedPart → List VariablePart → VariablePart → Prop)
    (assets : Nat → Prop) (selfInputs : List Term) (pool0 : PoolState) (s : AdjudicatorState)
    (hreach : Reachable sig appRel (genesis assets selfInputs pool0) s) :
    ∀ qasset qcid qpos qc, s.holdings qasset qcid = some (qpos, qc) →
      ∃ pre ownerField r, s.pool.preimageOf qc = some pre ∧ hashCommitment pre = qc ∧
        pre.token = qasset ∧
        s.self = ownerField ∧ s.pool.ownedRandomOf qc = some ⟨ownerField, r⟩ ∧
        npk ownerField r = pre.npk := by
  intro qasset qcid qpos qc hc
  obtain ⟨⟨pre, hpre, hconsist, _hval, htok, _hlive, r, hnpk, hown⟩, _, _⟩ :=
    holdingWellFormed_reachable sig appRel assets selfInputs pool0 s hreach qasset qcid qpos qc hc
  exact ⟨pre, s.self, r, hpre, hconsist, htok, rfl, hown, hnpk.symm⟩

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
    (hinv : HoldingWellFormed s)
    (hstep : Step sig appRel actor s call s') :
    ∀ qasset qcid qpos qc, s'.holdings qasset qcid = some (qpos, qc) →
      (∃ pre, (qpos, pre) ∈ s'.pool.live qasset ∧ hashCommitment pre = qc ∧
        ((∃ ownerField r, s.self = ownerField ∧ pre.npk = npk ownerField r) ∨
          ∃ r, pre.npk = npk s.self r)) ∧
      qpos.2 < (s'.pool.leavesAt' qpos.1).length ∧
      (∀ qasset' qcid' qpos' qc', s'.holdings qasset' qcid' = some (qpos', qc') →
        (qasset', qcid') ≠ (qasset, qcid) → qpos' ≠ qpos) := by
  intro qasset qcid qpos qc hc
  obtain ⟨⟨pre, _hpre, hconsist, _hval, _htok, hlive, r, hnpk, _hown⟩, hbound, huniq⟩ :=
    holdingWellFormed_step sig appRel actor s s' call hinv hstep qasset qcid qpos qc hc
  have hselfEq : s'.self = s.self := step_self sig appRel actor s s' call hstep
  rw [hselfEq] at hnpk
  exact ⟨⟨pre, hlive, hconsist, Or.inl ⟨s.self, r, rfl, hnpk⟩⟩, hbound, huniq⟩

end ArmadaLean.Adjudicator
