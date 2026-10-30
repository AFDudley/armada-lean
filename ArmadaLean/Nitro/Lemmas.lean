/-
  Nitro protocol specification: the `@[simp]` reading lemmas of the
  definitions and the proof helpers that `Safety.lean` uses. Each section
  follows one definition file, in dependency order: `Address.lean`,
  `Outcome.lean`, `Channel.lean`, `Adjudicator.lean`. (Rules E):
  `armada-laconic/docs/lean/writing-lean.md` (rules 3, 5, 6, 9).
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import ArmadaLean.Nitro.Adjudicator

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-! ## Addresses (`Address.lean`) -/

omit [DecidableEq E] in
@[simp] theorem FixedPart.address_eq (c : FixedPart) : (c.address : Address E) = .channel c := rfl

omit [DecidableEq E] in
@[simp] theorem Address.isExternal_external (e : E) :
    (Address.external e).isExternal = true := rfl

omit [DecidableEq E] in
@[simp] theorem Address.isExternal_channel (c : FixedPart) :
    (Address.channel c : Address E).isExternal = false := rfl

namespace Balances

@[simp] theorem get_nil (a : Address E) : Balances.get ([] : Balances E) a = 0 := rfl

theorem get_cons (k a : Address E) (w : Coins) (t : Balances E) :
    Balances.get ((k, w) :: t) a = if a = k then w else t.get a := by
  unfold Balances.get
  by_cases h : a = k
  · subst h; simp
  · simp [List.lookup_cons, beq_false_of_ne h, h]

/-- Dropping the entries of another address does not change a reading.
    Stated in `simp` normal form (`decide (x ≠ a)` becomes `!decide (x = a)`). -/
theorem get_filter_ne (b : Balances E) {a a' : Address E} (h : a' ≠ a) :
    Balances.get (b.filter (fun e => !decide (e.1 = a))) a' = b.get a' := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    by_cases hk : k = a
    · subst hk; simp [get_cons, h, ih]
    · simp [hk, get_cons, ih]

@[simp] theorem get_set (b : Balances E) (a a' : Address E) (v : Coins) :
    (b.set a v).get a' = if a' = a then v else b.get a' := by
  by_cases h : a' = a
  · subst h; simp [Balances.set, get_cons]
  · simp [Balances.set, get_cons, h, get_filter_ne b h]

@[simp] theorem get_add (b : Balances E) (a a' : Address E) (x : Coins) :
    (b.add a x).get a' = if a' = a then b.get a + x else b.get a' := by
  simp [Balances.add]

@[simp] theorem get_sub (b : Balances E) (a a' : Address E) (x : Coins) :
    (b.sub a x).get a' = if a' = a then b.get a - x else b.get a' := by
  simp [Balances.sub]

/-- The sum of the entries whose address satisfies `q`. `total`,
    `channelTotal` and `paidOutTotal` are instances. -/
def sumIf (q : Address E → Bool) (b : Balances E) : Coins :=
  ((b.filter (fun e => q e.1)).map (·.2)).sum

omit [DecidableEq E] in
@[simp] theorem sumIf_nil (q : Address E → Bool) : sumIf q [] = 0 := rfl

omit [DecidableEq E] in
theorem sumIf_cons (q : Address E → Bool) (k : Address E) (w : Coins) (t : Balances E) :
    sumIf q ((k, w) :: t) = (if q k then w else 0) + sumIf q t := by
  by_cases h : q k <;> simp [sumIf, h]

omit [DecidableEq E] in
theorem total_eq_sumIf (b : Balances E) : b.total = sumIf (fun _ => true) b := by
  simp [Balances.total, sumIf]

omit [DecidableEq E] in
theorem channelTotal_eq_sumIf (b : Balances E) :
    b.channelTotal = sumIf (fun a => decide (a.isExternal = false)) b := rfl

omit [DecidableEq E] in
theorem paidOutTotal_eq_sumIf (b : Balances E) :
    b.paidOutTotal = sumIf (fun a => decide (a.isExternal = true)) b := rfl

/-- The first entry of an address is one of the summed entries. -/
theorem get_le_sumIf (q : Address E → Bool) (b : Balances E) {a : Address E} (hq : q a = true) :
    b.get a ≤ sumIf q b := by
  induction b with
  | nil => simp
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    rw [get_cons, sumIf_cons]
    by_cases h : a = k
    · subst h; simp [hq]
    · simp only [h, if_false]; grind

/-- Each address has one entry. -/
def KeysNodup (b : Balances E) : Prop := (b.map Prod.fst).Nodup

omit [DecidableEq E] in
@[simp] theorem keysNodup_nil : KeysNodup ([] : Balances E) := List.nodup_nil

omit [DecidableEq E] in
theorem KeysNodup.filter {b : Balances E} (hb : b.KeysNodup) (p : Address E × Coins → Bool) :
    KeysNodup (b.filter p) :=
  List.Nodup.sublist ((List.filter_sublist).map _) hb

theorem KeysNodup.set {b : Balances E} (hb : b.KeysNodup) (a : Address E) (v : Coins) :
    KeysNodup (b.set a v) := by
  refine List.nodup_cons.2 ⟨?_, hb.filter _⟩
  simp

theorem KeysNodup.add {b : Balances E} (hb : b.KeysNodup) (a : Address E) (x : Coins) :
    KeysNodup (b.add a x) := hb.set _ _

theorem KeysNodup.sub {b : Balances E} (hb : b.KeysNodup) (a : Address E) (x : Coins) :
    KeysNodup (b.sub a x) := hb.set _ _

/-- With one entry per address, dropping `a` removes exactly `b.get a`. -/
theorem sumIf_filter_ne (q : Address E → Bool) {b : Balances E} (hb : b.KeysNodup) (a : Address E) :
    sumIf q (b.filter (fun e => decide (e.1 ≠ a))) + (if q a then b.get a else 0) = sumIf q b := by
  induction b with
  | nil => simp
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    have hk : k ∉ t.map Prod.fst := (List.nodup_cons.1 hb).1
    have ht : KeysNodup t := (List.nodup_cons.1 hb).2
    by_cases h : k = a
    · subst h
      have hself : t.filter (fun e => decide (e.1 ≠ k)) = t := by
        refine List.filter_eq_self.2 fun e he => ?_
        have : e.1 ≠ k := fun h' => hk (List.mem_map.2 ⟨e, he, h'⟩)
        simpa using this
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, hself, sumIf_cons, get_cons, if_true]
      grind
    · have := ih ht
      simp only [List.filter_cons, ne_eq, h, not_false_eq_true, decide_true, if_true, sumIf_cons,
        get_cons, Ne.symm h, if_false]
      grind

theorem sumIf_set (q : Address E → Bool) {b : Balances E} (hb : b.KeysNodup) (a : Address E) (v : Coins) :
    sumIf q (b.set a v) + (if q a then b.get a else 0) = sumIf q b + (if q a then v else 0) := by
  have := sumIf_filter_ne q hb a
  simp only [Balances.set, sumIf_cons]
  grind

/-- With one entry per address, the sum for one address is its reading. -/
theorem sumIf_eq_get {b : Balances E} (hb : b.KeysNodup) (d : Address E) :
    sumIf (fun a => decide (a = d)) b = b.get d := by
  have h := sumIf_filter_ne (fun a => decide (a = d)) hb d
  have h0 : sumIf (fun a => decide (a = d)) (b.filter (fun e => decide (e.1 ≠ d))) = 0 := by
    simp only [sumIf, List.filter_filter]
    rw [List.filter_eq_nil_iff.2 (by intro e _; simp)]
    rfl
  simp only [decide_true, if_true] at h
  grind

/-- A reading at a list position, when each address has one entry. -/
theorem get_of_getElem? {b : Balances E} (hb : b.KeysNodup) {j : Nat} {d : Address E} {x : Coins}
    (h : b[j]? = some (d, x)) : b.get d = x := by
  induction b generalizing j with
  | nil => simp at h
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    have hk : k ∉ t.map Prod.fst := (List.nodup_cons.1 hb).1
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [get_cons]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hdt : d ∈ t.map Prod.fst := List.mem_map.2 ⟨(d, x), List.mem_of_getElem? h, rfl⟩
      have hdk : d ≠ k := fun h' => hk (h' ▸ hdt)
      rw [get_cons, if_neg hdk]
      exact ih (List.nodup_cons.1 hb).2 h

/-- Nitro:162-163: an address with no entry reads zero. -/
theorem get_of_forall_ne {b : Balances E} {a : Address E} (h : ∀ e ∈ b, e.1 ≠ a) : b.get a = 0 := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    rw [get_cons, if_neg (Ne.symm (h _ (List.mem_cons_self ..)))]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- The balance effect of a transfer (`add b x`, then `sub a x`) on every
    sum, when `a` holds at least `x`. -/
theorem sumIf_add_sub (q : Address E → Bool) {b : Balances E} (hb : b.KeysNodup) (a d : Address E)
    {x : Coins} (hx : x ≤ b.get a) :
    sumIf q ((b.add d x).sub a x) + (if q a then x else 0) = sumIf q b + (if q d then x else 0) := by
  have h1 := sumIf_set q hb d (b.get d + x)
  have h2 := sumIf_set q (hb.add d x) a ((b.add d x).get a - x)
  have hge : x ≤ (b.add d x).get a := by
    rw [get_add]; split <;> grind
  simp only [Balances.sub, Balances.add] at h1 h2 hge ⊢
  split <;> split <;> grind


omit [DecidableEq E] in
/-- Every entry is either a channel entry or an external entry: `total` is
    the sum of `channelTotal` and `paidOutTotal`. No `KeysNodup` hypothesis
    needed: the split holds entry by entry. Used by `total_step` (below,
    `namespace Adjudicator`) to connect `held` (the `Adjudicator.held`
    field) to the balances sum, for the wallet conservation theorem
    (`Reachable.lean`, D10 ruling). -/
theorem total_eq_channelTotal_add_paidOutTotal (b : Balances E) :
    Balances.total b = Balances.channelTotal b + Balances.paidOutTotal b := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    have h3 : Balances.total ((k, w) :: t) = w + Balances.total t := by
      simp [Balances.total]
    rcases hk : k.isExternal with _ | _
    · have h1 : Balances.channelTotal ((k, w) :: t) = w + Balances.channelTotal t := by
        simp [Balances.channelTotal, hk]
      have h2 : Balances.paidOutTotal ((k, w) :: t) = Balances.paidOutTotal t := by
        simp [Balances.paidOutTotal, hk]
      grind
    · have h1 : Balances.channelTotal ((k, w) :: t) = Balances.channelTotal t := by
        simp [Balances.channelTotal, hk]
      have h2 : Balances.paidOutTotal ((k, w) :: t) = w + Balances.paidOutTotal t := by
        simp [Balances.paidOutTotal, hk]
      grind
end Balances

/-! ## Outcomes (`Outcome.lean`) -/

omit [DecidableEq E] in
@[simp] theorem Item.amount_alloc (a : Coins) : (Item.alloc a : Item E).amount = a := rfl

omit [DecidableEq E] in
@[simp] theorem Item.amount_guarantee (x : Coins) (ps : List (Address E)) :
    (Item.guarantee x ps).amount = x := rfl

omit [DecidableEq E] in
@[simp] theorem Entry.amount_mk (d : Address E) (i : Item E) : Entry.amount ⟨d, i⟩ = i.amount := rfl

namespace Allocation

omit [DecidableEq E] in
@[simp] theorem total_nil : Allocation.total ([] : Allocation E) = 0 := rfl

omit [DecidableEq E] in
@[simp] theorem total_cons (e : Entry E) (o : Allocation E) :
    Allocation.total (e :: o) = e.amount + Allocation.total o := by
  simp [Allocation.total]

omit [DecidableEq E] in
theorem total_append (o o' : Allocation E) :
    Allocation.total (o ++ o') = Allocation.total o + Allocation.total o' := by
  simp [Allocation.total]

omit [DecidableEq E] in
theorem total_take_succ {o : Allocation E} {k : Nat} {e : Entry E} (h : o[k]? = some e) :
    Allocation.total (o.take (k + 1)) = Allocation.total (o.take k) + e.amount := by
  rw [List.take_add_one, total_append, h]
  simp

omit [DecidableEq E] in
theorem total_take_mono (o : Allocation E) {i j : Nat} (h : i ≤ j) :
    Allocation.total (o.take i) ≤ Allocation.total (o.take j) := by
  have : o.take i = (o.take j).take i := by rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact List.Sublist.sum_le_sum (M := ℕ) ((List.take_sublist _ _).map _) (fun _ _ => Nat.zero_le _)

omit [DecidableEq E] in
theorem total_take_le (o : Allocation E) (k : Nat) :
    Allocation.total (o.take k) ≤ o.total :=
  List.Sublist.sum_le_sum (M := ℕ) ((List.take_sublist _ _).map _) (fun _ _ => Nat.zero_le _)

omit [DecidableEq E] in
theorem total_le_of_sublist {o o' : Allocation E} (h : o.Sublist o') : o.total ≤ o'.total :=
  List.Sublist.sum_le_sum (M := ℕ) (h.map _) (fun _ _ => Nat.zero_le _)

/-! ### `find` and `owed` -/

@[simp] theorem find_nil (d : Address E) : Allocation.find [] d = none := rfl

theorem find_cons (e : Entry E) (o : Allocation E) (d : Address E) :
    Allocation.find (e :: o) d = if e.dest = d then some e else o.find d := by
  by_cases h : e.dest = d <;> simp [Allocation.find, h]

theorem find_dest {o : Allocation E} {d : Address E} {e : Entry E} (h : o.find d = some e) :
    e.dest = d := by
  simpa using List.find?_some h

theorem find_eq_none {o : Allocation E} {d : Address E} :
    o.find d = none ↔ d ∉ o.map Entry.dest := by
  simp [Allocation.find, List.find?_eq_none]

theorem owed_cons (e : Entry E) (o : Allocation E) (d : Address E) :
    Allocation.owed (e :: o) d = if e.dest = d then e.amount else o.owed d := by
  by_cases h : e.dest = d <;> simp [Allocation.owed, find_cons, h]

/-- With distinct destinations, the entry at a position is the first entry
    for its destination. -/
theorem find_of_getElem? {o : Allocation E} (hnd : (o.map Entry.dest).Nodup) {j : Nat} {f : Entry E}
    (h : o[j]? = some f) : o.find f.dest = some f := by
  induction o generalizing j with
  | nil => simp at h
  | cons e t ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; simp [find_cons]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hne : e.dest ≠ f.dest := fun h' =>
        (List.nodup_cons.1 hnd).1 (h' ▸ List.mem_map.2 ⟨f, List.mem_of_getElem? h, rfl⟩)
      rw [find_cons, if_neg hne]
      exact ih (List.nodup_cons.1 hnd).2 h

/-! ### `dedup` -/

@[simp] theorem dedupFrom_nil (seen : List (Address E)) : Allocation.dedupFrom seen [] = [] := rfl

theorem dedupFrom_cons (seen : List (Address E)) (e : Entry E) (o : Allocation E) :
    Allocation.dedupFrom seen (e :: o) =
      if e.dest ∈ seen then Allocation.dedupFrom seen o
      else e :: Allocation.dedupFrom (e.dest :: seen) o := rfl

theorem dedupFrom_sublist (seen : List (Address E)) (o : Allocation E) :
    (Allocation.dedupFrom seen o).Sublist o := by
  induction o generalizing seen with
  | nil => simp
  | cons e t ih =>
    rw [dedupFrom_cons]
    split
    · exact (ih seen).cons e
    · exact (ih _).cons_cons e

theorem dest_not_mem_of_mem_dedupFrom {seen : List (Address E)} {o : Allocation E} {e : Entry E}
    (h : e ∈ Allocation.dedupFrom seen o) : e.dest ∉ seen := by
  induction o generalizing seen with
  | nil => simp at h
  | cons e' t ih =>
    rw [dedupFrom_cons] at h
    split at h
    · exact ih h
    · rcases List.mem_cons.1 h with rfl | h
      · assumption
      · exact fun hs => ih h (List.mem_cons_of_mem _ hs)

theorem dedupFrom_nodup (seen : List (Address E)) (o : Allocation E) :
    ((Allocation.dedupFrom seen o).map Entry.dest).Nodup := by
  induction o generalizing seen with
  | nil => simp
  | cons e t ih =>
    rw [dedupFrom_cons]
    split
    · exact ih seen
    · refine List.nodup_cons.2 ⟨fun hm => ?_, ih _⟩
      obtain ⟨f, hf, hfe⟩ := List.mem_map.1 hm
      exact dest_not_mem_of_mem_dedupFrom hf (hfe ▸ List.mem_cons_self ..)

theorem dedup_nodup (o : Allocation E) : (o.dedup.map Entry.dest).Nodup := dedupFrom_nodup [] o

theorem dedup_sublist (o : Allocation E) : o.dedup.Sublist o := dedupFrom_sublist [] o

theorem find_dedupFrom (seen : List (Address E)) (o : Allocation E) (d : Address E) :
    (Allocation.dedupFrom seen o).find d = if d ∈ seen then none else o.find d := by
  induction o generalizing seen with
  | nil => simp
  | cons e t ih =>
    rw [dedupFrom_cons, find_cons]
    by_cases hs : e.dest ∈ seen
    · rw [if_pos hs, ih]
      by_cases hd : e.dest = d
      · subst hd; simp [hs]
      · simp [hd]
    · rw [if_neg hs, find_cons, ih]
      by_cases hd : e.dest = d
      · subst hd; simp [hs]
      · have : d ≠ e.dest := Ne.symm hd
        simp [hd, this]

@[simp] theorem find_dedup (o : Allocation E) (d : Address E) : o.dedup.find d = o.find d := by
  simp [Allocation.dedup, find_dedupFrom]

@[simp] theorem owed_dedup (o : Allocation E) (d : Address E) : o.dedup.owed d = o.owed d := by
  simp [Allocation.owed]

/-! ### `payout` and `paidTo` -/

omit [DecidableEq E] in
@[simp] theorem payout_nil (held : Coins) : Allocation.payout held ([] : Allocation E) = [] := rfl

omit [DecidableEq E] in
@[simp] theorem payout_cons (held : Coins) (e : Entry E) (o : Allocation E) :
    Allocation.payout held (e :: o) =
      (e.dest, min e.amount held) :: Allocation.payout (held - min e.amount held) o := rfl

omit [DecidableEq E] in
theorem payout_map_fst (held : Coins) (o : Allocation E) :
    (o.payout held).map Prod.fst = o.map Entry.dest := by
  induction o generalizing held with
  | nil => rfl
  | cons e t ih => simp [ih]

omit [DecidableEq E] in
/-- ForceMove:1837-1853: entry `k` is paid `min(amount, held − total before k)`. -/
theorem payout_getElem? {held : Coins} {o : Allocation E} {k : Nat} {e : Entry E}
    (h : o[k]? = some e) :
    (o.payout held)[k]? = some (e.dest, min e.amount (held - Allocation.total (o.take k))) := by
  induction o generalizing held k with
  | nil => simp at h
  | cons e' t ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      rw [payout_cons, List.getElem?_cons_succ, ih h, List.take_succ_cons, total_cons]
      congr 3
      grind

omit [DecidableEq E] in
theorem payout_sum_le (held : Coins) (o : Allocation E) : ((o.payout held).map (·.2)).sum ≤ held := by
  induction o generalizing held with
  | nil => simp
  | cons e t ih =>
    have := ih (held - min e.amount held)
    simp only [payout_cons, List.map_cons, List.sum_cons]
    grind

omit [DecidableEq E] in
theorem payout_keysNodup {held : Coins} {o : Allocation E} (h : (o.map Entry.dest).Nodup) :
    Balances.KeysNodup (o.payout held) := by
  unfold Balances.KeysNodup; rwa [payout_map_fst]

/-- `paidTo` reads the payout of the deduplicated allocation. -/
theorem paidTo_eq_get (held : Coins) (o : Allocation E) (d : Address E) :
    o.paidTo held d = Balances.get (o.dedup.payout held) d :=
  Balances.sumIf_eq_get (payout_keysNodup (dedup_nodup o)) d

/-- A payout reading is at most the first entry's amount. -/
theorem payout_get_le_owed (held : Coins) (o : Allocation E) (d : Address E) :
    Balances.get (o.payout held) d ≤ o.owed d := by
  induction o generalizing held with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons]
    by_cases h : e.dest = d
    · simp [h]
    · simp only [Ne.symm h, if_false, h]; exact ih _

/-- When the coins held cover the total, each first entry is paid in full. -/
theorem owed_le_payout_get {held : Coins} {o : Allocation E} (h : o.total ≤ held) (d : Address E) :
    o.owed d ≤ Balances.get (o.payout held) d := by
  induction o generalizing held with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons]
    rw [total_cons] at h
    by_cases hd : e.dest = d
    · simp only [hd, if_true]; grind
    · simp only [Ne.symm hd, if_false, hd]; exact ih (by grind)

theorem paidTo_le_held (held : Coins) (o : Allocation E) (d : Address E) : o.paidTo held d ≤ held := by
  rw [paidTo_eq_get]
  refine le_trans (Balances.get_le_sumIf (fun _ => true) _ rfl) ?_
  rw [← Balances.total_eq_sumIf]
  exact payout_sum_le held _

/-- With distinct destinations, `paidTo` at the destination of entry `j` is
    the priority formula. -/
theorem paidTo_of_getElem? {held : Coins} {o : Allocation E} (hd : o.dedup = o) {j : Nat} {f : Entry E}
    (h : o[j]? = some f) :
    o.paidTo held f.dest = min f.amount (held - Allocation.total (o.take j)) := by
  have hnd : (o.map Entry.dest).Nodup := hd ▸ dedup_nodup o
  rw [paidTo_eq_get, hd]
  exact Balances.get_of_getElem? (payout_keysNodup hnd) (payout_getElem? h)

/-! ### `reduceOwed` -/

@[simp] theorem reduceOwed_nil (d : Address E) (x : Coins) : Allocation.reduceOwed [] d x = [] := rfl

theorem reduceOwed_cons (e : Entry E) (o : Allocation E) (d : Address E) (x : Coins) :
    Allocation.reduceOwed (e :: o) d x =
      if e.dest = d then { e with item := .alloc (e.amount - x) } :: o
      else e :: Allocation.reduceOwed o d x := rfl

theorem owed_reduceOwed (o : Allocation E) (d d' : Address E) (x : Coins) :
    (o.reduceOwed d x).owed d' = if d' = d then o.owed d - x else o.owed d' := by
  induction o with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [reduceOwed_cons]
    by_cases he : e.dest = d
    · subst he
      by_cases hd : d' = e.dest
      · subst hd; simp [owed_cons, Entry.amount]
      · simp [owed_cons, hd, Ne.symm hd]
    · rw [if_neg he, owed_cons, owed_cons, ih]
      by_cases hd : d' = d
      · subst hd; simp [he]
      · simp [owed_cons, hd]

/-- Reducing the amount owed to `d` by `x` leaves every other destination's
    first entry untouched, and rewrites `d`'s own first entry (if any) to an
    `.alloc` of its old amount minus `x` (`reduceOwed_cons`): only the FIRST
    match for `d` is ever rewritten, and always into that shape, whatever
    its own item used to be. -/
theorem find_reduceOwed (o : Allocation E) (d d' : Address E) (x : Coins) :
    (o.reduceOwed d x).find d' =
      if d' = d then (o.find d).map (fun e => (⟨d, .alloc (e.amount - x)⟩ : Entry E))
      else o.find d' := by
  induction o with
  | nil => simp [Allocation.reduceOwed]
  | cons e t ih =>
    rw [reduceOwed_cons]
    by_cases he : e.dest = d
    · subst he
      by_cases hd : d' = e.dest
      · subst hd; simp [find_cons]
      · simp [find_cons, hd, Ne.symm hd]
    · by_cases hd : d' = d
      · subst hd; simp [find_cons, he, ih]
      · simp only [if_neg he, find_cons, ih, if_neg hd]

/-- The amount owed to one destination never exceeds the allocation's whole
    total: `d`'s own entry (if any) is one summand of a sum of
    non-negatives. -/
theorem owed_le_total (o : Allocation E) (d : Address E) : o.owed d ≤ o.total := by
  induction o with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [owed_cons, total_cons]
    by_cases h : e.dest = d
    · rw [if_pos h]; grind
    · rw [if_neg h]; grind

/-- Reducing the amount owed to `d` by `x` (at most what `d` is owed) drops
    the total by exactly `x`: only `d`'s own first entry changes, by exactly
    `x` (`reduceOwed_cons`). Stated additively (`+ x = `) to avoid `Coins`
    truncated subtraction on either side. -/
theorem total_reduceOwed (o : Allocation E) (d : Address E) {x : Coins} (hx : x ≤ o.owed d) :
    (o.reduceOwed d x).total + x = o.total := by
  induction o with
  | nil => simp [Allocation.owed] at hx; simp [hx]
  | cons e t ih =>
    rw [owed_cons] at hx
    rw [reduceOwed_cons]
    by_cases he : e.dest = d
    · subst he
      rw [if_pos rfl] at hx ⊢
      have hv : Entry.amount ({ e with item := .alloc (e.amount - x) } : Entry E) = e.amount - x :=
        rfl
      rw [total_cons, hv, total_cons]
      grind
    · rw [if_neg he] at hx ⊢
      rw [total_cons, total_cons]
      have := ih hx
      grind

/-! ### Priority position, and one allocation ahead of another

`turbo_redistribution_unbeatable` (`Liveness.lean`, Nitro:775-777) compares
two states of one channel's allocation. `get_payout` is the priority formula
(Nitro:747-749) on any list. `dueBefore`, `Precedes` and `dueAfter` locate the
first entry of one destination in priority order. `AheadOf` is the per-channel
part of `Adjudicator.Ahead`. -/

/-- An entry's destination and whether it is a guarantee. `transfer` never
    changes this pair when it pays an allocation item (`map_kind_reduceOwed`). -/
def _root_.ArmadaLean.Nitro.Entry.kind (e : Entry E) : Address E × Bool :=
  (e.dest, e.item.isGuarantee)

/-- Nitro:747-749, on any list: the first entry for `b` receives
    `min(amount, held − the total of the entries ahead of it)`.
    `Balances.get` and `owed` both read the first entry for `b`, so the list
    need not be deduplicated. -/
theorem get_payout (held : Coins) (o : Allocation E) (b : Address E) :
    Balances.get (o.payout held) b =
      min (o.owed b) (held - Allocation.total (o.takeWhile (fun e => !decide (e.dest = b)))) := by
  induction o generalizing held with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons, List.takeWhile_cons]
    by_cases h : e.dest = b
    · simp [h]
    · simp only [Ne.symm h, h, if_false, ih, decide_false, Bool.not_false, if_true, total_cons]
      congr 1
      rcases le_total e.amount held with h1 | h1 <;> simp [h1] <;> unfold Coins at * <;> omega

/-- The entries ahead of `b`'s first entry, and that entry, are part of the
    total. -/
theorem total_takeWhile_add_owed_le (o : Allocation E) (b : Address E) :
    Allocation.total (o.takeWhile (fun e => !decide (e.dest = b))) + o.owed b ≤ o.total := by
  induction o with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [owed_cons, List.takeWhile_cons, total_cons]
    by_cases h : e.dest = b
    · simp [h]
    · simp only [h, decide_false, Bool.not_false, if_true, if_false, total_cons]
      unfold Coins at *
      omega

/-- Paying `x` to `c`'s first entry lowers the total ahead of `b`'s first
    entry by `x` when `c`'s entry lies ahead of `b`'s, and by nothing
    otherwise. -/
theorem total_takeWhile_reduceOwed (o : Allocation E) (b c : Address E) {x : Coins}
    (hx : x ≤ o.owed c) :
    Allocation.total ((o.reduceOwed c x).takeWhile (fun e => !decide (e.dest = b))) +
        (if c ∈ (o.map Entry.dest).takeWhile (fun d => !decide (d = b)) then x else 0) =
      Allocation.total (o.takeWhile (fun e => !decide (e.dest = b))) := by
  induction o with
  | nil => simp
  | cons e t ih =>
    rw [owed_cons] at hx
    rw [reduceOwed_cons]
    by_cases hc : e.dest = c
    · rw [if_pos hc] at hx ⊢
      subst hc
      rw [List.takeWhile_cons, List.takeWhile_cons, List.map_cons, List.takeWhile_cons]
      by_cases hb : e.dest = b
      · simp [hb]
      · simp [hb]
        unfold Coins at *
        omega
    · rw [if_neg hc] at hx ⊢
      rw [List.takeWhile_cons, List.takeWhile_cons, List.map_cons, List.takeWhile_cons]
      by_cases hb : e.dest = b
      · simp [hb]
      · simp [hb, Ne.symm hc]
        rw [← ih hx]
        unfold Coins at *
        omega

/-- When `b`'s first entry lies ahead of `c`'s first entry, that entry and
    everything ahead of it lie ahead of `c`'s entry. -/
theorem total_takeWhile_lt (o : Allocation E) {b c : Address E} (hbc : b ≠ c)
    (hc : 0 < o.owed c) (hnot : c ∉ (o.map Entry.dest).takeWhile (fun d => !decide (d = b))) :
    Allocation.total (o.takeWhile (fun e => !decide (e.dest = b))) + o.owed b ≤
      Allocation.total (o.takeWhile (fun e => !decide (e.dest = c))) := by
  induction o with
  | nil => simp [Allocation.owed] at hc
  | cons e t ih =>
    rw [owed_cons] at hc
    by_cases hb : e.dest = b
    · subst hb
      simp [owed_cons, hbc]
    · have hec : e.dest ≠ c := by
        rintro rfl
        exact hnot (by simp [hb])
      rw [if_neg hec] at hc
      have hnot' : c ∉ (t.map Entry.dest).takeWhile (fun d => !decide (d = b)) := by
        simpa [List.takeWhile_cons, hb, Ne.symm hec] using hnot
      have := ih hc hnot'
      simp [hb, hec, owed_cons]
      unfold Coins at *
      omega

/-- `reduceOwed` rewrites the first entry for `c`, and `dedupFrom` keeps the
    first entry for `c` once `c` is not yet seen: the two commute. -/
theorem dedupFrom_reduceOwed (o : Allocation E) (c : Address E) (x : Coins) :
    ∀ seen, c ∉ seen →
      (o.reduceOwed c x).dedupFrom seen = (o.dedupFrom seen).reduceOwed c x := by
  induction o with
  | nil => intros; rfl
  | cons e t ih =>
    intro seen hc
    rw [reduceOwed_cons, dedupFrom_cons]
    by_cases hec : e.dest = c
    · have hs : e.dest ∉ seen := hec ▸ hc
      simp [hec, dedupFrom_cons, reduceOwed_cons, hc]
    · by_cases hs : e.dest ∈ seen
      · simp [hec, dedupFrom_cons, hs, ih seen hc]
      · have hc' : c ∉ e.dest :: seen := by simp [Ne.symm hec, hc]
        simp [hec, dedupFrom_cons, hs, reduceOwed_cons, ih _ hc']

/-- Paying an allocation item keeps every entry's kind. -/
theorem map_kind_reduceOwed {o : Allocation E} {c : Address E} {amt : Coins}
    (h : o.find c = some ⟨c, .alloc amt⟩) (x : Coins) :
    (o.reduceOwed c x).map Entry.kind = o.map Entry.kind := by
  induction o with
  | nil => rfl
  | cons e t ih =>
    rw [find_cons] at h
    rw [reduceOwed_cons]
    by_cases hec : e.dest = c
    · rw [if_pos hec] at h
      cases h
      simp [Entry.kind, Item.isGuarantee]
    · rw [if_neg hec] at h
      simp [hec, ih h]

/-- Two allocations with the same entry kinds find entries of the same kind. -/
theorem find_map_kind {o o' : Allocation E} (h : o.map Entry.kind = o'.map Entry.kind)
    (c : Address E) : (o.find c).map Entry.kind = (o'.find c).map Entry.kind := by
  induction o generalizing o' with
  | nil => cases o' <;> simp_all
  | cons e t ih =>
    cases o' with
    | nil => simp at h
    | cons e' t' =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hd : e.dest = e'.dest := congrArg Prod.fst h.1
      rw [find_cons, find_cons, ← hd]
      split
      · simp [h.1]
      · exact ih h.2

/-- An allocation item for `c` in one allocation is an allocation item for
    `c` in every allocation with the same entry kinds. -/
theorem find_alloc_of_map_kind {o o' : Allocation E} (h : o.map Entry.kind = o'.map Entry.kind)
    {c : Address E} {amt : Coins} (hf : o.find c = some ⟨c, .alloc amt⟩) :
    ∃ amt', o'.find c = some ⟨c, .alloc amt'⟩ := by
  have hk := find_map_kind h c
  rw [hf] at hk
  cases hf' : o'.find c with
  | none => rw [hf'] at hk; cases hk
  | some e' =>
    rw [hf'] at hk
    obtain ⟨d', i'⟩ := e'
    cases i' with
    | alloc a' =>
      simp [Entry.kind] at hk
      exact ⟨a', by rw [hk.1]⟩
    | guarantee x ps => simp [Entry.kind, Item.isGuarantee] at hk

/-- The coins due, in priority order, ahead of `b`'s first entry. -/
def dueBefore (o : Allocation E) (b : Address E) : Coins :=
  Allocation.total (o.dedup.takeWhile (fun e => !decide (e.dest = b)))

/-- `c`'s first entry lies ahead of `b`'s first entry in priority order. -/
def Precedes (o : Allocation E) (c b : Address E) : Prop :=
  c ∈ (o.dedup.map Entry.dest).takeWhile (fun d => !decide (d = b))

instance (o : Allocation E) (c b : Address E) : Decidable (o.Precedes c b) :=
  inferInstanceAs (Decidable (c ∈ _))

/-- The coins due behind `b`'s first entry. -/
def dueAfter (o : Allocation E) (b : Address E) : Coins :=
  o.dedup.total - (o.dueBefore b + o.owed b)

/-- Nitro:747-749, the amount `transfer` pays `b`. -/
theorem paidTo_eq_min (held : Coins) (o : Allocation E) (b : Address E) :
    o.paidTo held b = min (o.owed b) (held - o.dueBefore b) := by
  rw [paidTo_eq_get, get_payout, owed_dedup]; rfl

theorem paidTo_le_owed (held : Coins) (o : Allocation E) (b : Address E) :
    o.paidTo held b ≤ o.owed b := by
  rw [paidTo_eq_min]; exact min_le_left _ _

theorem dueBefore_add_owed_le (o : Allocation E) (b : Address E) :
    o.dueBefore b + o.owed b ≤ o.dedup.total := by
  rw [← owed_dedup]; exact total_takeWhile_add_owed_le o.dedup b

theorem not_precedes_self (o : Allocation E) (c : Address E) : ¬ o.Precedes c c := by
  intro h
  simpa using List.all_eq_true.1 List.all_takeWhile c h

theorem dedup_reduceOwed (o : Allocation E) (c : Address E) (x : Coins) :
    (o.reduceOwed c x).dedup = o.dedup.reduceOwed c x :=
  dedupFrom_reduceOwed o c x [] List.not_mem_nil

theorem dueBefore_reduceOwed (o : Allocation E) (b c : Address E) {x : Coins} (hx : x ≤ o.owed c) :
    (o.reduceOwed c x).dueBefore b + (if o.Precedes c b then x else 0) = o.dueBefore b := by
  unfold dueBefore Precedes
  rw [dedup_reduceOwed]
  exact total_takeWhile_reduceOwed o.dedup b c (by rw [owed_dedup]; exact hx)

theorem dedup_total_reduceOwed (o : Allocation E) (c : Address E) {x : Coins} (hx : x ≤ o.owed c) :
    (o.reduceOwed c x).dedup.total + x = o.dedup.total := by
  rw [dedup_reduceOwed]; exact total_reduceOwed o.dedup c (by rw [owed_dedup]; exact hx)

theorem dueBefore_add_owed_le_of_not_precedes (o : Allocation E) {b c : Address E} (hbc : b ≠ c)
    (hc : 0 < o.owed c) (hnot : ¬ o.Precedes c b) :
    o.dueBefore b + o.owed b ≤ o.dueBefore c := by
  rw [← owed_dedup] at hc
  rw [← owed_dedup o b]
  exact total_takeWhile_lt o.dedup hbc hc hnot

/-- A payment from an allocation never raises the coins due behind an entry. -/
theorem dueAfter_reduceOwed_le (o : Allocation E) (b c : Address E) {x : Coins}
    (hx : x ≤ o.owed c) : (o.reduceOwed c x).dueAfter b ≤ o.dueAfter b := by
  have h1 := dueBefore_reduceOwed o b c hx
  have h2 := dedup_total_reduceOwed o c hx
  have h3 := owed_reduceOwed o c b x
  unfold dueAfter
  by_cases hbc : b = c
  · subst hbc
    rw [if_neg (not_precedes_self o b)] at h1
    rw [if_pos rfl] at h3
    unfold Coins at *
    omega
  · rw [if_neg hbc] at h3
    split_ifs at h1 <;> unfold Coins at * <;> omega

/-- `AheadOf.cover` survives a `transfer` from `og` to `c`. When the
    payment is positive and `c`'s entry lies behind `b`'s, the held coins
    covered `b`'s entry and everything ahead of it (Nitro:747-749). In every
    other case the coins due behind `b` do not change, and the old cover
    applies. -/
theorem cover_pay {og op op' : Allocation E} {hg : Coins}
    (hcov : ∀ b, og.dueAfter b < op.dueAfter b → og.dueBefore b + og.owed b ≤ hg)
    (c : Address E) (hop : ∀ b, op'.dueAfter b ≤ op.dueAfter b) (b : Address E)
    (hlt : (og.reduceOwed c (og.paidTo hg c)).dueAfter b < op'.dueAfter b) :
    (og.reduceOwed c (og.paidTo hg c)).dueBefore b + (og.reduceOwed c (og.paidTo hg c)).owed b ≤
      hg - og.paidTo hg c := by
  have hx := paidTo_eq_min hg og c
  have hxo := paidTo_le_owed hg og c
  have h1 := dueBefore_reduceOwed og b c hxo
  have h2 := dedup_total_reduceOwed og c hxo
  have h3 := owed_reduceOwed og c b (og.paidTo hg c)
  have h4 := dueBefore_add_owed_le og b
  have h5 := hop b
  have hcov' := hcov b
  unfold dueAfter at hlt h5 hcov'
  by_cases hbc : b = c
  · subst hbc
    rw [if_neg (not_precedes_self og b)] at h1
    rw [if_pos rfl] at h3
    unfold Coins at *
    omega
  · rw [if_neg hbc] at h3
    by_cases hp : og.Precedes c b
    · rw [if_pos hp] at h1
      unfold Coins at *
      omega
    · rw [if_neg hp] at h1
      by_cases hx0 : og.paidTo hg c = 0
      · unfold Coins at *
        omega
      · have h6 := dueBefore_add_owed_le_of_not_precedes og hbc
          (lt_of_lt_of_le (Nat.pos_of_ne_zero hx0) hxo) hp
        unfold Coins at *
        omega

/-- One channel's allocation `og`, holding `hg`, is ahead of the same
    channel's allocation `op` in another state: the same entries, each owing
    no more, and where fewer coins are due behind an entry than in `op`, the
    held coins cover that entry and everything ahead of it. A transfer pays
    an entry behind `b` only when the coins cover `b` (Nitro:747-749), so the
    last field records why `og` paid more behind `b`. -/
structure AheadOf (og op : Allocation E) (hg : Coins) : Prop where
  kind : og.map Entry.kind = op.map Entry.kind
  owed_le : ∀ d, og.owed d ≤ op.owed d
  cover : ∀ b, og.dueAfter b < op.dueAfter b → og.dueBefore b + og.owed b ≤ hg

theorem AheadOf.refl (o : Allocation E) (hg : Coins) : o.AheadOf o hg :=
  ⟨rfl, fun _ => le_rfl, fun _ h => absurd h (lt_irrefl _)⟩

theorem AheadOf.mono {og op : Allocation E} {hg hg' : Coins} (h : og.AheadOf op hg)
    (hle : hg ≤ hg') : og.AheadOf op hg' :=
  ⟨h.kind, h.owed_le, fun b hb => le_trans (h.cover b hb) hle⟩

/-- A transfer from `og` alone keeps it ahead of `op`. -/
theorem AheadOf.pay_left {og op : Allocation E} {hg : Coins} {c : Address E} {amt : Coins}
    (h : og.AheadOf op hg) (hf : og.find c = some ⟨c, .alloc amt⟩) :
    (og.reduceOwed c (og.paidTo hg c)).AheadOf op (hg - og.paidTo hg c) where
  kind := (map_kind_reduceOwed hf _).trans h.kind
  owed_le d := by
    rw [owed_reduceOwed]
    split_ifs with hd
    · subst hd; exact le_trans (Nat.sub_le _ _) (h.owed_le _)
    · exact h.owed_le d
  cover := cover_pay h.cover c (fun _ => le_rfl)

/-- The same transfer from both allocations leaves `og` owing `c` no more
    than `op`. `hC`: `og`'s channel received, beyond `op`'s, at least what
    `og` paid out beyond `op`. When fewer coins are due behind `c` in `og`,
    `AheadOf.cover` makes `og` pay `c` in full. Otherwise `hC` bounds the
    priority formula. -/
theorem AheadOf.owed_pay_le {og op : Allocation E} {hg hp : Coins} (h : og.AheadOf op hg)
    (hC : hp + og.dedup.total ≤ hg + op.dedup.total) (c : Address E) :
    og.owed c - og.paidTo hg c ≤ op.owed c - op.paidTo hp c := by
  rw [paidTo_eq_min, paidTo_eq_min]
  have h1 := h.owed_le c
  have h2 := dueBefore_add_owed_le og c
  have h3 := dueBefore_add_owed_le op c
  by_cases hs : og.dueAfter c < op.dueAfter c
  · have := h.cover c hs
    unfold Coins at *
    omega
  · unfold dueAfter at hs
    unfold Coins at *
    omega

/-- The same transfer from both allocations keeps `og` ahead of `op`. -/
theorem AheadOf.pay_both {og op : Allocation E} {hg hp : Coins} {c : Address E} {ag ap : Coins}
    (h : og.AheadOf op hg) (hfg : og.find c = some ⟨c, .alloc ag⟩)
    (hfp : op.find c = some ⟨c, .alloc ap⟩) (hC : hp + og.dedup.total ≤ hg + op.dedup.total) :
    (og.reduceOwed c (og.paidTo hg c)).AheadOf (op.reduceOwed c (op.paidTo hp c))
      (hg - og.paidTo hg c) where
  kind := by rw [map_kind_reduceOwed hfg, map_kind_reduceOwed hfp]; exact h.kind
  owed_le d := by
    rw [owed_reduceOwed, owed_reduceOwed]
    split_ifs with hd
    · subst hd; exact h.owed_pay_le hC d
    · exact h.owed_le d
  cover := cover_pay h.cover c (fun b => dueAfter_reduceOwed_le op b c (paidTo_le_owed hp op c))

/-! ### `addTo` and `remove` -/

theorem addTo_cons (e : Entry E) (o : Allocation E) (d : Address E) (x : Coins) :
    Allocation.addTo (e :: o) d x =
      if e.dest = d then { e with item := .alloc (e.amount + x) } :: o
      else e :: Allocation.addTo o d x := rfl

theorem addTo_map_dest (o : Allocation E) (d : Address E) (x : Coins) :
    (o.addTo d x).map Entry.dest = o.map Entry.dest := by
  induction o with
  | nil => rfl
  | cons e t ih => rw [addTo_cons]; split <;> simp [*]

theorem find_addTo_of_ne (o : Allocation E) {d d' : Address E} (x : Coins) (h : d' ≠ d) :
    (o.addTo d x).find d' = o.find d' := by
  induction o with
  | nil => rfl
  | cons e t ih =>
    rw [addTo_cons]
    split
    · rename_i he; subst he; simp [find_cons, Ne.symm h]
    · rw [find_cons, find_cons, ih]

/-- Raising the amount owed to `d` by `x` rewrites `d`'s own first entry (if
    any) to an `.alloc` of its old amount plus `x` (`addTo_cons`): only the
    FIRST match for `d` is ever rewritten, and always into that shape,
    whatever its own item used to be. -/
theorem find_addTo_self (o : Allocation E) (d : Address E) (x : Coins) :
    (o.addTo d x).find d = (o.find d).map (fun e => (⟨d, .alloc (e.amount + x)⟩ : Entry E)) := by
  induction o with
  | nil => rfl
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · subst he; simp [find_cons]
    · simp [find_cons, he, ih]

theorem owed_addTo_self {o : Allocation E} {d : Address E} (x : Coins) (h : o.find d ≠ none) :
    (o.addTo d x).owed d = o.owed d + x := by
  induction o with
  | nil => simp at h
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · subst he; simp [owed_cons, Entry.amount]
    · rw [find_cons, if_neg he] at h
      rw [if_neg he, owed_cons, owed_cons, if_neg he, if_neg he, ih h]

theorem owed_addTo_of_ne (o : Allocation E) {d d' : Address E} (x : Coins) (h : d' ≠ d) :
    (o.addTo d x).owed d' = o.owed d' := by
  simp [Allocation.owed, find_addTo_of_ne o x h]

theorem total_addTo {o : Allocation E} {d : Address E} (x : Coins) (h : o.find d ≠ none) :
    (o.addTo d x).total = o.total + x := by
  induction o with
  | nil => simp at h
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · simp only [he, if_true, total_cons, Entry.amount]; simp only [Item.amount_alloc]; grind
    · rw [find_cons, if_neg he] at h
      rw [if_neg he, total_cons, total_cons, ih h]; grind

/-- `addTo` never raises the total by more than `x`, whether or not `d` is
    found (if not found it is a no-op, by the same recursion as
    `total_addTo`). -/
theorem total_addTo_le (o : Allocation E) (d : Address E) (x : Coins) :
    (o.addTo d x).total ≤ o.total + x := by
  induction o with
  | nil => simp [Allocation.addTo]
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · simp only [he, if_true, total_cons, Entry.amount]; simp only [Item.amount_alloc]; grind
    · simp only [he, if_false, total_cons]; grind

/-- `addTo` never lowers the amount owed anywhere: at `d` itself it only
    raises it (`owed_addTo_self`, or leaves it at `0` when `d` has no entry
    to raise); everywhere else it is unchanged (`owed_addTo_of_ne`). -/
theorem owed_addTo_ge (o : Allocation E) (d d' : Address E) (x : Coins) :
    o.owed d' ≤ (o.addTo d x).owed d' := by
  by_cases h : d' = d
  · subst h
    by_cases hf : o.find d' = none
    · simp [Allocation.owed, hf]
    · rw [owed_addTo_self x hf]; grind
  · rw [owed_addTo_of_ne o x h]

theorem find_remove (o : Allocation E) (d d' : Address E) :
    (o.remove d).find d' = if d' = d then none else o.find d' := by
  induction o with
  | nil => simp [Allocation.remove]
  | cons e t ih =>
    simp only [Allocation.remove, List.filter_cons, ne_eq, decide_not] at ih ⊢
    by_cases he : e.dest = d
    · subst he
      by_cases hd : d' = e.dest
      · subst hd; simp [ih]
      · simp [find_cons, Ne.symm hd, ih, hd]
    · by_cases hd : d' = d
      · subst hd; simp [he, find_cons, ih]
      · simp [he, find_cons, ih, hd]

theorem owed_remove_of_ne (o : Allocation E) {d d' : Address E} (h : d' ≠ d) :
    (o.remove d).owed d' = o.owed d' := by
  simp [Allocation.owed, find_remove, h]

/-- With distinct destinations, removing `d` lowers the total by its amount. -/
theorem total_remove {o : Allocation E} (hnd : (o.map Entry.dest).Nodup) (d : Address E) :
    (o.remove d).total + o.owed d = o.total := by
  induction o with
  | nil => simp [Allocation.remove, Allocation.owed]
  | cons e t ih =>
    have ht := ih (List.nodup_cons.1 hnd).2
    simp only [Allocation.remove, List.filter_cons] at ht ⊢
    rw [owed_cons]
    by_cases he : e.dest = d
    · subst he
      have hno : Allocation.find t e.dest = none :=
        find_eq_none.2 (List.nodup_cons.1 hnd).1
      have hown : Allocation.owed t e.dest = 0 := by simp [Allocation.owed, hno]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true,
        total_cons]
      grind
    · simp only [ne_eq, he, not_false_eq_true, decide_true, if_true, if_false, total_cons]
      grind

/-- Without distinctness, removing `d` still lowers the total by at least
    its (first-entry) owed amount: every duplicate entry for `d` only
    removes more. -/
theorem total_remove_le (o : Allocation E) (d : Address E) :
    (o.remove d).total + o.owed d ≤ o.total := by
  induction o with
  | nil => simp [Allocation.remove, Allocation.owed]
  | cons e t ih =>
    simp only [Allocation.remove, List.filter_cons] at ih ⊢
    rw [owed_cons]
    by_cases he : e.dest = d
    · subst he
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true,
        total_cons]
      grind
    · simp only [ne_eq, he, not_false_eq_true, decide_true, if_true, if_false, total_cons]
      grind

end Allocation

/-! ## Channels (`Channel.lean`) -/

namespace ChannelStatus

omit [DecidableEq E] in
@[simp] theorem mode_open (t : Nat) (now : Time) :
    (ChannelStatus.open t : ChannelStatus E).mode now = .open := rfl

omit [DecidableEq E] in
@[simp] theorem mode_challenged (t : Nat) (ch : Challenge E) (now : Time) :
    (ChannelStatus.challenged t ch).mode now = if ch.deadline ≤ now then .finalized else .challenge :=
  rfl

omit [DecidableEq E] in
@[simp] theorem mode_finalized (t : Nat) (f o : Outcome E) (now : Time) :
    (ChannelStatus.finalized t f o).mode now = .finalized := rfl

omit [DecidableEq E] in
@[simp] theorem finalOutcome_open (t : Nat) (now : Time) :
    (ChannelStatus.open t : ChannelStatus E).finalOutcome now = none := rfl

omit [DecidableEq E] in
@[simp] theorem finalOutcome_challenged (t : Nat) (ch : Challenge E) (now : Time) :
    (ChannelStatus.challenged t ch).finalOutcome now =
      if ch.deadline ≤ now then some ch.state.outcome else none := rfl

omit [DecidableEq E] in
@[simp] theorem finalOutcome_finalized (t : Nat) (f o : Outcome E) (now : Time) :
    (ChannelStatus.finalized t f o).finalOutcome now = some o := rfl

omit [DecidableEq E] in
@[simp] theorem finalizedWith_open (t : Nat) (now : Time) :
    (ChannelStatus.open t : ChannelStatus E).finalizedWith now = none := rfl

omit [DecidableEq E] in
@[simp] theorem finalizedWith_challenged (t : Nat) (ch : Challenge E) (now : Time) :
    (ChannelStatus.challenged t ch).finalizedWith now =
      if ch.deadline ≤ now then some ch.state.outcome else none := rfl

omit [DecidableEq E] in
@[simp] theorem finalizedWith_finalized (t : Nat) (f o : Outcome E) (now : Time) :
    (ChannelStatus.finalized t f o).finalizedWith now = some f := rfl

omit [DecidableEq E] in
@[simp] theorem turnNumRecord_open (t : Nat) :
    (ChannelStatus.open t : ChannelStatus E).turnNumRecord = t := rfl

omit [DecidableEq E] in
@[simp] theorem turnNumRecord_challenged (t : Nat) (ch : Challenge E) :
    (ChannelStatus.challenged t ch).turnNumRecord = t := rfl

omit [DecidableEq E] in
@[simp] theorem turnNumRecord_finalized (t : Nat) (f o : Outcome E) :
    (ChannelStatus.finalized t f o).turnNumRecord = t := rfl

omit [DecidableEq E] in
@[simp] theorem withOutcome_open (t : Nat) (o : Outcome E) :
    (ChannelStatus.open t).withOutcome o = .finalized t o o := rfl

omit [DecidableEq E] in
@[simp] theorem withOutcome_challenged (t : Nat) (ch : Challenge E) (o : Outcome E) :
    (ChannelStatus.challenged t ch).withOutcome o = .finalized t ch.state.outcome o := rfl

omit [DecidableEq E] in
@[simp] theorem withOutcome_finalized (t : Nat) (f o' o : Outcome E) :
    (ChannelStatus.finalized t f o').withOutcome o = .finalized t f o := rfl

omit [DecidableEq E] in
@[simp] theorem turnNumRecord_withOutcome (st : ChannelStatus E) (o : Outcome E) :
    (st.withOutcome o).turnNumRecord = st.turnNumRecord := by
  cases st <;> rfl

omit [DecidableEq E] in
/-- A stored outcome is replaced; the status is finalized with it. -/
@[simp] theorem finalOutcome_withOutcome (st : ChannelStatus E) (o : Outcome E) (now : Time) :
    (st.withOutcome o).finalOutcome now = some o := by
  cases st <;> rfl

omit [DecidableEq E] in
@[simp] theorem mode_withOutcome (st : ChannelStatus E) (o : Outcome E) (now : Time) :
    (st.withOutcome o).mode now = .finalized := by
  cases st <;> rfl

omit [DecidableEq E] in
/-- A payout keeps the outcome of finalization. -/
theorem finalizedWith_withOutcome {st : ChannelStatus E} {now : Time} {f : Outcome E}
    (h : st.finalizedWith now = some f) (o : Outcome E) (now' : Time) :
    (st.withOutcome o).finalizedWith now' = some f := by
  cases st <;> simp at h ⊢
  · exact h.2
  · exact h

omit [DecidableEq E] in
theorem isOpen_iff_ne (st : ChannelStatus E) (now : Time) :
    st.IsOpen now ↔ st.mode now ≠ .finalized := Iff.rfl

omit [DecidableEq E] in
/-- The mode is finalized exactly when a final outcome exists. -/
theorem mode_eq_finalized_iff (st : ChannelStatus E) (now : Time) :
    st.mode now = .finalized ↔ (st.finalOutcome now).isSome := by
  cases st <;> simp

omit [DecidableEq E] in
/-- The outcome of finalization exists exactly when the stored outcome does. -/
theorem finalizedWith_isSome_iff (st : ChannelStatus E) (now : Time) :
    (st.finalizedWith now).isSome ↔ (st.finalOutcome now).isSome := by
  cases st <;> simp

omit [DecidableEq E] in
theorem finalOutcome_mono {st : ChannelStatus E} {now now' : Time} {o : Outcome E}
    (h : st.finalOutcome now = some o) (hle : now ≤ now') : st.finalOutcome now' = some o := by
  cases st <;> simp at h ⊢
  · exact ⟨by grind, h.2⟩
  · exact h

omit [DecidableEq E] in
theorem finalizedWith_mono {st : ChannelStatus E} {now now' : Time} {o : Outcome E}
    (h : st.finalizedWith now = some o) (hle : now ≤ now') : st.finalizedWith now' = some o := by
  cases st <;> simp at h ⊢
  · exact ⟨by grind, h.2⟩
  · exact h

omit [DecidableEq E] in
theorem mode_finalized_mono {st : ChannelStatus E} {now now' : Time}
    (h : st.mode now = .finalized) (hle : now ≤ now') : st.mode now' = .finalized := by
  rw [mode_eq_finalized_iff] at h ⊢
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
  rw [finalOutcome_mono ho hle]; rfl

end ChannelStatus

omit [DecidableEq E] in
theorem SignedState.byMover_iff (ss : SignedState E) : ss.byMover = true ↔ ss.ByMover := by
  unfold SignedState.byMover SignedState.ByMover
  split <;> simp_all

/-- Every consecutive pair of a valid run is a valid move. -/
theorem validRun_getElem? {vt : State E → State E → Bool} {l : SupportProof E} (h : validRun vt l = true)
    {i : Nat} {m1 m2 : SignedState E} (h1 : l[i]? = some m1) (h2 : l[i + 1]? = some m2) :
    validMove vt m1 m2 = true := by
  induction l generalizing i with
  | nil => simp at h1
  | cons a t ih =>
    cases t with
    | nil => simp at h2
    | cons b t =>
      simp only [validRun, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h1 h2
        subst h1 h2; exact h.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact ih h.2 (by simpa using h1) (by simpa using h2)

/-- SATP:262-266: the one signed state of a supported candidate is signed by
    every participant. Operator ruling 2026-10-30. -/
theorem consensusRules_noUnilateralSupport :
    (consensusRules : Rules E).NoUnilateralSupport := by
  intro c proof candidate hcon q hq
  match proof, hcon with
  | [ss], hcon =>
    simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
    obtain ⟨⟨-, hchan⟩, hall⟩ := hcon
    exact ⟨ss, List.mem_singleton_self ss, hall q (by rw [hchan]; exact hq)⟩
  | [], hcon => simp [consensusRules] at hcon
  | _ :: _ :: _, hcon => simp [consensusRules] at hcon

/-- `(t0 + i) % n` covers every residue `k < n` as `i` ranges over `0, …,
    n - 1`: the modular-arithmetic fact `forceMoveRules_noUnilateralSupport`
    needs. -/
theorem turn_mod_exists (n t0 k : Nat) (hn : 0 < n) (hk : k < n) :
    ∃ i, i < n ∧ (t0 + i) % n = k := by
  have hrlt : t0 % n < n := Nat.mod_lt _ hn
  have hdm : t0 / n * n + t0 % n = t0 := Nat.div_add_mod' t0 n
  by_cases hrk : t0 % n ≤ k
  · refine ⟨k - t0 % n, by omega, ?_⟩
    have heq : t0 + (k - t0 % n) = (t0 / n) * n + k := by omega
    rw [heq]
    exact Nat.mul_add_mod_of_lt hk
  · refine ⟨n - t0 % n + k, by omega, ?_⟩
    have hmul : (t0 / n + 1) * n = t0 / n * n + n := Nat.add_one_mul _ _
    have heq : t0 + (n - t0 % n + k) = (t0 / n + 1) * n + k := by omega
    rw [heq]
    exact Nat.mul_add_mod_of_lt hk

/-- ForceMove:1379-1381: each of the `n` moves of a support run increases
    the turn number by one, so the `n` movers are one full cycle of
    `c.participants`; every participant signs its own move. Operator ruling
    2026-10-30. -/
theorem forceMoveRules_noUnilateralSupport (vt : State E → State E → Bool) :
    (forceMoveRules vt : Rules E).NoUnilateralSupport := by
  intro c proof candidate h q hq
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Option.all_eq_true] at h
  obtain ⟨⟨⟨⟨hlen, hhead⟩, hrun⟩, hchanAll⟩, hlast⟩ := h
  obtain ⟨k, hklt, hget⟩ := List.mem_iff_getElem.mp hq
  have hklt' : k < c.n := hklt
  have hn : 0 < c.n := by omega
  cases proof with
  | nil => simp at hlen; omega
  | cons m0 rest =>
    have hm0mover : m0.ByMover := (SignedState.byMover_iff _).1 (hhead m0 rfl)
    have hm0chan : m0.state.channel = c := hchanAll m0 List.mem_cons_self
    have hstep : ∀ i, (hbound : i + 1 < (m0 :: rest).length) →
        ∃ m1 m2, (m0 :: rest)[i]? = some m1 ∧ (m0 :: rest)[i + 1]? = some m2 ∧
          m2.state.channel = m1.state.channel ∧ m2.state.turnNum = m1.state.turnNum + 1 ∧
          m2.ByMover := by
      intro i hbound
      have h1 : (m0 :: rest)[i]? = some ((m0 :: rest)[i]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      have h2 : (m0 :: rest)[i + 1]? = some ((m0 :: rest)[i + 1]'hbound) :=
        List.getElem?_eq_getElem hbound
      have hm := validRun_getElem? hrun h1 h2
      simp only [validMove, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
        Bool.not_eq_true'] at hm
      obtain ⟨⟨⟨⟨⟨hc, ht⟩, -⟩, -⟩, -⟩, hmv⟩ := hm
      exact ⟨_, _, h1, h2, hc, ht, (SignedState.byMover_iff _).1 hmv⟩
    have hind : ∀ i, (hi : i < (m0 :: rest).length) →
        ∃ m, (m0 :: rest)[i]? = some m ∧ m.state.channel = c ∧
          m.state.turnNum = m0.state.turnNum + i ∧ m.ByMover := by
      intro i
      induction i with
      | zero => intro _; exact ⟨m0, rfl, hm0chan, by simp, hm0mover⟩
      | succ i ih =>
        intro hi
        obtain ⟨m, hmget, hmchan, hmturn, hmmv⟩ := ih (by omega)
        obtain ⟨m1, m2, hm1, hm2, hc, ht, hmv⟩ := hstep i (by omega)
        rw [hmget] at hm1
        injection hm1 with hm1
        subst hm1
        refine ⟨m2, hm2, by rw [hc]; exact hmchan, by omega, hmv⟩
    have hlenn : (m0 :: rest).length = c.n := hlen
    obtain ⟨i, hilt, hieq⟩ := turn_mod_exists (m0 :: rest).length m0.state.turnNum k
      (by omega) (by omega)
    obtain ⟨m, hmget, hmchan, hmturn, hmmv⟩ := hind i (by omega)
    have hmover : m.state.mover = some q := by
      unfold State.mover
      rw [hmchan, hmturn]
      have hcn : c.n = (m0 :: rest).length := hlenn.symm
      rw [hcn, hieq]
      rw [List.getElem?_eq_getElem hklt, hget]
    obtain ⟨mv, hmv1, hmv2⟩ := hmmv
    rw [hmover] at hmv1
    injection hmv1 with hmv1
    subst hmv1
    exact ⟨m, List.mem_of_getElem? hmget, hmv2⟩

/-- `L` lists each element once. Changing `f` at `a` alone, by `y`, changes
    the sum of `f` over `L` by `y` exactly when `a` is in `L`. Used by
    `Adjudicator.transfer_effect`. -/
theorem sum_map_update {α : Type} [DecidableEq α] {L : List α} (hL : L.Nodup) {f g : α → Nat}
    {a : α} {y : Nat} (hne : ∀ c, c ≠ a → f c = g c) (ha : f a + y = g a) :
    (L.map f).sum + (if a ∈ L then y else 0) = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons c t ih =>
    obtain ⟨hct, ht⟩ := List.nodup_cons.1 hL
    have ih := ih ht
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    by_cases hca : c = a
    · subst hca
      rw [if_neg hct] at ih
      simp only [true_or, if_true]
      omega
    · rw [hne c hca, if_congr (or_iff_right (Ne.symm hca)) rfl rfl]
      omega

/-! ## The adjudicator (`Adjudicator.lean`) -/

namespace Adjudicator

omit [DecidableEq E] in
/-- A status list without the entries of `c` reads the same at `c' ≠ c`. -/
theorem lookup_filter_ne (l : List (FixedPart × (ChannelStatus E))) {c c' : FixedPart} (h : c' ≠ c) :
    (l.filter (fun e => !decide (e.1 = c))).lookup c' = l.lookup c' := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    by_cases hk : k = c
    · subst hk; simp [List.lookup_cons, beq_false_of_ne h, ih]
    · by_cases hk' : c' = k
      · subst hk'; simp [hk]
      · simp [hk, List.lookup_cons, beq_false_of_ne hk', ih]

omit [DecidableEq E] in
@[simp] theorem statusOf_setStatus (s : Adjudicator E) (c : FixedPart) (st : ChannelStatus E)
    (c' : FixedPart) : (s.setStatus c st).statusOf c' = if c' = c then st else s.statusOf c' := by
  unfold statusOf setStatus
  by_cases h : c' = c
  · subst h; simp
  · simp [List.lookup_cons, beq_false_of_ne h, h, lookup_filter_ne _ h]

omit [DecidableEq E] in
@[simp] theorem setStatus_balances (s : Adjudicator E) (c : FixedPart) (st : ChannelStatus E) :
    (s.setStatus c st).balances = s.balances := rfl

omit [DecidableEq E] in
@[simp] theorem setStatus_held (s : Adjudicator E) (c : FixedPart) (st : ChannelStatus E) :
    (s.setStatus c st).held = s.held := rfl

omit [DecidableEq E] in
@[simp] theorem setStatus_now (s : Adjudicator E) (c : FixedPart) (st : ChannelStatus E) :
    (s.setStatus c st).now = s.now := rfl

omit [DecidableEq E] in
theorem statusOf_of_status {s t : Adjudicator E} (h : s.status = t.status) (c : FixedPart) :
    s.statusOf c = t.statusOf c := by
  unfold statusOf; rw [h]

omit [DecidableEq E] in
@[simp] theorem finalOutcome_channel (s : Adjudicator E) (c : FixedPart) :
    s.finalOutcome (.channel c) = (s.statusOf c).finalOutcome s.now := rfl

omit [DecidableEq E] in
@[simp] theorem finalOutcome_external (s : Adjudicator E) (e : E) :
    s.finalOutcome (.external e) = none := rfl

omit [DecidableEq E] in
@[simp] theorem finalizedWith_channel (s : Adjudicator E) (c : FixedPart) :
    s.finalizedWith (.channel c) = (s.statusOf c).finalizedWith s.now := rfl

omit [DecidableEq E] in
@[simp] theorem finalizedWith_external (s : Adjudicator E) (e : E) :
    s.finalizedWith (.external e) = none := rfl

omit [DecidableEq E] in
theorem mode_eq (s : Adjudicator E) (c : FixedPart) : s.mode c = (s.statusOf c).mode s.now := rfl

@[simp] theorem payTo_balances (s : Adjudicator E) (b : Address E) (x : Coins) :
    (s.payTo b x).balances = s.balances.add b x := by
  cases b <;> rfl

@[simp] theorem payTo_held (s : Adjudicator E) (b : Address E) (x : Coins) :
    (s.payTo b x).held = if b.isExternal then s.held - x else s.held := by
  cases b <;> rfl

@[simp] theorem payTo_status (s : Adjudicator E) (b : Address E) (x : Coins) :
    (s.payTo b x).status = s.status := by
  cases b <;> rfl

@[simp] theorem payTo_now (s : Adjudicator E) (b : Address E) (x : Coins) :
    (s.payTo b x).now = s.now := by
  cases b <;> rfl

theorem deposit_some {s : Adjudicator E} {a : Address E} {e x : Coins} {s' : Adjudicator E}
    (h : s.deposit a e x = some s') :
    (∃ c, a = .channel c ∧ c.kind = .ledger) ∧ s.balances.get a = e ∧
      s'.balances = s.balances.add a x ∧ s'.held = s.held + x ∧ s'.status = s.status ∧
      s'.now = s.now := by
  unfold deposit at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨⟨_, rfl, hc.1⟩, hc.2, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- The exact effect of a successful transfer, field by field. -/
theorem transfer_some {s : Adjudicator E} {a : FixedPart} {b : Address E} {s' : Adjudicator E}
    (h : s.transfer a b = some s') :
    ∃ o amt x, s.finalOutcome a.address = some (.allocation o) ∧ o.find b = some ⟨b, .alloc amt⟩ ∧
      x = o.paidTo (s.balances.get a.address) b ∧
      s'.balances = (s.balances.add b x).sub a.address x ∧
      s'.held = (if b.isExternal then s.held - x else s.held) ∧
      s'.status = (s.setStatus a ((s.statusOf a).withOutcome
        (.allocation (o.reduceOwed b x)))).status ∧
      s'.now = s.now ∧ a.kind = .ledger ∧ b.fundable = true := by
  unfold transfer at h
  split at h
  · rename_i hcond
    split at h
    · rename_i o hf
      split at h
      · rename_i d amt hfind
        have hd : d = b := Allocation.find_dest hfind
        subst hd
        cases h
        exact ⟨o, amt, _, hf, hfind, rfl, by simp, by simp, by simp, by simp, hcond.1, hcond.2⟩
      · cases h
    · cases h
  · cases h

/-- A transfer whose guard holds does not revert (the converse of
    `transfer_some`'s guard facts). -/
theorem transfer_ne_none {s : Adjudicator E} {a : FixedPart} {b : Address E} {o : Allocation E}
    {amt : Coins} (hk : a.kind = .ledger) (hb : b.fundable = true)
    (hf : s.finalOutcome a.address = some (.allocation o)) (hfind : o.find b = some ⟨b, .alloc amt⟩) :
    s.transfer a b ≠ none := by
  unfold transfer
  rw [if_pos ⟨hk, hb⟩, hf]
  simp [hfind]

/-- The exact effect of a successful reclaim. -/
theorem reclaim_some {s : Adjudicator E} {l v : FixedPart} {s' : Adjudicator E}
    (h : s.reclaim l v = some s') :
    ∃ oL oV x left right, s.finalOutcome l.address = some (.allocation oL) ∧
      s.finalizedWith v.address = some (.allocation oV) ∧
      oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧
      (oL.remove v.address).find left ≠ none ∧ (oL.remove v.address).find right ≠ none ∧
      oV.amountAt 0 + oV.amountAt 1 = x ∧
      s' = s.setStatus l ((s.statusOf l).withOutcome (.allocation
        (((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address))) ∧
      l.kind = .ledger ∧ v.kind = .virtual := by
  unfold reclaim at h
  split at h
  · rename_i hk
    split at h
    · rename_i oL oV hL hV
      split at h
      · rename_i d x left right hfind
        have hd : d = v.address := Allocation.find_dest hfind
        subst hd
        split at h
        · rename_i hc
          cases h
          exact ⟨oL, oV, x, left, right, hL, hV, hfind, hc.1, hc.2.1, hc.2.2, rfl, hk.1, hk.2⟩
        · cases h
      · cases h
    · cases h
  · cases h


omit [DecidableEq E] in
theorem challenge_some {apps : Apps E} {s : Adjudicator E} {challenger : Participant} {c : FixedPart}
    {proof : SupportProof E} {candidate : State E} {s' : Adjudicator E}
    (h : s.challenge apps challenger c proof candidate = some s') :
    (challenger ∈ c.participants ∧
      (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
      ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
       (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum))) ∧
    s' = s.setStatus c (.challenged candidate.turnNum ⟨candidate, s.now + c.challengeDuration⟩) := by
  unfold challenge at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

omit [DecidableEq E] in
theorem checkpoint_some {apps : Apps E} {s : Adjudicator E} {c : FixedPart} {proof : SupportProof E}
    {candidate : State E} {s' : Adjudicator E} (h : s.checkpoint apps c proof candidate = some s') :
    ((s.statusOf c).IsOpen s.now ∧
      (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
      (s.statusOf c).turnNumRecord < candidate.turnNum) ∧
    s' = s.setStatus c (.open candidate.turnNum) := by
  unfold checkpoint at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

omit [DecidableEq E] in
theorem conclude_some {s : Adjudicator E} {c : FixedPart} {ss : SignedState E} {s' : Adjudicator E}
    (h : s.conclude c ss = some s') :
    ((s.statusOf c).IsOpen s.now ∧ ConclusionProof c ss) ∧
    s' = s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome) := by
  unfold conclude at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

@[simp] theorem apply_deposit (apps : Apps E) (caller : Participant) (s : Adjudicator E) (a : Address E)
    (e x : Coins) : s.apply apps caller (.deposit a e x) = s.deposit a e x := rfl

@[simp] theorem apply_transfer (apps : Apps E) (caller : Participant) (s : Adjudicator E) (a : FixedPart)
    (b : Address E) : s.apply apps caller (.transfer a b) = s.transfer a b := rfl

@[simp] theorem apply_reclaim (apps : Apps E) (caller : Participant) (s : Adjudicator E)
    (l v : FixedPart) : s.apply apps caller (.reclaim l v) = s.reclaim l v := rfl

@[simp] theorem apply_challenge (apps : Apps E) (caller : Participant) (s : Adjudicator E)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) :
    s.apply apps caller (.challenge c proof candidate) = s.challenge apps caller c proof candidate :=
  rfl

@[simp] theorem apply_checkpoint (apps : Apps E) (caller : Participant) (s : Adjudicator E)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) :
    s.apply apps caller (.checkpoint c proof candidate) = s.checkpoint apps c proof candidate := rfl

@[simp] theorem apply_conclude (apps : Apps E) (caller : Participant) (s : Adjudicator E)
    (c : FixedPart) (ss : SignedState E) : s.apply apps caller (.conclude c ss) = s.conclude c ss := rfl

@[simp] theorem apply_tick (apps : Apps E) (caller : Participant) (s : Adjudicator E) (dt : Time) :
    s.apply apps caller (.tick dt) = some (s.tick dt) := rfl

omit [DecidableEq E] in
@[simp] theorem tick_balances (s : Adjudicator E) (dt : Time) : (s.tick dt).balances = s.balances :=
  rfl

omit [DecidableEq E] in
@[simp] theorem tick_held (s : Adjudicator E) (dt : Time) : (s.tick dt).held = s.held := rfl

omit [DecidableEq E] in
@[simp] theorem tick_status (s : Adjudicator E) (dt : Time) : (s.tick dt).status = s.status := rfl

omit [DecidableEq E] in
@[simp] theorem tick_now (s : Adjudicator E) (dt : Time) : (s.tick dt).now = s.now + dt := rfl

omit [DecidableEq E] in
@[simp] theorem tick_statusOf (s : Adjudicator E) (dt : Time) (c : FixedPart) :
    (s.tick dt).statusOf c = s.statusOf c := rfl

theorem applyAll_append (apps : Apps E) (l l' : List (Participant × (Op E))) (s : Adjudicator E) :
    applyAll apps (l ++ l') s = applyAll apps l' (applyAll apps l s) := by
  induction l generalizing s with
  | nil => rfl
  | cons p t ih => obtain ⟨c, op⟩ := p; exact ih _

theorem applyAll_singleton_of_some {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') :
    applyAll apps [(caller, op)] s = s' := by
  simp [applyAll, h]

/-- Only `tick` moves the clock, and only forward. -/
theorem apply_now_le {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    (h : s.apply apps caller op = some s') : s.now ≤ s'.now := by
  cases op with
  | deposit a e x => simp [(deposit_some h).2.2.2.2.2]
  | transfer a b => obtain ⟨_, _, _, _, _, _, _, _, _, hn, _, _⟩ := transfer_some h; simp [hn]
  | reclaim l v => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h; simp
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; simp
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; simp
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; simp
  | tick dt => simp at h; subst h; simp

/-- Any operation that is not `tick` never moves the clock at all (not just
    forward, `apply_now_le`): `deposit`, `transfer`, `reclaim`, `challenge`,
    `checkpoint` and `conclude` each write `balances`/`status` only. Used
    by `Threat.Round.exists` (`Strategy.lean`): landing a reaction's own
    calls, none of which may be `.tick` (`Op.HonestFeasible`), never
    advances the clock, so the round's own bound is trivially met. -/
theorem apply_now_eq_of_not_tick {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (hop : ∀ dt, op ≠ .tick dt) (h : s.apply apps caller op = some s') :
    s'.now = s.now := by
  cases op with
  | deposit a e x => exact (deposit_some h).2.2.2.2.2
  | transfer a b => obtain ⟨_, _, _, _, _, _, _, _, _, hn, _, _⟩ := transfer_some h; exact hn
  | reclaim l v => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h; rfl
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; rfl
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; rfl
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; rfl
  | tick dt => exact absurd rfl (hop dt)

/- Footprint (`writing-lean.md` rule 6): the operations that may write
    `balances`. go-nitro: `deposit` (MultiAssetHolder.sol:30-56) and `transfer`
    (MultiAssetHolder.sol:72-100) move holdings; the others do not. -/
def _root_.ArmadaLean.Nitro.Op.touchesBalances : Op E → Bool
  | .deposit .. | .transfer .. => true
  | _ => false

/- Footprint: the operations that may write `held`. -/
def _root_.ArmadaLean.Nitro.Op.touchesHeld : Op E → Bool
  | .deposit .. | .transfer .. => true
  | _ => false

/- Frame lemma: an operation outside the footprint of `balances` leaves it unchanged. -/
theorem apply_balances_frame {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (hop : op.touchesBalances = false) (h : s.apply apps caller op = some s') :
    s'.balances = s.balances := by
  cases op with
  | deposit a e x =>
    simp [Op.touchesBalances] at hop
  | transfer a b =>
    simp [Op.touchesBalances] at hop
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h
    rfl
  | challenge c proof cand =>
    obtain ⟨_, rfl⟩ := challenge_some h
    rfl
  | checkpoint c proof cand =>
    obtain ⟨_, rfl⟩ := checkpoint_some h
    rfl
  | conclude c ss =>
    obtain ⟨_, rfl⟩ := conclude_some h
    rfl
  | tick dt =>
    simp only [apply_tick, Option.some.injEq] at h
    subst h
    exact tick_balances s dt

/- Frame lemma: an operation outside the footprint of `held` leaves it unchanged. -/
theorem apply_held_frame {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (hop : op.touchesHeld = false) (h : s.apply apps caller op = some s') :
    s'.held = s.held := by
  cases op with
  | deposit a e x =>
    simp [Op.touchesHeld] at hop
  | transfer a b =>
    simp [Op.touchesHeld] at hop
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h
    rfl
  | challenge c proof cand =>
    obtain ⟨_, rfl⟩ := challenge_some h
    rfl
  | checkpoint c proof cand =>
    obtain ⟨_, rfl⟩ := checkpoint_some h
    rfl
  | conclude c ss =>
    obtain ⟨_, rfl⟩ := conclude_some h
    rfl
  | tick dt =>
    simp only [apply_tick, Option.some.injEq] at h
    subst h
    exact tick_held s dt

/-- The outcome of finalization never changes: `transfer` and `reclaim`
    rewrite only the stored outcome, through `withOutcome`, which keeps the
    outcome of finalization; `challenge`, `checkpoint` and `conclude` all
    require the channel to be open, so none can act on an already-finalized
    one. Used by `Adjudicator.reclaim`'s channel-types repair (operator
    ruling 2026-10-27): a virtual channel's outcome, once finalized, is
    exactly what `reclaim` reads. -/
theorem finalizedWith_apply {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    (h : s.apply apps caller op = some s') {c : FixedPart} {f : Outcome E}
    (hf : s.finalizedWith c.address = some f) : s'.finalizedWith c.address = some f := by
  have hn := apply_now_le h
  simp only [FixedPart.address_eq, finalizedWith_channel] at hf ⊢
  have hmode : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, ← ChannelStatus.finalizedWith_isSome_iff, hf]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := deposit_some h
    rw [statusOf_of_status hs]; exact ChannelStatus.finalizedWith_mono hf hn
  | tick dt => simp at h; subst h; exact ChannelStatus.finalizedWith_mono hf hn
  | transfer a b =>
    obtain ⟨_, _, _, -, -, -, -, -, hs, hn', -, -⟩ := transfer_some h
    rw [statusOf_of_status hs, hn']
    simp only [statusOf_setStatus]
    split
    · rename_i hca; subst hca; exact ChannelStatus.finalizedWith_withOutcome hf _ _
    · exact hf
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h
    simp only [statusOf_setStatus, setStatus_now]
    split
    · rename_i hcl; subst hcl; exact ChannelStatus.finalizedWith_withOutcome hf _ _
    · exact hf
  | challenge c' proof cand =>
    obtain ⟨⟨-, -, -, hm⟩, rfl⟩ := challenge_some h
    simp only [statusOf_setStatus, setStatus_now]
    split
    · rename_i hcc; subst hcc; rw [mode_eq] at hm
      rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hmode <;> cases hmode
    · exact hf
  | checkpoint c' proof cand =>
    obtain ⟨⟨ho, -⟩, rfl⟩ := checkpoint_some h
    simp only [statusOf_setStatus, setStatus_now]
    split
    · rename_i hcc; subst hcc; exact absurd hmode ho
    · exact hf
  | conclude c' ss =>
    obtain ⟨⟨ho, -⟩, rfl⟩ := conclude_some h
    simp only [statusOf_setStatus, setStatus_now]
    split
    · rename_i hcc; subst hcc; exact absurd hmode ho
    · exact hf

/-- The outcome of finalization is permanent over every reachable step, not
    just one, by induction on `finalizedWith_apply`. Used by
    `Adjudicator.reclaim`'s channel-types repair (operator ruling
    2026-10-27): a virtual channel's outcome, once finalized, is exactly
    what `reclaim` reads. -/
theorem finalizedWith_stable {apps : Apps E} {s s' : Adjudicator E}
    (h : Relation.ReflTransGen (Step apps) s s') {c : FixedPart} {f : Outcome E}
    (hf : s.finalizedWith c.address = some f) : s'.finalizedWith c.address = some f := by
  induction h with
  | refl => exact hf
  | tail _ hstep ih =>
    obtain ⟨_, _, _, _, happ⟩ := hstep
    exact finalizedWith_apply happ ih

/-! ### The coins-held invariant -/

/-- Nitro:230-231 with go-nitro's external payouts: each address has one
    balance entry, and the coins held equal the channel balances. -/
def HeldInv (s : Adjudicator E) : Prop :=
  s.balances.KeysNodup ∧ s.held = s.balances.channelTotal

omit [DecidableEq E] in
theorem heldInv_genesis : (genesis : Adjudicator E).HeldInv := ⟨Balances.keysNodup_nil, rfl⟩

theorem heldInv_step {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    (hi : s.HeldInv) (h : s.apply apps caller op = some s') : s'.HeldInv := by
  obtain ⟨hnd, hheld⟩ := hi
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c, rfl, -⟩, -, hb, hh, -, -⟩ := deposit_some h
    refine ⟨hb ▸ hnd.add _ _, ?_⟩
    have := Balances.sumIf_set (fun a => decide (a.isExternal = false)) hnd (.channel c)
      (s.balances.get (.channel c) + x)
    rw [Balances.channelTotal_eq_sumIf] at hheld ⊢
    rw [hh, hb]
    simp only [Balances.add]
    simp at this
    grind
  | transfer a b =>
    obtain ⟨o, _, x, -, -, hx, hb, hh, -, -, -, -⟩ := transfer_some h
    have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
    refine ⟨hb ▸ (hnd.add _ _).sub _ _, ?_⟩
    have := Balances.sumIf_add_sub (fun a => decide (a.isExternal = false)) hnd a.address b hxa
    have hle := Balances.get_le_sumIf (fun a => decide (a.isExternal = false)) s.balances
      (a := a.address) (by simp)
    rw [hh, hb, Balances.channelTotal_eq_sumIf]
    rw [Balances.channelTotal_eq_sumIf] at hheld
    cases b <;> simp at this ⊢ <;> grind
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h; exact ⟨hnd, hheld⟩
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; exact ⟨hnd, hheld⟩
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; exact ⟨hnd, hheld⟩
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; exact ⟨hnd, hheld⟩
  | tick dt => simp at h; subst h; exact ⟨hnd, hheld⟩

theorem heldInv_reachable {apps : Apps E} {s : Adjudicator E} (hr : Reachable apps s) : s.HeldInv := by
  induction hr with
  | refl => exact heldInv_genesis
  | tail _ hstep ih =>
    cases hstep with
    | mk caller op _ _ h => exact heldInv_step ih h

/-- **The balances sum moves only by a deposit's own amount.** `deposit`
    raises it by `x` (`sumIf_set`, the indicator always true); `transfer`
    moves `x` from the source to the destination, net zero (`sumIf_add_sub`,
    the indicator always true, so both correction terms are `x`); every
    other operation leaves `balances` untouched (`reclaim_some`,
    `challenge_some`, `checkpoint_some`, `conclude_some`, `tick`'s own
    definition). D10 ruling, used by `held_paidOut_step` and the wallet
    conservation theorem (`Reachable.lean`). -/
theorem total_step_deposit {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {a : Address E} {e x : Coins} (hnd : s.balances.KeysNodup)
    (h : s.apply apps caller (Op.deposit a e x) = some s') :
    s'.balances.total = s.balances.total + x := by
  obtain ⟨-, -, hb, -, -, -⟩ := deposit_some h
  have hs := Balances.sumIf_set (fun _ => true) hnd a (s.balances.get a + x)
  rw [hb]
  simp only [Balances.add, Balances.total_eq_sumIf]
  grind

/-- **The balances sum is unchanged by every on-chain operation except
    `deposit`.** `transfer` moves `x` from the source to the destination,
    net zero (`sumIf_add_sub`, the indicator always true, so both
    correction terms are `x`); `reclaim`, `challenge`, `checkpoint`,
    `conclude` and `tick` never write `balances` (`reclaim_some`,
    `challenge_some`, `checkpoint_some`, `conclude_some`, `tick`'s own
    definition). D10 ruling, used by `held_paidOut_step_no_deposit` and
    the wallet conservation theorem (`Reachable.lean`). -/
theorem total_step_no_deposit {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} (hnd : s.balances.KeysNodup) (hop : ∀ a e x, op ≠ Op.deposit a e x)
    (h : s.apply apps caller op = some s') :
    s'.balances.total = s.balances.total := by
  cases op with
  | deposit a e x => exact absurd rfl (hop a e x)
  | transfer a b =>
    obtain ⟨o, amt, x, -, -, hx, hb, -, -, -, -, -⟩ := transfer_some h
    have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
    have hs := Balances.sumIf_add_sub (fun _ => true) hnd a.address b hxa
    simp at hs
    rw [hb]
    simp [Balances.total_eq_sumIf]
    omega
  | reclaim l v => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h; simp
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; simp
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; simp
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; simp
  | tick dt => simp at h; subst h; simp

/-- **A deposit's `held` plus everything ever paid out rises by exactly its
    own amount.** `HeldInv` (`held = channelTotal`) at both `s` and `s'`
    (`heldInv_step`), joined with `total_step_deposit` through
    `total_eq_channelTotal_add_paidOutTotal`. The D10 ruling's own
    conservation fact, chain side: `Reachable.lean`'s
    `Nitro.network_conservation` restates this for a `Network`'s wallets. -/
theorem held_paidOut_step_deposit {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {a : Address E} {e x : Coins} (hi : s.HeldInv)
    (h : s.apply apps caller (Op.deposit a e x) = some s') :
    s'.held + s'.balances.paidOutTotal = s.held + s.balances.paidOutTotal + x := by
  have hi' : s'.HeldInv := heldInv_step hi h
  have e1 : s.held + s.balances.paidOutTotal = s.balances.total := by
    rw [hi.2, Balances.total_eq_channelTotal_add_paidOutTotal]
  have e2 : s'.held + s'.balances.paidOutTotal = s'.balances.total := by
    rw [hi'.2, Balances.total_eq_channelTotal_add_paidOutTotal]
  have ht := total_step_deposit hi.1 h
  rw [e2, ht, e1]

/-- **Every non-deposit operation leaves `held` plus everything ever paid
    out unchanged.** Same proof shape as `held_paidOut_step_deposit`. -/
theorem held_paidOut_step_no_deposit {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} (hi : s.HeldInv) (hop : ∀ a e x, op ≠ Op.deposit a e x)
    (h : s.apply apps caller op = some s') :
    s'.held + s'.balances.paidOutTotal = s.held + s.balances.paidOutTotal := by
  have hi' : s'.HeldInv := heldInv_step hi h
  have e1 : s.held + s.balances.paidOutTotal = s.balances.total := by
    rw [hi.2, Balances.total_eq_channelTotal_add_paidOutTotal]
  have e2 : s'.held + s'.balances.paidOutTotal = s'.balances.total := by
    rw [hi'.2, Balances.total_eq_channelTotal_add_paidOutTotal]
  have ht := total_step_no_deposit hi.1 hop h
  rw [e2, ht, e1]

theorem held_paidOut_reachable {apps : Apps E} {s : Adjudicator E} (hr : Reachable apps s) :
    s.held + s.balances.paidOutTotal = s.balances.total := by
  rw [(heldInv_reachable hr).2, Balances.total_eq_channelTotal_add_paidOutTotal]

/-! ### One state ahead of another under transfers

Nitro:775-777: "if you can find one strategy to move a certain amount into an
address, then no-one else can prevent this from occurring". `Ahead sp sg`
says that `sg` is where `sp` goes after more transfers (`Ahead.transfer_right`),
and the same transfer in both states keeps the order (`Ahead.transfer`). An
external balance is never lower in `sg` (`Ahead.get_external_le`). -/

/-- What the stored outcome of channel `c` still owes `d` (zero when `c` is
    not finalized). -/
def owedBy (s : Adjudicator E) (c : FixedPart) (d : Address E) : Coins :=
  match s.finalOutcome c.address with
  | some (.allocation o) => o.owed d
  | none => 0

/-- What the stored outcome at address `d` still owes all its destinations,
    one entry per destination (zero when `d` is not a finalized channel). -/
def dueTotal (s : Adjudicator E) (d : Address E) : Coins :=
  match s.finalOutcome d with
  | some (.allocation o) => o.dedup.total
  | none => 0

theorem owedBy_of {s : Adjudicator E} {c : FixedPart} {o : Allocation E}
    (h : s.finalOutcome c.address = some (.allocation o)) (d : Address E) :
    s.owedBy c d = o.owed d := by
  simp only [owedBy, h]

theorem dueTotal_of {s : Adjudicator E} {d : Address E} {o : Allocation E}
    (h : s.finalOutcome d = some (.allocation o)) : s.dueTotal d = o.dedup.total := by
  simp only [dueTotal, h]

/-- The exact effect of a successful transfer, read through `finalOutcome`,
    `balances.get`, `dueTotal` and `owedBy`: `x` coins leave `a` for `b`
    (Nitro:765-772). -/
theorem transfer_effect {s s' : Adjudicator E} {a : FixedPart} {b : Address E}
    (h : s.transfer a b = some s') :
    ∃ o amt x, s.finalOutcome a.address = some (.allocation o) ∧
      o.find b = some ⟨b, .alloc amt⟩ ∧ a.kind = .ledger ∧ b.fundable = true ∧
      x = o.paidTo (s.balances.get a.address) b ∧
      (∀ c : FixedPart, s'.finalOutcome c.address =
        if c = a then some (.allocation (o.reduceOwed b x)) else s.finalOutcome c.address) ∧
      (∀ d, s'.balances.get d + (if d = a.address then x else 0) =
        s.balances.get d + (if d = b then x else 0)) ∧
      (∀ d, s'.dueTotal d + (if d = a.address then x else 0) = s.dueTotal d) ∧
      (∀ d (L : List FixedPart), L.Nodup → (L.map (s'.owedBy · d)).sum +
        (if a ∈ L then (if d = b then x else 0) else 0) = (L.map (s.owedBy · d)).sum) := by
  obtain ⟨o, amt, x, hf, hfind, hx, hbal, -, hst, hnow, hk, hb⟩ := transfer_some h
  have hxh : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
  have hxo : x ≤ o.owed b := hx ▸ Allocation.paidTo_le_owed _ _ _
  have hfo : ∀ c : FixedPart, s'.finalOutcome c.address =
      if c = a then some (.allocation (o.reduceOwed b x)) else s.finalOutcome c.address := by
    intro c
    simp only [FixedPart.address_eq, finalOutcome_channel, statusOf_of_status hst, hnow,
      statusOf_setStatus]
    split_ifs with hc
    · simp
    · rfl
  refine ⟨o, amt, x, hf, hfind, hk, hb, hx, hfo, fun d => ?_, fun d => ?_, fun d L hL => ?_⟩
  · rw [hbal, Balances.get_sub, Balances.get_add, Balances.get_add]
    split_ifs <;> simp_all
  · cases d with
    | external e => simp [dueTotal]
    | channel c =>
      have hc := hfo c
      simp only [FixedPart.address_eq] at hc hf
      by_cases hca : c = a
      · subst hca
        have h1 := Allocation.dedup_total_reduceOwed o b hxo
        simp only [dueTotal, hc, hf, FixedPart.address_eq, if_true]
        unfold Coins at *
        omega
      · simp [dueTotal, hc, hca]
  · refine sum_map_update hL (fun c hca => ?_) ?_
    · simp only [owedBy, hfo c, if_neg hca]
    · rw [owedBy_of (by rw [hfo a, if_pos rfl]), owedBy_of hf, Allocation.owed_reduceOwed]
      split_ifs with hd
      · subst hd
        unfold Coins at *
        omega
      · rfl

/-- `sg` is ahead of `sp`. `chan`: each channel is finalized in both states
    or in neither, and `sg`'s stored allocation is ahead of `sp`'s
    (`Allocation.AheadOf`). `flow`: for each address `d` and each list `L` of
    channels, what `d` received in `sg` beyond `sp` (its balance plus what it
    paid out) is at least what the channels in `L` paid `d` in `sg` beyond
    `sp`. -/
structure Ahead (sp sg : Adjudicator E) : Prop where
  chan : ∀ c : FixedPart, Option.Rel (fun op og : Outcome E =>
    og.entries.AheadOf op.entries (sg.balances.get c.address))
    (sp.finalOutcome c.address) (sg.finalOutcome c.address)
  flow : ∀ (d : Address E) (L : List FixedPart), L.Nodup →
    sp.balances.get d + sg.dueTotal d + (L.map (sp.owedBy · d)).sum ≤
      sg.balances.get d + sp.dueTotal d + (L.map (sg.owedBy · d)).sum

theorem Ahead.refl (s : Adjudicator E) : s.Ahead s where
  chan c := by
    generalize s.finalOutcome c.address = o
    cases o with
    | none => exact .none
    | some o => exact .some (Allocation.AheadOf.refl _ _)
  flow _ _ _ := le_rfl

theorem Ahead.get_external_le {sp sg : Adjudicator E} (h : sp.Ahead sg) (d : E) :
    sp.balances.get (.external d) ≤ sg.balances.get (.external d) := by
  simpa [dueTotal] using h.flow (.external d) [] List.nodup_nil

/-- A held amount that does not fall keeps a channel ahead. -/
theorem Ahead.chan_mono {sp sg sg' : Adjudicator E} {c : FixedPart}
    (h : Option.Rel (fun op og : Outcome E => og.entries.AheadOf op.entries
      (sg.balances.get c.address)) (sp.finalOutcome c.address) (sg.finalOutcome c.address))
    (hle : sg.balances.get c.address ≤ sg'.balances.get c.address) :
    Option.Rel (fun op og : Outcome E => og.entries.AheadOf op.entries
      (sg'.balances.get c.address)) (sp.finalOutcome c.address) (sg.finalOutcome c.address) := by
  generalize sp.finalOutcome c.address = op at h ⊢
  generalize sg.finalOutcome c.address = og at h ⊢
  cases h with
  | none => exact .none
  | some hrel => exact .some (hrel.mono hle)

/-- One transfer by the adversary alone keeps `sg` ahead of `sp`. -/
theorem Ahead.transfer_right {sp sg sg' : Adjudicator E} {a : FixedPart} {b : Address E}
    (h : sp.Ahead sg) (ht : sg.transfer a b = some sg') : sp.Ahead sg' := by
  obtain ⟨og, amt, x, hf, hfind, -, -, hx, hfo, hget, hdt, hsum⟩ := transfer_effect ht
  refine ⟨fun c => ?_, fun d L hL => ?_⟩
  · have hgc := hget c.address
    rw [hfo c]
    split_ifs with hca
    · subst hca
      have hc := h.chan c
      rw [hf] at hc
      generalize sp.finalOutcome c.address = op at hc ⊢
      cases hc with
      | some hrel =>
        refine .some ((hx ▸ hrel.pay_left hfind).mono ?_)
        simp only [if_true] at hgc
        split_ifs at hgc <;> unfold Coins at * <;> omega
    · refine Ahead.chan_mono (h.chan c) ?_
      have : (c.address : Address E) ≠ a.address := by simpa using hca
      rw [if_neg this] at hgc
      split_ifs at hgc <;> unfold Coins at * <;> omega
  · have h0 := h.flow d L hL
    have h1 := hget d
    have h2 := hdt d
    have h3 := hsum d L hL
    split_ifs at h1 h2 h3 <;> unfold Coins at * <;> omega

/-- A transfer reverts in `sp` exactly when it reverts in a state ahead of
    `sp`: the two states finalized the same channels, and the first entry for
    `b` has the same kind in both (`Allocation.AheadOf.kind`). -/
theorem Ahead.transfer_eq_none_iff {sp sg : Adjudicator E} (h : sp.Ahead sg) (a : FixedPart)
    (b : Address E) : sp.transfer a b = none ↔ sg.transfer a b = none := by
  have hc := h.chan a
  constructor
  · intro hp
    by_contra hg
    obtain ⟨sg', hsg'⟩ := Option.ne_none_iff_exists'.1 hg
    obtain ⟨og, amt, -, hf, hfind, hk, hb, -⟩ := transfer_effect hsg'
    rw [hf] at hc
    generalize hop : sp.finalOutcome a.address = op at hc
    cases hc with
    | some hrel =>
      obtain ⟨amt', hfind'⟩ := Allocation.find_alloc_of_map_kind hrel.kind hfind
      exact transfer_ne_none hk hb hop hfind' hp
  · intro hg
    by_contra hp
    obtain ⟨sp', hsp'⟩ := Option.ne_none_iff_exists'.1 hp
    obtain ⟨op, amt, -, hf, hfind, hk, hb, -⟩ := transfer_effect hsp'
    rw [hf] at hc
    generalize hog : sg.finalOutcome a.address = og at hc
    cases hc with
    | some hrel =>
      obtain ⟨amt', hfind'⟩ := Allocation.find_alloc_of_map_kind hrel.kind.symm hfind
      exact transfer_ne_none hk hb hog hfind' hg

/-- The same transfer in both states keeps `sg` ahead of `sp`. At the paying
    channel `a`, `Allocation.AheadOf.pay_both`. At the payee `b`, `sg` may pay
    less than `sp` only by what `a` paid `b` in `sg` beyond `sp` before, which
    `flow` at the list `a :: L` already counts. -/
theorem Ahead.transfer_both {sp sg sp' sg' : Adjudicator E} {a : FixedPart} {b : Address E}
    (h : sp.Ahead sg) (hp : sp.transfer a b = some sp') (hg : sg.transfer a b = some sg') :
    sp'.Ahead sg' := by
  obtain ⟨op, ap, xp, hfp, hfindp, -, -, hxp, hfop, hgetp, hdtp, hsump⟩ := transfer_effect hp
  obtain ⟨og, ag, xg, hfg, hfindg, -, -, hxg, hfog, hgetg, hdtg, hsumg⟩ := transfer_effect hg
  have hC : sp.balances.get a.address + og.dedup.total ≤
      sg.balances.get a.address + op.dedup.total := by
    have := h.flow a.address [] List.nodup_nil
    rw [dueTotal_of hfp, dueTotal_of hfg] at this
    simpa using this
  have hrel : og.AheadOf op (sg.balances.get a.address) := by
    have hc := h.chan a
    rw [hfp, hfg] at hc
    cases hc with
    | some hrel => exact hrel
  have hxpo : xp ≤ op.owed b := hxp ▸ Allocation.paidTo_le_owed _ _ _
  have hxgo : xg ≤ og.owed b := hxg ▸ Allocation.paidTo_le_owed _ _ _
  have hdom : og.owed b - xg ≤ op.owed b - xp := hxp ▸ hxg ▸ hrel.owed_pay_le hC b
  refine ⟨fun c => ?_, fun d L hL => ?_⟩
  · have hgc := hgetg c.address
    rw [hfop c, hfog c]
    split_ifs with hca
    · subst hca
      refine .some ((hxp ▸ hxg ▸ hrel.pay_both hfindg hfindp hC).mono ?_)
      simp only [if_true] at hgc
      split_ifs at hgc <;> unfold Coins at * <;> omega
    · refine Ahead.chan_mono (h.chan c) ?_
      have : (c.address : Address E) ≠ a.address := by simpa using hca
      rw [if_neg this] at hgc
      split_ifs at hgc <;> unfold Coins at * <;> omega
  · have h1 := hgetp d
    have h2 := hgetg d
    have h3 := hdtp d
    have h4 := hdtg d
    have h5 := hsump d L hL
    have h6 := hsumg d L hL
    by_cases hdb : d = b
    · subst hdb
      rw [if_pos rfl] at h1 h2
      by_cases haL : a ∈ L
      · have h0 := h.flow d L hL
        rw [if_pos haL, if_pos rfl] at h5 h6
        split_ifs at h1 h2 h3 h4 <;> unfold Coins at * <;> omega
      · have h0 := h.flow d (a :: L) (List.nodup_cons.2 ⟨haL, hL⟩)
        rw [if_neg haL] at h5 h6
        simp only [List.map_cons, List.sum_cons, owedBy_of hfp, owedBy_of hfg] at h0
        split_ifs at h1 h2 h3 h4 <;> unfold Coins at * <;> omega
    · have h0 := h.flow d L hL
      rw [if_neg hdb] at h1 h2
      simp only [if_neg hdb, ite_self] at h5 h6
      split_ifs at h1 h2 h3 h4 <;> unfold Coins at * <;> omega

/-- One transfer, applied to both states, keeps `sg` ahead of `sp`. A
    transfer that reverts reverts in both (`Ahead.transfer_eq_none_iff`). -/
theorem Ahead.transfer {sp sg : Adjudicator E} (h : sp.Ahead sg) (a : FixedPart) (b : Address E) :
    ((sp.transfer a b).getD sp).Ahead ((sg.transfer a b).getD sg) := by
  cases hp : sp.transfer a b with
  | none => rw [(h.transfer_eq_none_iff a b).1 hp]; exact h
  | some sp' =>
    cases hg : sg.transfer a b with
    | none => exact absurd ((h.transfer_eq_none_iff a b).2 hg) (by simp [hp])
    | some sg' => exact h.transfer_both hp hg

end Adjudicator

end ArmadaLean.Nitro
