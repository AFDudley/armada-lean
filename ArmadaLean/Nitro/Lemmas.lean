/-
  Nitro protocol specification: the `@[simp]` reading lemmas of the
  definitions and the proof helpers that `Safety.lean` uses. Each section
  follows one definition file, in dependency order: `Address.lean`,
  `Outcome.lean`, `Channel.lean`, `Adjudicator.lean`. Rules:
  `armada-laconic/docs/lean/writing-lean.md` (rules 3, 5, 6, 9).
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import ArmadaLean.Nitro.Adjudicator

namespace ArmadaLean.Nitro

/-! ## Addresses (`Address.lean`) -/

@[simp] theorem FixedPart.address_eq (c : FixedPart) : c.address = .channel c := rfl

@[simp] theorem Address.isParticipant_participant (p : Participant) :
    (Address.participant p).isParticipant = true := rfl

@[simp] theorem Address.isParticipant_channel (c : FixedPart) :
    (Address.channel c).isParticipant = false := rfl

namespace Balances

@[simp] theorem get_nil (a : Address) : Balances.get [] a = 0 := rfl

theorem get_cons (k a : Address) (w : Coins) (t : Balances) :
    Balances.get ((k, w) :: t) a = if a = k then w else t.get a := by
  unfold Balances.get
  by_cases h : a = k
  · subst h; simp
  · simp [List.lookup_cons, beq_false_of_ne h, h]

/-- Dropping the entries of another address does not change a reading.
    Stated in `simp` normal form (`decide (x ≠ a)` becomes `!decide (x = a)`). -/
theorem get_filter_ne (b : Balances) {a a' : Address} (h : a' ≠ a) :
    Balances.get (b.filter (fun e => !decide (e.1 = a))) a' = b.get a' := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    by_cases hk : k = a
    · subst hk; simp [get_cons, h, ih]
    · simp [hk, get_cons, ih]

@[simp] theorem get_set (b : Balances) (a a' : Address) (v : Coins) :
    (b.set a v).get a' = if a' = a then v else b.get a' := by
  by_cases h : a' = a
  · subst h; simp [Balances.set, get_cons]
  · simp [Balances.set, get_cons, h, get_filter_ne b h]

@[simp] theorem get_add (b : Balances) (a a' : Address) (x : Coins) :
    (b.add a x).get a' = if a' = a then b.get a + x else b.get a' := by
  simp [Balances.add]

@[simp] theorem get_sub (b : Balances) (a a' : Address) (x : Coins) :
    (b.sub a x).get a' = if a' = a then b.get a - x else b.get a' := by
  simp [Balances.sub]

/-- The sum of the entries whose address satisfies `q`. `total`,
    `channelTotal` and `paidOutTotal` are instances. -/
def sumIf (q : Address → Bool) (b : Balances) : Coins :=
  ((b.filter (fun e => q e.1)).map (·.2)).sum

@[simp] theorem sumIf_nil (q : Address → Bool) : sumIf q [] = 0 := rfl

theorem sumIf_cons (q : Address → Bool) (k : Address) (w : Coins) (t : Balances) :
    sumIf q ((k, w) :: t) = (if q k then w else 0) + sumIf q t := by
  by_cases h : q k <;> simp [sumIf, h]

theorem total_eq_sumIf (b : Balances) : b.total = sumIf (fun _ => true) b := by
  simp [Balances.total, sumIf]

theorem channelTotal_eq_sumIf (b : Balances) :
    b.channelTotal = sumIf (fun a => decide (a.isParticipant = false)) b := rfl

theorem paidOutTotal_eq_sumIf (b : Balances) :
    b.paidOutTotal = sumIf (fun a => decide (a.isParticipant = true)) b := rfl

/-- The first entry of an address is one of the summed entries. -/
theorem get_le_sumIf (q : Address → Bool) (b : Balances) {a : Address} (hq : q a = true) :
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
def KeysNodup (b : Balances) : Prop := (b.map Prod.fst).Nodup

@[simp] theorem keysNodup_nil : KeysNodup [] := List.nodup_nil

theorem KeysNodup.filter {b : Balances} (hb : b.KeysNodup) (p : Address × Coins → Bool) :
    KeysNodup (b.filter p) :=
  List.Nodup.sublist ((List.filter_sublist).map _) hb

theorem KeysNodup.set {b : Balances} (hb : b.KeysNodup) (a : Address) (v : Coins) :
    KeysNodup (b.set a v) := by
  refine List.nodup_cons.2 ⟨?_, hb.filter _⟩
  simp

theorem KeysNodup.add {b : Balances} (hb : b.KeysNodup) (a : Address) (x : Coins) :
    KeysNodup (b.add a x) := hb.set _ _

theorem KeysNodup.sub {b : Balances} (hb : b.KeysNodup) (a : Address) (x : Coins) :
    KeysNodup (b.sub a x) := hb.set _ _

/-- With one entry per address, dropping `a` removes exactly `b.get a`. -/
theorem sumIf_filter_ne (q : Address → Bool) {b : Balances} (hb : b.KeysNodup) (a : Address) :
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

theorem sumIf_set (q : Address → Bool) {b : Balances} (hb : b.KeysNodup) (a : Address) (v : Coins) :
    sumIf q (b.set a v) + (if q a then b.get a else 0) = sumIf q b + (if q a then v else 0) := by
  have := sumIf_filter_ne q hb a
  simp only [Balances.set, sumIf_cons]
  grind

/-- With one entry per address, the sum for one address is its reading. -/
theorem sumIf_eq_get {b : Balances} (hb : b.KeysNodup) (d : Address) :
    sumIf (fun a => decide (a = d)) b = b.get d := by
  have h := sumIf_filter_ne (fun a => decide (a = d)) hb d
  have h0 : sumIf (fun a => decide (a = d)) (b.filter (fun e => decide (e.1 ≠ d))) = 0 := by
    simp only [sumIf, List.filter_filter]
    rw [List.filter_eq_nil_iff.2 (by intro e _; simp)]
    rfl
  simp only [decide_true, if_true] at h
  grind

/-- A reading at a list position, when each address has one entry. -/
theorem get_of_getElem? {b : Balances} (hb : b.KeysNodup) {j : Nat} {d : Address} {x : Coins}
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
theorem get_of_forall_ne {b : Balances} {a : Address} (h : ∀ e ∈ b, e.1 ≠ a) : b.get a = 0 := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    rw [get_cons, if_neg (Ne.symm (h _ (List.mem_cons_self ..)))]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- The balance effect of a transfer (`add b x`, then `sub a x`) on every
    sum, when `a` holds at least `x`. -/
theorem sumIf_add_sub (q : Address → Bool) {b : Balances} (hb : b.KeysNodup) (a d : Address)
    {x : Coins} (hx : x ≤ b.get a) :
    sumIf q ((b.add d x).sub a x) + (if q a then x else 0) = sumIf q b + (if q d then x else 0) := by
  have h1 := sumIf_set q hb d (b.get d + x)
  have h2 := sumIf_set q (hb.add d x) a ((b.add d x).get a - x)
  have hge : x ≤ (b.add d x).get a := by
    rw [get_add]; split <;> grind
  simp only [Balances.sub, Balances.add] at h1 h2 hge ⊢
  split <;> split <;> grind

end Balances

/-! ## Outcomes (`Outcome.lean`) -/

@[simp] theorem Item.amount_alloc (a : Coins) : (Item.alloc a).amount = a := rfl

@[simp] theorem Item.amount_guarantee (x : Coins) (ps : List Address) :
    (Item.guarantee x ps).amount = x := rfl

@[simp] theorem Entry.amount_mk (d : Address) (i : Item) : Entry.amount ⟨d, i⟩ = i.amount := rfl

namespace Allocation

@[simp] theorem total_nil : Allocation.total [] = 0 := rfl

@[simp] theorem total_cons (e : Entry) (o : Allocation) :
    Allocation.total (e :: o) = e.amount + Allocation.total o := by
  simp [Allocation.total]

theorem total_append (o o' : Allocation) :
    Allocation.total (o ++ o') = Allocation.total o + Allocation.total o' := by
  simp [Allocation.total]

theorem total_take_succ {o : Allocation} {k : Nat} {e : Entry} (h : o[k]? = some e) :
    Allocation.total (o.take (k + 1)) = Allocation.total (o.take k) + e.amount := by
  rw [List.take_add_one, total_append, h]
  simp

theorem total_take_mono (o : Allocation) {i j : Nat} (h : i ≤ j) :
    Allocation.total (o.take i) ≤ Allocation.total (o.take j) := by
  have : o.take i = (o.take j).take i := by rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact List.Sublist.sum_le_sum (M := ℕ) ((List.take_sublist _ _).map _) (fun _ _ => Nat.zero_le _)

theorem total_take_le (o : Allocation) (k : Nat) :
    Allocation.total (o.take k) ≤ o.total :=
  List.Sublist.sum_le_sum (M := ℕ) ((List.take_sublist _ _).map _) (fun _ _ => Nat.zero_le _)

theorem total_le_of_sublist {o o' : Allocation} (h : o.Sublist o') : o.total ≤ o'.total :=
  List.Sublist.sum_le_sum (M := ℕ) (h.map _) (fun _ _ => Nat.zero_le _)

/-! ### `find` and `owed` -/

@[simp] theorem find_nil (d : Address) : Allocation.find [] d = none := rfl

theorem find_cons (e : Entry) (o : Allocation) (d : Address) :
    Allocation.find (e :: o) d = if e.dest = d then some e else o.find d := by
  by_cases h : e.dest = d <;> simp [Allocation.find, h]

theorem find_dest {o : Allocation} {d : Address} {e : Entry} (h : o.find d = some e) :
    e.dest = d := by
  simpa using List.find?_some h

theorem find_eq_none {o : Allocation} {d : Address} :
    o.find d = none ↔ d ∉ o.map Entry.dest := by
  simp [Allocation.find, List.find?_eq_none]

theorem owed_cons (e : Entry) (o : Allocation) (d : Address) :
    Allocation.owed (e :: o) d = if e.dest = d then e.amount else o.owed d := by
  by_cases h : e.dest = d <;> simp [Allocation.owed, find_cons, h]

/-- With distinct destinations, the entry at a position is the first entry
    for its destination. -/
theorem find_of_getElem? {o : Allocation} (hnd : (o.map Entry.dest).Nodup) {j : Nat} {f : Entry}
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

@[simp] theorem dedupFrom_nil (seen : List Address) : Allocation.dedupFrom seen [] = [] := rfl

theorem dedupFrom_cons (seen : List Address) (e : Entry) (o : Allocation) :
    Allocation.dedupFrom seen (e :: o) =
      if e.dest ∈ seen then Allocation.dedupFrom seen o
      else e :: Allocation.dedupFrom (e.dest :: seen) o := rfl

theorem dedupFrom_sublist (seen : List Address) (o : Allocation) :
    (Allocation.dedupFrom seen o).Sublist o := by
  induction o generalizing seen with
  | nil => simp
  | cons e t ih =>
    rw [dedupFrom_cons]
    split
    · exact (ih seen).cons e
    · exact (ih _).cons_cons e

theorem dest_not_mem_of_mem_dedupFrom {seen : List Address} {o : Allocation} {e : Entry}
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

theorem dedupFrom_nodup (seen : List Address) (o : Allocation) :
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

theorem dedup_nodup (o : Allocation) : (o.dedup.map Entry.dest).Nodup := dedupFrom_nodup [] o

theorem dedup_sublist (o : Allocation) : o.dedup.Sublist o := dedupFrom_sublist [] o

theorem find_dedupFrom (seen : List Address) (o : Allocation) (d : Address) :
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

@[simp] theorem find_dedup (o : Allocation) (d : Address) : o.dedup.find d = o.find d := by
  simp [Allocation.dedup, find_dedupFrom]

@[simp] theorem owed_dedup (o : Allocation) (d : Address) : o.dedup.owed d = o.owed d := by
  simp [Allocation.owed]

/-! ### `payout` and `paidTo` -/

@[simp] theorem payout_nil (held : Coins) : Allocation.payout held [] = [] := rfl

@[simp] theorem payout_cons (held : Coins) (e : Entry) (o : Allocation) :
    Allocation.payout held (e :: o) =
      (e.dest, min e.amount held) :: Allocation.payout (held - min e.amount held) o := rfl

theorem payout_map_fst (held : Coins) (o : Allocation) :
    (o.payout held).map Prod.fst = o.map Entry.dest := by
  induction o generalizing held with
  | nil => rfl
  | cons e t ih => simp [ih]

/-- ForceMove:1837-1853: entry `k` is paid `min(amount, held − total before k)`. -/
theorem payout_getElem? {held : Coins} {o : Allocation} {k : Nat} {e : Entry}
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

theorem payout_sum_le (held : Coins) (o : Allocation) : ((o.payout held).map (·.2)).sum ≤ held := by
  induction o generalizing held with
  | nil => simp
  | cons e t ih =>
    have := ih (held - min e.amount held)
    simp only [payout_cons, List.map_cons, List.sum_cons]
    grind

theorem payout_keysNodup {held : Coins} {o : Allocation} (h : (o.map Entry.dest).Nodup) :
    Balances.KeysNodup (o.payout held) := by
  unfold Balances.KeysNodup; rwa [payout_map_fst]

/-- `paidTo` reads the payout of the deduplicated allocation. -/
theorem paidTo_eq_get (held : Coins) (o : Allocation) (d : Address) :
    o.paidTo held d = Balances.get (o.dedup.payout held) d :=
  Balances.sumIf_eq_get (payout_keysNodup (dedup_nodup o)) d

/-- A payout reading is at most the first entry's amount. -/
theorem payout_get_le_owed (held : Coins) (o : Allocation) (d : Address) :
    Balances.get (o.payout held) d ≤ o.owed d := by
  induction o generalizing held with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons]
    by_cases h : e.dest = d
    · simp [h]
    · simp only [Ne.symm h, if_false, h]; exact ih _

/-- When the coins held cover the total, each first entry is paid in full. -/
theorem owed_le_payout_get {held : Coins} {o : Allocation} (h : o.total ≤ held) (d : Address) :
    o.owed d ≤ Balances.get (o.payout held) d := by
  induction o generalizing held with
  | nil => simp [Allocation.owed]
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons]
    rw [total_cons] at h
    by_cases hd : e.dest = d
    · simp only [hd, if_true]; grind
    · simp only [Ne.symm hd, if_false, hd]; exact ih (by grind)

theorem paidTo_le_held (held : Coins) (o : Allocation) (d : Address) : o.paidTo held d ≤ held := by
  rw [paidTo_eq_get]
  refine le_trans (Balances.get_le_sumIf (fun _ => true) _ rfl) ?_
  rw [← Balances.total_eq_sumIf]
  exact payout_sum_le held _

/-- With distinct destinations, `paidTo` at the destination of entry `j` is
    the priority formula. -/
theorem paidTo_of_getElem? {held : Coins} {o : Allocation} (hd : o.dedup = o) {j : Nat} {f : Entry}
    (h : o[j]? = some f) :
    o.paidTo held f.dest = min f.amount (held - Allocation.total (o.take j)) := by
  have hnd : (o.map Entry.dest).Nodup := hd ▸ dedup_nodup o
  rw [paidTo_eq_get, hd]
  exact Balances.get_of_getElem? (payout_keysNodup hnd) (payout_getElem? h)

/-! ### `reduceOwed` -/

@[simp] theorem reduceOwed_nil (d : Address) (x : Coins) : Allocation.reduceOwed [] d x = [] := rfl

theorem reduceOwed_cons (e : Entry) (o : Allocation) (d : Address) (x : Coins) :
    Allocation.reduceOwed (e :: o) d x =
      if e.dest = d then { e with item := .alloc (e.amount - x) } :: o
      else e :: Allocation.reduceOwed o d x := rfl

theorem owed_reduceOwed (o : Allocation) (d d' : Address) (x : Coins) :
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

/-! ### `addTo` and `remove` -/

theorem addTo_cons (e : Entry) (o : Allocation) (d : Address) (x : Coins) :
    Allocation.addTo (e :: o) d x =
      if e.dest = d then { e with item := .alloc (e.amount + x) } :: o
      else e :: Allocation.addTo o d x := rfl

theorem addTo_map_dest (o : Allocation) (d : Address) (x : Coins) :
    (o.addTo d x).map Entry.dest = o.map Entry.dest := by
  induction o with
  | nil => rfl
  | cons e t ih => rw [addTo_cons]; split <;> simp [*]

theorem find_addTo_of_ne (o : Allocation) {d d' : Address} (x : Coins) (h : d' ≠ d) :
    (o.addTo d x).find d' = o.find d' := by
  induction o with
  | nil => rfl
  | cons e t ih =>
    rw [addTo_cons]
    split
    · rename_i he; subst he; simp [find_cons, Ne.symm h]
    · rw [find_cons, find_cons, ih]

theorem owed_addTo_self {o : Allocation} {d : Address} (x : Coins) (h : o.find d ≠ none) :
    (o.addTo d x).owed d = o.owed d + x := by
  induction o with
  | nil => simp at h
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · subst he; simp [owed_cons, Entry.amount]
    · rw [find_cons, if_neg he] at h
      rw [if_neg he, owed_cons, owed_cons, if_neg he, if_neg he, ih h]

theorem owed_addTo_of_ne (o : Allocation) {d d' : Address} (x : Coins) (h : d' ≠ d) :
    (o.addTo d x).owed d' = o.owed d' := by
  simp [Allocation.owed, find_addTo_of_ne o x h]

theorem total_addTo {o : Allocation} {d : Address} (x : Coins) (h : o.find d ≠ none) :
    (o.addTo d x).total = o.total + x := by
  induction o with
  | nil => simp at h
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · simp only [he, if_true, total_cons, Entry.amount]; simp only [Item.amount_alloc]; grind
    · rw [find_cons, if_neg he] at h
      rw [if_neg he, total_cons, total_cons, ih h]; grind

theorem find_remove (o : Allocation) (d d' : Address) :
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

theorem owed_remove_of_ne (o : Allocation) {d d' : Address} (h : d' ≠ d) :
    (o.remove d).owed d' = o.owed d' := by
  simp [Allocation.owed, find_remove, h]

/-- With distinct destinations, removing `d` lowers the total by its amount. -/
theorem total_remove {o : Allocation} (hnd : (o.map Entry.dest).Nodup) (d : Address) :
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

end Allocation

/-! ## Channels (`Channel.lean`) -/

namespace ChannelStatus

@[simp] theorem mode_open (t : Nat) (now : Time) : (ChannelStatus.open t).mode now = .open := rfl

@[simp] theorem mode_challenged (t : Nat) (ch : Challenge) (now : Time) :
    (ChannelStatus.challenged t ch).mode now = if ch.deadline ≤ now then .finalized else .challenge :=
  rfl

@[simp] theorem mode_finalized (t : Nat) (o : Outcome) (now : Time) :
    (ChannelStatus.finalized t o).mode now = .finalized := rfl

@[simp] theorem finalOutcome_open (t : Nat) (now : Time) :
    (ChannelStatus.open t).finalOutcome now = none := rfl

@[simp] theorem finalOutcome_challenged (t : Nat) (ch : Challenge) (now : Time) :
    (ChannelStatus.challenged t ch).finalOutcome now =
      if ch.deadline ≤ now then some ch.state.outcome else none := rfl

@[simp] theorem finalOutcome_finalized (t : Nat) (o : Outcome) (now : Time) :
    (ChannelStatus.finalized t o).finalOutcome now = some o := rfl

@[simp] theorem turnNumRecord_open (t : Nat) : (ChannelStatus.open t).turnNumRecord = t := rfl

@[simp] theorem turnNumRecord_challenged (t : Nat) (ch : Challenge) :
    (ChannelStatus.challenged t ch).turnNumRecord = t := rfl

@[simp] theorem turnNumRecord_finalized (t : Nat) (o : Outcome) :
    (ChannelStatus.finalized t o).turnNumRecord = t := rfl

@[simp] theorem withOutcome_eq (st : ChannelStatus) (o : Outcome) :
    st.withOutcome o = .finalized st.turnNumRecord o := rfl

theorem isOpen_iff_ne (st : ChannelStatus) (now : Time) :
    st.IsOpen now ↔ st.mode now ≠ .finalized := Iff.rfl

/-- The mode is finalized exactly when a final outcome exists. -/
theorem mode_eq_finalized_iff (st : ChannelStatus) (now : Time) :
    st.mode now = .finalized ↔ (st.finalOutcome now).isSome := by
  cases st <;> simp

theorem finalOutcome_mono {st : ChannelStatus} {now now' : Time} {o : Outcome}
    (h : st.finalOutcome now = some o) (hle : now ≤ now') : st.finalOutcome now' = some o := by
  cases st <;> simp at h ⊢
  · exact ⟨by grind, h.2⟩
  · exact h

theorem mode_finalized_mono {st : ChannelStatus} {now now' : Time}
    (h : st.mode now = .finalized) (hle : now ≤ now') : st.mode now' = .finalized := by
  rw [mode_eq_finalized_iff] at h ⊢
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
  rw [finalOutcome_mono ho hle]; rfl

end ChannelStatus

theorem SignedState.byMover_iff (ss : SignedState) : ss.byMover = true ↔ ss.ByMover := by
  unfold SignedState.byMover SignedState.ByMover
  split <;> simp_all

/-- Every consecutive pair of a valid run is a valid move. -/
theorem validRun_getElem? {vt : State → State → Bool} {l : SupportProof} (h : validRun vt l = true)
    {i : Nat} {m1 m2 : SignedState} (h1 : l[i]? = some m1) (h2 : l[i + 1]? = some m2) :
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

/-! ## The adjudicator (`Adjudicator.lean`) -/

namespace Adjudicator

/-- A status list without the entries of `c` reads the same at `c' ≠ c`. -/
theorem lookup_filter_ne (l : List (FixedPart × ChannelStatus)) {c c' : FixedPart} (h : c' ≠ c) :
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

@[simp] theorem statusOf_setStatus (s : Adjudicator) (c : FixedPart) (st : ChannelStatus)
    (c' : FixedPart) : (s.setStatus c st).statusOf c' = if c' = c then st else s.statusOf c' := by
  unfold statusOf setStatus
  by_cases h : c' = c
  · subst h; simp
  · simp [List.lookup_cons, beq_false_of_ne h, h, lookup_filter_ne _ h]

@[simp] theorem setStatus_balances (s : Adjudicator) (c : FixedPart) (st : ChannelStatus) :
    (s.setStatus c st).balances = s.balances := rfl

@[simp] theorem setStatus_held (s : Adjudicator) (c : FixedPart) (st : ChannelStatus) :
    (s.setStatus c st).held = s.held := rfl

@[simp] theorem setStatus_now (s : Adjudicator) (c : FixedPart) (st : ChannelStatus) :
    (s.setStatus c st).now = s.now := rfl

theorem statusOf_of_status {s t : Adjudicator} (h : s.status = t.status) (c : FixedPart) :
    s.statusOf c = t.statusOf c := by
  unfold statusOf; rw [h]

@[simp] theorem finalOutcome_channel (s : Adjudicator) (c : FixedPart) :
    s.finalOutcome (.channel c) = (s.statusOf c).finalOutcome s.now := rfl

@[simp] theorem finalOutcome_participant (s : Adjudicator) (p : Participant) :
    s.finalOutcome (.participant p) = none := rfl

theorem mode_eq (s : Adjudicator) (c : FixedPart) : s.mode c = (s.statusOf c).mode s.now := rfl

@[simp] theorem payTo_balances (s : Adjudicator) (b : Address) (x : Coins) :
    (s.payTo b x).balances = s.balances.add b x := by
  cases b <;> rfl

@[simp] theorem payTo_held (s : Adjudicator) (b : Address) (x : Coins) :
    (s.payTo b x).held = if b.isParticipant then s.held - x else s.held := by
  cases b <;> rfl

@[simp] theorem payTo_status (s : Adjudicator) (b : Address) (x : Coins) :
    (s.payTo b x).status = s.status := by
  cases b <;> rfl

@[simp] theorem payTo_now (s : Adjudicator) (b : Address) (x : Coins) :
    (s.payTo b x).now = s.now := by
  cases b <;> rfl

theorem deposit_some {s : Adjudicator} {a : Address} {e x : Coins} {s' : Adjudicator}
    (h : s.deposit a e x = some s') :
    (∃ c, a = .channel c) ∧ s.balances.get a = e ∧ s'.balances = s.balances.add a x ∧
      s'.held = s.held + x ∧ s'.status = s.status ∧ s'.now = s.now := by
  unfold deposit at h
  split at h
  · split at h
    · cases h; exact ⟨⟨_, rfl⟩, by assumption, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- The exact effect of a successful transfer, field by field. -/
theorem transfer_some {s : Adjudicator} {a : FixedPart} {b : Address} {s' : Adjudicator}
    (h : s.transfer a b = some s') :
    ∃ o amt x, s.finalOutcome a.address = some (.allocation o) ∧ o.find b = some ⟨b, .alloc amt⟩ ∧
      x = o.paidTo (s.balances.get a.address) b ∧
      s'.balances = (s.balances.add b x).sub a.address x ∧
      s'.held = (if b.isParticipant then s.held - x else s.held) ∧
      s'.status = (s.setStatus a ((s.statusOf a).withOutcome
        (.allocation (o.reduceOwed b x)))).status ∧
      s'.now = s.now := by
  unfold transfer at h
  split at h
  · rename_i o hf
    split at h
    · rename_i d amt hfind
      have hd : d = b := Allocation.find_dest hfind
      subst hd
      cases h
      exact ⟨o, amt, _, hf, hfind, rfl, by simp, by simp, by simp, by simp⟩
    · cases h
  · cases h

/-- The exact effect of a successful reclaim. -/
theorem reclaim_some {s : Adjudicator} {l v : FixedPart} {s' : Adjudicator}
    (h : s.reclaim l v = some s') :
    ∃ oL oV x left right, s.finalOutcome l.address = some (.allocation oL) ∧
      s.finalOutcome v.address = some (.allocation oV) ∧
      oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧
      (oL.remove v.address).find left ≠ none ∧ (oL.remove v.address).find right ≠ none ∧
      oV.amountAt 0 + oV.amountAt 1 = x ∧
      s' = s.setStatus l ((s.statusOf l).withOutcome (.allocation
        (((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address))) := by
  unfold reclaim at h
  split at h
  · rename_i oL oV hL hV
    split at h
    · rename_i d x left right hfind
      have hd : d = v.address := Allocation.find_dest hfind
      subst hd
      split at h
      · rename_i hc
        cases h
        exact ⟨oL, oV, x, left, right, hL, hV, hfind, hc.1, hc.2.1, hc.2.2, rfl⟩
      · cases h
    · cases h
  · cases h

theorem challenge_some {apps : Apps} {s : Adjudicator} {challenger : Participant} {c : FixedPart}
    {proof : SupportProof} {candidate : State} {s' : Adjudicator}
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

theorem checkpoint_some {apps : Apps} {s : Adjudicator} {c : FixedPart} {proof : SupportProof}
    {candidate : State} {s' : Adjudicator} (h : s.checkpoint apps c proof candidate = some s') :
    ((s.statusOf c).IsOpen s.now ∧
      (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
      (s.statusOf c).turnNumRecord < candidate.turnNum) ∧
    s' = s.setStatus c (.open candidate.turnNum) := by
  unfold checkpoint at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

theorem conclude_some {s : Adjudicator} {c : FixedPart} {ss : SignedState} {s' : Adjudicator}
    (h : s.conclude c ss = some s') :
    ((s.statusOf c).IsOpen s.now ∧ ConclusionProof c ss) ∧
    s' = s.setStatus c (.finalized ss.state.turnNum ss.state.outcome) := by
  unfold conclude at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

@[simp] theorem apply_deposit (apps : Apps) (caller : Participant) (s : Adjudicator) (a : Address)
    (e x : Coins) : s.apply apps caller (.deposit a e x) = s.deposit a e x := rfl

@[simp] theorem apply_transfer (apps : Apps) (caller : Participant) (s : Adjudicator) (a : FixedPart)
    (b : Address) : s.apply apps caller (.transfer a b) = s.transfer a b := rfl

@[simp] theorem apply_reclaim (apps : Apps) (caller : Participant) (s : Adjudicator)
    (l v : FixedPart) : s.apply apps caller (.reclaim l v) = s.reclaim l v := rfl

@[simp] theorem apply_challenge (apps : Apps) (caller : Participant) (s : Adjudicator)
    (c : FixedPart) (proof : SupportProof) (candidate : State) :
    s.apply apps caller (.challenge c proof candidate) = s.challenge apps caller c proof candidate :=
  rfl

@[simp] theorem apply_checkpoint (apps : Apps) (caller : Participant) (s : Adjudicator)
    (c : FixedPart) (proof : SupportProof) (candidate : State) :
    s.apply apps caller (.checkpoint c proof candidate) = s.checkpoint apps c proof candidate := rfl

@[simp] theorem apply_conclude (apps : Apps) (caller : Participant) (s : Adjudicator)
    (c : FixedPart) (ss : SignedState) : s.apply apps caller (.conclude c ss) = s.conclude c ss := rfl

@[simp] theorem apply_tick (apps : Apps) (caller : Participant) (s : Adjudicator) (dt : Time) :
    s.apply apps caller (.tick dt) = some (s.tick dt) := rfl

@[simp] theorem tick_balances (s : Adjudicator) (dt : Time) : (s.tick dt).balances = s.balances :=
  rfl

@[simp] theorem tick_held (s : Adjudicator) (dt : Time) : (s.tick dt).held = s.held := rfl

@[simp] theorem tick_status (s : Adjudicator) (dt : Time) : (s.tick dt).status = s.status := rfl

@[simp] theorem tick_now (s : Adjudicator) (dt : Time) : (s.tick dt).now = s.now + dt := rfl

@[simp] theorem tick_statusOf (s : Adjudicator) (dt : Time) (c : FixedPart) :
    (s.tick dt).statusOf c = s.statusOf c := rfl

theorem applyAll_append (apps : Apps) (l l' : List (Participant × Op)) (s : Adjudicator) :
    applyAll apps (l ++ l') s = applyAll apps l' (applyAll apps l s) := by
  induction l generalizing s with
  | nil => rfl
  | cons p t ih => obtain ⟨c, op⟩ := p; exact ih _

theorem applyAll_singleton_of_some {apps : Apps} {caller : Participant} {op : Op}
    {s s' : Adjudicator} (h : s.apply apps caller op = some s') :
    applyAll apps [(caller, op)] s = s' := by
  simp [applyAll, h]

/-- Only `tick` moves the clock, and only forward. -/
theorem apply_now_le {apps : Apps} {caller : Participant} {op : Op} {s s' : Adjudicator}
    (h : s.apply apps caller op = some s') : s.now ≤ s'.now := by
  cases op with
  | deposit a e x => simp [(deposit_some h).2.2.2.2.2]
  | transfer a b => obtain ⟨_, _, _, _, _, _, _, _, _, hn⟩ := transfer_some h; simp [hn]
  | reclaim l v => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := reclaim_some h; simp
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; simp
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; simp
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; simp
  | tick dt => simp at h; subst h; simp

/-! ### The coins-held invariant -/

/-- Nitro:230-231 with go-nitro's external payouts: each address has one
    balance entry, and the coins held equal the channel balances. -/
def HeldInv (s : Adjudicator) : Prop :=
  s.balances.KeysNodup ∧ s.held = s.balances.channelTotal

theorem heldInv_genesis : genesis.HeldInv := ⟨Balances.keysNodup_nil, rfl⟩

theorem heldInv_step {apps : Apps} {caller : Participant} {op : Op} {s s' : Adjudicator}
    (hi : s.HeldInv) (h : s.apply apps caller op = some s') : s'.HeldInv := by
  obtain ⟨hnd, hheld⟩ := hi
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c, rfl⟩, -, hb, hh, -, -⟩ := deposit_some h
    refine ⟨hb ▸ hnd.add _ _, ?_⟩
    have := Balances.sumIf_set (fun a => decide (a.isParticipant = false)) hnd (.channel c)
      (s.balances.get (.channel c) + x)
    rw [Balances.channelTotal_eq_sumIf] at hheld ⊢
    rw [hh, hb]
    simp only [Balances.add]
    simp at this
    grind
  | transfer a b =>
    obtain ⟨o, _, x, -, -, hx, hb, hh, -, -⟩ := transfer_some h
    have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
    refine ⟨hb ▸ (hnd.add _ _).sub _ _, ?_⟩
    have := Balances.sumIf_add_sub (fun a => decide (a.isParticipant = false)) hnd a.address b hxa
    have hle := Balances.get_le_sumIf (fun a => decide (a.isParticipant = false)) s.balances
      (a := a.address) (by simp)
    rw [hh, hb, Balances.channelTotal_eq_sumIf]
    rw [Balances.channelTotal_eq_sumIf] at hheld
    cases b <;> simp at this ⊢ <;> grind
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := reclaim_some h; exact ⟨hnd, hheld⟩
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; exact ⟨hnd, hheld⟩
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; exact ⟨hnd, hheld⟩
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; exact ⟨hnd, hheld⟩
  | tick dt => simp at h; subst h; exact ⟨hnd, hheld⟩

theorem heldInv_reachable {apps : Apps} {s : Adjudicator} (hr : Reachable apps s) : s.HeldInv := by
  induction hr with
  | refl => exact heldInv_genesis
  | tail _ hstep ih =>
    cases hstep with
    | mk caller op _ _ h => exact heldInv_step ih h

end Adjudicator

end ArmadaLean.Nitro
