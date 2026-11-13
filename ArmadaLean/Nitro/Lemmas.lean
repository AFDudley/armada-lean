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
import Mathlib.Tactic.Says

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
  · subst h; (simp? says simp only [List.lookup_cons_self, Option.getD_some, ↓reduceIte])
  · (simp? [List.lookup_cons, beq_false_of_ne h, h] says simp only [List.lookup_cons, beq_false_of_ne h, h, ↓reduceIte])

/-- Dropping the entries of another address does not change a reading.
    Stated in `simp` normal form (`decide (x ≠ a)` becomes `!decide (x = a)`). -/
theorem get_filter_ne (b : Balances E) {a a' : Address E} (h : a' ≠ a) :
    Balances.get (b.filter (fun e => !decide (e.1 = a))) a' = b.get a' := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    by_cases hk : k = a
    · subst hk; (simp? [get_cons, h, ih] says simp only [decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, ih, get_cons, h, ↓reduceIte])
    · (simp? [hk, get_cons, ih] says simp only [hk, decide_false, Bool.not_false, List.filter_cons_of_pos, get_cons, ih])

@[simp] theorem get_set (b : Balances E) (a a' : Address E) (v : Coins) :
    (b.set a v).get a' = if a' = a then v else b.get a' := by
  by_cases h : a' = a
  · subst h; (simp? [Balances.set, get_cons] says simp only [set, ne_eq, decide_not, get_cons, ↓reduceIte])
  · (simp? [Balances.set, get_cons, h, get_filter_ne b h] says simp only [set, ne_eq, decide_not, get_cons, h, ↓reduceIte, get_filter_ne b h])

@[simp] theorem get_add (b : Balances E) (a a' : Address E) (x : Coins) :
    (b.add a x).get a' = if a' = a then b.get a + x else b.get a' := by
  (simp? [Balances.add] says simp only [add, get_set])

@[simp] theorem get_sub (b : Balances E) (a a' : Address E) (x : Coins) :
    (b.sub a x).get a' = if a' = a then b.get a - x else b.get a' := by
  (simp? [Balances.sub] says simp only [sub, get_set])

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
  (simp? [Balances.total, sumIf] says simp only [total, sumIf, List.filter_true])

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
  | nil => (simp? says simp only [get_nil, sumIf_nil, Std.le_refl])
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    rw [get_cons, sumIf_cons]
    by_cases h : a = k
    · subst h; (simp? [hq] says simp only [↓reduceIte, hq, le_add_iff_nonneg_right, zero_le])
    · simp only [h, if_false]; (grind? says grind only)

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
  (simp? says simp only [ne_eq, decide_not, List.mem_map, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Prod.exists, exists_and_right, exists_eq_right, not_true_eq_false, and_false, not_false_eq_true])

theorem KeysNodup.add {b : Balances E} (hb : b.KeysNodup) (a : Address E) (x : Coins) :
    KeysNodup (b.add a x) := hb.set _ _

theorem KeysNodup.sub {b : Balances E} (hb : b.KeysNodup) (a : Address E) (x : Coins) :
    KeysNodup (b.sub a x) := hb.set _ _

/-- With one entry per address, dropping `a` removes exactly `b.get a`. -/
theorem sumIf_filter_ne (q : Address E → Bool) {b : Balances E} (hb : b.KeysNodup) (a : Address E) :
    sumIf q (b.filter (fun e => decide (e.1 ≠ a))) + (if q a then b.get a else 0) = sumIf q b := by
  induction b with
  | nil => (simp? says simp only [ne_eq, decide_not, List.filter_nil, sumIf_nil, get_nil, ite_self, add_zero])
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    have hk : k ∉ t.map Prod.fst := (List.nodup_cons.1 hb).1
    have ht : KeysNodup t := (List.nodup_cons.1 hb).2
    by_cases h : k = a
    · subst h
      have hself : t.filter (fun e => decide (e.1 ≠ k)) = t := by
        refine List.filter_eq_self.2 fun e he => ?_
        have : e.1 ≠ k := fun h' => hk (List.mem_map.2 ⟨e, he, h'⟩)
        (simpa? using this says simpa only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] using this)
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, hself, sumIf_cons, get_cons, if_true]
      (grind? says grind only)
    · have := ih ht
      simp only [List.filter_cons, ne_eq, h, not_false_eq_true, decide_true, if_true, sumIf_cons,
        get_cons, Ne.symm h, if_false]
      (grind? says grind only)

theorem sumIf_set (q : Address E → Bool) {b : Balances E} (hb : b.KeysNodup) (a : Address E) (v : Coins) :
    sumIf q (b.set a v) + (if q a then b.get a else 0) = sumIf q b + (if q a then v else 0) := by
  have := sumIf_filter_ne q hb a
  simp only [Balances.set, sumIf_cons]
  (grind? says grind only)

/-- With one entry per address, the sum for one address is its reading. -/
theorem sumIf_eq_get {b : Balances E} (hb : b.KeysNodup) (d : Address E) :
    sumIf (fun a => decide (a = d)) b = b.get d := by
  have h := sumIf_filter_ne (fun a => decide (a = d)) hb d
  have h0 : sumIf (fun a => decide (a = d)) (b.filter (fun e => decide (e.1 ≠ d))) = 0 := by
    simp only [sumIf, List.filter_filter]
    rw [List.filter_eq_nil_iff.2 (by intro e _; (simp? says simp only [ne_eq, decide_not, Bool.and_not_self, Bool.false_eq_true, not_false_eq_true]))]
    rfl
  simp only [decide_true, if_true] at h
  (grind? says grind only)

/-- A reading at a list position, when each address has one entry. -/
theorem get_of_getElem? {b : Balances E} (hb : b.KeysNodup) {j : Nat} {d : Address E} {x : Coins}
    (h : b[j]? = some (d, x)) : b.get d = x := by
  induction b generalizing j with
  | nil => (simp? at h says simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h)
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    have hk : k ∉ t.map Prod.fst := (List.nodup_cons.1 hb).1
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      (simp? [get_cons] says simp only [get_cons, ↓reduceIte])
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
    rw [get_add]; split <;> (grind? says grind only)
  simp only [Balances.sub, Balances.add] at h1 h2 hge ⊢
  split <;> split <;> (grind? says grind only)


omit [DecidableEq E] in
/-- Every entry is either a channel entry or an external entry: `total` is
    the sum of `channelTotal` and `paidOutTotal`. No `KeysNodup` hypothesis
    needed: the split holds entry by entry. Used by `total_step` (below,
    `namespace Adjudicator`) to connect `held` (the `Adjudicator.held`
    field) to the balances sum, for the wallet conservation theorem
    (`Reachable.lean`, D10 design decision). -/
theorem total_eq_channelTotal_add_paidOutTotal (b : Balances E) :
    Balances.total b = Balances.channelTotal b + Balances.paidOutTotal b := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    have h3 : Balances.total ((k, w) :: t) = w + Balances.total t := by
      (simp? [Balances.total] says simp only [total, List.map_cons, List.sum_cons, Nat.add_left_cancel_iff])
    rcases hk : k.isExternal with _ | _
    · have h1 : Balances.channelTotal ((k, w) :: t) = w + Balances.channelTotal t := by
        (simp? [Balances.channelTotal, hk] says simp only [channelTotal, Bool.decide_eq_false, hk, Bool.not_false, List.filter_cons_of_pos, List.map_cons, List.sum_cons, Nat.add_left_cancel_iff])
      have h2 : Balances.paidOutTotal ((k, w) :: t) = Balances.paidOutTotal t := by
        (simp? [Balances.paidOutTotal, hk] says simp only [paidOutTotal, Bool.decide_eq_true, hk, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg])
      (grind? says grind only)
    · have h1 : Balances.channelTotal ((k, w) :: t) = Balances.channelTotal t := by
        (simp? [Balances.channelTotal, hk] says simp only [channelTotal, Bool.decide_eq_false, hk, Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg])
      have h2 : Balances.paidOutTotal ((k, w) :: t) = w + Balances.paidOutTotal t := by
        (simp? [Balances.paidOutTotal, hk] says simp only [paidOutTotal, Bool.decide_eq_true, hk, List.filter_cons_of_pos, List.map_cons, List.sum_cons, Nat.add_left_cancel_iff])
      (grind? says grind only)
end Balances

/-- A sum over a duplicate-free list `L` is at most the sum over a
    duplicate-free list `M` that holds each element of `L` where `g` is not
    zero. `turbo_value_upper_bound` uses it to bound the credits of the
    channels in `Ahead.flow`'s list by the credits along the topological
    order. -/
theorem sum_le_sum_of_support_subset {α : Type} [DecidableEq α] :
    ∀ (L M : List α), L.Nodup → M.Nodup → (g : α → Nat) → (∀ a ∈ L, g a ≠ 0 → a ∈ M) →
    (L.map g).sum ≤ (M.map g).sum := by
  intro L
  induction L with
  | nil => intro M _ _ g _; (simp? says simp only [List.map_nil, List.sum_nil, zero_le])
  | cons a rest ih =>
    intro M hL hM g hsupp
    rw [List.nodup_cons] at hL
    obtain ⟨hanotin, hrest⟩ := hL
    simp only [List.map_cons, List.sum_cons]
    by_cases hga : g a = 0
    · rw [hga, zero_add]
      exact ih M hrest hM g fun b hb hgb => hsupp b (List.mem_cons_of_mem a hb) hgb
    · obtain ⟨M1, M2, rfl, -⟩ := List.eq_append_cons_of_mem (hsupp a List.mem_cons_self hga)
      rw [List.nodup_append, List.nodup_cons] at hM
      obtain ⟨h1, ⟨-, h2⟩, h3⟩ := hM
      have hM' : (M1 ++ M2).Nodup :=
        List.nodup_append.mpr ⟨h1, h2, fun x hx y hy => h3 x hx y (List.mem_cons_of_mem a hy)⟩
      have hih := ih (M1 ++ M2) hrest hM' g fun b hb hgb => by
        have hbM := hsupp b (List.mem_cons_of_mem a hb) hgb
        rw [List.mem_append, List.mem_cons] at hbM
        rcases hbM with hb1 | rfl | hb2
        · exact List.mem_append.mpr (Or.inl hb1)
        · exact absurd hb hanotin
        · exact List.mem_append.mpr (Or.inr hb2)
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hih ⊢
      omega

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
  (simp? [Allocation.total] says simp only [total, List.map_cons, List.sum_cons, Nat.add_left_cancel_iff])

omit [DecidableEq E] in
theorem total_append (o o' : Allocation E) :
    Allocation.total (o ++ o') = Allocation.total o + Allocation.total o' := by
  (simp? [Allocation.total] says simp only [total, List.map_append, List.sum_append, Nat.add_left_cancel_iff])

omit [DecidableEq E] in
theorem total_take_succ {o : Allocation E} {k : Nat} {e : Entry E} (h : o[k]? = some e) :
    Allocation.total (o.take (k + 1)) = Allocation.total (o.take k) + e.amount := by
  rw [List.take_add_one, total_append, h]
  (simp? says simp only [Option.toList_some, total_cons, total_nil, add_zero, Nat.add_left_cancel_iff])

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
  (simpa? using List.find?_some h says simpa only [decide_eq_true_eq] using List.find?_some h)

theorem find_eq_none {o : Allocation E} {d : Address E} :
    o.find d = none ↔ d ∉ o.map Entry.dest := by
  (simp? [Allocation.find, List.find?_eq_none] says simp only [find, List.find?_eq_none, decide_eq_true_eq, List.mem_map, not_exists, not_and])

theorem owed_cons (e : Entry E) (o : Allocation E) (d : Address E) :
    Allocation.owed (e :: o) d = if e.dest = d then e.amount else o.owed d := by
  by_cases h : e.dest = d <;> simp [Allocation.owed, find_cons, h]

/-- With distinct destinations, the entry at a position is the first entry
    for its destination. -/
theorem find_of_getElem? {o : Allocation E} (hnd : (o.map Entry.dest).Nodup) {j : Nat} {f : Entry E}
    (h : o[j]? = some f) : o.find f.dest = some f := by
  induction o generalizing j with
  | nil => (simp? at h says simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h)
  | cons e t ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; (simp? [find_cons] says simp only [find_cons, ↓reduceIte])
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
  | nil => (simp? says simp only [dedupFrom_nil, List.Sublist.refl])
  | cons e t ih =>
    rw [dedupFrom_cons]
    split
    · exact (ih seen).cons e
    · exact (ih _).cons_cons e

theorem dest_not_mem_of_mem_dedupFrom {seen : List (Address E)} {o : Allocation E} {e : Entry E}
    (h : e ∈ Allocation.dedupFrom seen o) : e.dest ∉ seen := by
  induction o generalizing seen with
  | nil => (simp? at h says simp only [dedupFrom_nil, List.not_mem_nil] at h)
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
  | nil => (simp? says simp only [dedupFrom_nil, List.map_nil, List.nodup_nil])
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
  | nil => (simp? says simp only [dedupFrom_nil, find_nil, ite_self])
  | cons e t ih =>
    rw [dedupFrom_cons, find_cons]
    by_cases hs : e.dest ∈ seen
    · rw [if_pos hs, ih]
      by_cases hd : e.dest = d
      · subst hd; (simp? [hs] says simp only [hs, ↓reduceIte])
      · (simp? [hd] says simp only [hd, ↓reduceIte])
    · rw [if_neg hs, find_cons, ih]
      by_cases hd : e.dest = d
      · subst hd; (simp? [hs] says simp only [↓reduceIte, hs])
      · have : d ≠ e.dest := Ne.symm hd
        (simp? [hd, this] says simp only [hd, ↓reduceIte, List.mem_cons, this, false_or])

@[simp] theorem find_dedup (o : Allocation E) (d : Address E) : o.dedup.find d = o.find d := by
  (simp? [Allocation.dedup, find_dedupFrom] says simp only [dedup, find_dedupFrom, List.not_mem_nil, ↓reduceIte])

@[simp] theorem owed_dedup (o : Allocation E) (d : Address E) : o.dedup.owed d = o.owed d := by
  (simp? [Allocation.owed] says simp only [owed, find_dedup])

/-- `dedupFrom` is a no-op on an allocation whose destinations are already
    distinct from each other and from `seen`: every entry passes the
    membership test, so nothing is dropped. -/
theorem dedupFrom_eq_self {seen : List (Address E)} {o : Allocation E}
    (hseen : ∀ e ∈ o, e.dest ∉ seen) (hnd : (o.map Entry.dest).Nodup) :
    Allocation.dedupFrom seen o = o := by
  induction o generalizing seen with
  | nil => rfl
  | cons e rest ih =>
    rw [dedupFrom_cons, if_neg (hseen e List.mem_cons_self)]
    have hrest : (rest.map Entry.dest).Nodup := (List.nodup_cons.1 hnd).2
    have he : e.dest ∉ rest.map Entry.dest := (List.nodup_cons.1 hnd).1
    have hseen' : ∀ e' ∈ rest, e'.dest ∉ e.dest :: seen := by
      intro e' he' hmem
      rcases List.mem_cons.1 hmem with heq | hmem
      · exact he (heq ▸ List.mem_map_of_mem he')
      · exact hseen e' (List.mem_cons_of_mem e he') hmem
    rw [ih hseen' hrest]

/-- A deduplicated allocation with already-distinct destinations is
    unchanged by `dedup`. -/
theorem dedup_eq_self_of_nodup {o : Allocation E} (hnd : (o.map Entry.dest).Nodup) :
    o.dedup = o :=
  dedupFrom_eq_self (by (simp? says simp only [List.not_mem_nil, not_false_eq_true, implies_true])) hnd

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
  | cons e t ih => (simp? [ih] says simp only [payout_cons, List.map_cons, ih])

omit [DecidableEq E] in
/-- ForceMove:1837-1853: entry `k` is paid `min(amount, held − total before k)`. -/
theorem payout_getElem? {held : Coins} {o : Allocation E} {k : Nat} {e : Entry E}
    (h : o[k]? = some e) :
    (o.payout held)[k]? = some (e.dest, min e.amount (held - Allocation.total (o.take k))) := by
  induction o generalizing held k with
  | nil => (simp? at h says simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h)
  | cons e' t ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; (simp? says simp only [payout_cons, List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, List.getElem_cons_zero, List.take_zero, total_nil, tsub_zero])
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      rw [payout_cons, List.getElem?_cons_succ, ih h, List.take_succ_cons, total_cons]
      congr 3
      (grind? says grind only [= min_def, #9d14, #839b, #d2b4])

omit [DecidableEq E] in
theorem payout_sum_le (held : Coins) (o : Allocation E) : ((o.payout held).map (·.2)).sum ≤ held := by
  induction o generalizing held with
  | nil => (simp? says simp only [payout_nil, List.map_nil, List.sum_nil, zero_le])
  | cons e t ih =>
    have := ih (held - min e.amount held)
    simp only [payout_cons, List.map_cons, List.sum_cons]
    (grind? says grind only [= min_def, #7e16, #ab6a])

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
  | nil => (simp? [Allocation.owed] says simp only [payout_nil, Balances.get_nil, owed, find_nil, Option.map_none, Option.getD_none, Std.le_refl])
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons]
    by_cases h : e.dest = d
    · (simp? [h] says simp only [h, ↓reduceIte, inf_le_left])
    · simp only [Ne.symm h, if_false, h]; exact ih _

/-- When the coins held cover the total, each first entry is paid in full. -/
theorem owed_le_payout_get {held : Coins} {o : Allocation E} (h : o.total ≤ held) (d : Address E) :
    o.owed d ≤ Balances.get (o.payout held) d := by
  induction o generalizing held with
  | nil => (simp? [Allocation.owed] says simp only [owed, find_nil, Option.map_none, Option.getD_none, payout_nil, Balances.get_nil, Std.le_refl])
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons]
    rw [total_cons] at h
    by_cases hd : e.dest = d
    · simp only [hd, if_true]; (grind? says grind only [= min_def, #ab6a])
    · simp only [Ne.symm hd, if_false, hd]; exact ih (by (grind? says grind only [= min_def, #7e16, #ab6a]))

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
  | nil => (simp? [Allocation.owed] says simp only [owed, reduceOwed_nil, find_nil, Option.map_none, Option.getD_none, zero_le, Nat.sub_eq_zero_of_le, ite_self])
  | cons e t ih =>
    rw [reduceOwed_cons]
    by_cases he : e.dest = d
    · subst he
      by_cases hd : d' = e.dest
      · subst hd; (simp? [owed_cons, Entry.amount] says simp only [↓reduceIte, Entry.amount, owed_cons, Item.amount_alloc])
      · (simp? [owed_cons, hd, Ne.symm hd] says simp only [↓reduceIte, owed_cons, Ne.symm hd, hd])
    · rw [if_neg he, owed_cons, owed_cons, ih]
      by_cases hd : d' = d
      · subst hd; (simp? [he] says simp only [he, ↓reduceIte])
      · (simp? [owed_cons, hd] says simp only [hd, ↓reduceIte, owed_cons])

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
  | nil => (simp? [Allocation.reduceOwed] says simp only [reduceOwed, find_nil, Option.map_none, ite_self])
  | cons e t ih =>
    rw [reduceOwed_cons]
    by_cases he : e.dest = d
    · subst he
      by_cases hd : d' = e.dest
      · subst hd; (simp? [find_cons] says simp only [↓reduceIte, find_cons, Option.map_some])
      · (simp? [find_cons, hd, Ne.symm hd] says simp only [↓reduceIte, find_cons, Ne.symm hd, hd])
    · by_cases hd : d' = d
      · subst hd; (simp? [find_cons, he, ih] says simp only [he, ↓reduceIte, find_cons, ih])
      · simp only [if_neg he, find_cons, ih, if_neg hd]

/-- The amount owed to one destination never exceeds the allocation's whole
    total: `d`'s own entry (if any) is one summand of a sum of
    non-negatives. -/
theorem owed_le_total (o : Allocation E) (d : Address E) : o.owed d ≤ o.total := by
  induction o with
  | nil => (simp? [Allocation.owed] says simp only [owed, find_nil, Option.map_none, Option.getD_none, total_nil, Std.le_refl])
  | cons e t ih =>
    rw [owed_cons, total_cons]
    by_cases h : e.dest = d
    · rw [if_pos h]; (grind? says grind only)
    · rw [if_neg h]; (grind? says grind only)

/-- Reducing the amount owed to `d` by `x` (at most what `d` is owed) drops
    the total by exactly `x`: only `d`'s own first entry changes, by exactly
    `x` (`reduceOwed_cons`). Stated additively (`+ x = `) to avoid `Coins`
    truncated subtraction on either side. -/
theorem total_reduceOwed (o : Allocation E) (d : Address E) {x : Coins} (hx : x ≤ o.owed d) :
    (o.reduceOwed d x).total + x = o.total := by
  induction o with
  | nil => (simp? [Allocation.owed] at hx says simp only [owed, find_nil, Option.map_none, Option.getD_none, nonpos_iff_eq_zero] at hx); (simp? [hx] says simp only [hx, reduceOwed_nil, total_nil, add_zero])
  | cons e t ih =>
    rw [owed_cons] at hx
    rw [reduceOwed_cons]
    by_cases he : e.dest = d
    · subst he
      rw [if_pos rfl] at hx ⊢
      have hv : Entry.amount ({ e with item := .alloc (e.amount - x) } : Entry E) = e.amount - x :=
        rfl
      rw [total_cons, hv, total_cons]
      (grind? says grind only)
    · rw [if_neg he] at hx ⊢
      rw [total_cons, total_cons]
      have := ih hx
      (grind? says grind only)

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
  | nil => (simp? [Allocation.owed] says simp only [payout_nil, Balances.get_nil, owed, find_nil, Option.map_none, Option.getD_none, List.takeWhile_nil, total_nil, tsub_zero, zero_le, inf_of_le_left])
  | cons e t ih =>
    rw [payout_cons, Balances.get_cons, owed_cons, List.takeWhile_cons]
    by_cases h : e.dest = b
    · (simp? [h] says simp only [h, ↓reduceIte, decide_true, Bool.not_true, Bool.false_eq_true, total_nil, tsub_zero])
    · simp only [Ne.symm h, h, if_false, ih, decide_false, Bool.not_false, if_true, total_cons]
      congr 1
      rcases le_total e.amount held with h1 | h1 <;> simp [h1] <;> unfold Coins at * <;> omega

/-- The entries ahead of `b`'s first entry, and that entry, are part of the
    total. -/
theorem total_takeWhile_add_owed_le (o : Allocation E) (b : Address E) :
    Allocation.total (o.takeWhile (fun e => !decide (e.dest = b))) + o.owed b ≤ o.total := by
  induction o with
  | nil => (simp? [Allocation.owed] says simp only [List.takeWhile_nil, total_nil, owed, find_nil, Option.map_none, Option.getD_none, add_zero, Std.le_refl])
  | cons e t ih =>
    rw [owed_cons, List.takeWhile_cons, total_cons]
    by_cases h : e.dest = b
    · (simp? [h] says simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, total_nil, zero_add, le_add_iff_nonneg_right, zero_le])
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
  | nil => (simp? says simp only [reduceOwed_nil, List.takeWhile_nil, total_nil, List.map_nil, List.not_mem_nil, ↓reduceIte, add_zero])
  | cons e t ih =>
    rw [owed_cons] at hx
    rw [reduceOwed_cons]
    by_cases hc : e.dest = c
    · rw [if_pos hc] at hx ⊢
      subst hc
      rw [List.takeWhile_cons, List.takeWhile_cons, List.map_cons, List.takeWhile_cons]
      by_cases hb : e.dest = b
      · (simp? [hb] says simp only [hb, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, total_nil, List.not_mem_nil, add_zero])
      · (simp? [hb] says simp only [hb, decide_false, Bool.not_false, ↓reduceIte, total_cons, Entry.amount_mk, Item.amount_alloc, List.mem_cons, true_or])
        unfold Coins at *
        omega
    · rw [if_neg hc] at hx ⊢
      rw [List.takeWhile_cons, List.takeWhile_cons, List.map_cons, List.takeWhile_cons]
      by_cases hb : e.dest = b
      · (simp? [hb] says simp only [hb, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, total_nil, List.not_mem_nil, add_zero])
      · (simp? [hb, Ne.symm hc] says simp only [hb, decide_false, Bool.not_false, ↓reduceIte, total_cons, List.mem_cons, Ne.symm hc, false_or])
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
  | nil => (simp? [Allocation.owed] at hc says simp only [owed, find_nil, Option.map_none, Option.getD_none, lt_self_iff_false] at hc)
  | cons e t ih =>
    rw [owed_cons] at hc
    by_cases hb : e.dest = b
    · subst hb
      (simp? [owed_cons, hbc] says simp only [decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.takeWhile_cons_of_neg, total_nil, owed_cons, ↓reduceIte, zero_add, hbc, decide_false, Bool.not_false, List.takeWhile_cons_of_pos, total_cons, le_add_iff_nonneg_right, zero_le])
    · have hec : e.dest ≠ c := by
        rintro rfl
        exact hnot (by (simp? [hb] says simp only [List.map_cons, hb, decide_false, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons, true_or]))
      rw [if_neg hec] at hc
      have hnot' : c ∉ (t.map Entry.dest).takeWhile (fun d => !decide (d = b)) := by
        (simpa? [List.takeWhile_cons, hb, Ne.symm hec] using hnot says simpa only [List.map_cons, hb, decide_false, Bool.not_false, List.takeWhile_cons_of_pos, List.mem_cons, Ne.symm hec, false_or] using hnot)
      have := ih hc hnot'
      (simp? [hb, hec, owed_cons] says simp only [hb, decide_false, Bool.not_false, List.takeWhile_cons_of_pos, total_cons, owed_cons, ↓reduceIte, hec, ge_iff_le])
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
      (simp? [hec, dedupFrom_cons, reduceOwed_cons, hc] says simp only [hec, ↓reduceIte, dedupFrom_cons, hc, reduceOwed_cons])
    · by_cases hs : e.dest ∈ seen
      · (simp? [hec, dedupFrom_cons, hs, ih seen hc] says simp only [hec, ↓reduceIte, dedupFrom_cons, hs, ih seen hc])
      · have hc' : c ∉ e.dest :: seen := by (simp? [Ne.symm hec, hc] says simp only [List.mem_cons, Ne.symm hec, hc, or_self, not_false_eq_true])
        (simp? [hec, dedupFrom_cons, hs, reduceOwed_cons, ih _ hc'] says simp only [hec, ↓reduceIte, dedupFrom_cons, hs, ih _ hc', reduceOwed_cons])

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
      (simp? [Entry.kind, Item.isGuarantee] says simp only [↓reduceIte, Entry.amount_mk, Item.amount_alloc, List.map_cons, Entry.kind, Item.isGuarantee])
    · rw [if_neg hec] at h
      (simp? [hec, ih h] says simp only [hec, ↓reduceIte, List.map_cons, ih h])

/-- Two allocations with the same entry kinds find entries of the same kind. -/
theorem find_map_kind {o o' : Allocation E} (h : o.map Entry.kind = o'.map Entry.kind)
    (c : Address E) : (o.find c).map Entry.kind = (o'.find c).map Entry.kind := by
  induction o generalizing o' with
  | nil => cases o' <;> simp_all
  | cons e t ih =>
    cases o' with
    | nil => (simp? at h says simp only [List.map_cons, List.map_nil, reduceCtorEq] at h)
    | cons e' t' =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hd : e.dest = e'.dest := congrArg Prod.fst h.1
      rw [find_cons, find_cons, ← hd]
      split
      · (simp? [h.1] says simp only [Option.map_some, h.1])
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
      (simp? [Entry.kind] at hk says simp only [Option.map_some, Entry.kind, Option.some.injEq, Prod.mk.injEq] at hk)
      exact ⟨a', by rw [hk.1]⟩
    | guarantee x ps => (simp? [Entry.kind, Item.isGuarantee] at hk says simp only [Option.map_some, Entry.kind, Item.isGuarantee, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false] at hk)

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
  (simpa? using List.all_eq_true.1 List.all_takeWhile c h says simpa only [decide_true, Bool.not_true, Bool.false_eq_true] using List.all_eq_true.1 List.all_takeWhile c h)

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
    · rename_i he; subst he; (simp? [find_cons, Ne.symm h] says simp only [find_cons, Ne.symm h, ↓reduceIte])
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
    · subst he; (simp? [find_cons] says simp only [↓reduceIte, find_cons, Option.map_some])
    · (simp? [find_cons, he, ih] says simp only [he, ↓reduceIte, find_cons, ih])

theorem owed_addTo_self {o : Allocation E} {d : Address E} (x : Coins) (h : o.find d ≠ none) :
    (o.addTo d x).owed d = o.owed d + x := by
  induction o with
  | nil => (simp? at h says simp only [find_nil, ne_eq, not_true_eq_false] at h)
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · subst he; (simp? [owed_cons, Entry.amount] says simp only [↓reduceIte, Entry.amount, owed_cons, Item.amount_alloc, Nat.add_left_cancel_iff])
    · rw [find_cons, if_neg he] at h
      rw [if_neg he, owed_cons, owed_cons, if_neg he, if_neg he, ih h]

theorem owed_addTo_of_ne (o : Allocation E) {d d' : Address E} (x : Coins) (h : d' ≠ d) :
    (o.addTo d x).owed d' = o.owed d' := by
  (simp? [Allocation.owed, find_addTo_of_ne o x h] says simp only [owed, find_addTo_of_ne o x h])

theorem total_addTo {o : Allocation E} {d : Address E} (x : Coins) (h : o.find d ≠ none) :
    (o.addTo d x).total = o.total + x := by
  induction o with
  | nil => (simp? at h says simp only [find_nil, ne_eq, not_true_eq_false] at h)
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · simp only [he, if_true, total_cons, Entry.amount]; simp only [Item.amount_alloc]; (grind? says grind only)
    · rw [find_cons, if_neg he] at h
      rw [if_neg he, total_cons, total_cons, ih h]; (grind? says grind only)

/-- `addTo` never raises the total by more than `x`, whether or not `d` is
    found (if not found it is a no-op, by the same recursion as
    `total_addTo`). -/
theorem total_addTo_le (o : Allocation E) (d : Address E) (x : Coins) :
    (o.addTo d x).total ≤ o.total + x := by
  induction o with
  | nil => (simp? [Allocation.addTo] says simp only [addTo, total_nil, zero_add, zero_le])
  | cons e t ih =>
    rw [addTo_cons]
    by_cases he : e.dest = d
    · simp only [he, if_true, total_cons, Entry.amount]; simp only [Item.amount_alloc]; (grind? says grind only)
    · simp only [he, if_false, total_cons]; (grind? says grind only)

/-- `addTo` never lowers the amount owed anywhere: at `d` itself it only
    raises it (`owed_addTo_self`, or leaves it at `0` when `d` has no entry
    to raise); everywhere else it is unchanged (`owed_addTo_of_ne`). -/
theorem owed_addTo_ge (o : Allocation E) (d d' : Address E) (x : Coins) :
    o.owed d' ≤ (o.addTo d x).owed d' := by
  by_cases h : d' = d
  · subst h
    by_cases hf : o.find d' = none
    · (simp? [Allocation.owed, hf] says simp only [owed, hf, Option.map_none, Option.getD_none, zero_le])
    · rw [owed_addTo_self x hf]; (grind? says grind only)
  · rw [owed_addTo_of_ne o x h]

theorem find_remove (o : Allocation E) (d d' : Address E) :
    (o.remove d).find d' = if d' = d then none else o.find d' := by
  induction o with
  | nil => (simp? [Allocation.remove] says simp only [remove, ne_eq, decide_not, List.filter_nil, find_nil, ite_self])
  | cons e t ih =>
    simp only [Allocation.remove, List.filter_cons, ne_eq, decide_not] at ih ⊢
    by_cases he : e.dest = d
    · subst he
      by_cases hd : d' = e.dest
      · subst hd; (simp? [ih] says simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih])
      · (simp? [find_cons, Ne.symm hd, ih, hd] says simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, hd, find_cons, Ne.symm hd])
    · by_cases hd : d' = d
      · subst hd; (simp? [he, find_cons, ih] says simp only [he, decide_false, Bool.not_false, ↓reduceIte, find_cons, ih])
      · (simp? [he, find_cons, ih, hd] says simp only [he, decide_false, Bool.not_false, ↓reduceIte, find_cons, ih, hd])

theorem owed_remove_of_ne (o : Allocation E) {d d' : Address E} (h : d' ≠ d) :
    (o.remove d).owed d' = o.owed d' := by
  (simp? [Allocation.owed, find_remove, h] says simp only [owed, find_remove, h, ↓reduceIte])

/-- With distinct destinations, removing `d` lowers the total by its amount. -/
theorem total_remove {o : Allocation E} (hnd : (o.map Entry.dest).Nodup) (d : Address E) :
    (o.remove d).total + o.owed d = o.total := by
  induction o with
  | nil => (simp? [Allocation.remove, Allocation.owed] says simp only [remove, ne_eq, decide_not, List.filter_nil, total_nil, owed, find_nil, Option.map_none, Option.getD_none, add_zero])
  | cons e t ih =>
    have ht := ih (List.nodup_cons.1 hnd).2
    simp only [Allocation.remove, List.filter_cons] at ht ⊢
    rw [owed_cons]
    by_cases he : e.dest = d
    · subst he
      have hno : Allocation.find t e.dest = none :=
        find_eq_none.2 (List.nodup_cons.1 hnd).1
      have hown : Allocation.owed t e.dest = 0 := by (simp? [Allocation.owed, hno] says simp only [owed, hno, Option.map_none, Option.getD_none])
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true,
        total_cons]
      (grind? says grind only)
    · simp only [ne_eq, he, not_false_eq_true, decide_true, if_true, if_false, total_cons]
      (grind? says grind only)

/-- Without distinctness, removing `d` still lowers the total by at least
    its (first-entry) owed amount: every duplicate entry for `d` only
    removes more. -/
theorem total_remove_le (o : Allocation E) (d : Address E) :
    (o.remove d).total + o.owed d ≤ o.total := by
  induction o with
  | nil => (simp? [Allocation.remove, Allocation.owed] says simp only [remove, ne_eq, decide_not, List.filter_nil, total_nil, owed, find_nil, Option.map_none, Option.getD_none, add_zero, Std.le_refl])
  | cons e t ih =>
    simp only [Allocation.remove, List.filter_cons] at ih ⊢
    rw [owed_cons]
    by_cases he : e.dest = d
    · subst he
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true,
        total_cons]
      (grind? says grind only)
    · simp only [ne_eq, he, not_false_eq_true, decide_true, if_true, if_false, total_cons]
      (grind? says grind only)


/-! ### `chainPay`: paying an allocation's own destinations in order -/

/-- Pay every destination in `ds`, in order, out of one allocation's own
    coins (`AheadOf.pay_left`, one call per destination). A destination
    whose current first entry is not an allocation item (already paid down
    to a zero-owed item in an earlier call does not change this; a
    guarantee item never does) is skipped. -/
def chainPay : List (Address E) → Allocation E → Coins → Allocation E × Coins
  | [], og, hg => (og, hg)
  | d :: ds, og, hg =>
    match og.find d with
    | some ⟨_, .alloc _⟩ => chainPay ds (og.reduceOwed d (og.paidTo hg d)) (hg - og.paidTo hg d)
    | _ => chainPay ds og hg

/-- One unfolding step of `chainPay`, in the shape the definition's match
    gives. -/
theorem chainPay_cons (d : Address E) (ds : List (Address E)) (og : Allocation E) (hg : Coins) :
    chainPay (d :: ds) og hg =
      match og.find d with
      | some ⟨_, .alloc _⟩ => chainPay ds (og.reduceOwed d (og.paidTo hg d)) (hg - og.paidTo hg d)
      | _ => chainPay ds og hg := rfl

/-- Chaining `AheadOf.pay_left` over an allocation's own destinations, in
    its own priority order, keeps it ahead of any fixed allocation it
    started ahead of. Each step is a no-op (`og`, `hg` unchanged) or exactly
    one `AheadOf.pay_left` call, which `AheadOf.pay_left` already shows
    keeps `AheadOf` true. -/
theorem chainPay_AheadOf (ds : List (Address E)) (og op : Allocation E) (hg : Coins)
    (h : og.AheadOf op hg) :
    (chainPay ds og hg).1.AheadOf op (chainPay ds og hg).2 := by
  induction ds generalizing og hg with
  | nil => exact h
  | cons d ds ih =>
    rw [chainPay_cons]
    cases hf : og.find d with
    | none => exact ih _ _ h
    | some entry =>
      obtain ⟨dd, item⟩ := entry
      have hdd : dd = d := find_dest hf
      cases item with
      | alloc amt =>
        subst dd
        exact ih _ _ (AheadOf.pay_left h hf)
      | guarantee amt ps => exact ih _ _ h

/-- Paying `c`'s own first entry down to zero owed to it never raises the
    gap between the running budget and `c`'s own (unchanged) coins due
    before it: either `c`'s whole owed amount was paid (new owed `0`), or
    the budget ran out exactly at `c`'s coins due before it. -/
theorem paidTo_reduceOwed_self_zero (o : Allocation E) (hg : Coins) (c : Address E) :
    (o.reduceOwed c (o.paidTo hg c)).paidTo (hg - o.paidTo hg c) c = 0 := by
  have hxo : o.paidTo hg c ≤ o.owed c := paidTo_le_owed hg o c
  have h1 := dueBefore_reduceOwed o c c hxo
  rw [if_neg (not_precedes_self o c)] at h1
  have h3 := owed_reduceOwed o c c (o.paidTo hg c)
  rw [if_pos rfl] at h3
  have hm := paidTo_eq_min hg o c
  rw [paidTo_eq_min]
  unfold Coins at *
  omega

/-- A destination's own first entry is one summand of the coins due before
    any destination it precedes: `c`'s own entry is inside the prefix of
    `o`'s destinations that lies before `d`. -/
theorem owed_le_total_takeWhile_of_mem {o : Allocation E} {c : Address E} {p : Address E → Bool}
    (hc : c ∈ (o.map Entry.dest).takeWhile p) :
    o.owed c ≤ Allocation.total (o.takeWhile (fun e => p e.dest)) := by
  induction o with
  | nil => (simp? at hc says simp only [List.map_nil, List.takeWhile_nil, List.not_mem_nil] at hc)
  | cons e t ih =>
    rw [List.map_cons, List.takeWhile_cons] at hc
    rw [owed_cons, List.takeWhile_cons]
    by_cases hp : p e.dest
    · simp only [hp, if_true] at hc ⊢
      rw [List.mem_cons] at hc
      rw [total_cons]
      by_cases hec : e.dest = c
      · (simp? [hec] says simp only [hec, ↓reduceIte, le_add_iff_nonneg_right, zero_le])
      · rw [if_neg hec]
        have hc' : c ∈ (t.map Entry.dest).takeWhile p := hc.resolve_left (Ne.symm hec)
        exact le_trans (ih hc') (Nat.le_add_left _ _)
    · (simp? [hp] at hc says simp only [hp, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hc)

/-- When `c` precedes `d` in priority order, `c`'s own entry is one of the
    entries due before `d`. -/
theorem owed_le_dueBefore_of_precedes {o : Allocation E} {c d : Address E} (h : o.Precedes c d) :
    o.owed c ≤ o.dueBefore d := by
  unfold dueBefore
  rw [← owed_dedup]
  exact owed_le_total_takeWhile_of_mem h

/-- Paying some destination `c` never un-zeroes a destination `d` whose
    `paidTo` is already zero: paying `c` only lowers the running budget and
    only lowers (never raises) `d`'s own coins due before it
    (`dueBefore_reduceOwed`), so the gap that was already non-positive
    stays non-positive. When `c` precedes `d`, `c`'s own owed amount (so
    also the lower amount `og.paidTo hg c`) is at most `d`'s coins due
    before it (`owed_le_dueBefore_of_precedes`), which keeps the budget-side
    subtraction from wrapping. -/
theorem paidTo_zero_reduceOwed (og : Allocation E) (hg : Coins) (d c : Address E)
    (h0 : og.paidTo hg d = 0) :
    (og.reduceOwed c (og.paidTo hg c)).paidTo (hg - og.paidTo hg c) d = 0 := by
  have hxo : og.paidTo hg c ≤ og.owed c := paidTo_le_owed hg og c
  have hxh : og.paidTo hg c ≤ hg := paidTo_le_held hg og c
  have h1 := dueBefore_reduceOwed og d c hxo
  have h3 := owed_reduceOwed og c d (og.paidTo hg c)
  have hm := paidTo_eq_min hg og d
  rw [h0] at hm
  rw [paidTo_eq_min]
  by_cases hdc : d = c
  · subst hdc
    rw [if_pos rfl] at h3
    rw [if_neg (not_precedes_self og _)] at h1
    unfold Coins at *
    omega
  · rw [if_neg hdc] at h3
    by_cases hp : og.Precedes c d
    · rw [if_pos hp] at h1
      have hxd : og.paidTo hg c ≤ og.dueBefore d := le_trans hxo (owed_le_dueBefore_of_precedes hp)
      unfold Coins at *
      omega
    · rw [if_neg hp] at h1
      unfold Coins at *
      omega

/-- Once a destination's `paidTo` is zero at some point along a `chainPay`
    run, it stays zero for the rest of the run: every further step is a
    no-op or one more `paidTo_zero_reduceOwed` step. -/
theorem chainPay_paidTo_invariant (ds : List (Address E)) (og : Allocation E) (hg : Coins)
    (d : Address E) (h0 : og.paidTo hg d = 0) :
    (chainPay ds og hg).1.paidTo (chainPay ds og hg).2 d = 0 := by
  induction ds generalizing og hg with
  | nil => exact h0
  | cons e ds ih =>
    rw [chainPay_cons]
    cases hf : og.find e with
    | none => exact ih _ _ h0
    | some entry =>
      obtain ⟨ee, item⟩ := entry
      cases item with
      | alloc amt => exact ih _ _ (paidTo_zero_reduceOwed og hg d e h0)
      | guarantee amt ps => exact ih _ _ h0

/-- A destination `d` that is in the list `ds` a `chainPay` run processes,
    and whose current first entry (at the point the run reaches it) is an
    allocation item, ends the run with `paidTo = 0`: the step that reaches
    `d` zeroes it (`paidTo_reduceOwed_self_zero`), and `chainPay_paidTo_invariant`
    keeps it zero through every later step. -/
theorem chainPay_processes_alloc (ds : List (Address E)) (og : Allocation E) (hg : Coins)
    (d : Address E) (hd : d ∈ ds) (amt : Coins) (hf : og.find d = some ⟨d, .alloc amt⟩) :
    (chainPay ds og hg).1.paidTo (chainPay ds og hg).2 d = 0 := by
  induction ds generalizing og hg with
  | nil => exact absurd hd (List.not_mem_nil)
  | cons e ds ih =>
    rw [chainPay_cons]
    rcases eq_or_ne e d with hed | hed
    · subst hed
      rw [hf]
      exact chainPay_paidTo_invariant ds _ _ e (paidTo_reduceOwed_self_zero og hg e)
    · have hd' : d ∈ ds := (List.mem_cons.1 hd).resolve_left (Ne.symm hed)
      cases hfe : og.find e with
      | none => exact ih _ _ hd' hf
      | some entry =>
        obtain ⟨ee, item⟩ := entry
        cases item with
        | alloc amt' =>
          have hfd' : (og.reduceOwed e (og.paidTo hg e)).find d = some ⟨d, .alloc amt⟩ := by
            rw [find_reduceOwed, if_neg (Ne.symm hed), hf]
          exact ih _ _ hd' hfd'
        | guarantee amt' ps => exact ih _ _ hd' hf

/-- A destination found in an allocation is one of its entries' destinations. -/
theorem find_mem_map_dest {o : Allocation E} {d : Address E} {f : Entry E}
    (h : o.find d = some f) : f.dest ∈ o.map Entry.dest := by
  induction o with
  | nil => (simp? at h says simp only [find_nil, reduceCtorEq] at h)
  | cons e t ih =>
    rw [find_cons] at h
    by_cases he : e.dest = d
    · rw [if_pos he] at h
      cases h
      (simp? says simp only [List.map_cons, List.mem_cons, List.mem_map, true_or])
    · rw [if_neg he] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Two allocations with the same entry kinds find matching
    whether-a-guarantee entries at every destination. -/
theorem find_some_of_map_kind {o o' : Allocation E} (h : o.map Entry.kind = o'.map Entry.kind)
    {d : Address E} {f : Entry E} (hf : o.find d = some f) :
    ∃ f', o'.find d = some f' ∧ f'.item.isGuarantee = f.item.isGuarantee := by
  have hk := find_map_kind h d
  rw [hf] at hk
  cases hc : o'.find d with
  | none => rw [hc] at hk; (simp? at hk says simp only [Option.map_some, Option.map_none, reduceCtorEq] at hk)
  | some g' =>
    refine ⟨g', rfl, ?_⟩
    rw [hc] at hk
    (simp? [Entry.kind] at hk says simp only [Option.map_some, Entry.kind, Option.some.injEq, Prod.mk.injEq] at hk)
    exact hk.2.symm

/-- Processing every destination of an allocation `o`, in `o`'s own
    priority order, exhausts it: every address either has no entry left, or
    its entry is a guarantee (never touched, `AheadOf.kind`), or its
    `paidTo` against the leftover budget is `0` (`chainPay_processes_alloc`). -/
theorem chainPay_exhausted (o : Allocation E) (hg : Coins) (d : Address E) :
    ((chainPay (o.map Entry.dest) o hg).1.find d).elim True
      (fun e => e.item.isGuarantee = true ∨
        (chainPay (o.map Entry.dest) o hg).1.paidTo (chainPay (o.map Entry.dest) o hg).2 d = 0) := by
  have hahead := chainPay_AheadOf (o.map Entry.dest) o o hg (AheadOf.refl o hg)
  cases hfod : o.find d with
  | none =>
    have hk := find_map_kind hahead.kind d
    rw [hfod] at hk
    cases hc : (chainPay (o.map Entry.dest) o hg).1.find d with
    | none => trivial
    | some f' => rw [hc] at hk; (simp? at hk says simp only [Option.map_some, Option.map_none, reduceCtorEq] at hk)
  | some f =>
    obtain ⟨fd, fi⟩ := f
    have hfd : fd = d := find_dest hfod
    subst fd
    obtain ⟨f', hf', hkind⟩ := find_some_of_map_kind hahead.kind.symm hfod
    rw [hf']
    cases fi with
    | alloc amt =>
      have hmem : d ∈ o.map Entry.dest := find_mem_map_dest hfod
      exact Or.inr (chainPay_processes_alloc (o.map Entry.dest) o hg d hmem amt hfod)
    | guarantee x ps => exact Or.inl hkind


theorem chainPay_dedup_total_conservation (ds : List (Address E)) (og : Allocation E) (hg : Coins) :
    (chainPay ds og hg).2 + (og.dedup.total - (chainPay ds og hg).1.dedup.total) = hg ∧
    (chainPay ds og hg).1.dedup.total ≤ og.dedup.total := by
  induction ds generalizing og hg with
  | nil => (simp? [chainPay] says simp only [chainPay, Nat.sub_self, add_zero, Std.le_refl, and_self])
  | cons e ds ih =>
    cases hf : og.find e with
    | none =>
      rw [chainPay_cons]
      simp only [hf]
      exact ih og hg
    | some entry =>
      obtain ⟨ee, item⟩ := entry
      cases item with
      | alloc amt =>
        rw [chainPay_cons]
        simp only [hf]
        have howed : og.owed e = amt := by unfold Allocation.owed; rw [hf]; rfl
        have hxo : og.paidTo hg e ≤ og.owed e := by
          rw [howed]
          have := Allocation.paidTo_le_owed hg og e
          rwa [howed] at this
        have htot : (og.reduceOwed e (og.paidTo hg e)).dedup.total + og.paidTo hg e =
            og.dedup.total := Allocation.dedup_total_reduceOwed og e hxo
        obtain ⟨ihc, ihle⟩ := ih (og.reduceOwed e (og.paidTo hg e)) (hg - og.paidTo hg e)
        have hxh : og.paidTo hg e ≤ hg := Allocation.paidTo_le_held hg og e
        refine ⟨?_, ?_⟩
        · have h1 := ihc
          have h2 := htot
          have h3 := ihle
          have h4 := hxh
          unfold Coins at h1 h2 h3 h4 ⊢
          omega
        · have h1 := ihle
          have h2 := htot
          unfold Coins at h1 h2 ⊢
          omega
      | guarantee amt ps =>
        rw [chainPay_cons]
        simp only [hf]
        exact ih og hg

theorem chainPay_owed_invariant (ds : List (Address E)) (og : Allocation E) (hg : Coins)
    (d : Address E) (h0 : og.paidTo hg d = 0) :
    (chainPay ds og hg).1.owed d = og.owed d := by
  induction ds generalizing og hg with
  | nil => rfl
  | cons e ds ih =>
    rw [chainPay_cons]
    cases hfe : og.find e with
    | none => simp only [hfe]; exact ih og hg h0
    | some entry =>
      obtain ⟨ee, item⟩ := entry
      cases item with
      | alloc amt' =>
        simp only [hfe]
        have h0' := paidTo_zero_reduceOwed og hg d e h0
        rw [ih (og.reduceOwed e (og.paidTo hg e)) (hg - og.paidTo hg e) h0']
        rw [owed_reduceOwed]
        by_cases hed : d = e
        · subst hed; rw [if_pos rfl, h0]; unfold Coins; omega
        · rw [if_neg hed]
      | guarantee amt' ps =>
        simp only [hfe]
        exact ih og hg h0


theorem chainPay_append (ds1 ds2 : List (Address E)) (og : Allocation E) (hg : Coins) :
    chainPay (ds1 ++ ds2) og hg =
      chainPay ds2 (chainPay ds1 og hg).1 (chainPay ds1 og hg).2 := by
  induction ds1 generalizing og hg with
  | nil => rfl
  | cons d ds1 ih =>
    rw [List.cons_append, chainPay_cons, chainPay_cons]
    cases hfd : og.find d with
    | none => exact ih og hg
    | some entry =>
      obtain ⟨ed, item⟩ := entry
      cases item with
      | alloc amt => exact ih _ _
      | guarantee amt ps => exact ih og hg

/-- An entry never targeted during a `chainPay` run is never found at
    (hence never touched at) any later point. -/
theorem chainPay_find_unchanged (ds : List (Address E)) (og : Allocation E) (hg : Coins)
    (d : Address E) (hd : d ∉ ds) :
    (chainPay ds og hg).1.find d = og.find d := by
  induction ds generalizing og hg with
  | nil => rfl
  | cons e ds ih =>
    simp only [List.mem_cons, not_or] at hd
    obtain ⟨hed, hd⟩ := hd
    rw [chainPay_cons]
    cases hfe : og.find e with
    | none => simp only [hfe]; exact ih og hg hd
    | some entry =>
      obtain ⟨ee, item⟩ := entry
      cases item with
      | alloc amt' =>
        simp only [hfe]
        rw [ih (og.reduceOwed e (og.paidTo hg e)) (hg - og.paidTo hg e) hd]
        rw [find_reduceOwed, if_neg hed]
      | guarantee amt' ps => simp only [hfe]; exact ih og hg hd

/-- Paying `c`'s own first entry down leaves `d`'s `paidTo` unchanged, as
    long as `c` precedes `d` in priority order: both the running budget and
    `d`'s own coins due before it drop by the same amount
    (`dueBefore_reduceOwed`, `owed_le_dueBefore_of_precedes`). -/
theorem paidTo_eq_reduceOwed_of_precedes (og : Allocation E) (hg : Coins) (d c : Address E)
    (hp : og.Precedes c d) :
    (og.reduceOwed c (og.paidTo hg c)).paidTo (hg - og.paidTo hg c) d = og.paidTo hg d := by
  have hcd : c ≠ d := fun h => not_precedes_self og d (h ▸ hp)
  have hxo : og.paidTo hg c ≤ og.owed c := paidTo_le_owed hg og c
  have hxd : og.paidTo hg c ≤ og.dueBefore d := le_trans hxo (owed_le_dueBefore_of_precedes hp)
  have h1 := dueBefore_reduceOwed og d c hxo
  rw [if_pos hp] at h1
  have h3 := owed_reduceOwed og c d (og.paidTo hg c)
  rw [if_neg (Ne.symm hcd)] at h3
  rw [paidTo_eq_min hg og d]
  conv_lhs => rw [paidTo_eq_min]
  rw [h3]
  have heq : hg - og.paidTo hg c -
      (og.reduceOwed c (og.paidTo hg c)).dueBefore d = hg - og.dueBefore d := by
    unfold Coins at *
    omega
  rw [heq]

theorem reduceOwed_map_dest (o : Allocation E) (c : Address E) (x : Coins) :
    (o.reduceOwed c x).map Entry.dest = o.map Entry.dest := by
  induction o with
  | nil => rfl
  | cons e t ih =>
    rw [reduceOwed_cons]
    by_cases h : e.dest = c
    · (simp? [h] says simp only [h, ↓reduceIte, List.map_cons])
    · (simp? [h, ih] says simp only [h, ↓reduceIte, List.map_cons, ih])

/-- `Precedes` only reads the destination list, which `reduceOwed` never
    changes. -/
theorem precedes_reduceOwed' (o : Allocation E) (e : Address E) (x : Coins) (c d : Address E) :
    (o.reduceOwed e x).Precedes c d ↔ o.Precedes c d := by
  unfold Precedes
  rw [dedup_reduceOwed, reduceOwed_map_dest]

/-- Chains `paidTo_eq_reduceOwed_of_precedes` over a whole run: processing
    only destinations that precede `d` never moves `d`'s own `paidTo`
    reading. -/
theorem chainPay_paidTo_eq_of_precedes (ds : List (Address E)) (og : Allocation E) (hg : Coins)
    (d : Address E) (hds : ∀ c ∈ ds, og.Precedes c d) :
    (chainPay ds og hg).1.paidTo (chainPay ds og hg).2 d = og.paidTo hg d := by
  induction ds generalizing og hg with
  | nil => rfl
  | cons e ds ih =>
    rw [chainPay_cons]
    have hpe : og.Precedes e d := hds e List.mem_cons_self
    cases hfe : og.find e with
    | none => simp only [hfe]; exact ih og hg (fun c hc => hds c (List.mem_cons_of_mem e hc))
    | some entry =>
      obtain ⟨ee, item⟩ := entry
      cases item with
      | alloc amt' =>
        simp only [hfe]
        have heq := paidTo_eq_reduceOwed_of_precedes og hg d e hpe
        have hds' : ∀ c ∈ ds, (og.reduceOwed e (og.paidTo hg e)).Precedes c d := by
          intro c hc
          rw [precedes_reduceOwed']
          exact hds c (List.mem_cons_of_mem e hc)
        rw [ih (og.reduceOwed e (og.paidTo hg e)) (hg - og.paidTo hg e) hds']
        exact heq
      | guarantee amt' ps =>
        simp only [hfe]
        exact ih og hg (fun c hc => hds c (List.mem_cons_of_mem e hc))


theorem chainPay_owed_eq (og : Allocation E) (hnd : (og.map Entry.dest).Nodup) (hg : Coins)
    (d : Address E) (amt : Coins) (hf : og.find d = some ⟨d, .alloc amt⟩) :
    og.owed d - (chainPay (og.map Entry.dest) og hg).1.owed d = og.paidTo hg d := by
  have hdmem : d ∈ og.map Entry.dest := find_mem_map_dest hf
  obtain ⟨pre, suf, heq, hdpre⟩ := List.eq_append_cons_of_mem hdmem
  have hprecedes : ∀ c ∈ pre, og.Precedes c d := by
    intro c hc
    unfold Precedes
    rw [dedup_eq_self_of_nodup hnd, heq, List.takeWhile_append_of_pos]
    · exact List.mem_append_left _ hc
    · intro x hx
      by_cases hxd : x = d
      · subst hxd
        exact absurd hx hdpre
      · (simp? [hxd] says simp only [hxd, decide_false, Bool.not_false])
  rw [heq, chainPay_append, chainPay_cons]
  set og1 := (chainPay pre og hg).1 with hog1
  set hg1 := (chainPay pre og hg).2 with hhg1
  have hpaidto : og1.paidTo hg1 d = og.paidTo hg d :=
    chainPay_paidTo_eq_of_precedes pre og hg d hprecedes
  have hfind1 : og1.find d = og.find d := chainPay_find_unchanged pre og hg d hdpre
  rw [hfind1, hf]
  rw [chainPay_owed_invariant suf (og1.reduceOwed d (og1.paidTo hg1 d))
    (hg1 - og1.paidTo hg1 d) d (paidTo_reduceOwed_self_zero og1 hg1 d)]
  rw [owed_reduceOwed, if_pos rfl]
  have hown1 : og1.owed d = og.owed d := by
    unfold Allocation.owed
    rw [hfind1]
  rw [hown1, hpaidto]
  have hxo := paidTo_le_owed hg og d
  unfold Coins at *
  omega

/-- `chainPay` never changes the amount of a guarantee entry: each step
    reduces an allocation item at another destination
    (`owed_reduceOwed`), and that step keeps `d`'s first entry
    (`find_reduceOwed`). -/
theorem chainPay_owed_of_find_guarantee (ds : List (Address E)) (og : Allocation E)
    (hg : Coins) (d : Address E) (x : Coins) (ps : List (Address E))
    (hf : og.find d = some ⟨d, .guarantee x ps⟩) :
    (chainPay ds og hg).1.owed d = og.owed d := by
  induction ds generalizing og hg with
  | nil => rfl
  | cons e ds ih =>
    rw [chainPay_cons]
    cases hfe : og.find e with
    | none => exact ih og hg hf
    | some entry =>
      obtain ⟨ee, item⟩ := entry
      cases item with
      | alloc amt =>
        have hne : d ≠ e := by rintro rfl; rw [hf] at hfe; cases hfe
        rw [ih _ _ (by rw [find_reduceOwed, if_neg hne]; exact hf), owed_reduceOwed, if_neg hne]
      | guarantee _ _ => exact ih og hg hf

/-- What `og` owes `d`, before a `chainPay` run over its own destinations,
    is at most what it owes after, plus the run's payment to `d`
    (`chainPay_owed_eq`). A guarantee entry or no entry gets no payment
    (`chainPay_owed_of_find_guarantee`). The guard is the shape of
    `Adjudicator.CreditsTo`. -/
theorem owed_le_chainPay_owed_add (og : Allocation E) (hnd : (og.map Entry.dest).Nodup)
    (hg : Coins) (d : Address E) :
    og.owed d ≤ (chainPay (og.map Entry.dest) og hg).1.owed d +
      if ((og.find d).elim false (fun e => !e.item.isGuarantee)) then og.paidTo hg d else 0 := by
  cases hf : og.find d with
  | none => (simp? [Allocation.owed, hf] says simp only [owed, hf, Option.map_none, Option.getD_none, Option.elim_none, Bool.false_eq_true, ↓reduceIte, add_zero, zero_le])
  | some e =>
    obtain ⟨de, item⟩ := e
    obtain rfl : de = d := find_dest hf
    cases item with
    | alloc amt =>
      have h := chainPay_owed_eq og hnd hg de amt hf
      simp only [Option.elim, Item.isGuarantee, Bool.not_false, if_true]
      unfold Coins at *
      omega
    | guarantee x ps =>
      rw [chainPay_owed_of_find_guarantee _ og hg de x ps hf]
      (simp? says simp only [Option.elim_some, Bool.not_eq_eq_eq_not, Bool.not_true, le_add_iff_nonneg_right, zero_le])

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
  · exact ⟨by (grind? says grind only), h.2⟩
  · exact h

omit [DecidableEq E] in
theorem finalizedWith_mono {st : ChannelStatus E} {now now' : Time} {o : Outcome E}
    (h : st.finalizedWith now = some o) (hle : now ≤ now') : st.finalizedWith now' = some o := by
  cases st <;> simp at h ⊢
  · exact ⟨by (grind? says grind only), h.2⟩
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
  | nil => (simp? at h1 says simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h1)
  | cons a t ih =>
    cases t with
    | nil => (simp? at h2 says simp only [List.length_cons, List.length_nil, zero_add, add_lt_iff_neg_right, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h2)
    | cons b t =>
      simp only [validRun, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h1 h2
        subst h1 h2; exact h.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact ih h.2 (by (simpa? using h1 says simpa only using h1)) (by (simpa? using h2 says simpa only [List.getElem?_cons_succ] using h2))

/-- A run whose consecutive pairs are valid moves is a valid run: the
    converse of `validRun_getElem?`. -/
theorem validRun_of_getElem? {vt : State E → State E → Bool} {l : SupportProof E}
    (h : ∀ (i : Nat) m1 m2, l[i]? = some m1 → l[i + 1]? = some m2 → validMove vt m1 m2 = true) :
    validRun vt l = true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      simp only [validRun, Bool.and_eq_true]
      exact ⟨h 0 a b rfl rfl, ih fun i m1 m2 h1 h2 => h (i + 1) m1 m2 h1 h2⟩

/-- SATP:262-266, go-nitro Consensus.sol: the one signed state of a
    supported candidate is the candidate, signed by every participant, so
    it meets `Rules.SupportWindow`. Design decision 2026-11-01. -/
theorem consensusRules_supportWindow :
    (consensusRules : Rules E).SupportWindow := by
  intro c proof candidate hcon q hq
  match proof, hcon with
  | [ss], hcon =>
    simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
    obtain ⟨⟨hst, hchan⟩, hall⟩ := hcon
    have hn : 0 < c.n := List.length_pos_of_mem hq
    refine ⟨ss, List.mem_singleton_self ss, hall q (by rw [hchan]; exact hq), hchan,
      by rw [hst], by rw [hst]; omega⟩
  | [], hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
  | _ :: _ :: _, hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)

/-- `(t0 + i) % n` covers every residue `k < n` as `i` ranges over `0, …,
    n - 1`: the modular-arithmetic fact `forceMoveRules_supportWindow`
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

/-- ForceMove:1340-1354, 1379-1381, go-nitro StrictTurnTaking.sol: each of
    the `n` moves of a support run increases the turn number by one, so the
    `n` movers are one full cycle of `c.participants`, at the `n` turns up to
    the candidate; every participant signs its own move. Design decision
    2026-11-01. -/
theorem forceMoveRules_supportWindow (vt : State E → State E → Bool) :
    (forceMoveRules vt : Rules E).SupportWindow := by
  intro c proof candidate h q hq
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Option.all_eq_true] at h
  obtain ⟨⟨⟨⟨hlen, hhead⟩, hrun⟩, hchanAll⟩, hlast⟩ := h
  obtain ⟨k, hklt, hget⟩ := List.mem_iff_getElem.mp hq
  have hklt' : k < c.n := hklt
  have hn : 0 < c.n := by omega
  cases proof with
  | nil => (simp? at hlen says simp only [List.length_nil] at hlen); omega
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
      | zero => intro _; exact ⟨m0, rfl, hm0chan, by (simp? says simp only [add_zero]), hm0mover⟩
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
    have hlastturn : candidate.turnNum = m0.state.turnNum + (c.n - 1) := by
      obtain ⟨ml, hml, hmls⟩ : ∃ ml, (m0 :: rest).getLast? = some ml ∧ ml.state = candidate := by
        cases hl : (m0 :: rest).getLast? with
        | none => simp at hl
        | some ml => rw [hl] at hlast; exact ⟨ml, rfl, Option.some.inj hlast⟩
      rw [List.getLast?_eq_getElem?] at hml
      obtain ⟨m', hm'get, -, hm'turn, -⟩ := hind ((m0 :: rest).length - 1) (by omega)
      rw [hml] at hm'get
      obtain rfl := Option.some.inj hm'get
      rw [← hmls, hm'turn, hlenn]
    exact ⟨m, List.mem_of_getElem? hmget, hmv2, hmchan, by omega, by omega⟩

/-- `L` lists each element once. Changing `f` at `a` alone, by `y`, changes
    the sum of `f` over `L` by `y` exactly when `a` is in `L`. Used by
    `Adjudicator.transfer_effect`. -/
theorem sum_map_update {α : Type} [DecidableEq α] {L : List α} (hL : L.Nodup) {f g : α → Nat}
    {a : α} {y : Nat} (hne : ∀ c, c ≠ a → f c = g c) (ha : f a + y = g a) :
    (L.map f).sum + (if a ∈ L then y else 0) = (L.map g).sum := by
  induction L with
  | nil => (simp? says simp only [List.map_nil, List.sum_nil, List.not_mem_nil, ↓reduceIte, add_zero])
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
    · subst hk; (simp? [List.lookup_cons, beq_false_of_ne h, ih] says simp only [decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, ih, List.lookup_cons, beq_false_of_ne h])
    · by_cases hk' : c' = k
      · subst hk'; (simp? [hk] says simp only [hk, decide_false, Bool.not_false, List.filter_cons_of_pos, List.lookup_cons_self])
      · (simp? [hk, List.lookup_cons, beq_false_of_ne hk', ih] says simp only [hk, decide_false, Bool.not_false, List.filter_cons_of_pos, List.lookup_cons, beq_false_of_ne hk', ih])

omit [DecidableEq E] in
@[simp] theorem statusOf_setStatus (s : Adjudicator E) (c : FixedPart) (st : ChannelStatus E)
    (c' : FixedPart) : (s.setStatus c st).statusOf c' = if c' = c then st else s.statusOf c' := by
  unfold statusOf setStatus
  by_cases h : c' = c
  · subst h; (simp? says simp only [ne_eq, decide_not, List.lookup_cons_self, Option.getD_some, ↓reduceIte])
  · (simp? [List.lookup_cons, beq_false_of_ne h, h, lookup_filter_ne _ h] says simp only [ne_eq, decide_not, List.lookup_cons, beq_false_of_ne h, lookup_filter_ne _ h, h, ↓reduceIte])

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
        exact ⟨o, amt, _, hf, hfind, rfl, by (simp? says simp only [FixedPart.address_eq, payTo_balances, setStatus_balances]), by (simp? says simp only [FixedPart.address_eq, payTo_held, setStatus_held]), by (simp? says simp only [FixedPart.address_eq, payTo_status]), by (simp? says simp only [FixedPart.address_eq, payTo_now, setStatus_now]), hcond.1, hcond.2⟩
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
  (simp? [hfind] says simp only [hfind, FixedPart.address_eq, payTo_balances, setStatus_balances, payTo_held, setStatus_held, payTo_status, payTo_now, setStatus_now, ne_eq, reduceCtorEq, not_false_eq_true])

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
  (simp? [applyAll, h] says simp only [applyAll, h, Option.getD_some])

/-- Only `tick` moves the clock, and only forward. -/
theorem apply_now_le {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    (h : s.apply apps caller op = some s') : s.now ≤ s'.now := by
  cases op with
  | deposit a e x => (simp? [(deposit_some h).2.2.2.2.2] says simp only [(deposit_some h).2.2.2.2.2, Std.le_refl])
  | transfer a b => obtain ⟨_, _, _, _, _, _, _, _, _, hn, _, _⟩ := transfer_some h; (simp? [hn] says simp only [hn, Std.le_refl])
  | reclaim l v => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h; (simp? says simp only [FixedPart.address_eq, setStatus_now, Std.le_refl])
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; (simp? says simp only [setStatus_now, Std.le_refl])
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; (simp? says simp only [setStatus_now, Std.le_refl])
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; (simp? says simp only [setStatus_now, Std.le_refl])
  | tick dt => (simp? at h says simp only [apply_tick, Option.some.injEq] at h); subst h; (simp? says simp only [tick_now, le_add_iff_nonneg_right, zero_le])

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
    (simp? [Op.touchesBalances] at hop says simp only [Op.touchesBalances, Bool.true_eq_false] at hop)
  | transfer a b =>
    (simp? [Op.touchesBalances] at hop says simp only [Op.touchesBalances, Bool.true_eq_false] at hop)
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
    (simp? [Op.touchesHeld] at hop says simp only [Op.touchesHeld, Bool.true_eq_false] at hop)
  | transfer a b =>
    (simp? [Op.touchesHeld] at hop says simp only [Op.touchesHeld, Bool.true_eq_false] at hop)
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

/-- The exact effect of one step on channel `c`'s status: unchanged, or the
    step redistributes `c`'s finalized outcome (`reduceOwed`/`addTo`+`remove`),
    or the step is a challenge/checkpoint/conclude of `c` with the stated new
    status. Replaces the `cases op with` split repeated in `finalized_permanent`,
    `finalized_outcome_only_redistributed`, `turnNumRecord_monotone`,
    `statusOrigin_step`, and the narrower `finalizedWith_apply`. -/
theorem statusOf_step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} (h : s.apply apps caller op = some s') (c : FixedPart) :
    s'.statusOf c = s.statusOf c ∨
    (∃ o b x, (s.statusOf c).finalOutcome s.now = some (.allocation o) ∧
      s'.statusOf c = (s.statusOf c).withOutcome (.allocation (o.reduceOwed b x))) ∨
    (∃ oL left x1 right x2 rm, (s.statusOf c).finalOutcome s.now = some (.allocation oL) ∧
      s'.statusOf c =
        (s.statusOf c).withOutcome (.allocation (((oL.addTo left x1).addTo right x2).remove rm))) ∨
    (∃ proof cand, s.apply apps caller (.challenge c proof cand) = some s' ∧
      s'.statusOf c = .challenged cand.turnNum ⟨cand, s.now + c.challengeDuration⟩) ∨
    (∃ proof cand, s.apply apps caller (.checkpoint c proof cand) = some s' ∧
      s'.statusOf c = .open cand.turnNum) ∨
    (∃ ss, s.apply apps caller (.conclude c ss) = some s' ∧
      s'.statusOf c = .finalized ss.state.turnNum ss.state.outcome ss.state.outcome) := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := deposit_some h
    exact Or.inl (statusOf_of_status hs c)
  | tick dt =>
    simp only [apply_tick, Option.some.injEq] at h
    subst h
    exact Or.inl (tick_statusOf s dt c)
  | transfer a b =>
    obtain ⟨o, _, x, hf, -, -, -, -, hs, -⟩ := transfer_some h
    have hsc := statusOf_of_status hs c
    simp only [statusOf_setStatus] at hsc
    by_cases hca : c = a
    · subst hca
      simp only [if_true] at hsc
      simp only [FixedPart.address_eq, finalOutcome_channel] at hf
      exact Or.inr (Or.inl ⟨o, b, x, hf, hsc⟩)
    · simp only [hca, if_false] at hsc
      exact Or.inl hsc
  | reclaim l v =>
    obtain ⟨oL, oV, x, left, right, hL, -, -, -, -, -, rfl, -, -⟩ := reclaim_some h
    by_cases hcl : c = l
    · subst hcl
      simp only [FixedPart.address_eq, finalOutcome_channel] at hL
      refine Or.inr (Or.inr (Or.inl ⟨oL, left, oV.amountAt 0, right, oV.amountAt 1, v.address, hL, ?_⟩))
      simp only [statusOf_setStatus, if_true]
    · exact Or.inl (by simp only [statusOf_setStatus, hcl, if_false])
  | challenge c' proof cand =>
    have h' := h
    obtain ⟨-, rfl⟩ := challenge_some h
    by_cases hcc : c = c'
    · subst hcc
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨proof, cand, h', ?_⟩)))
      simp only [statusOf_setStatus, if_true]
    · exact Or.inl (by simp only [statusOf_setStatus, hcc, if_false])
  | checkpoint c' proof cand =>
    have h' := h
    obtain ⟨-, rfl⟩ := checkpoint_some h
    by_cases hcc : c = c'
    · subst hcc
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨proof, cand, h', ?_⟩))))
      simp only [statusOf_setStatus, if_true]
    · exact Or.inl (by simp only [statusOf_setStatus, hcc, if_false])
  | conclude c' ss =>
    have h' := h
    obtain ⟨-, rfl⟩ := conclude_some h
    by_cases hcc : c = c'
    · subst hcc
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ss, h', ?_⟩))))
      simp only [statusOf_setStatus, if_true]
    · exact Or.inl (by simp only [statusOf_setStatus, hcc, if_false])

/-- The outcome of finalization never changes: `transfer` and `reclaim`
    rewrite only the stored outcome, through `withOutcome`, which keeps the
    outcome of finalization; `challenge`, `checkpoint` and `conclude` all
    require the channel to be open, so none can act on an already-finalized
    one. Used by `Adjudicator.reclaim`'s channel-types repair (design
    decision 2026-10-27): a virtual channel's outcome, once finalized, is
    exactly what `reclaim` reads. Built from `statusOf_step`: the challenge/
    checkpoint/conclude disjuncts contradict `hmode` (each needs the channel
    open), the redistribution disjuncts call `finalizedWith_withOutcome`. -/
theorem finalizedWith_apply {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    (h : s.apply apps caller op = some s') {c : FixedPart} {f : Outcome E}
    (hf : s.finalizedWith c.address = some f) : s'.finalizedWith c.address = some f := by
  have hn := apply_now_le h
  simp only [FixedPart.address_eq, finalizedWith_channel] at hf ⊢
  have hmode : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, ← ChannelStatus.finalizedWith_isSome_iff, hf]; rfl
  rcases statusOf_step h c with
    heq | ⟨_, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, heq⟩ |
    ⟨proof, cand, hch, heq⟩ | ⟨proof, cand, hcp, heq⟩ | ⟨ss, hcl, heq⟩
  · rw [heq]; exact ChannelStatus.finalizedWith_mono hf hn
  · rw [heq]; exact ChannelStatus.finalizedWith_withOutcome hf _ _
  · rw [heq]; exact ChannelStatus.finalizedWith_withOutcome hf _ _
  · obtain ⟨⟨-, -, -, hm⟩, -⟩ := challenge_some hch
    rw [mode_eq] at hm
    rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hmode <;> cases hmode
  · obtain ⟨⟨ho, -⟩, -⟩ := checkpoint_some hcp
    exact absurd hmode ho
  · obtain ⟨⟨ho, -⟩, -⟩ := conclude_some hcl
    exact absurd hmode ho

/-- The outcome of finalization is permanent over every reachable step, not
    just one, by induction on `finalizedWith_apply`. SATP §2.4 (SATP:335-338)
    reads "the 'finalized' outcome of V" as fixed once set; used by
    `Adjudicator.reclaim`'s channel-types repair: a virtual channel's outcome, once finalized, is exactly
    what `reclaim` reads. -/
theorem finalizedWith_stable {apps : Apps E} {s s' : Adjudicator E}
    (h : Relation.ReflTransGen (Step apps) s s') {c : FixedPart} {f : Outcome E}
    (hf : s.finalizedWith c.address = some f) : s'.finalizedWith c.address = some f := by
  induction h with
  | refl => exact hf
  | tail _ hstep ih =>
    obtain ⟨_, _, _, _, happ⟩ := hstep
    exact finalizedWith_apply happ ih

/-- **The balances sum moves only by a deposit's own amount.** `deposit`
    raises it by `x` (`sumIf_set`, the indicator always true); `transfer`
    moves `x` from the source to the destination, net zero (`sumIf_add_sub`,
    the indicator always true, so both correction terms are `x`); every
    other operation leaves `balances` untouched (`reclaim_some`,
    `challenge_some`, `checkpoint_some`, `conclude_some`, `tick`'s own
    definition). D10 design decision, used by `held_paidOut_step` and the wallet
    conservation theorem (`Reachable.lean`). -/
theorem total_step_deposit {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {a : Address E} {e x : Coins} (hnd : s.balances.KeysNodup)
    (h : s.apply apps caller (Op.deposit a e x) = some s') :
    s'.balances.total = s.balances.total + x := by
  obtain ⟨-, -, hb, -, -, -⟩ := deposit_some h
  have hs := Balances.sumIf_set (fun _ => true) hnd a (s.balances.get a + x)
  rw [hb]
  simp only [Balances.add, Balances.total_eq_sumIf]
  (grind? says grind only)

/-- **The balances sum is unchanged by every on-chain operation except
    `deposit`.** `transfer` moves `x` from the source to the destination,
    net zero (`sumIf_add_sub`, the indicator always true, so both
    correction terms are `x`); `reclaim`, `challenge`, `checkpoint`,
    `conclude` and `tick` never write `balances` (`reclaim_some`,
    `challenge_some`, `checkpoint_some`, `conclude_some`, `tick`'s own
    definition). D10 design decision, used by `held_paidOut_step_no_deposit` and
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
    (simp? at hs says simp only [FixedPart.address_eq, ↓reduceIte, Nat.add_right_cancel_iff] at hs)
    rw [hb]
    (simp? [Balances.total_eq_sumIf] says simp only [FixedPart.address_eq, Balances.total_eq_sumIf])
    omega
  | reclaim l v => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h; (simp? says simp only [FixedPart.address_eq, setStatus_balances])
  | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; (simp? says simp only [setStatus_balances])
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; (simp? says simp only [setStatus_balances])
  | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; (simp? says simp only [setStatus_balances])
  | tick dt => (simp? at h says simp only [apply_tick, Option.some.injEq] at h); subst h; (simp? says simp only [tick_balances])

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
    · (simp? says simp only [ChannelStatus.finalOutcome_withOutcome])
    · rfl
  refine ⟨o, amt, x, hf, hfind, hk, hb, hx, hfo, fun d => ?_, fun d => ?_, fun d L hL => ?_⟩
  · rw [hbal, Balances.get_sub, Balances.get_add, Balances.get_add]
    split_ifs <;> simp_all
  · cases d with
    | external e => (simp? [dueTotal] says simp only [dueTotal, finalOutcome_external, FixedPart.address_eq, reduceCtorEq, ↓reduceIte, add_zero])
    | channel c =>
      have hc := hfo c
      simp only [FixedPart.address_eq] at hc hf
      by_cases hca : c = a
      · subst hca
        have h1 := Allocation.dedup_total_reduceOwed o b hxo
        simp only [dueTotal, hc, hf, FixedPart.address_eq, if_true]
        unfold Coins at *
        omega
      · (simp? [dueTotal, hc, hca] says simp only [dueTotal, hc, hca, ↓reduceIte, finalOutcome_channel, FixedPart.address_eq, Address.channel.injEq, add_zero])
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
  (simpa? [dueTotal] using h.flow (.external d) [] List.nodup_nil says simpa only [dueTotal, finalOutcome_external, add_zero, List.map_nil, List.sum_nil] using h.flow (.external d) [] List.nodup_nil)

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

/-- One transfer by the adversary alone, reverted or not, keeps `sg` ahead of `sp`. -/
theorem Ahead.transfer_right {sp sg : Adjudicator E} (h : sp.Ahead sg) (a : FixedPart)
    (b : Address E) : sp.Ahead ((sg.transfer a b).getD sg) := by
  rcases ht : sg.transfer a b with _ | sg'
  · exact h
  rw [Option.getD_some]
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
      have : (c.address : Address E) ≠ a.address := by (simpa? using hca says simpa only [FixedPart.address_eq, ne_eq, Address.channel.injEq] using hca)
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
    (simpa? using this says simpa only [FixedPart.address_eq, ge_iff_le, List.map_nil, List.sum_nil, add_zero] using this)
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
      have : (c.address : Address E) ≠ a.address := by (simpa? using hca says simpa only [FixedPart.address_eq, ne_eq, Address.channel.injEq] using hca)
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
    | none => exact absurd ((h.transfer_eq_none_iff a b).2 hg) (by (simp? [hp] says simp only [hp, reduceCtorEq, not_false_eq_true]))
    | some sg' => exact h.transfer_both hp hg

end Adjudicator

end ArmadaLean.Nitro
