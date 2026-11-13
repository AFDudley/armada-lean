/-
  Nitro protocol specification: the network of outcomes and the Turbo Value
  Algorithm (Nitro:818-835).
  See `Address.lean` for the source list. SATP and go-nitro have no value
  algorithm, so Nitro is the primary source for this file. The Nitro
  Lower-bound Value Algorithm (Nitro:1178-1255) reads Nitro's `claim`, which
  SATP and go-nitro replaced by `reclaim`; it is not modelled.

  DAG. "The network of outcomes is a DAG" means
  "no channel can reach itself by following edges": `Acyclic s.Edge`, with
  core Lean's `Relation.TransGen`. Nitro:796-799 chooses a topological
  ordering; a proof that needs one derives it as a lemma. No theorem type
  carries an ordering: the algorithm's result is the relation
  `Adjudicator.TurboValue`.
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.WellFoundedSet
import ArmadaLean.Nitro.Strategy
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- The stored allocation of a node, with duplicate destinations dropped
    (Nitro:744-746). A node with no finalized allocation has the empty
    allocation. -/
def Adjudicator.allocationOf (s : Adjudicator E) (n : Address E) : Allocation E :=
  match s.finalOutcome n with
  | some (.allocation o) => o.dedup
  | _ => []

/-- Nitro:790-792: "the nodes are channels and the edges represent allocations
    from one channel to the other." `edge n d`: `n`'s outcome allocates to
    channel `d`. -/
def Adjudicator.Edge (s : Adjudicator E) (n d : Address E) : Prop :=
  d.isExternal = false ∧ ∃ e ∈ s.allocationOf n, e.dest = d
/-- A relation with no cycle: no node reaches itself by one or more steps,
    `∀ c, ¬ Relation.TransGen edge c c`, stated
    as `Std.Irrefl` of the transitive closure (Mathlib `Relation.TransGen`,
    core `Std.Irrefl`). -/
def Acyclic {α : Type} (edge : α → α → Prop) : Prop :=
  Std.Irrefl (Relation.TransGen edge)

/-- Nitro:796-798: "A topological ordering is an ordering of nodes such that, if
    N1 ↦ N2 is an edge, then N1 < N2." Every node with a balance or an
    allocation appears once. -/
def Adjudicator.IsTopologicalOrder (s : Adjudicator E) (order : List (Address E)) : Prop :=
  order.Nodup ∧
  (∀ n d, s.Edge n d → ∃ i j : Nat, order[i]? = some n ∧ order[j]? = some d ∧ i < j) ∧
  (∀ n, (s.balances.get n ≠ 0 ∨ s.allocationOf n ≠ []) → n ∈ order)

/-- Nitro:790-795: "We will only consider the case where the network of
    outcomes forms a directed acyclic graph (DAG)". -/
def Adjudicator.IsDAG (s : Adjudicator E) : Prop :=
  Acyclic s.Edge

/-- A list that orders every edge of `s` forward rules out a cycle of `s`: along a path, the
    position in the list rises. So a topological order makes `s` a DAG. -/
theorem Adjudicator.IsTopologicalOrder.isDAG {s : Adjudicator E} {order : List (Address E)}
    (h : s.IsTopologicalOrder order) : s.IsDAG := by
  have hpos : ∀ {a b}, Relation.TransGen s.Edge a b →
      ∃ i j : Nat, order[i]? = some a ∧ order[j]? = some b ∧ i < j := by
    intro a b hab
    induction hab with
    | single he => exact h.2.1 _ _ he
    | tail _ he ih =>
      obtain ⟨i, j, hi, hj, hij⟩ := ih
      obtain ⟨j', k, hj', hk, hjk⟩ := h.2.1 _ _ he
      have := (List.getElem?_inj (List.getElem?_eq_some_iff.mp hj).1 h.1).mp (hj.trans hj'.symm)
      exact ⟨i, k, hi, hk, by omega⟩
  refine ⟨fun c hc => ?_⟩
  obtain ⟨i, j, hi, hj, hij⟩ := hpos hc
  have := (List.getElem?_inj (List.getElem?_eq_some_iff.mp hi).1 h.1).mp (hi.trans hj.symm)
  omega

/-- Nitro:824-834, step 3: pay `remaining` through one node's allocation in
    order; each destination's value rises by `min(payout, remaining)`. A
    guarantee item takes its place in the priority order but credits no
    one: `transfer` cannot pay a guarantee (go-nitro MultiAssetHolder.sol:169-170,
    "cannot transfer a guarantee"), and the Turbo game has no `reclaim`. -/
def payoutValues : Balances E → Coins → Allocation E → Balances E
  | vals, _, [] => vals
  | vals, remaining, e :: rest =>
    let x := min e.amount remaining
    payoutValues (if e.item.isGuarantee then vals else vals.add e.dest x) (remaining - x) rest

/-! ### Monotonicity of the Turbo Value Algorithm

    `turbo_value_upper_bound` needs: no sequence of real `transfer` calls, in
    the transfer-only game, can ever raise `turboValueAlong` at any address
    above its value at the start. Two facts drive this: `payoutValues_le`
    (the algorithm never reports less than its own starting balances) and
    `payoutValues_absorb` (one real `transfer` call, applied to the exact
    allocation the algorithm reads, is exactly one step of the algorithm's
    own computation: pre-paying it for real and lowering what the
    allocation still owes leaves the algorithm's eventual answer, at every
    address, unchanged). -/

theorem payoutValues_get_add_le (vals : Balances E) (d : Address E) (x : Coins) (n : Address E) :
    vals.get n ≤ (vals.add d x).get n := by
  rw [Balances.get_add]
  by_cases h : n = d
  · subst h
    rw [if_pos rfl]
    exact Nat.le_add_right _ _
  · (simp? [h] says simp only [h, ↓reduceIte, Std.le_refl])

/-- `payoutValues` never lowers any address's recorded value: every update
    it makes is an addition. -/
theorem payoutValues_le (o : Allocation E) (vals : Balances E) (remaining : Coins) (n : Address E) :
    vals.get n ≤ (payoutValues vals remaining o).get n := by
  induction o generalizing vals remaining with
  | nil => (simp? [payoutValues] says simp only [payoutValues, Std.le_refl])
  | cons e rest ih =>
    simp only [payoutValues]
    refine le_trans ?_ (ih _ _)
    split
    · exact le_refl _
    · exact payoutValues_get_add_le vals e.dest _ n

/-- `payoutValues` is congruent in its starting balances, pointwise. -/
theorem payoutValues_congr {vals1 vals2 : Balances E} (h : ∀ m, vals1.get m = vals2.get m)
    (remaining : Coins) (o : Allocation E) (n : Address E) :
    (payoutValues vals1 remaining o).get n = (payoutValues vals2 remaining o).get n := by
  induction o generalizing vals1 vals2 remaining with
  | nil => simp only [payoutValues]; exact h n
  | cons e rest ih =>
    simp only [payoutValues]
    apply ih
    intro m
    split
    · exact h m
    · (simp? [Balances.get_add, h] says simp only [Balances.get_add, h])

/-- Processing an allocation that never mentions `d` as a destination
    leaves `d`'s recorded value unchanged. -/
theorem payoutValues_get_of_not_mem {o : Allocation E} {d : Address E}
    (hd : d ∉ o.map Entry.dest) (vals : Balances E) (remaining : Coins) :
    (payoutValues vals remaining o).get d = vals.get d := by
  induction o generalizing vals remaining with
  | nil => (simp? [payoutValues] says simp only [payoutValues])
  | cons e rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hd
    simp only [payoutValues]
    rw [ih hd.2]
    split
    · rfl
    · rw [Balances.get_add, if_neg hd.1]

/-- One real `transfer`'s payout to a non-guarantee destination, absorbed
    into `vals`/`remaining` and lowered out of the allocation, is exactly
    one step of `payoutValues`'s own computation: a real on-chain transfer
    never does more, nor less, than the Turbo Value Algorithm's own
    priority formula already credits, so the algorithm's eventual answer,
    at every address, is unchanged by it. -/
theorem min_sub_of_le_sub_min (a b x : Nat) (hx : x ≤ b - min a b) :
    min a (b - x) = min a b := by omega

theorem sub_sub_swap (b x y : Nat) : b - x - y = b - y - x := by omega

theorem min_sub_min_eq_zero (a b : Nat) : min (a - min a b) (b - min a b) = 0 := by omega

theorem payoutValues_absorb {o : Allocation E} (hnd : (o.map Entry.dest).Nodup)
    {b : Address E} {amt : Coins} (hb : o.find b = some ⟨b, .alloc amt⟩)
    (vals : Balances E) (remaining : Coins) (n : Address E) :
    (payoutValues vals remaining o).get n =
      (payoutValues (vals.add b (Allocation.paidTo remaining o b))
        (remaining - Allocation.paidTo remaining o b)
        (Allocation.reduceOwed o b (Allocation.paidTo remaining o b))).get n := by
  induction o generalizing vals remaining with
  | nil => (simp? at hb says simp only [Allocation.find_nil, reduceCtorEq] at hb)
  | cons e rest ih =>
    rw [Allocation.find_cons] at hb
    have hnde : e.dest ∉ rest.map Entry.dest := (List.nodup_cons.1 hnd).1
    have hndr : (rest.map Entry.dest).Nodup := (List.nodup_cons.1 hnd).2
    have hdeq := Allocation.dedup_eq_self_of_nodup hnd
    by_cases he : e.dest = b
    · subst he
      rw [if_pos rfl] at hb
      have hee : e = (⟨e.dest, .alloc amt⟩ : Entry E) := by injection hb
      have heitem : e.item = Item.alloc amt := by rw [hee]
      have heamt : e.amount = amt := by (simp? [Entry.amount, heitem] says simp only [Entry.amount, heitem, Item.amount_alloc])
      have hx : Allocation.paidTo remaining (e :: rest) e.dest = min amt remaining := by
        rw [Allocation.paidTo_eq_get, hdeq]
        conv_lhs => rw [hee]
        (simp? [Allocation.payout_cons, Balances.get_cons] says simp only [Allocation.payout_cons, Entry.amount_mk, Item.amount_alloc, Balances.get_cons, ↓reduceIte])
      rw [hx]
      have hro : Allocation.reduceOwed (e :: rest) e.dest (min amt remaining) =
          ({ e with item := .alloc (amt - min amt remaining) } : Entry E) :: rest := by
        rw [Allocation.reduceOwed_cons, if_pos rfl]
        (simp? [Entry.amount, heitem] says simp only [Entry.amount, heitem, Item.amount_alloc])
      rw [hro]
      simp only [payoutValues]
      have hcond1 : ¬ e.item.isGuarantee = true := by rw [heitem]; (simp? [Item.isGuarantee] says simp only [Item.isGuarantee, Bool.false_eq_true, not_false_eq_true])
      have hcond2 : ¬ ({ e with item := .alloc (amt - min amt remaining) } : Entry E).item.isGuarantee = true := by
        (simp? [Item.isGuarantee] says simp only [Item.isGuarantee, Bool.false_eq_true, not_false_eq_true])
      have hmodamt : ({ e with item := .alloc (amt - min amt remaining) } : Entry E).amount
          = amt - min amt remaining := rfl
      rw [if_neg hcond1, if_neg hcond2, heamt, hmodamt]
      have hxnn : min (amt - min amt remaining) (remaining - min amt remaining) = 0 :=
        min_sub_min_eq_zero amt remaining
      rw [hxnn]
      simp only [Nat.sub_zero]
      apply payoutValues_congr
      intro m
      by_cases hm : m = e.dest
      · (simp? [hm, Balances.get_add] says simp only [hm, Balances.get_add, ↓reduceIte, add_zero, Nat.add_left_cancel_iff])
      · (simp? [hm, Balances.get_add] says simp only [Balances.get_add, hm, ↓reduceIte])
    · rw [if_neg he] at hb
      have hx : Allocation.paidTo remaining (e :: rest) b =
          Allocation.paidTo (remaining - min e.amount remaining) rest b := by
        conv_lhs => rw [Allocation.paidTo_eq_get, hdeq, Allocation.payout_cons, Balances.get_cons,
          if_neg (Ne.symm he)]
        rw [Allocation.paidTo_eq_get, Allocation.dedup_eq_self_of_nodup hndr]
      rw [hx]
      have hro : Allocation.reduceOwed (e :: rest) b
          (Allocation.paidTo (remaining - min e.amount remaining) rest b) =
          e :: Allocation.reduceOwed rest b
            (Allocation.paidTo (remaining - min e.amount remaining) rest b) := by
        rw [Allocation.reduceOwed_cons, if_neg he]
      rw [hro]
      simp only [payoutValues]
      have hxle : Allocation.paidTo (remaining - min e.amount remaining) rest b ≤
          remaining - min e.amount remaining :=
        Allocation.paidTo_le_held _ _ _
      have hmineq : min e.amount (remaining - Allocation.paidTo (remaining - min e.amount remaining) rest b)
          = min e.amount remaining := min_sub_of_le_sub_min _ _ _ hxle
      rw [hmineq]
      have hsub : remaining - Allocation.paidTo (remaining - min e.amount remaining) rest b -
          min e.amount remaining =
          remaining - min e.amount remaining - Allocation.paidTo (remaining - min e.amount remaining) rest b :=
        sub_sub_swap _ _ _
      rw [hsub]
      have hbridge : ∀ m,
          ((if e.item.isGuarantee then vals else vals.add e.dest (min e.amount remaining)).add b
              (Allocation.paidTo (remaining - min e.amount remaining) rest b)).get m
            = (if e.item.isGuarantee then vals.add b (Allocation.paidTo (remaining - min e.amount remaining) rest b)
                else (vals.add b (Allocation.paidTo (remaining - min e.amount remaining) rest b)).add e.dest
                  (min e.amount remaining)).get m := by
        intro m
        by_cases hg : e.item.isGuarantee = true
        · (simp? [hg] says simp only [hg, ↓reduceIte, Balances.get_add])
        · by_cases hmb : m = b
          · by_cases hme : m = e.dest
            · exact absurd (hme.symm.trans hmb) he
            · (simp_all? [Balances.get_add] says simp_all only [forall_const, List.map_cons, List.nodup_cons, not_false_eq_true, and_self, List.mem_map, not_exists, not_and, Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte, Balances.get_add, Nat.add_left_cancel_iff])
          · by_cases hme : m = e.dest
            · (simp_all? [Balances.get_add] says simp_all only [forall_const, List.map_cons, List.nodup_cons, not_false_eq_true, and_self, List.mem_map, not_exists, not_and, Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte, Balances.get_add, Nat.add_left_cancel_iff])
            · (simp_all? [Balances.get_add] says simp_all only [forall_const, List.map_cons, List.nodup_cons, not_false_eq_true, and_self, List.mem_map, not_exists, not_and, Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte, Balances.get_add])
      calc (payoutValues (if e.item.isGuarantee then vals else vals.add e.dest (min e.amount remaining))
                (remaining - min e.amount remaining) rest).get n
          = (payoutValues
              ((if e.item.isGuarantee then vals else vals.add e.dest (min e.amount remaining)).add b
                (Allocation.paidTo (remaining - min e.amount remaining) rest b))
              (remaining - min e.amount remaining - Allocation.paidTo (remaining - min e.amount remaining) rest b)
              (Allocation.reduceOwed rest b (Allocation.paidTo (remaining - min e.amount remaining) rest b))).get n :=
            ih hndr hb _ _
        _ = (payoutValues
              (if e.item.isGuarantee then vals.add b (Allocation.paidTo (remaining - min e.amount remaining) rest b)
                else (vals.add b (Allocation.paidTo (remaining - min e.amount remaining) rest b)).add e.dest
                  (min e.amount remaining))
              (remaining - min e.amount remaining - Allocation.paidTo (remaining - min e.amount remaining) rest b)
              (Allocation.reduceOwed rest b (Allocation.paidTo (remaining - min e.amount remaining) rest b))).get n :=
            payoutValues_congr hbridge _ _ n

/-- Two raises commute at every reading. -/
theorem Balances.get_add_add_comm (v : Balances E) (a b : Address E) (x y : Coins) (m : Address E) :
    ((v.add a x).add b y).get m = ((v.add b y).add a x).get m := by
  simp only [Balances.get_add]
  by_cases hma : m = a <;> by_cases hmb : m = b
  · have hba : b = a := hmb.symm.trans hma
    rw [if_pos hmb, if_pos hba, if_pos hma, if_pos hba.symm, hba]
    exact Nat.add_right_comm _ _ _
  · rw [if_neg hmb, if_pos hma, if_pos hma, if_neg (fun h => hmb (hma.trans h))]
  · rw [if_pos hmb, if_neg (fun h => hma (hmb.trans h)), if_neg hma, if_pos hmb]
  · rw [if_neg hmb, if_neg hma, if_neg hma, if_neg hmb]

/-- The `Nat` identity of `payoutValues_absorb_le` at the paid entry: a first
    payment `min amt held` out of a budget `held ≤ remaining`, then the entry's
    own turn, pay what the entry's turn alone pays, and leave the same rest. -/
theorem min_add_min_sub_of_le (amt held remaining : Nat) (h : held ≤ remaining) :
    min amt held + min (amt - min amt held) (remaining - min amt held) = min amt remaining ∧
      remaining - min amt held - min (amt - min amt held) (remaining - min amt held) =
        remaining - min amt remaining := by
  omega

/-- The `Nat` identity of `payoutValues_absorb_le` before the paid entry: a
    payment out of what `held` leaves after an earlier entry does not lower that
    entry's own share of `remaining ≥ held`, and the budgets stay ordered. -/
theorem min_sub_of_le_held_sub (a held remaining y : Nat) (h : held ≤ remaining)
    (hy : y + min a held ≤ held) :
    min a (remaining - y) = min a remaining ∧ held - min a held ≤ remaining - min a remaining := by
  omega

/-- `payoutValues_absorb` with the payment read from a budget `held ≤ remaining`.
    A real `transfer` pays what the channel's holding affords (`paidTo held`); the
    algorithm pays out the channel's value `remaining`, which is at least the
    holding. Paying the smaller amount for real and lowering what the allocation
    still owes leaves the algorithm's answer at every address unchanged. -/
theorem payoutValues_absorb_le {o : Allocation E} (hnd : (o.map Entry.dest).Nodup)
    {b : Address E} {amt : Coins} (hb : o.find b = some ⟨b, .alloc amt⟩)
    (vals : Balances E) {held remaining : Coins} (hle : held ≤ remaining) (n : Address E) :
    (payoutValues vals remaining o).get n =
      (payoutValues (vals.add b (Allocation.paidTo held o b))
        (remaining - Allocation.paidTo held o b)
        (Allocation.reduceOwed o b (Allocation.paidTo held o b))).get n := by
  induction o generalizing vals held remaining with
  | nil => cases hb
  | cons e rest ih =>
    rw [Allocation.find_cons] at hb
    have hndr : (rest.map Entry.dest).Nodup := (List.nodup_cons.1 hnd).2
    have hdeq := Allocation.dedup_eq_self_of_nodup hnd
    by_cases he : e.dest = b
    · subst he
      rw [if_pos rfl] at hb
      have hee : e = (⟨e.dest, .alloc amt⟩ : Entry E) := by injection hb
      have heitem : e.item = Item.alloc amt := by rw [hee]
      have heamt : e.amount = amt := by show e.item.amount = amt; rw [heitem]; rfl
      have hx : Allocation.paidTo held (e :: rest) e.dest = min amt held := by
        rw [Allocation.paidTo_eq_get, hdeq]
        conv_lhs => rw [hee]
        simp only [Allocation.payout_cons, Entry.amount_mk, Item.amount_alloc, Balances.get_cons,
          ↓reduceIte]
      rw [hx]
      have hro : Allocation.reduceOwed (e :: rest) e.dest (min amt held) =
          ({ e with item := .alloc (amt - min amt held) } : Entry E) :: rest := by
        rw [Allocation.reduceOwed_cons, if_pos rfl]
        simp only [Entry.amount, heitem, Item.amount_alloc]
      rw [hro]
      simp only [payoutValues]
      have hcond1 : ¬ e.item.isGuarantee = true := by rw [heitem]; exact Bool.false_ne_true
      have hcond2 :
          ¬ ({ e with item := .alloc (amt - min amt held) } : Entry E).item.isGuarantee = true := by
        exact Bool.false_ne_true
      have hmodamt : ({ e with item := .alloc (amt - min amt held) } : Entry E).amount
          = amt - min amt held := rfl
      rw [if_neg hcond1, if_neg hcond2, heamt, hmodamt]
      obtain ⟨hsum, hrem⟩ := min_add_min_sub_of_le amt held remaining hle
      rw [hrem]
      apply payoutValues_congr
      intro m
      by_cases hm : m = e.dest
      · rw [hm]
        simp only [Balances.get_add, if_true]
        rw [Nat.add_assoc, hsum]
      · simp only [Balances.get_add, hm, if_false]
    · rw [if_neg he] at hb
      have hx : Allocation.paidTo held (e :: rest) b =
          Allocation.paidTo (held - min e.amount held) rest b := by
        conv_lhs => rw [Allocation.paidTo_eq_get, hdeq, Allocation.payout_cons, Balances.get_cons,
          if_neg (Ne.symm he)]
        rw [Allocation.paidTo_eq_get, Allocation.dedup_eq_self_of_nodup hndr]
      rw [hx]
      obtain ⟨y, hy⟩ : ∃ y, y = Allocation.paidTo (held - min e.amount held) rest b := ⟨_, rfl⟩
      rw [← hy]
      have hro : Allocation.reduceOwed (e :: rest) b y = e :: Allocation.reduceOwed rest b y := by
        rw [Allocation.reduceOwed_cons, if_neg he]
      rw [hro]
      simp only [payoutValues]
      have hyle : y ≤ held - min e.amount held := hy ▸ Allocation.paidTo_le_held _ _ _
      obtain ⟨hmineq, hle'⟩ := min_sub_of_le_held_sub e.amount held remaining y hle
        (Nat.add_le_of_le_sub (Nat.min_le_right _ _) hyle)
      rw [hmineq, sub_sub_swap remaining y (min e.amount remaining)]
      have key := ih hndr hb
        (if e.item.isGuarantee then vals else vals.add e.dest (min e.amount remaining)) hle'
      rw [← hy] at key
      rw [key]
      apply payoutValues_congr
      intro m
      by_cases hg : e.item.isGuarantee = true
      · simp only [hg, if_true]
      · simp only [hg, Bool.false_eq_true, if_false]
        exact Balances.get_add_add_comm vals e.dest b _ _ m

/-- While `payoutValues` processes an allocation that names neither `a` nor
    `b`, starting balances that differ only by moving `x` from `a` to `b`
    (Nitro:765-772 `T(A,B,x)`, before `A`'s own turn in the algorithm) stay
    exactly that far apart at every address, and the bound `x ≤ vals.get a`
    (what makes the move affordable) persists: nothing here ever lowers
    `a`'s own recorded value (`payoutValues_le`). -/
theorem payoutValues_delta_step (a b : Address E) (hab : a ≠ b) :
    ∀ (o : Allocation E) (vals1 vals2 : Balances E) (x : Coins), x ≤ vals1.get a →
      (∀ m, m ≠ a → m ≠ b → vals1.get m = vals2.get m) →
      vals2.get a = vals1.get a - x → vals2.get b = vals1.get b + x →
      ∀ remaining : Coins,
        (∀ m, m ≠ a → m ≠ b →
          (payoutValues vals1 remaining o).get m = (payoutValues vals2 remaining o).get m) ∧
        x ≤ (payoutValues vals1 remaining o).get a ∧
        (payoutValues vals2 remaining o).get a = (payoutValues vals1 remaining o).get a - x ∧
        (payoutValues vals2 remaining o).get b = (payoutValues vals1 remaining o).get b + x := by
  intro o
  induction o with
  | nil => intro vals1 vals2 x hxle hagree ha hb remaining; exact ⟨hagree, hxle, ha, hb⟩
  | cons e rest ih =>
    intro vals1 vals2 x hxle hagree ha hb remaining
    simp only [payoutValues]
    by_cases hg : e.item.isGuarantee = true
    · simp only [hg, if_true]
      exact ih vals1 vals2 x hxle hagree ha hb (remaining - min e.amount remaining)
    · simp only [hg, if_false]
      have hxle' : x ≤ (vals1.add e.dest (min e.amount remaining)).get a := by
        rw [Balances.get_add]
        split
        · next h => rw [← h]; exact le_trans hxle (Nat.le_add_right _ _)
        · next h => exact hxle
      have hagree' : ∀ m, m ≠ a → m ≠ b →
          (vals1.add e.dest (min e.amount remaining)).get m
            = (vals2.add e.dest (min e.amount remaining)).get m := by
        intro m hma hmb
        simp only [Balances.get_add]
        split
        · next h => rw [hagree e.dest (h ▸ hma) (h ▸ hmb)]
        · next h => exact hagree m hma hmb
      have ha' : (vals2.add e.dest (min e.amount remaining)).get a
          = (vals1.add e.dest (min e.amount remaining)).get a - x := by
        simp only [Balances.get_add]
        split
        · next h => rw [← h, ha]; exact (Nat.sub_add_comm hxle).symm
        · next h => exact ha
      have hb' : (vals2.add e.dest (min e.amount remaining)).get b
          = (vals1.add e.dest (min e.amount remaining)).get b + x := by
        simp only [Balances.get_add]
        split
        · next h => rw [← h, hb]; exact add_right_comm _ _ _
        · next h => exact hb
      exact ih _ _ x hxle' hagree' ha' hb' (remaining - min e.amount remaining)


/-- Nitro:818-835 Turbo Value Algorithm, steps 2-3: start from the balances,
    then for each node in order pay its value through its allocation. -/
def Adjudicator.turboValues (s : Adjudicator E) : List (Address E) → Balances E → Balances E
  | [], vals => vals
  | n :: rest, vals => s.turboValues rest (payoutValues vals (vals.get n) (s.allocationOf n))

/-- Nitro:835 step 4: "Then Values[n] gives the value of node n." -/
def Adjudicator.turboValueAlong (s : Adjudicator E) (order : List (Address E)) (n : Address E) :
    Coins :=
  (s.turboValues order s.balances).get n

/-- Nitro:818-835: `x` is the Turbo Value Algorithm's value of `n` for some
    topological ordering (step 1). The ordering is chosen here, not in a
    theorem type. -/
def Adjudicator.TurboValue (s : Adjudicator E) (n : Address E) (x : Coins) : Prop :=
  ∃ order, s.IsTopologicalOrder order ∧ s.turboValueAlong order n = x

-- Piece 1: generic "exists source" lemma for a finite set under a transitive
-- irreflexive relation.
theorem exists_source {α : Type} (r : α → α → Prop) [IsTrans α r]
    (hirr : Std.Irrefl r) (s : Set α) (hfin : s.Finite) (hne : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, ¬ r b a := by
  have : IsStrictOrder α r := { toIrrefl := hirr, toIsTrans := inferInstance }
  have hwf : s.WellFoundedOn r := hfin.wellFoundedOn
  rw [Set.wellFoundedOn_iff] at hwf
  obtain ⟨a, ha, hmin⟩ := hwf.has_min s hne
  exact ⟨a, ha, fun b hb hrba => hmin b hb ⟨hrba, hb, ha⟩⟩

-- Piece 2: generic topological-sort existence for a finite list under an
-- acyclic relation.
theorem exists_topo_list {α : Type} [DecidableEq α] (Edge : α → α → Prop)
    (hdag : Std.Irrefl (Relation.TransGen Edge)) :
    ∀ n (W : List α), W.length = n → W.Nodup →
      ∃ order : List α, order.Nodup ∧ (∀ x, x ∈ order ↔ x ∈ W) ∧
        ∀ a b, a ∈ W → b ∈ W → Edge a b →
          ∃ i j : Nat, order[i]? = some a ∧ order[j]? = some b ∧ i < j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hlen hW
    rcases W with _ | ⟨w, ws⟩
    · exact ⟨[], List.nodup_nil, by (simp? says simp only [List.not_mem_nil, implies_true]), by (simp? says simp only [List.not_mem_nil, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq, false_and, and_self, exists_const, imp_false, IsEmpty.forall_iff, implies_true])⟩
    · obtain ⟨a, ha, hamin⟩ := exists_source (Relation.TransGen Edge) hdag
        {x | x ∈ (w :: ws)} (List.finite_toSet _) ⟨w, List.mem_cons_self⟩
      have hanp : ∀ b ∈ w :: ws, ¬ Edge b a := fun b hb hba =>
        hamin b hb (Relation.TransGen.single hba)
      obtain ⟨pre, post, hWeq, hapre⟩ := List.eq_append_cons_of_mem ha
      rw [hWeq] at hlen hW
      have hlen2 : (pre ++ a :: post).length = (pre ++ post).length + 1 := by
        simp only [List.length_append, List.length_cons]; omega
      have hlt : (pre ++ post).length < n := by omega
      rw [List.nodup_append] at hW
      obtain ⟨hpre_nd, hapost_nd, hdisj⟩ := hW
      rw [List.nodup_cons] at hapost_nd
      obtain ⟨ha_notin_post, hpost_nd⟩ := hapost_nd
      have hW' : (pre ++ post).Nodup :=
        List.nodup_append.mpr ⟨hpre_nd, hpost_nd,
          fun x hx y hy => hdisj x hx y (List.mem_cons_of_mem _ hy)⟩
      obtain ⟨order', hnd', hmem', hedge'⟩ := ih (pre ++ post).length hlt (pre ++ post) rfl hW'
      have hmemW : ∀ x, x ∈ pre ++ post ↔ (x ∈ w :: ws ∧ x ≠ a) := by
        intro x
        rw [hWeq, List.mem_append, List.mem_append, List.mem_cons]
        constructor
        · rintro (hx | hx)
          · exact ⟨Or.inl hx, fun h => hapre (h ▸ hx)⟩
          · exact ⟨Or.inr (Or.inr hx), fun h => ha_notin_post (h ▸ hx)⟩
        · rintro ⟨hx | hx | hx, hne⟩
          · exact Or.inl hx
          · exact absurd hx hne
          · exact Or.inr hx
      have ha_notin_order' : a ∉ order' := fun h => ((hmemW a).mp ((hmem' a).mp h)).2 rfl
      refine ⟨a :: order', List.nodup_cons.mpr ⟨ha_notin_order', hnd'⟩, ?_, ?_⟩
      · intro x
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hx)
          · exact ha
          · exact ((hmemW x).mp ((hmem' x).mp hx)).1
        · intro hx
          by_cases hxa : x = a
          · exact Or.inl hxa
          · exact Or.inr ((hmem' x).mpr ((hmemW x).mpr ⟨hx, hxa⟩))
      · intro x y hx hy hxy
        by_cases hya : y = a
        · subst hya
          exact absurd hxy (hanp x hx)
        · by_cases hxa : x = a
          · subst hxa
            have hyW' : y ∈ order' := (hmem' y).mpr ((hmemW y).mpr ⟨hy, hya⟩)
            obtain ⟨j, hj⟩ := List.getElem?_of_mem hyW'
            exact ⟨0, j + 1, List.getElem?_cons_zero, by (simpa? using hj says simpa only [List.getElem?_cons_succ] using hj), by omega⟩
          · have hxW' : x ∈ order' := (hmem' x).mpr ((hmemW x).mpr ⟨hx, hxa⟩)
            have hyW' : y ∈ order' := (hmem' y).mpr ((hmemW y).mpr ⟨hy, hya⟩)
            have hxpp : x ∈ pre ++ post := (hmemW x).mpr ⟨hx, hxa⟩
            have hypp : y ∈ pre ++ post := (hmemW y).mpr ⟨hy, hya⟩
            obtain ⟨i, j, hi, hj, hij⟩ := hedge' x y hxpp hypp hxy
            exact ⟨i + 1, j + 1, by (simpa? using hi says simpa only [List.getElem?_cons_succ] using hi), by (simpa? using hj says simpa only [List.getElem?_cons_succ] using hj), by omega⟩

-- Piece 3: concrete finite node list covering every node that MUST appear
-- in a topological order of `s`.
def requiredNodes (s : Adjudicator E) : List (Address E) :=
  (s.balances.map Prod.fst) ++ (s.status.map (fun p => (p.1.address : Address E))) ++
    (s.status.flatMap (fun p => (s.allocationOf p.1.address).map Entry.dest))

theorem channel_active_mem_status (s : Adjudicator E) (c : FixedPart)
    (h : s.allocationOf (c.address : Address E) ≠ []) :
    ∃ st, (c, st) ∈ s.status ∧ s.statusOf c = st := by
  unfold Adjudicator.allocationOf at h
  rw [FixedPart.address_eq, Adjudicator.finalOutcome] at h
  cases hlk : s.status.lookup c with
  | none =>
    exact absurd (by unfold Adjudicator.statusOf; rw [hlk]; rfl) h
  | some st =>
    have hmem : (c, st) ∈ s.status := List.lookup_eq_some_iff.mp hlk |>.elim
      (fun l1 h' => h'.elim (fun l2 ⟨heq, _⟩ => heq ▸ by (simp? says simp only [List.mem_append, List.mem_cons, true_or, or_true])))
    exact ⟨st, hmem, by unfold Adjudicator.statusOf; rw [hlk]; rfl⟩

theorem active_mem_requiredNodes (s : Adjudicator E) (n : Address E)
    (h : s.balances.get n ≠ 0 ∨ s.allocationOf n ≠ []) : n ∈ requiredNodes s := by
  unfold requiredNodes
  rcases h with h | h
  · refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
    unfold Balances.get at h
    cases hlk : s.balances.lookup n with
    | none => (simp? [hlk] at h says simp only [hlk, Option.getD_none, ne_eq, not_true_eq_false] at h)
    | some v =>
      have hmem : (n, v) ∈ s.balances := List.lookup_eq_some_iff.mp hlk |>.elim
        (fun l1 h' => h'.elim (fun l2 ⟨heq, _⟩ => heq ▸ by (simp? says simp only [List.mem_append, List.mem_cons, true_or, or_true])))
      exact List.mem_map.mpr ⟨(n, v), hmem, rfl⟩
  · obtain ⟨c, hceq⟩ : ∃ c : FixedPart, n = c.address := by
      cases n with
      | external d => (simp? [Adjudicator.allocationOf, Adjudicator.finalOutcome] at h says simp only [Adjudicator.allocationOf, Adjudicator.finalOutcome, ne_eq, not_true_eq_false] at h)
      | channel c => exact ⟨c, rfl⟩
    subst hceq
    obtain ⟨st, hmemstatus, -⟩ := channel_active_mem_status s c h
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
    exact List.mem_map.mpr ⟨(c, st), hmemstatus, rfl⟩

theorem edge_mem_requiredNodes (s : Adjudicator E) (n d : Address E) (h : s.Edge n d) :
    n ∈ requiredNodes s ∧ d ∈ requiredNodes s := by
  obtain ⟨hdext, e, he, hed⟩ := h
  have hnactive : s.allocationOf n ≠ [] := fun hemp => by rw [hemp] at he; exact (List.not_mem_nil he)
  refine ⟨active_mem_requiredNodes s n (Or.inr hnactive), ?_⟩
  obtain ⟨c, hceq⟩ : ∃ c : FixedPart, n = c.address := by
    cases n with
    | external dd => (simp? [Adjudicator.allocationOf, Adjudicator.finalOutcome] at hnactive says simp only [Adjudicator.allocationOf, Adjudicator.finalOutcome, ne_eq, not_true_eq_false] at hnactive)
    | channel c => exact ⟨c, rfl⟩
  subst hceq
  obtain ⟨st, hmemstatus, -⟩ := channel_active_mem_status s c hnactive
  unfold requiredNodes
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(c, st), hmemstatus, ?_⟩
  rw [← hed]
  exact List.mem_map.mpr ⟨e, he, rfl⟩


theorem exists_valid_topo_order (s : Adjudicator E) (hdag : s.IsDAG) :
    ∃ order : List (Address E), s.IsTopologicalOrder order := by
  obtain ⟨order, hnd, hmem, hedge⟩ :=
    exists_topo_list s.Edge hdag (requiredNodes s).dedup.length (requiredNodes s).dedup rfl
      (List.nodup_dedup _)
  refine ⟨order, hnd, ?_, ?_⟩
  · intro n d hed
    obtain ⟨hn, hdreq⟩ := edge_mem_requiredNodes s n d hed
    have hn' : n ∈ (requiredNodes s).dedup := List.mem_dedup.mpr hn
    have hd' : d ∈ (requiredNodes s).dedup := List.mem_dedup.mpr hdreq
    exact hedge n d hn' hd' hed
  · intro n h
    exact (hmem n).mpr (List.mem_dedup.mpr (active_mem_requiredNodes s n h))

-- Piece 4a: payoutValues doesn't touch addresses that aren't any entry's
-- destination.
theorem payoutValues_get_ne (vals : Balances E) (remaining : Coins) (alloc : Allocation E)
    (a : Address E) (h : ∀ e ∈ alloc, e.dest ≠ a) :
    (payoutValues vals remaining alloc).get a = vals.get a := by
  induction alloc generalizing vals remaining with
  | nil => rfl
  | cons e rest ih =>
    have hne : e.dest ≠ a := h e (List.mem_cons_self)
    have hrest : ∀ e' ∈ rest, e'.dest ≠ a := fun e' he' => h e' (List.mem_cons_of_mem _ he')
    unfold payoutValues
    rw [ih _ _ hrest]
    by_cases hg : e.item.isGuarantee
    · (simp? [hg] says simp only [hg, ↓reduceIte])
    · (simp? [hg, Balances.get_add, Ne.symm hne] says simp only [hg, Bool.false_eq_true, ↓reduceIte, Balances.get_add, Ne.symm hne])

-- Index utilities: an explicit split gives a direct index witness, and
-- Nodup makes that witness the unique one `hvalid`-style existentials
-- must agree with.
theorem getElem?_append_cons_right {α : Type} (l1 : List α) (x : α) (l2 : List α) :
    (l1 ++ x :: l2)[l1.length]? = some x := by
  induction l1 with
  | nil => rfl
  | cons h t ih => (simp? says simp only [List.cons_append, List.length_cons, List.length_append, add_lt_add_iff_right, lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true, getElem?_pos, List.getElem_cons_succ, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero])

theorem not_edge_of_before_split {α : Type} [DecidableEq α] (Edge : α → α → Prop)
    (l : List α) (hnd : l.Nodup)
    (hvalid : ∀ m d, m ∈ l → d ∈ l → Edge m d →
      ∃ i j : Nat, l[i]? = some m ∧ l[j]? = some d ∧ i < j)
    (pre1 pre2 post : List α) (a p : α) (heq : l = pre1 ++ p :: (pre2 ++ a :: post)) :
    ¬ Edge a p := by
  intro hep
  have hpmem : p ∈ l := heq ▸ (List.mem_append.mpr (Or.inr List.mem_cons_self))
  have hamem : a ∈ l := heq ▸ (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem p
    (List.mem_append.mpr (Or.inr List.mem_cons_self)))))
  obtain ⟨i, j, hi, hj, hij⟩ := hvalid a p hamem hpmem hep
  have hp_idx : l[pre1.length]? = some p := heq ▸ getElem?_append_cons_right pre1 p (pre2 ++ a :: post)
  have ha_idx : l[pre1.length + 1 + pre2.length]? = some a := by
    have hraw := getElem?_append_cons_right (pre1 ++ p :: pre2) a post
    rw [List.append_assoc, List.cons_append] at hraw
    rw [heq, show pre1.length + 1 + pre2.length = (pre1 ++ p :: pre2).length from by
      (simp? [List.length_append, List.length_cons] says simp only [List.length_append, List.length_cons]); omega]
    exact hraw
  have hilt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjlt : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hieq : i = pre1.length + 1 + pre2.length :=
    (List.getElem?_inj hilt hnd).mp (hi.trans ha_idx.symm)
  have hjeq : j = pre1.length := (List.getElem?_inj hjlt hnd).mp (hj.trans hp_idx.symm)
  omega

-- Piece 4b: payoutValues depends on `vals` only through `.get` (not list
-- structure), and is "affine": its effect on `.get q` is a `vals`-independent
-- increment.
theorem payoutValues_get_congr (vals1 vals2 : Balances E) (r : Coins) (alloc : Allocation E)
    (h : ∀ q, vals1.get q = vals2.get q) (q : Address E) :
    (payoutValues vals1 r alloc).get q = (payoutValues vals2 r alloc).get q := by
  induction alloc generalizing vals1 vals2 r with
  | nil => exact h q
  | cons e rest ih =>
    simp only [payoutValues]
    by_cases hg : e.item.isGuarantee
    · rw [if_pos hg, if_pos hg]
      exact ih vals1 vals2 _ h
    · rw [if_neg hg, if_neg hg]
      refine ih _ _ _ (fun q' => ?_)
      simp only [Balances.get_add, h]

theorem payoutValues_get_eq (vals : Balances E) (r : Coins) (alloc : Allocation E)
    (q : Address E) :
    (payoutValues vals r alloc).get q = vals.get q + (payoutValues [] r alloc).get q := by
  induction alloc generalizing vals r with
  | nil => rfl
  | cons e rest ih =>
    simp only [payoutValues]
    by_cases hg : e.item.isGuarantee
    · rw [if_pos hg, if_pos hg]
      exact ih vals _
    · rw [if_neg hg, if_neg hg]
      rw [ih (vals.add e.dest (min e.amount r)) _, ih (Balances.add [] e.dest (min e.amount r)) _,
        Balances.get_add, Balances.get_add]
      simp only [Balances.get_nil]
      split_ifs with hqe
      · subst hqe; rw [Nat.add_assoc]; (simp? says simp only [zero_add, Nat.add_left_cancel_iff])
      · (simp? says simp only [zero_add, Nat.add_left_cancel_iff])

theorem payoutValues_comm (vals : Balances E) (r1 : Coins) (alloc1 : Allocation E)
    (r2 : Coins) (alloc2 : Allocation E) (q : Address E) :
    (payoutValues (payoutValues vals r1 alloc1) r2 alloc2).get q =
      (payoutValues (payoutValues vals r2 alloc2) r1 alloc1).get q := by
  rw [payoutValues_get_eq (payoutValues vals r1 alloc1) r2 alloc2 q, payoutValues_get_eq vals r1 alloc1 q,
    payoutValues_get_eq (payoutValues vals r2 alloc2) r1 alloc1 q, payoutValues_get_eq vals r2 alloc2 q]
  exact Nat.add_right_comm _ _ _

-- Piece 4c: turboValues depends on `vals` only through `.get` (not list
-- structure).
theorem turboValues_get_congr (s : Adjudicator E) (order : List (Address E))
    (vals1 vals2 : Balances E) (h : ∀ q, vals1.get q = vals2.get q) (n : Address E) :
    (s.turboValues order vals1).get n = (s.turboValues order vals2).get n := by
  induction order generalizing vals1 vals2 with
  | nil => exact h n
  | cons x rest ih =>
    unfold Adjudicator.turboValues
    apply ih
    intro q
    rw [h x]
    exact payoutValues_get_congr vals1 vals2 (vals2.get x) (s.allocationOf x) h q

-- Piece 4d: processing a node with empty allocation is a no-op, so
-- `turboValues` only depends on the subsequence of nodes with a nonempty
-- own allocation.
theorem turboValues_filter_activeAlloc (s : Adjudicator E) (order : List (Address E))
    (vals : Balances E) :
    s.turboValues order vals =
      s.turboValues (order.filter (fun x => !(s.allocationOf x).isEmpty)) vals := by
  induction order generalizing vals with
  | nil => rfl
  | cons x rest ih =>
    by_cases hx : (s.allocationOf x).isEmpty
    · have hxnil : s.allocationOf x = [] := List.isEmpty_iff.mp hx
      rw [List.filter_cons_of_neg (by (simp? [hx] says simp only [hx, Bool.not_true, Bool.false_eq_true, not_false_eq_true]))]
      simp only [Adjudicator.turboValues, hxnil, payoutValues]
      exact ih vals
    · rw [List.filter_cons_of_pos (by (simp? [hx] says simp only [hx, Bool.not_false]))]
      simp only [Adjudicator.turboValues]
      exact ih _

-- Piece 4e: a node with no incoming AND no outgoing edge to the rest of the
-- processing list can be moved to the very front without changing the
-- result, since its own reading is untouched by anyone and its payout
-- doesn't touch anyone it's moved past.
theorem turboValues_move_source_front (s : Adjudicator E) (a : Address E)
    (pre post : List (Address E)) (vals : Balances E)
    (hext : ∀ x, x = a ∨ x ∈ pre ∨ x ∈ post → x.isExternal = false)
    (hsrc : ∀ m ∈ pre ++ post, ¬ s.Edge m a)
    (hnoout : ∀ p ∈ pre, ¬ s.Edge a p) (n : Address E) :
    (s.turboValues (pre ++ a :: post) vals).get n =
      (s.turboValues (a :: (pre ++ post)) vals).get n := by
  induction pre generalizing vals with
  | nil => rfl
  | cons p pre' ih =>
    have hp_ext : p.isExternal = false := hext p (Or.inr (Or.inl List.mem_cons_self))
    have ha_ext : a.isExternal = false := hext a (Or.inl rfl)
    have hp_nosrc : ¬ s.Edge p a := hsrc p (List.mem_append.mpr (Or.inl List.mem_cons_self))
    have hp_noout : ¬ s.Edge a p := hnoout p List.mem_cons_self
    have hdest_pa : ∀ e ∈ s.allocationOf p, e.dest ≠ a := fun e he hcontra =>
      hp_nosrc ⟨ha_ext, e, he, hcontra⟩
    have hdest_ap : ∀ e ∈ s.allocationOf a, e.dest ≠ p := fun e he hcontra =>
      hp_noout ⟨hp_ext, e, he, hcontra⟩
    have hsrc' : ∀ m ∈ pre' ++ post, ¬ s.Edge m a := fun m hm =>
      hsrc m (List.mem_append.mpr (by
        rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl (List.mem_cons_of_mem _ hm)
        · exact Or.inr hm))
    have hnoout' : ∀ q ∈ pre', ¬ s.Edge a q := fun q hq => hnoout q (List.mem_cons_of_mem _ hq)
    have hext' : ∀ x, x = a ∨ x ∈ pre' ∨ x ∈ post → x.isExternal = false := fun x hx =>
      hext x (by
        rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hx))
        · exact Or.inr (Or.inr hx))
    have e1 : (payoutValues vals (vals.get p) (s.allocationOf p)).get a = vals.get a :=
      payoutValues_get_ne vals (vals.get p) (s.allocationOf p) a hdest_pa
    have e2 : (payoutValues vals (vals.get a) (s.allocationOf a)).get p = vals.get p :=
      payoutValues_get_ne vals (vals.get a) (s.allocationOf a) p hdest_ap
    have hcomm : ∀ q, (payoutValues (payoutValues vals (vals.get p) (s.allocationOf p))
          (vals.get a) (s.allocationOf a)).get q =
        (payoutValues (payoutValues vals (vals.get a) (s.allocationOf a))
          (vals.get p) (s.allocationOf p)).get q :=
      fun q => payoutValues_comm vals (vals.get p) (s.allocationOf p) (vals.get a)
        (s.allocationOf a) q
    simp only [List.cons_append, Adjudicator.turboValues]
    rw [ih (payoutValues vals (vals.get p) (s.allocationOf p)) hext' hsrc' hnoout']
    simp only [Adjudicator.turboValues]
    rw [e1, e2]
    exact turboValues_get_congr s (pre' ++ post) _ _ hcomm n






-- Piece 4f: removing one non-endpoint element from a Nodup list preserves
-- the relative "before" order of every surviving pair.
theorem before_remove_mid {α : Type} {l pre post : List α} {a m d : α} (heq : l = pre ++ a :: post)
    (_hnd : l.Nodup) {im id : Nat} (him : l[im]? = some m) (hid : l[id]? = some d) (hij : im < id)
    (hma : m ≠ a) (hda : d ≠ a) :
    ∃ i j : Nat, (pre ++ post)[i]? = some m ∧ (pre ++ post)[j]? = some d ∧ i < j := by
  have hia : l[pre.length]? = some a := heq ▸ getElem?_append_cons_right pre a post
  have hima : im ≠ pre.length := by
    intro h; rw [h] at him; rw [hia] at him; exact hma (Option.some.inj him).symm
  have hida : id ≠ pre.length := by
    intro h; rw [h] at hid; rw [hia] at hid; exact hda (Option.some.inj hid).symm
  have key : ∀ i : Nat, i ≠ pre.length → l[i]? = (pre ++ post)[(if i < pre.length then i else i - 1)]? := by
    intro i hine
    rcases Nat.lt_or_ge i pre.length with hlt | hge
    · rw [if_pos hlt, heq, List.getElem?_append_left hlt, List.getElem?_append_left hlt]
    · have hgt : pre.length < i := lt_of_le_of_ne hge (Ne.symm hine)
      obtain ⟨k, hk⟩ : ∃ k, i = pre.length + 1 + k := ⟨i - pre.length - 1, by omega⟩
      rw [if_neg (Nat.not_lt.mpr hge), heq, hk]
      rw [show pre.length + 1 + k - 1 = pre.length + k from by omega]
      rw [List.getElem?_append_right (show pre.length ≤ pre.length + 1 + k from by omega)]
      rw [List.getElem?_append_right (show pre.length ≤ pre.length + k from by omega)]
      rw [show pre.length + 1 + k - pre.length = k + 1 from by omega,
        show pre.length + k - pre.length = k from by omega]
      exact List.getElem?_cons_succ
  refine ⟨if im < pre.length then im else im - 1, if id < pre.length then id else id - 1,
    (key im hima) ▸ him, (key id hida) ▸ hid, ?_⟩
  by_cases h1 : im < pre.length <;> by_cases h2 : id < pre.length <;> (simp? [h1, h2] says simp only [h1, ↓reduceIte, h2]) <;> omega

-- Piece 4g: the main order-independence theorem. Any two Nodup lists with
-- the same elements, each respecting `s.Edge`'s before-order, give the same
-- `turboValues` result.
theorem turboValues_order_indep (s : Adjudicator E) (hdag : s.IsDAG) :
    ∀ (n : Nat) (L1 : List (Address E)), L1.length = n → L1.Nodup →
    ∀ (L2 : List (Address E)), L2.Nodup → (∀ x, x ∈ L1 ↔ x ∈ L2) →
    (∀ x ∈ L1, x.isExternal = false) →
    (∀ m d, m ∈ L1 → d ∈ L1 → s.Edge m d →
      ∃ i j : Nat, L1[i]? = some m ∧ L1[j]? = some d ∧ i < j) →
    (∀ m d, m ∈ L2 → d ∈ L2 → s.Edge m d →
      ∃ i j : Nat, L2[i]? = some m ∧ L2[j]? = some d ∧ i < j) →
    ∀ (vals : Balances E) (n' : Address E),
      (s.turboValues L1 vals).get n' = (s.turboValues L2 vals).get n' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L1 hlen hnd1 L2 hnd2 hmem hext hvalid1 hvalid2 vals n'
    rcases L1 with _ | ⟨w, ws⟩
    · have hL2nil : L2 = [] := by
        cases L2 with
        | nil => rfl
        | cons y ys => exact absurd ((hmem y).mpr List.mem_cons_self) (by (simp? says simp only [List.not_mem_nil, not_false_eq_true]))
      rw [hL2nil]
    · obtain ⟨a, ha, hamin⟩ := exists_source (Relation.TransGen s.Edge) hdag
        {x | x ∈ (w :: ws)} (List.finite_toSet _) ⟨w, List.mem_cons_self⟩
      have ha2 : a ∈ L2 := (hmem a).mp ha
      obtain ⟨pre1, post1, heq1, hapre1⟩ := List.eq_append_cons_of_mem ha
      obtain ⟨pre2, post2, heq2, hapre2⟩ := List.eq_append_cons_of_mem ha2
      -- Membership facts: `x ∈ preI ++ postI ↔ x ∈ LI ∧ x ≠ a`.
      have hmemW1 : ∀ x, x ∈ pre1 ++ post1 ↔ (x ∈ w :: ws ∧ x ≠ a) := by
        intro x
        rw [heq1, List.mem_append, List.mem_append, List.mem_cons]
        constructor
        · rintro (hx | hx)
          · exact ⟨Or.inl hx, fun h => hapre1 (h ▸ hx)⟩
          · refine ⟨Or.inr (Or.inr hx), fun h => ?_⟩
            have hnd' := hnd1
            rw [heq1, List.nodup_append, List.nodup_cons] at hnd'
            exact hnd'.2.1.1 (h ▸ hx)
        · rintro ⟨hx | hx | hx, hne⟩
          · exact Or.inl hx
          · exact absurd hx hne
          · exact Or.inr hx
      have hmemW2 : ∀ x, x ∈ pre2 ++ post2 ↔ (x ∈ L2 ∧ x ≠ a) := by
        intro x
        rw [heq2, List.mem_append, List.mem_append, List.mem_cons]
        constructor
        · rintro (hx | hx)
          · exact ⟨Or.inl hx, fun h => hapre2 (h ▸ hx)⟩
          · refine ⟨Or.inr (Or.inr hx), fun h => ?_⟩
            have hnd' := hnd2
            rw [heq2, List.nodup_append, List.nodup_cons] at hnd'
            exact hnd'.2.1.1 (h ▸ hx)
        · rintro ⟨hx | hx | hx, hne⟩
          · exact Or.inl hx
          · exact absurd hx hne
          · exact Or.inr hx
      -- `a` has no predecessor in either list (same membership).
      have hsrc1 : ∀ m ∈ pre1 ++ post1, ¬ s.Edge m a := fun m hm hedge =>
        hamin m ((hmemW1 m).mp hm).1 (Relation.TransGen.single hedge)
      have hsrc2 : ∀ m ∈ pre2 ++ post2, ¬ s.Edge m a := fun m hm hedge =>
        hamin m (hmem m |>.mpr ((hmemW2 m).mp hm).1) (Relation.TransGen.single hedge)
      -- `a` has no edge to any predecessor-position element of either list
      -- (else the hypothesis order would be violated).
      have hnoout1 : ∀ p ∈ pre1, ¬ s.Edge a p := by
        intro p hp
        obtain ⟨prepre, postpre, hpeq, -⟩ := List.eq_append_cons_of_mem hp
        refine not_edge_of_before_split s.Edge (w :: ws) hnd1 hvalid1 prepre postpre post1 a p ?_
        rw [heq1, hpeq]; (simp? [List.append_assoc] says simp only [List.append_assoc, List.cons_append])
      have hnoout2 : ∀ p ∈ pre2, ¬ s.Edge a p := by
        intro p hp
        obtain ⟨prepre, postpre, hpeq, -⟩ := List.eq_append_cons_of_mem hp
        refine not_edge_of_before_split s.Edge L2 hnd2 hvalid2 prepre postpre post2 a p ?_
        rw [heq2, hpeq]; (simp? [List.append_assoc] says simp only [List.append_assoc, List.cons_append])
      have hext1 : ∀ x, x = a ∨ x ∈ pre1 ∨ x ∈ post1 → x.isExternal = false := by
        intro x hx
        apply hext
        rw [heq1]
        rcases hx with hx | hx | hx
        · exact hx ▸ List.mem_append.mpr (Or.inr List.mem_cons_self)
        · exact List.mem_append.mpr (Or.inl hx)
        · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))
      have hext2 : ∀ x, x = a ∨ x ∈ pre2 ∨ x ∈ post2 → x.isExternal = false := by
        intro x hx
        apply hext
        apply (hmem x).mpr
        rw [heq2]
        rcases hx with hx | hx | hx
        · exact hx ▸ List.mem_append.mpr (Or.inr List.mem_cons_self)
        · exact List.mem_append.mpr (Or.inl hx)
        · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))
      have hmove1 := turboValues_move_source_front s a pre1 post1 vals hext1 hsrc1 hnoout1 n'
      have hmove2 := turboValues_move_source_front s a pre2 post2 vals hext2 hsrc2 hnoout2 n'
      rw [← heq1] at hmove1
      rw [← heq2] at hmove2
      rw [hmove1, hmove2]
      simp only [Adjudicator.turboValues]
      -- Reduce to the smaller lists via the induction hypothesis.
      have hnd1' : (pre1 ++ post1).Nodup := by
        have hnd' := hnd1
        rw [heq1, List.nodup_append, List.nodup_cons] at hnd'
        exact List.nodup_append.mpr ⟨hnd'.1, hnd'.2.1.2, fun x hx y hy => hnd'.2.2 x hx y (List.mem_cons_of_mem _ hy)⟩
      have hnd2' : (pre2 ++ post2).Nodup := by
        have hnd' := hnd2
        rw [heq2, List.nodup_append, List.nodup_cons] at hnd'
        exact List.nodup_append.mpr ⟨hnd'.1, hnd'.2.1.2, fun x hx y hy => hnd'.2.2 x hx y (List.mem_cons_of_mem _ hy)⟩
      have hmem' : ∀ x, x ∈ pre1 ++ post1 ↔ x ∈ pre2 ++ post2 := by
        intro x
        rw [hmemW1, hmemW2]
        constructor
        · rintro ⟨hx, hne⟩; exact ⟨(hmem x).mp hx, hne⟩
        · rintro ⟨hx, hne⟩; exact ⟨(hmem x).mpr hx, hne⟩
      have hvalid1' : ∀ m d, m ∈ pre1 ++ post1 → d ∈ pre1 ++ post1 → s.Edge m d →
          ∃ i j : Nat, (pre1 ++ post1)[i]? = some m ∧ (pre1 ++ post1)[j]? = some d ∧ i < j := by
        intro m d hm hd hedge
        have hmL : m ∈ w :: ws := ((hmemW1 m).mp hm).1
        have hdL : d ∈ w :: ws := ((hmemW1 d).mp hd).1
        obtain ⟨i, j, hi, hj, hij⟩ := hvalid1 m d hmL hdL hedge
        exact before_remove_mid heq1 hnd1 hi hj hij ((hmemW1 m).mp hm).2 ((hmemW1 d).mp hd).2
      have hvalid2' : ∀ m d, m ∈ pre2 ++ post2 → d ∈ pre2 ++ post2 → s.Edge m d →
          ∃ i j : Nat, (pre2 ++ post2)[i]? = some m ∧ (pre2 ++ post2)[j]? = some d ∧ i < j := by
        intro m d hm hd hedge
        have hmL : m ∈ L2 := ((hmemW2 m).mp hm).1
        have hdL : d ∈ L2 := ((hmemW2 d).mp hd).1
        obtain ⟨i, j, hi, hj, hij⟩ := hvalid2 m d hmL hdL hedge
        exact before_remove_mid heq2 hnd2 hi hj hij ((hmemW2 m).mp hm).2 ((hmemW2 d).mp hd).2
      have hlt : (pre1 ++ post1).length < n := by
        have h1 : (pre1 ++ a :: post1).length = (pre1 ++ post1).length + 1 := by
          (simp? [List.length_append, List.length_cons] says simp only [List.length_append, List.length_cons]); omega
        have h2 : (w :: ws).length = n := hlen
        rw [heq1] at h2
        omega
      have hext1' : ∀ x ∈ pre1 ++ post1, x.isExternal = false := fun x hx =>
        hext x ((hmemW1 x).mp hx).1
      exact ih (pre1 ++ post1).length hlt (pre1 ++ post1) rfl hnd1' (pre2 ++ post2) hnd2' hmem'
        hext1' hvalid1' hvalid2' (payoutValues vals (vals.get a) (s.allocationOf a)) n'

-- Piece 4h: filtering a Nodup list preserves the relative "before" order of
-- every pair of elements that both survive the filter.
theorem before_filter {α : Type} [DecidableEq α] {l : List α} (hnd : l.Nodup) (P : α → Bool)
    {m d : α} {i j : Nat} (hi : l[i]? = some m) (hj : l[j]? = some d) (hij : i < j)
    (hPm : P m = true) (hPd : P d = true) :
    ∃ i' j' : Nat, (l.filter P)[i']? = some m ∧ (l.filter P)[j']? = some d ∧ i' < j' := by
  obtain ⟨X, rest, hXeq, -⟩ := List.eq_append_cons_of_mem (List.mem_of_getElem? hi)
  have hXm : l[X.length]? = some m := hXeq ▸ getElem?_append_cons_right X m rest
  have hiX : i = X.length := (List.getElem?_inj (List.getElem?_eq_some_iff.mp hi).1 hnd).mp
    (hi.trans hXm.symm)
  have hjX : X.length < j := hiX ▸ hij
  have hdrest : rest[j - X.length - 1]? = some d := by
    have hstep : l[j]? = rest[j - X.length - 1]? := by
      obtain ⟨k, hk⟩ : ∃ k, j - X.length = k + 1 := ⟨j - X.length - 1, by omega⟩
      rw [hXeq, List.getElem?_append_right (Nat.le_of_lt hjX), hk, List.getElem?_cons_succ]
      congr 1
    rw [← hstep]; exact hj
  obtain ⟨Y, Z, hresteq, -⟩ := List.eq_append_cons_of_mem (List.mem_of_getElem? hdrest)
  have hl : l = X ++ m :: (Y ++ d :: Z) := by rw [hXeq, hresteq]
  refine ⟨(X.filter P).length, (X.filter P).length + 1 + (Y.filter P).length, ?_, ?_, by omega⟩
  · rw [hl]
    simp only [List.filter_append, List.filter_cons_of_pos hPm, List.filter_cons_of_pos hPd]
    exact getElem?_append_cons_right (X.filter P) m (Y.filter P ++ d :: Z.filter P)
  · rw [hl]
    simp only [List.filter_append, List.filter_cons_of_pos hPm, List.filter_cons_of_pos hPd]
    have hlen2 : (X.filter P).length + 1 + (Y.filter P).length =
        (X.filter P ++ m :: Y.filter P).length := by
      (simp? [List.length_append, List.length_cons] says simp only [List.length_append, List.length_cons]); omega
    rw [hlen2]
    (simp? says simp only [List.length_append, List.length_cons, add_lt_add_iff_left, add_lt_add_iff_right, lt_add_iff_pos_right, add_pos_iff, List.length_filter_pos_iff, zero_lt_one, or_true, getElem?_pos, le_add_iff_nonneg_right, zero_le, List.getElem_append_right, add_tsub_cancel_left, List.getElem_cons_succ, Std.le_refl, Nat.sub_self, List.getElem_cons_zero])

/-- A transfer sequence is maximal when no further transfer moves coins.
    Nitro:840-842: "we have done every possible transfer on these
    channels". go-nitro's `transfer` pays the whole affordable amount, so a
    further transfer moves coins only if some entry still affords a
    positive amount. -/
def Adjudicator.TransferExhausted (s : Adjudicator E) : Prop :=
  ∀ a b s', s.transfer a b = some s' → s'.balances = s.balances

/-- A list of transfers only. -/
def OnlyTransfers (ops : List (Participant × Op E)) : Prop :=
  ∀ e ∈ ops, ∃ a b, e.2 = Op.transfer a b

/-- An honest transfer move: the moves of the Turbo game (Nitro:779-781,
    "strategies and counter-strategies involving transfer operations only").
    A reaction counts only when it is exactly today's single transfer call
    (`HonestMove.chain (.transfer a b)`, no other calls, no sends). -/
def HonestMove.IsTransfer : HonestMove E → Prop
  | .react r => ∃ a b, r.calls = [Op.transfer a b] ∧ r.sends = []
  | .wait _ => False

/-- Nitro:779-781: the adversary of the Turbo game plays transfers only
    (go-nitro `transfer`). The clock does not move. -/
def Threat.TransfersOnly {p : Participant} (T : Threat E p) : Prop :=
  ∀ net m, T.feasible net m → ∃ caller a b, m = .chain caller (.transfer a b)

/-- The capability of the Turbo adversary: every transfer by another
    participant is feasible (Nitro:460-461 with Nitro:779-781). -/
def Threat.CapableTransfers {p : Participant} (T : Threat E p) : Prop :=
  ∀ net caller a b, caller ≠ p → T.feasible net (.chain caller (.transfer a b))

/-! ### Credit decomposition: `payoutValues` and `turboValueAlong`

    `payoutValues_get_eq_add_paidTo` reads one node's processing step as a
    single `Allocation.paidTo` credit. `turboValueAlong_eq_add_credits`
    reads the whole algorithm's answer at `d` as the starting balance plus
    one `paidTo` credit from every node whose own (stabilized) allocation
    owes `d` a non-guarantee amount. -/

/-- One processing step's net credit to one destination, in terms of
    `Allocation.paidTo`: `payoutValues` raises `vals.get d` by `o`'s
    priority-order payout to `d`, unless `d`'s first entry in `o` is a
    guarantee, which contributes no credit (`payoutValues`'s own skip). -/
theorem payoutValues_get_eq_add_paidTo (vals : Balances E) (remaining : Coins) (o : Allocation E)
    (hnd : (o.map Entry.dest).Nodup) (d : Address E) :
    (payoutValues vals remaining o).get d =
      vals.get d +
        (if (o.find d).elim false (fun e => !e.item.isGuarantee) then o.paidTo remaining d
          else 0) := by
  induction o generalizing vals remaining with
  | nil => (simp? [payoutValues] says simp only [payoutValues, Allocation.find_nil, Option.elim_none, Bool.false_eq_true, ↓reduceIte, add_zero])
  | cons e rest ih =>
    have hned : e.dest ∉ rest.map Entry.dest := (List.nodup_cons.1 hnd).1
    have hndr : (rest.map Entry.dest).Nodup := (List.nodup_cons.1 hnd).2
    rw [Allocation.find_cons]
    by_cases hde : e.dest = d
    · have hdnotrest : d ∉ rest.map Entry.dest := by rw [← hde]; exact hned
      have hne' : ∀ e' ∈ rest, e'.dest ≠ d := fun e' he' hcontra =>
        hdnotrest (List.mem_map.mpr ⟨e', he', hcontra⟩)
      have hpaid : Allocation.paidTo remaining (e :: rest) d = min e.amount remaining := by
        rw [Allocation.paidTo_eq_get, Allocation.dedup_eq_self_of_nodup hnd,
          Allocation.payout_cons, Balances.get_cons, if_pos hde.symm]
      rw [if_pos hde, hpaid]
      simp only [payoutValues]
      by_cases hg : e.item.isGuarantee
      · rw [if_pos hg, payoutValues_get_ne _ _ rest d hne']
        (simp? [hg] says simp only [Option.elim_some, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, add_zero])
      · rw [if_neg hg, payoutValues_get_ne _ _ rest d hne', Balances.get_add, if_pos hde.symm]
        rw [hde]
        (simp? [hg] says simp only [Option.elim_some, hg, Bool.not_false, ↓reduceIte, Nat.add_left_cancel_iff])
    · rw [if_neg hde]
      have hpaid : Allocation.paidTo remaining (e :: rest) d =
          Allocation.paidTo (remaining - min e.amount remaining) rest d := by
        conv_lhs => rw [Allocation.paidTo_eq_get, Allocation.dedup_eq_self_of_nodup hnd,
          Allocation.payout_cons, Balances.get_cons, if_neg (Ne.symm hde)]
        rw [Allocation.paidTo_eq_get, Allocation.dedup_eq_self_of_nodup hndr]
      rw [hpaid]
      simp only [payoutValues]
      by_cases hg : e.item.isGuarantee
      · rw [if_pos hg]
        exact ih vals (remaining - min e.amount remaining) hndr
      · rw [if_neg hg,
          ih (vals.add e.dest (min e.amount remaining)) (remaining - min e.amount remaining) hndr,
          Balances.get_add, if_neg (Ne.symm hde)]

/-! ### `turboValues` list-structure facts, used to stabilize one node's
    reading at the moment the algorithm processes it. -/

/-- `turboValues` folds over the list structurally: processing an append is
    processing the first part, then the second, on the result. -/
theorem turboValues_append (s : Adjudicator E) (l1 l2 : List (Address E)) (vals : Balances E) :
    s.turboValues (l1 ++ l2) vals = s.turboValues l2 (s.turboValues l1 vals) := by
  induction l1 generalizing vals with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, Adjudicator.turboValues]
    exact ih _

/-- Folding `turboValues` over a list none of whose nodes' own allocations
    credit `c` leaves `c`'s recorded value untouched. -/
theorem turboValues_get_ne (s : Adjudicator E) (L : List (Address E)) (c : Address E)
    (h : ∀ m ∈ L, ∀ e ∈ s.allocationOf m, e.dest ≠ c) (vals : Balances E) :
    (s.turboValues L vals).get c = vals.get c := by
  induction L generalizing vals with
  | nil => rfl
  | cons m rest ih =>
    simp only [Adjudicator.turboValues]
    rw [ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    exact payoutValues_get_ne vals (vals.get m) (s.allocationOf m) c (h m List.mem_cons_self)

/-- `takeWhile` over an explicit split that the predicate holds on the
    prefix and fails at the split point stops exactly at the prefix. -/
theorem takeWhile_append_eq_of_forall_true_of_false {α : Type} (p : α → Bool)
    (pre post : List α) (a : α) (hpre : ∀ x ∈ pre, p x = true) (ha : p a = false) :
    (pre ++ a :: post).takeWhile p = pre := by
  induction pre with
  | nil => (simp? [ha] says simp only [List.nil_append, ha, Bool.false_eq_true, not_false_eq_true, List.takeWhile_cons_of_neg])
  | cons x xs ih =>
    have hx : p x = true := hpre x List.mem_cons_self
    simp only [List.cons_append, List.takeWhile_cons, hx, if_true]
    exact congrArg (x :: ·) (ih (fun y hy => hpre y (List.mem_cons_of_mem _ hy)))

/-- An external destination never has a finalized outcome (Nitro:263-264),
    so its own allocation is always empty. -/
theorem allocationOf_eq_nil_of_isExternal (s : Adjudicator E) {c : Address E}
    (hc : c.isExternal = true) : s.allocationOf c = [] := by
  cases c with
  | external a => rfl
  | channel cc => (simp? [Address.isExternal] at hc says simp only [Address.isExternal, Bool.false_eq_true] at hc)

/-- Every node's own allocation has Nodup destinations: it is always the
    `.dedup` of a finalized outcome, or empty. -/
theorem allocationOf_nodup (s : Adjudicator E) (c : Address E) :
    ((s.allocationOf c).map Entry.dest).Nodup := by
  unfold Adjudicator.allocationOf
  cases s.finalOutcome c with
  | none => (simp? says simp only [List.map_nil, List.nodup_nil])
  | some outcome =>
    cases outcome with
    | allocation o => exact Allocation.dedup_nodup o

/-- The algorithm's recorded value at `c`, once the full order is folded,
    already agrees with the value fed into `c`'s own processing step: no
    node after `c` in a valid topological order can credit `c` (its own
    predecessors in `s.Edge` all come first, by `IsTopologicalOrder`), and
    `c` cannot credit itself (a self-edge would be a 1-cycle, excluded by
    `s.IsDAG`). So folding the rest of the order past `c`'s position never
    moves `c`'s reading again. -/
theorem turboValues_get_eq_takeWhile (s : Adjudicator E) (order : List (Address E))
    (hord : s.IsTopologicalOrder order) (vals : Balances E)
    (c : Address E) (hc : c ∈ order) (hcext : c.isExternal = false) :
    (s.turboValues order vals).get c =
      (s.turboValues (order.takeWhile (fun x => decide (x ≠ c))) vals).get c := by
  obtain ⟨pre, post, heq, hcpre⟩ := List.eq_append_cons_of_mem hc
  have htw : order.takeWhile (fun x => decide (x ≠ c)) = pre := by
    rw [heq]
    refine takeWhile_append_eq_of_forall_true_of_false _ pre post c (fun x hx => ?_) (by (simp? says simp only [ne_eq, not_true_eq_false, decide_false]))
    have hxc : x ≠ c := fun h => hcpre (h ▸ hx)
    (simpa? using hxc says simpa only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] using hxc)
  rw [htw, heq, turboValues_append]
  simp only [Adjudicator.turboValues]
  have hnoself : ∀ e ∈ s.allocationOf c, e.dest ≠ c := fun e he hcontra =>
    hord.isDAG.irrefl c (Relation.TransGen.single ⟨hcext, e, he, hcontra⟩)
  have hnopost : ∀ m ∈ post, ∀ e ∈ s.allocationOf m, e.dest ≠ c := by
    intro m hm e he hec
    obtain ⟨post1, post2, hpost_eq, -⟩ := List.eq_append_cons_of_mem hm
    have hle : order = pre ++ c :: (post1 ++ m :: post2) := by rw [heq, hpost_eq]
    have hvalid' : ∀ m d, m ∈ order → d ∈ order → s.Edge m d →
        ∃ i j : Nat, order[i]? = some m ∧ order[j]? = some d ∧ i < j :=
      fun m d _ _ hed => hord.2.1 m d hed
    exact not_edge_of_before_split s.Edge order hord.1 hvalid' pre post1 post2 m c hle
      ⟨hcext, e, he, hec⟩
  rw [turboValues_get_ne s post c hnopost]
  exact payoutValues_get_ne (s.turboValues pre vals) ((s.turboValues pre vals).get c)
    (s.allocationOf c) c hnoself

/-! ### One real `transfer` and the Turbo Value Algorithm

    A successful `transfer` from a channel `a` to an external destination
    leaves `turboValueAlong` unchanged at every address except `a` itself
    (`Adjudicator.turboValueAlong_transfer`). Before `a`'s turn the two runs
    differ only by the paid amount moved from `a` to the destination
    (`payoutValues_delta_step`). At `a`'s turn the real payment is one part of
    what the algorithm pays (`payoutValues_absorb_le`). After `a`'s turn only
    `a`'s own reading differs (`payoutValues_get_congr_ne`). -/

/-- `payoutValues` never lowers a reading, so neither does `turboValues`. -/
theorem Adjudicator.turboValues_get_le (s : Adjudicator E) (L : List (Address E))
    (vals : Balances E) (n : Address E) : vals.get n ≤ (s.turboValues L vals).get n := by
  induction L generalizing vals with
  | nil => exact le_refl _
  | cons m rest ih => exact le_trans (payoutValues_le _ _ _ n) (ih _)

/-- Starting balances that agree except at `c` give `payoutValues` results that
    agree except at `c`. -/
theorem payoutValues_get_congr_ne {vals1 vals2 : Balances E} {c : Address E}
    (h : ∀ m, m ≠ c → vals1.get m = vals2.get m) (remaining : Coins) (o : Allocation E)
    (n : Address E) (hn : n ≠ c) :
    (payoutValues vals1 remaining o).get n = (payoutValues vals2 remaining o).get n := by
  induction o generalizing vals1 vals2 remaining with
  | nil => exact h n hn
  | cons e rest ih =>
    simp only [payoutValues]
    apply ih
    intro m hm
    by_cases hg : e.item.isGuarantee = true
    · rw [if_pos hg, if_pos hg]
      exact h m hm
    · rw [if_neg hg, if_neg hg, Balances.get_add, Balances.get_add]
      by_cases hme : m = e.dest
      · rw [if_pos hme, if_pos hme, h e.dest (hme ▸ hm)]
      · rw [if_neg hme, if_neg hme]
        exact h m hm

/-- A successful `transfer` changes no allocation but the paying channel's. -/
theorem Adjudicator.allocationOf_transfer_ne {s s' : Adjudicator E} {a : FixedPart}
    {b : Address E} (h : s.transfer a b = some s') {m : Address E} (hm : m ≠ a.address) :
    s'.allocationOf m = s.allocationOf m := by
  obtain ⟨_, _, _, -, -, -, -, -, hfo, -, -⟩ := Adjudicator.transfer_effect h
  cases m with
  | external e => rfl
  | channel c =>
    have hca : c ≠ a := fun hc => hm (by rw [hc, FixedPart.address_eq])
    have h1 := hfo c
    rw [if_neg hca, FixedPart.address_eq] at h1
    unfold Adjudicator.allocationOf
    rw [h1]

/-- A successful `transfer` lowers one entry of the paying channel's
    allocation (`Allocation.reduceOwed`). -/
theorem Adjudicator.allocationOf_transfer_self {s s' : Adjudicator E} {a : FixedPart}
    {b : Address E} (h : s.transfer a b = some s') :
    ∃ x, s'.allocationOf a.address = (s.allocationOf a.address).reduceOwed b x := by
  obtain ⟨o, -, x, hf, -, -, -, -, hfo, -, -⟩ := Adjudicator.transfer_effect h
  have h1 := hfo a
  rw [if_pos rfl] at h1
  refine ⟨x, ?_⟩
  unfold Adjudicator.allocationOf
  rw [h1, hf]
  exact Allocation.dedup_reduceOwed o b x

/-- A successful `transfer` keeps the destination list of every allocation. -/
theorem Adjudicator.allocationOf_dest_transfer {s s' : Adjudicator E} {a : FixedPart}
    {b : Address E} (h : s.transfer a b = some s') (m : Address E) :
    (s'.allocationOf m).map Entry.dest = (s.allocationOf m).map Entry.dest := by
  by_cases hm : m = a.address
  · obtain ⟨x, hx⟩ := Adjudicator.allocationOf_transfer_self h
    rw [hm, hx, Allocation.reduceOwed_map_dest]
  · rw [Adjudicator.allocationOf_transfer_ne h hm]

/-- A successful `transfer` keeps every edge of the outcome network. -/
theorem Adjudicator.Edge_transfer_iff {s s' : Adjudicator E} {a : FixedPart} {b : Address E}
    (h : s.transfer a b = some s') (n m : Address E) : s'.Edge n m ↔ s.Edge n m := by
  have hdest := Adjudicator.allocationOf_dest_transfer h n
  unfold Adjudicator.Edge
  constructor
  · rintro ⟨hext, e, he, hed⟩
    have hmem : m ∈ (s'.allocationOf n).map Entry.dest := List.mem_map.mpr ⟨e, he, hed⟩
    rw [hdest] at hmem
    obtain ⟨e', he', hed'⟩ := List.mem_map.mp hmem
    exact ⟨hext, e', he', hed'⟩
  · rintro ⟨hext, e, he, hed⟩
    have hmem : m ∈ (s.allocationOf n).map Entry.dest := List.mem_map.mpr ⟨e, he, hed⟩
    rw [← hdest] at hmem
    obtain ⟨e', he', hed'⟩ := List.mem_map.mp hmem
    exact ⟨hext, e', he', hed'⟩

/-- A successful `transfer` keeps the outcome network a DAG. -/
theorem Adjudicator.IsDAG.transfer {s s' : Adjudicator E} {a : FixedPart} {b : Address E}
    (hdag : s.IsDAG) (h : s.transfer a b = some s') : s'.IsDAG :=
  ⟨fun n hn => hdag.irrefl n
    (Relation.TransGen.mono (fun x y hxy => (Adjudicator.Edge_transfer_iff h x y).mp hxy) n n hn)⟩

/-- One real `transfer` from `a` to an external destination `q` leaves the
    Turbo Value Algorithm's answer unchanged at every address but `a`, along
    a topological order of the state after the transfer that lists `a`. -/
theorem Adjudicator.turboValueAlong_transfer {s s' : Adjudicator E} {a : FixedPart} {q : E}
    (h : s.transfer a (.external q) = some s') {order : List (Address E)}
    (hord : s'.IsTopologicalOrder order) (ha : a.address ∈ order) {n : Address E}
    (hn : n ≠ a.address) :
    s'.turboValueAlong order n = s.turboValueAlong order n := by
  obtain ⟨o, amt, x, hf, hfind, -, -, hx, hfo, hbal, -, -⟩ := Adjudicator.transfer_effect h
  have hab : (a.address : Address E) ≠ .external q := by
    rw [FixedPart.address_eq]; exact fun h => by cases h
  have hext : ∀ t : Adjudicator E, t.allocationOf (.external q) = [] := fun _ => rfl
  have hallocA : s.allocationOf a.address = o.dedup := by
    unfold Adjudicator.allocationOf; rw [hf]
  have hallocA' : s'.allocationOf a.address = o.dedup.reduceOwed (.external q) x := by
    have h1 := hfo a
    rw [if_pos rfl] at h1
    unfold Adjudicator.allocationOf
    rw [h1]
    exact Allocation.dedup_reduceOwed o _ x
  have hagree : ∀ m, m ≠ a.address → m ≠ .external q →
      s.balances.get m = s'.balances.get m := by
    intro m hma hmq
    have h1 := hbal m
    rw [if_neg hma, if_neg hmq] at h1
    exact h1.symm
  have hA : s'.balances.get a.address = s.balances.get a.address - x := by
    have h1 := hbal a.address
    rw [if_pos rfl, if_neg hab, Nat.add_zero] at h1
    rw [← h1, Nat.add_sub_cancel]
  have hQ : s'.balances.get (.external q) = s.balances.get (.external q) + x := by
    have h1 := hbal (.external q)
    rw [if_neg hab.symm, if_pos rfl, Nat.add_zero] at h1
    exact h1
  have hxle : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
  -- Before `a`'s turn: the two runs differ only by `x` moved from `a` to `q`
  -- (`payoutValues_delta_step`, node by node; `q` has no allocation).
  have hdelta : ∀ L : List (Address E), a.address ∉ L →
      ∀ (vals1 vals2 : Balances E), x ≤ vals1.get a.address →
      (∀ m, m ≠ a.address → m ≠ .external q → vals1.get m = vals2.get m) →
      vals2.get a.address = vals1.get a.address - x →
      vals2.get (.external q) = vals1.get (.external q) + x →
      (∀ m, m ≠ a.address → m ≠ .external q →
        (s.turboValues L vals1).get m = (s'.turboValues L vals2).get m) ∧
      (s'.turboValues L vals2).get a.address = (s.turboValues L vals1).get a.address - x ∧
      (s'.turboValues L vals2).get (.external q) =
        (s.turboValues L vals1).get (.external q) + x := by
    intro L
    induction L with
    | nil => intro _ vals1 vals2 _ hag ha' hb'; exact ⟨hag, ha', hb'⟩
    | cons k rest ih =>
      intro hka vals1 vals2 hxle' hag ha' hb'
      have hk : k ≠ a.address := fun hk => hka (hk ▸ List.mem_cons_self)
      have hrest : a.address ∉ rest := fun hm => hka (List.mem_cons_of_mem k hm)
      simp only [Adjudicator.turboValues]
      by_cases hkq : k = .external q
      · rw [hkq, hext, hext]
        simp only [payoutValues]
        exact ih hrest vals1 vals2 hxle' hag ha' hb'
      · rw [hag k hk hkq, Adjudicator.allocationOf_transfer_ne h hk]
        obtain ⟨h1, h2, h3, h4⟩ := payoutValues_delta_step a.address (.external q) hab
          (s.allocationOf k) vals1 vals2 x hxle' hag ha' hb' (vals2.get k)
        exact ih hrest _ _ h2 h1 h3 h4
  -- After `a`'s turn: runs that agree except at `a` stay so.
  have hpost : ∀ L : List (Address E), a.address ∉ L → ∀ (vals1 vals2 : Balances E),
      (∀ m, m ≠ a.address → vals1.get m = vals2.get m) →
      ∀ m, m ≠ a.address → (s'.turboValues L vals1).get m = (s.turboValues L vals2).get m := by
    intro L
    induction L with
    | nil => intro _ vals1 vals2 hv m hm; exact hv m hm
    | cons k rest ih =>
      intro hc vals1 vals2 hv m hm
      have hkc : k ≠ a.address := fun hk => hc (hk ▸ List.mem_cons_self)
      simp only [Adjudicator.turboValues]
      rw [hv k hkc, Adjudicator.allocationOf_transfer_ne h hkc]
      exact ih (fun hm' => hc (List.mem_cons_of_mem k hm')) _ _
        (fun m' hm' => payoutValues_get_congr_ne hv _ _ m' hm') m hm
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
  have hnd := hord.1
  rw [List.nodup_append, List.nodup_cons] at hnd
  have hapre : a.address ∉ pre := fun hm => hnd.2.2 _ hm _ List.mem_cons_self rfl
  have hapost : a.address ∉ post := hnd.2.1.1
  unfold Adjudicator.turboValueAlong
  rw [turboValues_append, turboValues_append]
  simp only [Adjudicator.turboValues]
  obtain ⟨D1, D3, D4⟩ := hdelta pre hapre s.balances s'.balances hxle hagree hA hQ
  have hheld : s.balances.get a.address ≤ (s.turboValues pre s.balances).get a.address :=
    Adjudicator.turboValues_get_le s pre s.balances a.address
  have hxd : x = o.dedup.paidTo (s.balances.get a.address) (.external q) := by
    rw [hx, Allocation.paidTo_eq_get, Allocation.paidTo_eq_get,
      Allocation.dedup_eq_self_of_nodup (Allocation.dedup_nodup o)]
  have hfindd : o.dedup.find (.external q) = some ⟨.external q, .alloc amt⟩ := by
    rw [Allocation.find_dedup]; exact hfind
  have habs := payoutValues_absorb_le (Allocation.dedup_nodup o) hfindd
    (s.turboValues pre s.balances) hheld
  rw [← hxd] at habs
  rw [hallocA', hallocA, D3]
  refine hpost post hapost _ _ (fun m hm => ?_) n hn
  rw [habs m]
  refine payoutValues_get_congr_ne (fun k hk => ?_) _ _ m hm
  rw [Balances.get_add]
  by_cases hkq : k = .external q
  · rw [if_pos hkq, hkq, D4]
  · rw [if_neg hkq]
    exact (D1 k hk hkq).symm

/-- Whether `c`'s own allocation owes `d` through a non-guarantee entry
    (same guard `payoutValues_get_eq_add_paidTo` reads). -/
def Adjudicator.CreditsTo (s : Adjudicator E) (c d : Address E) : Bool :=
  ((s.allocationOf c).find d).elim false (fun e => !e.item.isGuarantee)

theorem turboValueAlong_eq_add_credits_aux (s : Adjudicator E) (order : List (Address E))
    (hord : s.IsTopologicalOrder order) (d : Address E) :
    ∀ suf pre : List (Address E), order = pre ++ suf →
      (s.turboValues suf (s.turboValues pre s.balances)).get d =
        (s.turboValues pre s.balances).get d +
          ((suf.filter (s.CreditsTo · d)).map
            (fun c => (s.allocationOf c).paidTo (s.turboValueAlong order c) d)).sum := by
  intro suf
  induction suf with
  | nil => intro pre _; (simp? [Adjudicator.turboValues] says simp only [Adjudicator.turboValues, List.filter_nil, List.map_nil, List.sum_nil, add_zero])
  | cons c rest ih =>
    intro pre heq
    have heq' : order = (pre ++ [c]) ++ rest := by rw [heq]; (simp? says simp only [List.append_assoc, List.cons_append, List.nil_append])
    have hstep : s.turboValues (pre ++ [c]) s.balances =
        payoutValues (s.turboValues pre s.balances) ((s.turboValues pre s.balances).get c)
          (s.allocationOf c) := by
      rw [turboValues_append]; rfl
    have hih := ih (pre ++ [c]) heq'
    rw [hstep] at hih
    simp only [Adjudicator.turboValues]
    rw [hih]
    have hcmem : c ∈ order := heq ▸ (List.mem_append.mpr (Or.inr List.mem_cons_self))
    have hA := payoutValues_get_eq_add_paidTo (s.turboValues pre s.balances)
      ((s.turboValues pre s.balances).get c) (s.allocationOf c) (allocationOf_nodup s c) d
    by_cases hP : s.CreditsTo c d = true
    · rw [List.filter_cons_of_pos (p := fun x => s.CreditsTo x d) (a := c) hP,
        List.map_cons, List.sum_cons]
      have hallocne : s.allocationOf c ≠ [] := by
        intro hempty
        (simp? [Adjudicator.CreditsTo, hempty, Allocation.find] at hP says simp only [Adjudicator.CreditsTo, Allocation.find, hempty, List.find?_nil, Option.elim_none, Bool.false_eq_true] at hP)
      have hcext : c.isExternal = false := by
        by_contra hb
        exact hallocne (allocationOf_eq_nil_of_isExternal s (by (simpa? using hb says simpa only [Bool.not_eq_false] using hb)))
      have hstab : (s.turboValues pre s.balances).get c = s.turboValueAlong order c := by
        unfold Adjudicator.turboValueAlong
        have htw : order.takeWhile (fun x => decide (x ≠ c)) = pre := by
          have hnd := hord.1
          rw [heq, List.nodup_append] at hnd
          have hcnotpre : c ∉ pre := fun hcp => hnd.2.2 c hcp c List.mem_cons_self rfl
          rw [heq]
          refine takeWhile_append_eq_of_forall_true_of_false _ pre rest c
            (fun x hx => ?_) (by (simp? says simp only [ne_eq, not_true_eq_false, decide_false]))
          have hxc : x ≠ c := fun h => hcnotpre (h ▸ hx)
          (simpa? using hxc says simpa only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] using hxc)
        rw [turboValues_get_eq_takeWhile s order hord s.balances c hcmem hcext, htw]
      rw [Adjudicator.CreditsTo] at hP
      rw [hP, if_pos rfl] at hA
      rw [hA, hstab]
      exact Nat.add_assoc _ _ _
    · rw [List.filter_cons_of_neg (p := fun x => s.CreditsTo x d) (a := c) hP]
      have hPfalse : s.CreditsTo c d = false := Bool.eq_false_iff.mpr hP
      rw [Adjudicator.CreditsTo] at hPfalse
      rw [hPfalse, if_neg (by (simp? says simp only [Bool.false_eq_true, not_false_eq_true]))] at hA
      rw [hA, Nat.add_zero]

/-- Nitro:818-835 step 4's value at `d`, decomposed into the starting
    balance plus one `Allocation.paidTo` credit from every node in `order`
    whose own allocation owes `d` a non-guarantee amount: each such node's
    processing-time reading equals its final, stabilized reading
    (`turboValues_get_eq_takeWhile`), so the credit can be read off the
    algorithm's final answer at that node. -/
theorem turboValueAlong_eq_add_credits (s : Adjudicator E) (hdag : s.IsDAG)
    (order : List (Address E)) (hord : s.IsTopologicalOrder order) (d : Address E) :
    s.turboValueAlong order d =
      s.balances.get d +
        ((order.filter (s.CreditsTo · d)).map
          (fun c => (s.allocationOf c).paidTo (s.turboValueAlong order c) d)).sum := by
  have h := turboValueAlong_eq_add_credits_aux s order hord d order [] (by (simp? says simp only [List.nil_append]))
  (simpa? [Adjudicator.turboValueAlong, Adjudicator.turboValues] using h says simpa only [Adjudicator.turboValueAlong, Adjudicator.turboValues] using h)


/-! ### A deposit and the Turbo Value Algorithm

    A deposit of `y` coins raises one starting balance by `y` and changes
    no allocation. Along one order, the algorithm's value at an external
    destination then rises by at least `0` and at most `y`
    (`Adjudicator.turboValueAlong_deposit`). -/

/-- A deposit changes no status and not the clock, so it changes no
    allocation. -/
theorem Adjudicator.allocationOf_deposit {s s' : Adjudicator E} {a : Address E} {e y : Coins}
    (hd : s.deposit a e y = some s') (n : Address E) : s'.allocationOf n = s.allocationOf n := by
  obtain ⟨-, -, -, -, hs, hn⟩ := Adjudicator.deposit_some hd
  cases n with
  | external b => rfl
  | channel c =>
    unfold Adjudicator.allocationOf
    rw [Adjudicator.finalOutcome_channel, Adjudicator.finalOutcome_channel,
      Adjudicator.statusOf_of_status hs, hn]

/-- A deposit of `y` coins: along one topological order of `s`, the
    algorithm's value at an external destination rises by at least `0` and
    at most `y`. The invariant of the run: every value is at least its old
    value, and over the nodes still to be processed and the destination the
    rise sums to at most `y`. Processing a node passes on at most its own
    rise (`hsumle`), and the destination has an empty allocation. -/
theorem Adjudicator.turboValueAlong_deposit {s s' : Adjudicator E} {a : Address E} {e y : Coins}
    (hd : s.deposit a e y = some s') {order : List (Address E)} (hord : s.IsTopologicalOrder order)
    (d : E) :
    s.turboValueAlong order (.external d) ≤ s'.turboValueAlong order (.external d) ∧
      s'.turboValueAlong order (.external d) ≤ s.turboValueAlong order (.external d) + y := by
  obtain ⟨-, -, hb, -, -, -⟩ := Adjudicator.deposit_some hd
  -- A raise of `b` by `x`, summed over a list with no repeated address.
  have hsum_add : ∀ (v : Balances E) (b : Address E) (x : Coins) (S : List (Address E)),
      S.Nodup → (S.map (v.add b x).get).sum = (S.map v.get).sum + if b ∈ S then x else 0 := by
    intro v b x S hS
    induction S with
    | nil => rfl
    | cons m S ih =>
      obtain ⟨hm, hS'⟩ := List.nodup_cons.1 hS
      simp only [List.map_cons, List.sum_cons]
      by_cases hmb : m = b
      · subst hmb
        have hrest : (S.map (v.add m x).get).sum = (S.map v.get).sum :=
          congrArg List.sum (List.map_congr_left fun k hk => by
            rw [Balances.get_add, if_neg (fun h : k = m => hm (h ▸ hk))])
        rw [Balances.get_add, if_pos rfl, hrest, if_pos List.mem_cons_self]
        unfold Coins at *
        omega
      · have hmem : (b ∈ m :: S) ↔ b ∈ S := by
          rw [List.mem_cons]
          exact ⟨fun h => h.resolve_left (Ne.symm hmb), Or.inr⟩
        rw [Balances.get_add, if_neg hmb, ih hS', if_congr hmem rfl rfl]
        unfold Coins at *
        omega
  -- `payoutValues` is monotone in its starting values and its amount.
  have hmono : ∀ (o : Allocation E) (v1 v2 : Balances E) (r1 r2 : Coins),
      (∀ m, v1.get m ≤ v2.get m) → r1 ≤ r2 →
      ∀ m, (payoutValues v1 r1 o).get m ≤ (payoutValues v2 r2 o).get m := by
    intro o
    induction o with
    | nil => intro v1 v2 r1 r2 hv _; exact hv
    | cons f rest ih =>
      intro v1 v2 r1 r2 hv hr
      simp only [payoutValues]
      refine ih _ _ _ _ ?_ (by unfold Coins at *; omega)
      intro m
      by_cases hg : f.item.isGuarantee = true
      · simp only [if_pos hg]
        exact hv m
      · simp only [if_neg hg, Balances.get_add]
        split
        · next h =>
          have := hv f.dest
          unfold Coins at *
          omega
        · exact hv m
  -- Over a list with no repeated address, paying `r2` instead of `r1 ≤ r2`
  -- adds at most `r2 - r1` to the sum beyond the starting difference.
  have hsumle : ∀ (o : Allocation E) (S : List (Address E)), S.Nodup →
      ∀ (v1 v2 : Balances E) (r1 r2 : Coins), r1 ≤ r2 →
      (S.map (payoutValues v2 r2 o).get).sum + (S.map v1.get).sum + r1 ≤
        (S.map (payoutValues v1 r1 o).get).sum + (S.map v2.get).sum + r2 := by
    intro o S hS
    induction o with
    | nil =>
      intro v1 v2 r1 r2 hr
      simp only [payoutValues]
      unfold Coins at *
      omega
    | cons f rest ih =>
      intro v1 v2 r1 r2 hr
      simp only [payoutValues]
      have hrest := ih (if f.item.isGuarantee then v1 else v1.add f.dest (min f.amount r1))
        (if f.item.isGuarantee then v2 else v2.add f.dest (min f.amount r2))
        (r1 - min f.amount r1) (r2 - min f.amount r2) (by unfold Coins at *; omega)
      by_cases hg : f.item.isGuarantee = true
      · simp only [if_pos hg] at hrest ⊢
        unfold Coins at *
        omega
      · simp only [if_neg hg] at hrest ⊢
        rw [hsum_add v1 _ _ S hS, hsum_add v2 _ _ S hS] at hrest
        unfold Coins at *
        split at hrest <;> omega
  -- The run of the algorithm keeps the invariant.
  have ha : s.allocationOf (.external d) = [] := allocationOf_eq_nil_of_isExternal s rfl
  have hrun : ∀ (order : List (Address E)) (v1 v2 : Balances E), order.Nodup →
      (∀ m, v1.get m ≤ v2.get m) →
      (∀ S : List (Address E), S.Nodup → (∀ m ∈ S, m ∈ order ∨ m = .external d) →
        (S.map v2.get).sum ≤ (S.map v1.get).sum + y) →
      (s.turboValues order v1).get (.external d) ≤ (s.turboValues order v2).get (.external d) ∧
        (s.turboValues order v2).get (.external d) ≤
          (s.turboValues order v1).get (.external d) + y := by
    intro order
    induction order with
    | nil =>
      intro v1 v2 _ hle hsum
      have h := hsum [.external d] (List.nodup_singleton _)
        (fun m hm => Or.inr (List.mem_singleton.1 hm))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
      simp only [Adjudicator.turboValues]
      unfold Coins at *
      exact ⟨hle _, by omega⟩
    | cons n rest ih =>
      intro v1 v2 hnd hle hsum
      obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
      simp only [Adjudicator.turboValues]
      refine ih _ _ hnd' (hmono _ v1 v2 _ _ hle (hle n)) fun S hS hSsub => ?_
      by_cases hnS : n ∈ S
      · have hna : n = .external d := (hSsub n hnS).resolve_left hn
        subst hna
        simp only [ha, payoutValues]
        exact hsum S hS fun m hm => (hSsub m hm).imp_left (List.mem_cons_of_mem _)
      · have hstep := hsumle (s.allocationOf n) S hS v1 v2 _ _ (hle n)
        have hcons := hsum (n :: S) (List.nodup_cons.2 ⟨hnS, hS⟩) fun m hm => by
          rcases List.mem_cons.1 hm with rfl | hm
          · exact Or.inl List.mem_cons_self
          · exact (hSsub m hm).imp_left (List.mem_cons_of_mem _)
        simp only [List.map_cons, List.sum_cons] at hcons
        unfold Coins at *
        omega
  -- `s'` runs the algorithm with the same allocations.
  have hcongr : ∀ (order : List (Address E)) (v : Balances E),
      s'.turboValues order v = s.turboValues order v := by
    intro order
    induction order with
    | nil => intro v; rfl
    | cons n rest ih =>
      intro v
      simp only [Adjudicator.turboValues, Adjudicator.allocationOf_deposit hd n, ih]
  unfold Adjudicator.turboValueAlong
  rw [hcongr, hb]
  refine hrun order _ _ hord.1 (fun m => ?_) fun S hS _ => ?_
  · rw [Balances.get_add]
    split
    · next h =>
      subst h
      unfold Coins at *
      omega
    · exact le_rfl
  · rw [hsum_add _ _ _ S hS]
    unfold Coins at *
    split <;> omega


end ArmadaLean.Nitro
