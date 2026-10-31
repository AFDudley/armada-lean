/-
  Nitro protocol specification: the network of outcomes and the Turbo Value
  Algorithm (Nitro:818-835).
  See `Address.lean` for the source list. SATP and go-nitro have no value
  algorithm, so Nitro is the primary source for this file. The Nitro
  Lower-bound Value Algorithm (Nitro:1178-1255) reads Nitro's `claim`, which
  SATP and go-nitro replaced by `reclaim`; it is not modelled (operator
  ruling 2026-10-27).

  DAG (operator ruling 2026-10-27). "The network of outcomes is a DAG" means
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
    `∀ c, ¬ Relation.TransGen edge c c` (operator ruling 2026-10-27), stated
    as `Std.Irrefl` of the transitive closure (Mathlib `Relation.TransGen`,
    core `Std.Irrefl`; its `irrefl` field is the ruling's formula). -/
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
  · simp [h]

/-- `payoutValues` never lowers any address's recorded value: every update
    it makes is an addition. -/
theorem payoutValues_le (o : Allocation E) (vals : Balances E) (remaining : Coins) (n : Address E) :
    vals.get n ≤ (payoutValues vals remaining o).get n := by
  induction o generalizing vals remaining with
  | nil => simp [payoutValues]
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
    · simp [Balances.get_add, h]

/-- Processing an allocation that never mentions `d` as a destination
    leaves `d`'s recorded value unchanged. -/
theorem payoutValues_get_of_not_mem {o : Allocation E} {d : Address E}
    (hd : d ∉ o.map Entry.dest) (vals : Balances E) (remaining : Coins) :
    (payoutValues vals remaining o).get d = vals.get d := by
  induction o generalizing vals remaining with
  | nil => simp [payoutValues]
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
  | nil => simp at hb
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
      have heamt : e.amount = amt := by simp [Entry.amount, heitem]
      have hx : Allocation.paidTo remaining (e :: rest) e.dest = min amt remaining := by
        rw [Allocation.paidTo_eq_get, hdeq]
        conv_lhs => rw [hee]
        simp [Allocation.payout_cons, Balances.get_cons]
      rw [hx]
      have hro : Allocation.reduceOwed (e :: rest) e.dest (min amt remaining) =
          ({ e with item := .alloc (amt - min amt remaining) } : Entry E) :: rest := by
        rw [Allocation.reduceOwed_cons, if_pos rfl]
        simp [Entry.amount, heitem]
      rw [hro]
      simp only [payoutValues]
      have hcond1 : ¬ e.item.isGuarantee = true := by rw [heitem]; simp [Item.isGuarantee]
      have hcond2 : ¬ ({ e with item := .alloc (amt - min amt remaining) } : Entry E).item.isGuarantee = true := by
        simp [Item.isGuarantee]
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
      · simp [hm, Balances.get_add]
      · simp [hm, Balances.get_add]
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
        · simp [hg]
        · by_cases hmb : m = b
          · by_cases hme : m = e.dest
            · exact absurd (hme.symm.trans hmb) he
            · simp_all [Balances.get_add]
          · by_cases hme : m = e.dest
            · simp_all [Balances.get_add]
            · simp_all [Balances.get_add]
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
    · exact ⟨[], List.nodup_nil, by simp, by simp⟩
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
            exact ⟨0, j + 1, List.getElem?_cons_zero, by simpa using hj, by omega⟩
          · have hxW' : x ∈ order' := (hmem' x).mpr ((hmemW x).mpr ⟨hx, hxa⟩)
            have hyW' : y ∈ order' := (hmem' y).mpr ((hmemW y).mpr ⟨hy, hya⟩)
            have hxpp : x ∈ pre ++ post := (hmemW x).mpr ⟨hx, hxa⟩
            have hypp : y ∈ pre ++ post := (hmemW y).mpr ⟨hy, hya⟩
            obtain ⟨i, j, hi, hj, hij⟩ := hedge' x y hxpp hypp hxy
            exact ⟨i + 1, j + 1, by simpa using hi, by simpa using hj, by omega⟩

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
      (fun l1 h' => h'.elim (fun l2 ⟨heq, _⟩ => heq ▸ by simp))
    exact ⟨st, hmem, by unfold Adjudicator.statusOf; rw [hlk]; rfl⟩

theorem active_mem_requiredNodes (s : Adjudicator E) (n : Address E)
    (h : s.balances.get n ≠ 0 ∨ s.allocationOf n ≠ []) : n ∈ requiredNodes s := by
  unfold requiredNodes
  rcases h with h | h
  · refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
    unfold Balances.get at h
    cases hlk : s.balances.lookup n with
    | none => simp [hlk] at h
    | some v =>
      have hmem : (n, v) ∈ s.balances := List.lookup_eq_some_iff.mp hlk |>.elim
        (fun l1 h' => h'.elim (fun l2 ⟨heq, _⟩ => heq ▸ by simp))
      exact List.mem_map.mpr ⟨(n, v), hmem, rfl⟩
  · obtain ⟨c, hceq⟩ : ∃ c : FixedPart, n = c.address := by
      cases n with
      | external d => simp [Adjudicator.allocationOf, Adjudicator.finalOutcome] at h
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
    | external dd => simp [Adjudicator.allocationOf, Adjudicator.finalOutcome] at hnactive
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
    · simp [hg]
    · simp [hg, Balances.get_add, Ne.symm hne]

-- Index utilities: an explicit split gives a direct index witness, and
-- Nodup makes that witness the unique one `hvalid`-style existentials
-- must agree with.
theorem getElem?_append_cons_right {α : Type} (l1 : List α) (x : α) (l2 : List α) :
    (l1 ++ x :: l2)[l1.length]? = some x := by
  induction l1 with
  | nil => rfl
  | cons h t ih => simp

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
      simp [List.length_append, List.length_cons]; omega]
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
      · subst hqe; rw [Nat.add_assoc]; simp
      · simp

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
      rw [List.filter_cons_of_neg (by simp [hx])]
      simp only [Adjudicator.turboValues, hxnil, payoutValues]
      exact ih vals
    · rw [List.filter_cons_of_pos (by simp [hx])]
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
  by_cases h1 : im < pre.length <;> by_cases h2 : id < pre.length <;> simp [h1, h2] <;> omega

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
        | cons y ys => exact absurd ((hmem y).mpr List.mem_cons_self) (by simp)
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
        rw [heq1, hpeq]; simp [List.append_assoc]
      have hnoout2 : ∀ p ∈ pre2, ¬ s.Edge a p := by
        intro p hp
        obtain ⟨prepre, postpre, hpeq, -⟩ := List.eq_append_cons_of_mem hp
        refine not_edge_of_before_split s.Edge L2 hnd2 hvalid2 prepre postpre post2 a p ?_
        rw [heq2, hpeq]; simp [List.append_assoc]
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
          simp [List.length_append, List.length_cons]; omega
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
      simp [List.length_append, List.length_cons]; omega
    rw [hlen2]
    simp

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
  | nil => simp [payoutValues]
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
        simp [hg]
      · rw [if_neg hg, payoutValues_get_ne _ _ rest d hne', Balances.get_add, if_pos hde.symm]
        rw [hde]
        simp [hg]
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
  | nil => simp [ha]
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
  | channel cc => simp [Address.isExternal] at hc

/-- Every node's own allocation has Nodup destinations: it is always the
    `.dedup` of a finalized outcome, or empty. -/
theorem allocationOf_nodup (s : Adjudicator E) (c : Address E) :
    ((s.allocationOf c).map Entry.dest).Nodup := by
  unfold Adjudicator.allocationOf
  cases s.finalOutcome c with
  | none => simp
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
theorem turboValues_get_eq_takeWhile (s : Adjudicator E) (hdag : s.IsDAG)
    (order : List (Address E)) (hord : s.IsTopologicalOrder order) (vals : Balances E)
    (c : Address E) (hc : c ∈ order) (hcext : c.isExternal = false) :
    (s.turboValues order vals).get c =
      (s.turboValues (order.takeWhile (fun x => decide (x ≠ c))) vals).get c := by
  obtain ⟨pre, post, heq, hcpre⟩ := List.eq_append_cons_of_mem hc
  have htw : order.takeWhile (fun x => decide (x ≠ c)) = pre := by
    rw [heq]
    refine takeWhile_append_eq_of_forall_true_of_false _ pre post c (fun x hx => ?_) (by simp)
    have hxc : x ≠ c := fun h => hcpre (h ▸ hx)
    simpa using hxc
  rw [htw, heq, turboValues_append]
  simp only [Adjudicator.turboValues]
  have hnoself : ∀ e ∈ s.allocationOf c, e.dest ≠ c := fun e he hcontra =>
    hdag.irrefl c (Relation.TransGen.single ⟨hcext, e, he, hcontra⟩)
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

/-- Whether `c`'s own allocation owes `d` through a non-guarantee entry
    (same guard `payoutValues_get_eq_add_paidTo` reads). -/
def Adjudicator.CreditsTo (s : Adjudicator E) (c d : Address E) : Bool :=
  ((s.allocationOf c).find d).elim false (fun e => !e.item.isGuarantee)

theorem turboValueAlong_eq_add_credits_aux (s : Adjudicator E) (hdag : s.IsDAG)
    (order : List (Address E)) (hord : s.IsTopologicalOrder order) (d : Address E) :
    ∀ suf pre : List (Address E), order = pre ++ suf →
      (s.turboValues suf (s.turboValues pre s.balances)).get d =
        (s.turboValues pre s.balances).get d +
          ((suf.filter (s.CreditsTo · d)).map
            (fun c => (s.allocationOf c).paidTo (s.turboValueAlong order c) d)).sum := by
  intro suf
  induction suf with
  | nil => intro pre _; simp [Adjudicator.turboValues]
  | cons c rest ih =>
    intro pre heq
    have heq' : order = (pre ++ [c]) ++ rest := by rw [heq]; simp
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
        simp [Adjudicator.CreditsTo, hempty, Allocation.find] at hP
      have hcext : c.isExternal = false := by
        by_contra hb
        exact hallocne (allocationOf_eq_nil_of_isExternal s (by simpa using hb))
      have hstab : (s.turboValues pre s.balances).get c = s.turboValueAlong order c := by
        unfold Adjudicator.turboValueAlong
        have htw : order.takeWhile (fun x => decide (x ≠ c)) = pre := by
          have hnd := hord.1
          rw [heq, List.nodup_append] at hnd
          have hcnotpre : c ∉ pre := fun hcp => hnd.2.2 c hcp c List.mem_cons_self rfl
          rw [heq]
          refine takeWhile_append_eq_of_forall_true_of_false _ pre rest c
            (fun x hx => ?_) (by simp)
          have hxc : x ≠ c := fun h => hcnotpre (h ▸ hx)
          simpa using hxc
        rw [turboValues_get_eq_takeWhile s hdag order hord s.balances c hcmem hcext, htw]
      rw [Adjudicator.CreditsTo] at hP
      rw [hP, if_pos rfl] at hA
      rw [hA, hstab]
      exact Nat.add_assoc _ _ _
    · rw [List.filter_cons_of_neg (p := fun x => s.CreditsTo x d) (a := c) hP]
      have hPfalse : s.CreditsTo c d = false := Bool.eq_false_iff.mpr hP
      rw [Adjudicator.CreditsTo] at hPfalse
      rw [hPfalse, if_neg (by simp)] at hA
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
  have h := turboValueAlong_eq_add_credits_aux s hdag order hord d order [] (by simp)
  simpa [Adjudicator.turboValueAlong, Adjudicator.turboValues] using h


end ArmadaLean.Nitro
