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

end ArmadaLean.Nitro
