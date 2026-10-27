/-
  Nitro protocol specification: the `@[simp]` reading lemmas of the
  definitions and the proof helpers that `Safety.lean` uses. Each section
  follows one definition file, in dependency order: `Address.lean`,
  `Outcome.lean`, `Channel.lean`, `Adjudicator.lean`. Rules:
  `armada-laconic/docs/lean/writing-lean.md` (rules 3, 5, 6, 9).
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
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
  by_cases h : q k <;> simp [sumIf, List.filter_cons, h]

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

end Balances

end ArmadaLean.Nitro
