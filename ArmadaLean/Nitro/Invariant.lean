/-
  Nitro protocol: the adjudicator safety invariant `Adjudicator.Inv`. One
  structure holds the safety facts of a reachable adjudicator state as
  fields: the coins-held facts, the origin of each channel status, and the
  facts of each step from the state. `Adjudicator.inv_genesis` and
  `Adjudicator.inv_step` give `Adjudicator.inv_reachable`. The
  reachable-state theorems of `Safety.lean` are projections of its fields.
  Design record: armada-laconic `docs/process.md`, rule 2.1 (one invariant
  with one step lemma) and the repair pass R.2.
-/
import ArmadaLean.Nitro.Lemmas
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- One redistribution of a finalized outcome: Nitro:770 (transfer),
    SATP:358-361 and go-nitro `compute_reclaim_effects` (reclaim on the
    ledger). -/
inductive RedistributeStep : Outcome E → Outcome E → Prop
  | reduce (o : Allocation E) (d : Address E) (x : Coins) :
      RedistributeStep (.allocation o) (.allocation (o.reduceOwed d x))
  | reclaim (o : Allocation E) (left right v : Address E) (x y : Coins) :
      RedistributeStep (.allocation o) (.allocation (((o.addTo left x).addTo right y).remove v))

/-- Zero or more redistributions (Mathlib `Relation.ReflTransGen`). -/
def Redistributed : Outcome E → Outcome E → Prop :=
  Relation.ReflTransGen RedistributeStep

/-- The conclusion of `finalized_two_ways` for a channel `c` and an outcome
    `Ω` at the state `s`: a conclude, or a challenge whose deadline is at or
    before `s.now`, followed by redistributions. -/
def FinalizedTwoWays (apps : Apps E) (s : Adjudicator E) (c : FixedPart) (Ω : Outcome E) : Prop :=
  ∃ s0 s1 caller, Reachable apps s0 ∧
    ((∃ ss, s0.apply apps caller (.conclude c ss) = some s1 ∧ ConclusionProof c ss ∧
        Redistributed ss.state.outcome Ω) ∨
     (∃ proof candidate, s0.apply apps caller (.challenge c proof candidate) = some s1 ∧
        s0.now + c.challengeDuration ≤ s.now ∧ Redistributed candidate.outcome Ω))

theorem FinalizedTwoWays.mono {apps : Apps E} {s s' : Adjudicator E} {c : FixedPart} {Ω Ω' : Outcome E}
    (h : FinalizedTwoWays apps s c Ω) (hn : s.now ≤ s'.now) (hR : Redistributed Ω Ω') :
    FinalizedTwoWays apps s' c Ω' := by
  obtain ⟨s0, s1, caller, hr0, ⟨ss, h1, h2, h3⟩ | ⟨proof, cand, h1, h2, h3⟩⟩ := h
  · exact ⟨s0, s1, caller, hr0, Or.inl ⟨ss, h1, h2, h3.trans hR⟩⟩
  · exact ⟨s0, s1, caller, hr0, Or.inr ⟨proof, cand, h1, by (grind? says grind only), h3.trans hR⟩⟩

/-- Nitro:288-290: the origin of a channel status. A running challenge came
    from a challenge step whose deadline it keeps; a finalized status
    satisfies `FinalizedTwoWays`. -/
def StatusOrigin (apps : Apps E) (s : Adjudicator E) (c : FixedPart) : Prop :=
  match s.statusOf c with
  | .open _ => True
  | .challenged _ ch => ∃ s0 s1 caller proof, Reachable apps s0 ∧
      s0.apply apps caller (.challenge c proof ch.state) = some s1 ∧
      s0.now + c.challengeDuration = ch.deadline
  | .finalized _ _ Ω => FinalizedTwoWays apps s c Ω

theorem statusOrigin_of_eq {apps : Apps E} {s s' : Adjudicator E} {c : FixedPart}
    (ho : StatusOrigin apps s c) (hs : s'.statusOf c = s.statusOf c) (hn : s.now ≤ s'.now) :
    StatusOrigin apps s' c := by
  unfold StatusOrigin at ho ⊢
  rw [hs]
  split at ho
  · trivial
  · exact ho
  · exact ho.mono hn Relation.ReflTransGen.refl

/-- A redistribution of a finalized outcome keeps its origin. -/
theorem statusOrigin_redistribute {apps : Apps E} {s s' : Adjudicator E} {c : FixedPart} {Ω Ω' : Outcome E}
    (ho : StatusOrigin apps s c) (hf : (s.statusOf c).finalOutcome s.now = some Ω)
    (hR : Redistributed Ω Ω') (hn : s.now ≤ s'.now)
    (hs : s'.statusOf c = (s.statusOf c).withOutcome Ω') :
    StatusOrigin apps s' c := by
  unfold StatusOrigin at ho ⊢
  rw [hs]
  revert ho hf
  cases s.statusOf c with
  | «open» t => intro _ hf; (simp? at hf says simp only [ChannelStatus.finalOutcome_open, reduceCtorEq] at hf)
  | challenged t ch =>
    intro ho hf
    simp only [ChannelStatus.finalOutcome_challenged] at hf
    split at hf
    · cases hf
      obtain ⟨s0, s1, caller, proof, hr0, h1, h2⟩ := ho
      exact ⟨s0, s1, caller, hr0, Or.inr ⟨proof, ch.state, h1, by (grind? says grind only), hR⟩⟩
    · cases hf
  | finalized t f o =>
    intro ho hf
    simp only [ChannelStatus.finalOutcome_finalized, Option.some.injEq] at hf
    subst hf
    exact ho.mono hn hR

/-! ### The safety invariant -/

/-- The adjudicator safety invariant: the safety facts of one reachable
    state. The fields `keysNodup`, `held` and `origin` carry the induction.
    The other fields follow from them at the same state
    (`Adjudicator.inv_of_state`). -/
structure Adjudicator.Inv (apps : Apps E) (s : Adjudicator E) : Prop where
  /-- Each address has one balance entry. -/
  keysNodup : s.balances.KeysNodup
  /-- Nitro:230-231: the coins held equal the sum of the channel balances. A
      payout to an external destination leaves the contract (go-nitro
      MultiAssetHolder.sol:401-402). -/
  held : s.held = s.balances.channelTotal
  /-- Each channel status has its origin (`StatusOrigin`). -/
  origin : ∀ c, StatusOrigin apps s c
  /-- Nitro:288-290: a finalized outcome comes from a conclude or from a
      challenge that timed out. Only redistributions follow it. -/
  twoWays : ∀ (c : FixedPart) (Ω : Outcome E), s.finalOutcome c.address = some Ω →
    FinalizedTwoWays apps s c Ω
  /-- Nitro:227-229: a step lowers the coins held only by a redistribution.
      The redistribution pays the fall to one external destination. -/
  heldFalls : ∀ {caller : Participant} {op : Op E} {s' : Adjudicator E},
    s.apply apps caller op = some s' → s'.held < s.held →
    op.isRedistribution = true ∧
    ∃ d : E, s'.balances.get (.external d) = s.balances.get (.external d) + (s.held - s'.held) ∧
      ∀ d', d' ≠ d → s'.balances.get (.external d') = s.balances.get (.external d')
  /-- A redistribution keeps the sum of all balances, and keeps the coins
      held plus the coins paid out. -/
  conserves : ∀ {caller : Participant} {op : Op E} {s' : Adjudicator E},
    op.isRedistribution = true → s.apply apps caller op = some s' →
    s'.balances.total = s.balances.total ∧
    s'.held + s'.balances.paidOutTotal = s.held + s.balances.paidOutTotal

namespace Adjudicator

/-- The invariant from the three facts that carry the induction. -/
theorem inv_of_state {apps : Apps E} {s : Adjudicator E} (hnd : s.balances.KeysNodup)
    (hheld : s.held = s.balances.channelTotal) (ho : ∀ c, StatusOrigin apps s c) :
    s.Inv apps where
  keysNodup := hnd
  held := hheld
  origin := ho
  twoWays c Ω hf := by
    have ho := ho c
    unfold FinalizedTwoWays
    simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
    unfold StatusOrigin at ho
    revert ho hf
    cases s.statusOf c with
    | «open» t => (simp? says simp only [ChannelStatus.finalOutcome_open, reduceCtorEq, apply_conclude, apply_challenge, exists_and_left, forall_const, IsEmpty.forall_iff])
    | challenged t ch =>
      intro hf ho
      simp only [ChannelStatus.finalOutcome_challenged] at hf
      split at hf
      · cases hf
        obtain ⟨s0, s1, caller, proof, hr0, h1, h2⟩ := ho
        exact ⟨s0, s1, caller, hr0, Or.inr ⟨proof, ch.state, h1, by (grind? says grind only), Relation.ReflTransGen.refl⟩⟩
      · cases hf
    | finalized t Ω0 =>
      intro hf ho
      cases hf
      exact ho
  heldFalls {caller op s'} h hlt := by
    cases op with
    | transfer a b =>
      obtain ⟨o, _, x, -, -, hx, hb, hh, -, -⟩ := Adjudicator.transfer_some h
      have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
      have hle := Balances.get_le_sumIf (fun a => decide (a.isExternal = false)) s.balances
        (a := a.address) (by (simp? says simp only [FixedPart.address_eq, Address.isExternal_channel, decide_true]))
      rw [← Balances.channelTotal_eq_sumIf, ← hheld] at hle
      cases b with
      | channel d => (simp? [hh] at hlt says simp only [hh, Address.isExternal_channel, Bool.false_eq_true, ↓reduceIte, lt_self_iff_false] at hlt)
      | external p =>
        refine ⟨rfl, p, ?_, fun q hq => ?_⟩
        · rw [hb, hh]; (simp? says simp only [FixedPart.address_eq, Balances.get_sub, reduceCtorEq, ↓reduceIte, Balances.get_add, Address.isExternal_external, Nat.add_left_cancel_iff]); (grind? says grind only [#299a])
        · rw [hb]; (simp? [hq] says simp only [FixedPart.address_eq, Balances.get_sub, reduceCtorEq, ↓reduceIte, Balances.get_add, Address.external.injEq, hq])
    | deposit a e x => obtain ⟨-, -, -, hh, -, -⟩ := Adjudicator.deposit_some h; (grind? says grind only)
    | _ => exact absurd (Adjudicator.apply_held_frame rfl h) (ne_of_lt hlt)
  conserves {caller op s'} hop h := by
    cases op with
    | transfer a b =>
      obtain ⟨o, _, x, -, -, hx, hb, hh, -, -⟩ := Adjudicator.transfer_some h
      have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
      have hle := Balances.get_le_sumIf (fun a => decide (a.isExternal = false)) s.balances
        (a := a.address) (by (simp? says simp only [FixedPart.address_eq, Address.isExternal_channel, decide_true]))
      rw [← Balances.channelTotal_eq_sumIf, ← hheld] at hle
      have h1 := Balances.sumIf_add_sub (fun _ => true) hnd a.address b hxa
      have h2 := Balances.sumIf_add_sub (fun a => decide (a.isExternal = true)) hnd a.address b hxa
      rw [Balances.total_eq_sumIf, Balances.total_eq_sumIf, Balances.paidOutTotal_eq_sumIf,
        Balances.paidOutTotal_eq_sumIf, hb, hh]
      cases b <;> simp at h1 h2 ⊢ <;> (grind? says grind only)
    | reclaim l v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := Adjudicator.reclaim_some h; (simp? says simp only [FixedPart.address_eq, setStatus_balances, setStatus_held, Nat.add_left_cancel_iff, and_self])
    | _ => (simp? [Op.isRedistribution] at hop says simp only [Op.isRedistribution, Bool.false_eq_true] at hop)

/-- Genesis satisfies the invariant. -/
theorem inv_genesis {apps : Apps E} : (genesis : Adjudicator E).Inv apps :=
  inv_of_state Balances.keysNodup_nil rfl fun _ => by unfold StatusOrigin; exact trivial

/-- Every step from a reachable state keeps the invariant. The status
    origin of a new challenge names the state before the step, so the step
    needs that state's reachability `hr`. -/
theorem inv_step {apps : Apps E} {s s' : Adjudicator E} (hr : Reachable apps s) (hi : s.Inv apps)
    (hs : Step apps s s') : s'.Inv apps := by
  obtain ⟨caller, op, _, _, h⟩ := hs
  have hcore : s'.balances.KeysNodup ∧ s'.held = s'.balances.channelTotal := by
    have hnd := hi.keysNodup
    have hheld := hi.held
    cases op with
    | deposit a e x =>
      obtain ⟨⟨c, rfl, -⟩, -, hb, hh, -, -⟩ := deposit_some h
      refine ⟨hb ▸ hnd.add _ _, ?_⟩
      have := Balances.sumIf_set (fun a => decide (a.isExternal = false)) hnd (.channel c)
        (s.balances.get (.channel c) + x)
      rw [Balances.channelTotal_eq_sumIf] at hheld ⊢
      rw [hh, hb]
      simp only [Balances.add]
      (simp? at this says simp only [Bool.decide_eq_false, Address.isExternal_channel, decide_true, ↓reduceIte] at this)
      (grind only)
    | transfer a b =>
      obtain ⟨o, _, x, -, -, hx, hb, hh, -, -, -, -⟩ := transfer_some h
      have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
      refine ⟨hb ▸ (hnd.add _ _).sub _ _, ?_⟩
      have := Balances.sumIf_add_sub (fun a => decide (a.isExternal = false)) hnd a.address b hxa
      have hle := Balances.get_le_sumIf (fun a => decide (a.isExternal = false)) s.balances
        (a := a.address) (by (simp? says simp only [FixedPart.address_eq, Address.isExternal_channel, decide_true]))
      rw [hh, hb, Balances.channelTotal_eq_sumIf]
      rw [Balances.channelTotal_eq_sumIf] at hheld
      cases b <;> simp at this ⊢ <;> (grind only)
    | reclaim l v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := reclaim_some h; exact ⟨hnd, hheld⟩
    | challenge c proof cand => obtain ⟨_, rfl⟩ := challenge_some h; exact ⟨hnd, hheld⟩
    | checkpoint c proof cand => obtain ⟨_, rfl⟩ := checkpoint_some h; exact ⟨hnd, hheld⟩
    | conclude c ss => obtain ⟨_, rfl⟩ := conclude_some h; exact ⟨hnd, hheld⟩
    | tick dt => (simp? at h says simp only [apply_tick, Option.some.injEq] at h); subst h; exact ⟨hnd, hheld⟩
  refine inv_of_state hcore.1 hcore.2 fun c => ?_
  have hn := apply_now_le h
  rcases statusOf_step h c with
    heq | ⟨o, b, x, hf, heq⟩ | ⟨oL, left, x1, right, x2, rm, hL, heq⟩ |
    ⟨proof, cand, hch, heq⟩ | ⟨proof, cand, hcp, heq⟩ | ⟨ss, hcl, heq⟩
  · exact statusOrigin_of_eq (hi.origin c) heq hn
  · exact statusOrigin_redistribute (hi.origin c) hf
      (Relation.ReflTransGen.single (RedistributeStep.reduce o b x)) hn heq
  · exact statusOrigin_redistribute (hi.origin c) hL
      (Relation.ReflTransGen.single (RedistributeStep.reclaim oL left right rm x1 x2)) hn heq
  · unfold StatusOrigin
    rw [heq]
    exact ⟨s, s', caller, proof, hr, hch, rfl⟩
  · unfold StatusOrigin
    rw [heq]
    trivial
  · unfold StatusOrigin
    rw [heq]
    obtain ⟨⟨-, hp⟩, -⟩ := conclude_some hcl
    exact ⟨s, s', caller, hr, Or.inl ⟨ss, hcl, hp, Relation.ReflTransGen.refl⟩⟩

/-- Every reachable state satisfies the invariant. -/
theorem inv_reachable {apps : Apps E} {s : Adjudicator E} (hr : Reachable apps s) : s.Inv apps := by
  induction hr with
  | refl => exact inv_genesis
  | tail hr' hstep ih => exact inv_step hr' ih hstep

/-- **A deposit's `held` plus everything ever paid out rises by exactly its
    own amount.** `Inv.held` (`held = channelTotal`) at both `s` and `s'`
    (`inv_step`), joined with `total_step_deposit` through
    `total_eq_channelTotal_add_paidOutTotal`. The D10 design decision's own
    conservation fact, chain side: `Reachable.lean`'s
    `Nitro.network_conservation` restates this for a `Network`'s wallets. -/
theorem held_paidOut_step_deposit {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {a : Address E} {e x : Coins} (hr : Reachable apps s)
    (h : s.apply apps caller (Op.deposit a e x) = some s') :
    s'.held + s'.balances.paidOutTotal = s.held + s.balances.paidOutTotal + x := by
  have hi := inv_reachable hr
  have hi' := inv_step hr hi (.mk caller _ s s' h)
  have e1 : s.held + s.balances.paidOutTotal = s.balances.total := by
    rw [hi.held, Balances.total_eq_channelTotal_add_paidOutTotal]
  have e2 : s'.held + s'.balances.paidOutTotal = s'.balances.total := by
    rw [hi'.held, Balances.total_eq_channelTotal_add_paidOutTotal]
  have ht := total_step_deposit hi.keysNodup h
  rw [e2, ht, e1]

/-- **Every non-deposit operation leaves `held` plus everything ever paid
    out unchanged.** Same proof shape as `held_paidOut_step_deposit`. -/
theorem held_paidOut_step_no_deposit {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} (hr : Reachable apps s) (hop : ∀ a e x, op ≠ Op.deposit a e x)
    (h : s.apply apps caller op = some s') :
    s'.held + s'.balances.paidOutTotal = s.held + s.balances.paidOutTotal := by
  have hi := inv_reachable hr
  have hi' := inv_step hr hi (.mk caller _ s s' h)
  have e1 : s.held + s.balances.paidOutTotal = s.balances.total := by
    rw [hi.held, Balances.total_eq_channelTotal_add_paidOutTotal]
  have e2 : s'.held + s'.balances.paidOutTotal = s'.balances.total := by
    rw [hi'.held, Balances.total_eq_channelTotal_add_paidOutTotal]
  have ht := total_step_no_deposit hi.keysNodup hop h
  rw [e2, ht, e1]

end Adjudicator

end ArmadaLean.Nitro
