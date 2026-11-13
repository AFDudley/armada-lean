/-
  Non-vacuity witnesses (`armada-laconic/docs/lean/verification.md` §5a). For
  every theorem of `Safety.lean` and `Liveness.lean` with hypotheses beyond
  its binders' types, one `example` builds concrete values for the binders
  and proves every hypothesis. No example uses the theorem's conclusion.

  The destination type is `Nat`. Theorems with no hypotheses beyond their
  binders' types (no witness needed): `channel_address_ne_external`,
  `balances_total_split`, `deposit_to_external_fails`,
  `payout_bounded`, `paidTo_first_entry_only`, `reduceOwed_owed`,
  `tick_moves_only_time`, `mover_cyclic`, `isOpen_iff`.
-/
import ArmadaLean.Nitro.Liveness
import ArmadaLean.Nitro.TakeOut
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro.NonVacuity

open ArmadaLean.Nitro

/-! ## Shared values -/

def p0 : Participant := ⟨0⟩
def q0 : Participant := ⟨1⟩
/-- A one-participant channel; challenge duration 4. -/
def c1 : FixedPart := ⟨[p0], 0, ⟨0⟩, 4, .ledger⟩
/-- A second one-participant channel. -/
def c3 : FixedPart := ⟨[p0], 3, ⟨0⟩, 4, .ledger⟩
/-- A two-participant channel. -/
def c2 : FixedPart := ⟨[p0, q0], 1, ⟨0⟩, 4, .ledger⟩
def apps0 : Apps Nat := fun _ => consensusRules
def d0 : Address Nat := .external 0
def d1 : Address Nat := .external 1
def o1 : Allocation Nat := [alloc d0 1]
def g0 : Adjudicator Nat := Adjudicator.genesis
/-- No deposits: the genesis wallet for every witness that is not about
    funds (D10 design decision leaves `Nitro.network`'s initial wallet arbitrary;
    `0` reproduces the pre-decision zero-balance behavior these witnesses
    already had). -/
def noDeposits : Participant → Coins := fun _ => 0

/-- The final state of `c1` with outcome `o1`, and its signature by `p0`. -/
def stF : State Nat := ⟨c1, 0, .allocation o1, true, .opaque 0⟩
def ssF : SignedState Nat := ⟨stF, [p0]⟩

/-- genesis → deposit 1 into `c1` → conclude `c1` with `o1` → transfer to `d0`. -/
def sDep : Adjudicator Nat := { balances := [(c1.address, 1)], held := 1, status := [], now := 0 }
def sCon : Adjudicator Nat := sDep.setStatus c1 (.finalized 0 (.allocation o1) (.allocation o1))

theorem g0_dep : g0.apply apps0 p0 (.deposit c1.address 0 1) = some sDep := rfl
theorem sDep_con : sDep.apply apps0 p0 (.conclude c1 ssF) = some sCon := rfl
theorem sDep_reach : Reachable apps0 sDep := .single (.mk _ _ _ _ g0_dep)
theorem sCon_reach : Reachable apps0 sCon := .tail sDep_reach (.mk _ _ _ _ sDep_con)

/-! ## Reclaim values: ledger `cL` guarantees `cV` for `[d0, d1]`. -/

def cL : FixedPart := ⟨[p0], 5, ⟨0⟩, 4, .ledger⟩
def cV : FixedPart := ⟨[p0], 6, ⟨0⟩, 4, .virtual⟩
def oL : Allocation Nat := [alloc d0 0, alloc d1 0, ⟨cV.address, .guarantee 1 [d0, d1]⟩]
def oV : Allocation Nat := [alloc d0 1, alloc d1 0]
def sR : Adjudicator Nat :=
  { balances := [], held := 0,
    status := [(cL, .finalized 0 (.allocation oL) (.allocation oL)),
      (cV, .finalized 0 (.allocation oV) (.allocation oV))], now := 0 }

/-! ## `Safety.lean` -/

/-- `channel_address_inj`. -/
theorem channel_address_inj.nonvacuity : ∃ c c' : FixedPart, (c.address : Address Nat) = c'.address := ⟨c1, c1, rfl⟩

/-- `balances_absent_zero`. -/
theorem balances_absent_zero.nonvacuity : ∃ (b : Balances Nat) (a : Address Nat), ∀ e ∈ b, e.1 ≠ a :=
  ⟨[], d0, fun _ h => absurd h (List.not_mem_nil)⟩

/-- `held_eq_channel_balances`. -/
example : ∃ s : Adjudicator Nat, Reachable apps0 s := ⟨g0, .refl⟩

/-- `deposit_effects`. -/
theorem deposit_effects.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (e x : Coins) (s' : Adjudicator Nat),
    s.deposit c.address e x = some s' := ⟨g0, c1, 0, 1, _, rfl⟩

/-- `deposit_requires_expectedHeld`. -/
theorem deposit_requires_expectedHeld.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (e : Coins), s.balances.get c.address ≠ e :=
  ⟨g0, c1, 1, by decide⟩

/-- `deposit_respects_funding_order`. -/
theorem deposit_respects_funding_order.nonvacuity : ∃ (s s' : Adjudicator Nat) (caller : Participant) (c : FixedPart) (o : Allocation Nat)
    (k : Nat) (e : Entry Nat), Reachable apps0 s ∧ o.dedup = o ∧ o[k]? = some e ∧
    s.apply apps0 caller (.deposit c.address (o.aheadOf k) e.amount) = some s' :=
  ⟨g0, sDep, p0, c1, o1, 0, alloc d0 1, .refl, by decide, by decide, rfl⟩

/-- `deposit_can_happen`. -/
theorem deposit_can_happen.nonvacuity : ∃ (c : FixedPart), c.kind = .ledger := ⟨c1, by decide⟩

/-- `deposits_in_order_succeed`. -/
theorem deposits_in_order_succeed.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart), c.kind = .ledger ∧
    s.balances.get c.address = 0 :=
  ⟨g0, c1, by decide, by decide⟩

/-- `held_falls_only_by_payout`. -/
theorem held_falls_only_by_payout.nonvacuity : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat),
    Reachable apps0 s ∧ s.apply apps0 caller op = some s' ∧ s'.held < s.held :=
  ⟨sCon, _, p0, .transfer c1 d0, sCon_reach, rfl, by decide⟩

/-- `channel_balance_falls_only_by_redistribution`. -/
theorem channel_balance_falls_only_by_redistribution.nonvacuity : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat) (c : FixedPart),
    s.apply apps0 caller op = some s' ∧ s'.balances.get c.address < s.balances.get c.address :=
  ⟨sCon, _, p0, .transfer c1 d0, c1, rfl, by decide⟩

/-- `paid_out_monotone`. -/
theorem paid_out_monotone.nonvacuity : ∃ s s' : Adjudicator Nat, Step apps0 s s' := ⟨g0, sDep, .mk _ _ _ _ g0_dep⟩

/-- `payout_priority_formula`. -/
theorem payout_priority_formula.nonvacuity : ∃ (o : Allocation Nat) (k : Nat) (e : Entry Nat), o[k]? = some e :=
  ⟨o1, 0, alloc d0 1, by decide⟩

/-- `payout_earlier_paid_in_full`. -/
theorem payout_earlier_paid_in_full.nonvacuity : ∃ (held : Coins) (o : Allocation Nat) (i j : Nat) (ei ej : Entry Nat) (pi pj : Coins),
    o[i]? = some ei ∧ o[j]? = some ej ∧ i < j ∧ (o.payout held)[i]? = some (ei.dest, pi) ∧
    (o.payout held)[j]? = some (ej.dest, pj) ∧ 0 < pj :=
  ⟨2, [alloc d0 1, alloc d1 1], 0, 1, alloc d0 1, alloc d1 1, 1, 1, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- `affords_when_fully_funded`. -/
theorem affords_when_fully_funded.nonvacuity : ∃ (held : Coins) (o : Allocation Nat), o.total ≤ held := ⟨1, o1, by decide⟩

/-- `transfer_effects`. -/
theorem transfer_effects.nonvacuity : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (s' : Adjudicator Nat),
    Reachable apps0 s ∧ s.transfer a b = some s' := ⟨sCon, c1, d0, _, sCon_reach, rfl⟩

/-- `transfer_can_happen`. -/
theorem transfer_can_happen.nonvacuity : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (o : Allocation Nat) (amt : Coins),
    a.kind = .ledger ∧ b.fundable = true ∧
    s.finalOutcome a.address = some (.allocation o) ∧ o.find b = some ⟨b, .alloc amt⟩ :=
  ⟨sCon, c1, d0, o1, 1, by decide, by decide, by decide, by decide⟩

/-- `transfer_fails_otherwise`. -/
theorem transfer_fails_otherwise.nonvacuity : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat),
    ∀ o, s.finalOutcome a.address = some (.allocation o) → ∀ amt, o.find b ≠ some ⟨b, .alloc amt⟩ :=
  ⟨g0, c1, d0, fun o h => by (simp? [g0, Adjudicator.genesis, Adjudicator.statusOf] at h says simp only [g0, Adjudicator.genesis, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf, List.lookup_nil, Option.getD_none, ChannelStatus.finalOutcome_open, reduceCtorEq] at h)⟩

/-- `transfer_zero_moves_nothing`. -/
theorem transfer_zero_moves_nothing.nonvacuity : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (s' : Adjudicator Nat),
    s.transfer a b = some s' ∧
    ∀ o, s.finalOutcome a.address = some (.allocation o) → o.paidTo (s.balances.get a.address) b = 0 :=
  ⟨sCon.setStatus c1 (.finalized 0 (.allocation [alloc d0 0]) (.allocation [alloc d0 0])), c1, d0, _,
    rfl, fun o h => by
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus,
        if_true, ChannelStatus.finalOutcome_finalized, Option.some.injEq, Outcome.allocation.injEq] at h
      subst h; decide⟩

/-- `transfer_requires_finalized`. -/
theorem transfer_requires_finalized.nonvacuity : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (s' : Adjudicator Nat),
    s.transfer a b = some s' := ⟨sCon, c1, d0, _, rfl⟩

/-- `redistribution_ignores_caller`. -/
theorem redistribution_ignores_caller.nonvacuity : ∃ op : Op Nat, op.isRedistribution = true := ⟨.transfer c1 d0, rfl⟩

/-- `redistribution_conserves_total`. -/
theorem redistribution_conserves_total.nonvacuity : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat),
    Reachable apps0 s ∧ op.isRedistribution = true ∧ s.apply apps0 caller op = some s' :=
  ⟨sCon, _, p0, .transfer c1 d0, sCon_reach, rfl, rfl⟩

/-- `FinalizedTwoWays.mono`. -/
theorem redistribution_conserves_total.nonvacuity_2 : ∃ (s s' : Adjudicator Nat) (c : FixedPart) (Ω Ω' : Outcome Nat),
    FinalizedTwoWays apps0 s c Ω ∧ s.now ≤ s'.now ∧ Redistributed Ω Ω' :=
  ⟨sCon, sCon, c1, _, _, ⟨sDep, sCon, p0, sDep_reach, .inl ⟨ssF, sDep_con, by decide, .refl⟩⟩,
    le_rfl, .refl⟩

/-- `statusOrigin_of_eq`. -/
theorem redistribution_conserves_total.nonvacuity_3 : ∃ (s s' : Adjudicator Nat) (c : FixedPart),
    StatusOrigin apps0 s c ∧ s'.statusOf c = s.statusOf c ∧ s.now ≤ s'.now :=
  ⟨g0, g0, c1, trivial, rfl, le_rfl⟩

/-- `statusOrigin_redistribute`. -/
theorem redistribution_conserves_total.nonvacuity_4 : ∃ (s s' : Adjudicator Nat) (c : FixedPart) (Ω Ω' : Outcome Nat),
    StatusOrigin apps0 s c ∧ (s.statusOf c).finalOutcome s.now = some Ω ∧ Redistributed Ω Ω' ∧
    s.now ≤ s'.now ∧ s'.statusOf c = (s.statusOf c).withOutcome Ω' :=
  ⟨sCon, sCon, c1, _, _, ⟨sDep, sCon, p0, sDep_reach, .inl ⟨ssF, sDep_con, by decide, .refl⟩⟩,
    rfl, .refl, le_rfl, rfl⟩

/-- `Adjudicator.inv_step`. -/
theorem redistribution_conserves_total.nonvacuity_5 : ∃ s s' : Adjudicator Nat,
    Reachable apps0 s ∧ s.Inv apps0 ∧ Step apps0 s s' :=
  ⟨g0, sDep, .refl, Adjudicator.inv_genesis, .mk p0 _ _ _ g0_dep⟩

/-- `Adjudicator.inv_reachable`. -/
theorem redistribution_conserves_total.nonvacuity_6 : ∃ s : Adjudicator Nat, Reachable apps0 s := ⟨g0, .refl⟩

/-- `finalized_two_ways`. -/
theorem finalized_two_ways.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (Ω : Outcome Nat),
    Reachable apps0 s ∧ s.finalOutcome c.address = some Ω := ⟨sCon, c1, _, sCon_reach, rfl⟩

/-- `finalized_permanent`. -/
theorem finalized_permanent.nonvacuity : ∃ (s s' : Adjudicator Nat) (c : FixedPart), Step apps0 s s' ∧ s.mode c = .finalized :=
  ⟨sCon, _, c1, .mk p0 (.tick 1) _ _ rfl, by decide⟩

/-- `finalized_outcome_only_redistributed`. -/
theorem finalized_outcome_only_redistributed.nonvacuity : ∃ (s s' : Adjudicator Nat) (c : FixedPart) (Ω : Outcome Nat),
    Step apps0 s s' ∧ s.finalOutcome c.address = some Ω :=
  ⟨sCon, _, c1, _, .mk p0 (.tick 1) _ _ rfl, rfl⟩

/-- A challenge of the open channel `c1` with the state `stO` signed by `p0`. -/
def stO : State Nat := ⟨c1, 1, .allocation o1, false, .opaque 0⟩
def ssO : SignedState Nat := ⟨stO, [p0]⟩

/-- `challenge_requires`. -/
theorem challenge_requires.nonvacuity : ∃ (s : Adjudicator Nat) (challenger : Participant) (c : FixedPart)
    (proof : SupportProof Nat) (candidate : State Nat) (s' : Adjudicator Nat),
    s.challenge apps0 challenger c proof candidate = some s' := ⟨g0, p0, c1, [ssO], stO, _, rfl⟩

/-- `challenge_fails_when_finalized`. -/
theorem challenge_fails_when_finalized.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart), s.mode c = .finalized := ⟨sCon, c1, by decide⟩

/-- The status of `c1` after the challenge with `stO`. -/
def sCh : Adjudicator Nat := g0.setStatus c1 (.challenged 1 ⟨stO, 4⟩)

/-- `rechallenge_equal_turn_fails`. -/
theorem rechallenge_equal_turn_fails.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (candidate : State Nat),
    s.mode c = .challenge ∧ candidate.turnNum ≤ (s.statusOf c).turnNumRecord :=
  ⟨sCh, c1, stO, by decide, by decide⟩

/-- `challenge_can_happen`. -/
theorem challenge_can_happen.nonvacuity : ∃ (s : Adjudicator Nat) (challenger : Participant) (c : FixedPart)
    (proof : SupportProof Nat) (candidate : State Nat),
    challenger ∈ c.participants ∧ (apps0 c.appDef).supports c proof candidate = true ∧
    candidate.channel = c ∧
    ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
     (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum)) :=
  ⟨g0, p0, c1, [ssO], stO, by decide, by decide, rfl, .inl ⟨by decide, by decide⟩⟩

/-- `challenge_effects`. -/
theorem challenge_effects.nonvacuity : ∃ (s : Adjudicator Nat) (challenger : Participant) (c : FixedPart)
    (proof : SupportProof Nat) (candidate : State Nat) (s' : Adjudicator Nat),
    s.challenge apps0 challenger c proof candidate = some s' ∧ 0 < c.challengeDuration :=
  ⟨g0, p0, c1, [ssO], stO, _, rfl, by decide⟩

/-- `checkpoint_requires`. -/
theorem checkpoint_requires.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (proof : SupportProof Nat) (candidate : State Nat)
    (s' : Adjudicator Nat), s.checkpoint apps0 c proof candidate = some s' :=
  ⟨g0, c1, [ssO], stO, _, rfl⟩

/-- `checkpoint_can_happen`. -/
theorem checkpoint_can_happen.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (proof : SupportProof Nat) (candidate : State Nat),
    s.mode c ≠ .finalized ∧ (apps0 c.appDef).supports c proof candidate = true ∧
    candidate.channel = c ∧ (s.statusOf c).turnNumRecord < candidate.turnNum :=
  ⟨g0, c1, [ssO], stO, by decide, by decide, rfl, by decide⟩

/-- `turnNumRecord_monotone`. -/
theorem turnNumRecord_monotone.nonvacuity : ∃ s s' : Adjudicator Nat, Step apps0 s s' := ⟨g0, sDep, .mk _ _ _ _ g0_dep⟩

/-- `conclude_requires`. -/
theorem conclude_requires.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat) (s' : Adjudicator Nat),
    s.conclude c ss = some s' := ⟨sDep, c1, ssF, _, rfl⟩

/-- `conclude_needs_all`. -/
theorem conclude_needs_all.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat) (s' : Adjudicator Nat)
    (p : Participant), s.conclude c ss = some s' ∧ p ∈ c.participants :=
  ⟨sDep, c1, ssF, _, p0, rfl, by decide⟩

/-- `conclude_can_happen`. -/
theorem conclude_can_happen.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat),
    s.mode c ≠ .finalized ∧ ConclusionProof c ss := ⟨sDep, c1, ssF, by decide, by decide⟩

/-- `conclude_moves_no_value`. -/
theorem conclude_moves_no_value.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat) (s' : Adjudicator Nat),
    s.conclude c ss = some s' := ⟨sDep, c1, ssF, _, rfl⟩

/-- `timeout_finalizes`. -/
theorem timeout_finalizes.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (t : Nat) (ch : Challenge Nat),
    s.statusOf c = .challenged t ch ∧ ch.deadline ≤ s.now :=
  ⟨sCh.tick 4, c1, 1, ⟨stO, 4⟩, by decide, by decide⟩

/-- `challenge_in_progress_before_deadline`. -/
theorem challenge_in_progress_before_deadline.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart) (t : Nat) (ch : Challenge Nat),
    s.statusOf c = .challenged t ch ∧ s.now < ch.deadline :=
  ⟨sCh, c1, 1, ⟨stO, 4⟩, by decide, by decide⟩

/-- `failed_op_no_effect`. -/
theorem failed_op_no_effect.nonvacuity : ∃ (caller : Participant) (op : Op Nat) (s : Adjudicator Nat),
    s.apply apps0 caller op = none := ⟨p0, .transfer c1 d0, g0, rfl⟩

/-- `funding_decoupled_from_rules`. -/
theorem funding_decoupled_from_rules.nonvacuity : ∃ op : Op Nat, op.isRedistribution = false ∧ ∀ a e x, op ≠ .deposit a e x :=
  ⟨.tick 0, rfl, fun _ _ _ h => by cases h⟩

/-- A ForceMove run of one state for `c1` (one participant). -/
def vtAll : State Nat → State Nat → Bool := fun s1 s2 => decide (s2.outcome = s1.outcome)

/-- `forceMove_supports_valid_run`. -/
theorem forceMove_supports_valid_run.nonvacuity : ∃ (vt : State Nat → State Nat → Bool) (c : FixedPart) (proof : SupportProof Nat)
    (candidate : State Nat), (forceMoveRules vt).supports c proof candidate = true :=
  ⟨vtAll, c1, [⟨stO, [p0]⟩], stO, by decide⟩

/-- `forceMove_conclude_keeps_outcome`: two moves in the two-party channel
    `c2`, the first by `p0` at turn 0, the second by `q0` at turn 1. -/
def stM0 : State Nat := ⟨c2, 0, .allocation o1, false, .opaque 0⟩
def stM1 : State Nat := ⟨c2, 1, .allocation o1, false, .opaque 0⟩

theorem forceMove_conclude_keeps_outcome.nonvacuity : ∃ (vt : State Nat → State Nat → Bool) (c : FixedPart) (proof : SupportProof Nat)
    (candidate : State Nat) (i : Nat) (m1 m2 : SignedState Nat),
    (forceMoveRules vt).supports c proof candidate = true ∧ proof[i]? = some m1 ∧
    proof[i + 1]? = some m2 :=
  ⟨vtAll, c2, [⟨stM0, [p0]⟩, ⟨stM1, [q0]⟩], stM1, 0, ⟨stM0, [p0]⟩, ⟨stM1, [q0]⟩,
    by decide, by decide, by decide⟩

/-- `mover_determined_by_turn`. -/
theorem mover_determined_by_turn.nonvacuity : ∃ s t : State Nat, s.channel = t.channel ∧ s.turnNum = t.turnNum := ⟨stO, stO, rfl, rfl⟩

/-- `reclaim_requires`. -/
theorem reclaim_requires.nonvacuity : ∃ (s : Adjudicator Nat) (l v : FixedPart) (s' : Adjudicator Nat),
    s.reclaim l v = some s' := ⟨sR, cL, cV, _, rfl⟩

/-- `reclaim_effects`. -/
theorem reclaim_effects.nonvacuity : ∃ (s : Adjudicator Nat) (l v : FixedPart) (s' : Adjudicator Nat) (oL oV : Allocation Nat)
    (x : Coins) (left right : Address Nat),
    s.finalOutcome l.address = some (.allocation oL) ∧
    s.finalizedWith v.address = some (.allocation oV) ∧
    oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧ left ≠ right ∧
    left ≠ v.address ∧ right ≠ v.address ∧ l ≠ v ∧ oL.dedup = oL ∧ s.reclaim l v = some s' :=
  ⟨sR, cL, cV, _, oL, oV, 1, d0, d1, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, rfl⟩

/-- `reclaim_can_happen`. -/
theorem reclaim_can_happen.nonvacuity : ∃ (s : Adjudicator Nat) (l v : FixedPart) (oL oV : Allocation Nat) (x : Coins)
    (left right : Address Nat),
    l.kind = .ledger ∧ v.kind = .virtual ∧
    s.finalOutcome l.address = some (.allocation oL) ∧
    s.finalizedWith v.address = some (.allocation oV) ∧
    oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧
    (oL.remove v.address).find left ≠ none ∧ (oL.remove v.address).find right ≠ none ∧
    oV.amountAt 0 + oV.amountAt 1 = x :=
  ⟨sR, cL, cV, oL, oV, 1, d0, d1, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- `reclaim_fails_without_entries`: the target's amounts sum to 1, the
    guarantee says 2. -/
def oL2 : Allocation Nat := [alloc d0 0, alloc d1 0, ⟨cV.address, .guarantee 2 [d0, d1]⟩]
def sR2 : Adjudicator Nat :=
  { sR with status := [(cL, .finalized 0 (.allocation oL2) (.allocation oL2)),
      (cV, .finalized 0 (.allocation oV) (.allocation oV))] }

theorem reclaim_fails_without_entries.nonvacuity : ∃ (s : Adjudicator Nat) (l v : FixedPart) (oL oV : Allocation Nat) (x : Coins)
    (left right : Address Nat),
    s.finalOutcome l.address = some (.allocation oL) ∧
    s.finalizedWith v.address = some (.allocation oV) ∧
    oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧
    ((oL.remove v.address).find left = none ∨ (oL.remove v.address).find right = none ∨
      oV.amountAt 0 + oV.amountAt 1 ≠ x) :=
  ⟨sR2, cL, cV, oL2, oV, 2, d0, d1, by decide, by decide, by decide, by decide⟩

/-- `mode_of_absent`. -/
theorem mode_of_absent.nonvacuity : ∃ (s : Adjudicator Nat) (c : FixedPart), ∀ e ∈ s.status, e.1 ≠ c :=
  ⟨g0, c1, fun _ h => absurd h List.not_mem_nil⟩

/-- `held_changes_only_by_deposit_payout`. -/
theorem held_changes_only_by_deposit_payout.nonvacuity : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat),
    s.apply apps0 caller op = some s' ∧ s'.held ≠ s.held :=
  ⟨g0, sDep, p0, _, g0_dep, by decide⟩

/-! ## Chain facts used by the strategies below -/

section Chain

variable {E : Type} [DecidableEq E]

/-- The channel an operation writes. -/
def opOn : Op E → FixedPart → Prop
  | .transfer a _, c => a = c
  | .reclaim l _, c => l = c
  | .challenge c' _ _, c => c' = c
  | .checkpoint c' _ _, c => c' = c
  | .conclude c' _, c => c' = c
  | _, _ => False

/-- An operation on another channel keeps the status of `c`. -/
theorem statusOf_apply_of_not_on {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') {c : FixedPart}
    (hc : ¬ opOn op c) : s'.statusOf c = s.statusOf c := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
    exact Adjudicator.statusOf_of_status hs c
  | tick dt => (simp? at h says simp only [Adjudicator.apply_tick, Option.some.injEq] at h); subst h; rfl
  | transfer a b =>
    obtain ⟨_, _, _, -, -, -, -, -, hs, -⟩ := Adjudicator.transfer_some h
    rw [Adjudicator.statusOf_of_status hs]
    simp only [Adjudicator.statusOf_setStatus, opOn] at hc ⊢
    rw [if_neg (Ne.symm hc)]
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := Adjudicator.reclaim_some h
    simp only [Adjudicator.statusOf_setStatus, opOn] at hc ⊢
    rw [if_neg (Ne.symm hc)]
  | challenge c' proof cand =>
    obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
    simp only [Adjudicator.statusOf_setStatus, opOn] at hc ⊢
    rw [if_neg (Ne.symm hc)]
  | checkpoint c' proof cand =>
    obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
    simp only [Adjudicator.statusOf_setStatus, opOn] at hc ⊢
    rw [if_neg (Ne.symm hc)]
  | conclude c' ss =>
    obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
    simp only [Adjudicator.statusOf_setStatus, opOn] at hc ⊢
    rw [if_neg (Ne.symm hc)]

end Chain

/-! ## Game facts used by the strategies below -/

section Game

variable {E : Type} [DecidableEq E]

/-- The chain part of the invariant of `conclude_strategy`. -/
def ConcludeInv (c : FixedPart) (Ω : Outcome E) (t1 : Time) (s : Adjudicator E) : Prop :=
  s.finalizedWith c.address = some Ω ∨ (∃ t, s.statusOf c = .open t) ∨
    (∃ t ch, s.statusOf c = .challenged t ch ∧ t1 ≤ ch.deadline)

theorem concludeInv_apply {apps : Apps E} {caller p : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') {c : FixedPart} {Ω : Outcome E}
    {t0 ε : Time} (sent : List (SignedState E)) (hp : p ∈ c.participants)
    (hU : ∀ ss ∈ op.proofStates, p ∈ ss.signers → ∃ x ∈ sent, x.state = ss.state)
    (hsent : ∀ t ∈ sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hdur : ε ≤ c.challengeDuration) (ht0 : t0 ≤ s.now) (hlt : s'.now < t0 + ε)
    (hk : ConcludeInv c Ω (t0 + ε) s) : ConcludeInv c Ω (t0 + ε) s' := by
  have hnow := Adjudicator.apply_now_le h
  rcases hk with hf | ho | hc
  · exact .inl (Adjudicator.finalizedWith_apply h hf)
  · by_cases hon : opOn op c
    · obtain ⟨t, ht⟩ := ho
      cases op with
      | deposit a e x => exact absurd hon id
      | tick dt => exact absurd hon id
      | transfer a b =>
        simp only [opOn] at hon; subst a
        obtain ⟨o, _, _, hfo, -⟩ := Adjudicator.transfer_some h
        (simp? [ht] at hfo says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ht, ChannelStatus.finalOutcome_open, reduceCtorEq] at hfo)
      | reclaim l v =>
        simp only [opOn] at hon; subst l
        obtain ⟨_, _, _, _, _, hL, -⟩ := Adjudicator.reclaim_some h
        (simp? [ht] at hL says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ht, ChannelStatus.finalOutcome_open, reduceCtorEq] at hL)
      | challenge c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        refine .inr (.inr ⟨cand.turnNum, ⟨cand, s.now + c.challengeDuration⟩, by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte]), ?_⟩)
        show t0 + ε ≤ s.now + c.challengeDuration
        exact Nat.add_le_add ht0 hdur
      | checkpoint c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        exact .inr (.inl ⟨cand.turnNum, by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])⟩)
      | conclude c' ss' =>
        simp only [opOn] at hon; subst c'
        obtain ⟨⟨-, hch, hfin, hall⟩, rfl⟩ := Adjudicator.conclude_some h
        obtain ⟨x, hx, hst⟩ := hU ss' (List.mem_singleton_self _) (hall p (hch ▸ hp))
        have := hsent x hx (by rw [hst]; exact hch) (by rw [hst]; exact hfin)
        rw [hst] at this
        exact .inl (by (simp? [this] says simp only [this, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized]))
    · exact .inr (.inl (by rw [statusOf_apply_of_not_on h hon]; exact ho))
  · by_cases hon : opOn op c
    · obtain ⟨t, ch, ht, hd⟩ := hc
      have hnexp : ¬ ch.deadline ≤ s.now := fun h' =>
        absurd (lt_of_le_of_lt (le_trans (le_trans hd h') hnow) hlt) (lt_irrefl _)
      cases op with
      | deposit a e x => exact absurd hon id
      | tick dt => exact absurd hon id
      | transfer a b =>
        simp only [opOn] at hon; subst a
        obtain ⟨o, _, _, hfo, -⟩ := Adjudicator.transfer_some h
        (simp? [ht, hnexp] at hfo says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ht, ChannelStatus.finalOutcome_challenged, hnexp, ↓reduceIte, reduceCtorEq] at hfo)
      | reclaim l v =>
        simp only [opOn] at hon; subst l
        obtain ⟨_, _, _, _, _, hL, -⟩ := Adjudicator.reclaim_some h
        (simp? [ht, hnexp] at hL says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ht, ChannelStatus.finalOutcome_challenged, hnexp, ↓reduceIte, reduceCtorEq] at hL)
      | challenge c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        refine .inr (.inr ⟨cand.turnNum, ⟨cand, s.now + c.challengeDuration⟩, by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte]), ?_⟩)
        show t0 + ε ≤ s.now + c.challengeDuration
        exact Nat.add_le_add ht0 hdur
      | checkpoint c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        exact .inr (.inl ⟨cand.turnNum, by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])⟩)
      | conclude c' ss' =>
        simp only [opOn] at hon; subst c'
        obtain ⟨⟨-, hch, hfin, hall⟩, rfl⟩ := Adjudicator.conclude_some h
        obtain ⟨x, hx, hst⟩ := hU ss' (List.mem_singleton_self _) (hall p (hch ▸ hp))
        have := hsent x hx (by rw [hst]; exact hch) (by rw [hst]; exact hfin)
        rw [hst] at this
        exact .inl (by (simp? [this] says simp only [this, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized]))
    · exact .inr (.inr (by rw [statusOf_apply_of_not_on h hon]; exact hc))

/-- One round's worth of adversary/land play, for a reaction whose only pending
    call is `conclude c ss`, carries `ConcludeInv` forward (reusing
    `concludeInv_apply` for every ordinary adversary step) and resolves it
    deterministically at the landing step (`conclude_can_happen`, since a
    known `ConclusionProof` needs no `Bounds.unforgeable` detour: `op` is
    `p`'s own known call, not a claim that could be forged). -/
theorem concludeRound {apps : Apps E} {p : Participant} {T : Threat E p}
    (B : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω : Outcome E}
    (hp : p ∈ c.participants) (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω)
    (hdur : T.ε ≤ c.challengeDuration) (t : Time) (sent0 : List (SignedState E))
    {net net' : NetworkState E p} (hseq : Threat.RoundSeq apps T t [Op.conclude c ss] net net')
    (ht0 : t ≤ net.chain.now) (hsent0 : net.sent = sent0) :
    net'.chain.now < t + T.ε →
    (∀ t0 ∈ sent0, t0.state.channel = c → t0.state.isFinal = true → t0.state.outcome = Ω) →
    ConcludeInv c Ω (t + T.ε) net.chain →
    net'.chain.finalizedWith c.address = some Ω := by
  generalize heq : ([Op.conclude c ss] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => cases heq
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    cases heq
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨hopeq, -⟩ := hsplit
        subst hopeq
        intro hεbound hsent hk
        have hn1 : net1.chain.now < t + T.ε :=
          lt_of_le_of_lt
            (le_trans (NetworkState.applyAdv_now_le apps net1 (.land (Op.conclude c ss)))
              hrest.now_le)
            hεbound
        have hland : (net1.applyAdv apps (AdvMove.land (Op.conclude c ss))).chain.finalizedWith
            c.address = some Ω := by
          rcases hk with hf | ⟨t1, ho⟩ | ⟨t1, ch, ht1, hd⟩
          · cases hop : net1.chain.apply apps p (Op.conclude c ss) with
            | none => (simpa? [NetworkState.applyAdv_land_none apps hop] using hf says simpa only [NetworkState.applyAdv_land_none apps hop, FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
            | some s' => (simpa? [NetworkState.applyAdv_land_some apps hop] using Adjudicator.finalizedWith_apply hop hf says simpa only [NetworkState.applyAdv_land_some apps hop, FixedPart.address_eq, Adjudicator.finalizedWith_channel] using Adjudicator.finalizedWith_apply hop hf)
          · have hm : net1.chain.mode c ≠ .finalized := by rw [Adjudicator.mode_eq, ho]; (simp? says simp only [ChannelStatus.mode_open, ne_eq, reduceCtorEq, not_false_eq_true])
            have hop : net1.chain.apply apps p (Op.conclude c ss) =
                some (net1.chain.setStatus c
                  (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)) := by
              rw [Adjudicator.apply_conclude]; exact (conclude_can_happen _ _ _ hm hproof).1
            simp only [NetworkState.applyAdv_land_some apps hop]
            (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
              Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_finalized, hΩ] says simp only [hΩ, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized])
          · have hm : net1.chain.mode c ≠ .finalized := by
              rw [Adjudicator.mode_eq, ht1]
              simp only [ChannelStatus.mode_challenged, ne_eq]
              split
              · rename_i h'
                exact absurd (lt_of_le_of_lt (le_trans hd h') hn1) (lt_irrefl _)
              · (simp? says simp only [reduceCtorEq, not_false_eq_true])
            have hop : net1.chain.apply apps p (Op.conclude c ss) =
                some (net1.chain.setStatus c
                  (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)) := by
              rw [Adjudicator.apply_conclude]; exact (conclude_can_happen _ _ _ hm hproof).1
            simp only [NetworkState.applyAdv_land_some apps hop]
            (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
              Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_finalized, hΩ] says simp only [hΩ, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized])
        exact hrest.finalizedWith_mono hland
      · (simp? at hsplit says simp only [List.nil_append, List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at hsplit)
    · (simp? at hsplit says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hsent hk
    have ht0' : t ≤ (net1.applyAdv apps (AdvMove.tick dt)).chain.now :=
      le_trans ht0 (NetworkState.applyAdv_now_le apps net1 (.tick dt))
    have hsent0' : (net1.applyAdv apps (AdvMove.tick dt)).sent = sent0 := by
      rw [NetworkState.applyAdv_sent]; exact hsent0
    have happ : net1.chain.apply apps p (.tick dt) = some (net1.chain.tick dt) := rfl
    have hlt1 : (net1.chain.tick dt).now < t + T.ε :=
      lt_of_le_of_lt hrest.now_le hεbound
    have hk' : ConcludeInv c Ω (t + T.ε) (net1.applyAdv apps (AdvMove.tick dt)).chain := by
      show ConcludeInv c Ω (t + T.ε) (net1.chain.tick dt)
      exact concludeInv_apply happ sent0 hp (by (simp? [Op.proofStates] says simp only [Op.proofStates, List.not_mem_nil, IsEmpty.forall_iff, implies_true])) hsent hdur ht0 hlt1 hk
    exact ih ht0' hsent0' heq hεbound hsent hk'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hsent hk
    have ht0' : t ≤ (net1.applyAdv apps m).chain.now :=
      le_trans ht0 (NetworkState.applyAdv_now_le apps net1 m)
    have hsent0' : (net1.applyAdv apps m).sent = sent0 := by
      rw [NetworkState.applyAdv_sent]; exact hsent0
    have hk' : ConcludeInv c Ω (t + T.ε) (net1.applyAdv apps m).chain := by
      cases m with
      | deliver ss' => exact hk
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | chain caller op =>
        cases happ : net1.chain.apply apps caller op with
        | none =>
          simp only [NetworkState.applyAdv_chain_none apps happ]
          exact hk
        | some s' =>
          have hlt1 : s'.now < t + T.ε := by
            have := hrest.now_le
            (simpa? [NetworkState.applyAdv_chain_some apps happ] using lt_of_le_of_lt this hεbound says simpa only [gt_iff_lt, NetworkState.applyAdv_chain_some apps happ] using lt_of_le_of_lt this hεbound)
          simp only [NetworkState.applyAdv_chain_some apps happ]
          exact concludeInv_apply happ sent0 hp
            (fun ss' hss' hp' => hsent0 ▸ (B.unforgeable net1 caller op hfeas ss' hss').1 hp')
            hsent hdur ht0 hlt1 hk
    exact ih ht0' hsent0' heq hεbound hsent hk'

/-- The strategy "conclude now". The adversary cannot finalize another
    outcome before the conclude lands: a conclude needs a final state `p`
    signed, and no challenge ends within `ε`. -/
theorem conclude_strategy (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (allowed : HonestMove E → Prop) (net : NetworkState E p)
    (c : FixedPart) (ss : SignedState E) (Ω : Outcome E)
    (hal : allowed (.chain (.conclude c ss))) (hp : p ∈ c.participants) (hh : net.Holds ss)
    (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hchain : net.chain.finalizedWith c.address = none ∨ net.Finalized c Ω)
    (hdur : T.ε ≤ c.challengeDuration) (hpend : net.DeadlineAfter c T.ε) :
    UnbeatableIn apps T allowed (fun n => n.Finalized c Ω) net := by
  have hK0 : ConcludeInv c Ω (net.chain.now + T.ε) net.chain := by
    rcases hchain with hn | hn
    · simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hn
      cases hs : net.chain.statusOf c with
      | «open» t => exact .inr (.inl ⟨t, hs⟩)
      | challenged t ch => exact .inr (.inr ⟨t, ch, hs, hpend t ch hs⟩)
      | finalized t f o => rw [hs] at hn; (simp? at hn says simp only [ChannelStatus.finalizedWith_finalized, reduceCtorEq] at hn)
    · exact .inl hn
  refine .move (.chain (.conclude c ss)) hal
    (by (simpa? [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh says simpa only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hh)) ?_
  intro n' hround
  apply UnbeatableIn.done
  show (n'.applyHonest (.chain (.conclude c ss))).Finalized c Ω
  rw [NetworkState.applyHonest_chain]
  show n'.chain.finalizedWith c.address = some Ω
  obtain ⟨hseq, htime⟩ := hround
  simp only [HonestMove.calls_chain] at hseq
  exact concludeRound B hp hproof hΩ hdur net.chain.now net.sent hseq (le_refl _) rfl htime hsent
    hK0

/-- Appending one more `RoundSeq` derivation (from whatever state the first
    one ends at) onto the first: the round's own `pending` is unaffected by
    what plays out after it closes. -/
theorem Threat.RoundSeq.append {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net1 net2 : NetworkState E p}
    (h1 : Threat.RoundSeq apps T t pending net net1)
    (h2 : Threat.RoundSeq apps T t [] net1 net2) :
    Threat.RoundSeq apps T t pending net net2 := by
  induction h1 with
  | nil => exact h2
  | land hsplit _ ih => exact Threat.RoundSeq.land hsplit (ih h2)
  | tick hfeas hgate _ ih => exact Threat.RoundSeq.tick hfeas hgate (ih h2)
  | other hfeas hnotick hnoland _ ih => exact Threat.RoundSeq.other hfeas hnotick hnoland (ih h2)

/-- The outcome of finalization survives every adversary move. -/
theorem finalizedWith_applyAdv (apps : Apps E) {p : Participant} (m : AdvMove E)
    (n : NetworkState E p) {c : FixedPart} {f : Outcome E}
    (hf : n.chain.finalizedWith c.address = some f) :
    (n.applyAdv apps m).chain.finalizedWith c.address = some f := by
  cases m with
  | chain caller op =>
    cases happ : n.chain.apply apps caller op with
    | none =>
      simp only [NetworkState.applyAdv_chain_none apps happ]
      exact hf
    | some s' =>
      simp only [NetworkState.applyAdv_chain_some apps happ]
      exact Adjudicator.finalizedWith_apply happ hf
  | deliver ss => exact hf
  | tick dt => exact Adjudicator.finalizedWith_apply (show n.chain.apply apps p (.tick dt) = _ from rfl) hf
  | land op =>
    cases happ : n.chain.apply apps p op with
    | none =>
      simp only [NetworkState.applyAdv_land_none apps happ]
      exact hf
    | some s' =>
      simp only [NetworkState.applyAdv_land_some apps happ]
      exact Adjudicator.finalizedWith_apply happ hf

/-- The outcome of finalization survives every honest move: a reaction never
    touches the chain (`NetworkState.applyHonest`'s `.react` case only
    writes `sent`), and `wait` only ticks. -/
theorem finalizedWith_applyHonest (apps : Apps E) {p : Participant} (m : HonestMove E)
    (n : NetworkState E p) {c : FixedPart} {f : Outcome E}
    (hf : n.chain.finalizedWith c.address = some f) :
    (n.applyHonest m).chain.finalizedWith c.address = some f := by
  cases m with
  | react r => (simpa? [NetworkState.applyHonest] using hf says simpa only [NetworkState.applyHonest, FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
  | wait dt => exact Adjudicator.finalizedWith_apply (show n.chain.apply apps p (.tick dt) = _ from rfl) hf

/-- A channel finalized with `Ω` stays finalized with `Ω` along every play. -/
theorem Run.finalized {apps : Apps E} {p : Participant} {T : Threat E p} {σ : Strategy E p}
    {net n : NetworkState E p} {c : FixedPart} {Ω : Outcome E} (hf : net.Finalized c Ω)
    (hrun : Run apps T σ net n) : n.Finalized c Ω := by
  induction hrun with
  | refl => exact hf
  | round _ hr ih => exact finalizedWith_applyHonest apps _ _ (hr.1.finalizedWith_mono ih)

end Game

/-! ## Reachability helpers (`ArmadaLean/Machine.lean`, `ArmadaLean/Nitro/Reachable.lean`)

    Every witness below that supports a theorem taking `(Nitro.participant apps T).Reachable net`
    or `(Nitro.network apps Ts).Reachable n` proves it by a short chain of these helpers per
    machine, mirroring the real move sequence that reaches the witness state: one honest move, one
    landed call of `p`'s own, one adversary move, or the genesis state itself. -/

section Reachability

variable {E : Type} [DecidableEq E]

theorem participant_reachable_init {p : Participant} (apps : Apps E) (T : Threat E p) :
    (Nitro.participant apps T).Reachable (⟨Adjudicator.genesis, [], []⟩ : NetworkState E p) :=
  ⟨_, rfl, .refl⟩

theorem participant_reachable_honest {apps : Apps E} {p : Participant} {T : Threat E p} {net : NetworkState E p}
    (h : (Nitro.participant apps T).Reachable net) (m : HonestMove E) (hm : m.Feasible apps net) :
    (Nitro.participant apps T).Reachable (net.applyHonest m) :=
  h.tail (Or.inl ⟨m, hm, rfl⟩)

theorem participant_reachable_land {apps : Apps E} {p : Participant} {T : Threat E p} {net : NetworkState E p}
    (h : (Nitro.participant apps T).Reachable net) (op : Op E)
    (hop : op.HonestFeasible net) :
    (Nitro.participant apps T).Reachable (net.applyAdv apps (.land op)) :=
  h.tail (Or.inr (Or.inl ⟨op, hop, rfl⟩))

theorem participant_reachable_adv {apps : Apps E} {p : Participant} {T : Threat E p} {net : NetworkState E p}
    (h : (Nitro.participant apps T).Reachable net) (m : AdvMove E)
    (hm : T.feasible net m) (hnoland : ∀ op, m ≠ .land op) :
    (Nitro.participant apps T).Reachable (net.applyAdv apps m) :=
  h.tail (Or.inr (Or.inr (Or.inl (⟨m, hm, hnoland, Eq.refl (net.applyAdv apps m)⟩ :
    ∃ m' : AdvMove E, T.feasible net m' ∧ (∀ op, m' ≠ .land op) ∧
      net.applyAdv apps m = net.applyAdv apps m'))))

/-- `HonestSend.FundsCommitted` for a state whose allocation names one channel
    `W` and otherwise only external destinations: `p` must hold the pre-fund
    state of `W` alone. -/
theorem fundsCommitted_one {held : FixedPart → Prop} {st : State E} (W : FixedPart)
    (hdest : ∀ e ∈ st.outcome.entries, e.dest = W.address ∨ e.dest.isExternal = true)
    (hW : held W) : HonestSend.FundsCommitted held st := by
  intro V _ hf
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hf
  have hd : e.dest = V.address := Allocation.find_dest he
  rcases hdest e (List.mem_of_find?_eq_some he) with hW' | hx
  · rw [hd, FixedPart.address_eq, FixedPart.address_eq] at hW'
    injection hW' with hVW
    rw [hVW]
    exact hW
  · rw [hd, FixedPart.address_eq] at hx
    cases hx

/-- Every wallet-funded genesis network is reachable: `Nitro.network.init`
    leaves `wallet` unconstrained (D10 design decision). -/
theorem network_reachable_init (apps : Apps E) (Ts : Threats E apps) (w : Participant → Coins) :
    (Nitro.network apps Ts).Reachable
      (⟨Adjudicator.genesis, fun _ => [], fun _ => [], w⟩ : Network E) :=
  ⟨_, ⟨rfl, rfl, rfl⟩, .refl⟩

theorem network_reachable_honest {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) (p : Participant) (m : HonestMove E)
    (hm : m.Feasible apps (n.view p))
    (hvgate : ∀ r : Reaction E, m = .react r → ∀ st ∈ r.sends, n.VoucherSendable st) :
    (Nitro.network apps Ts).Reachable (Network.applyHonest n p m) :=
  h.tail ⟨p, Or.inl ⟨m, hm, hvgate, rfl⟩⟩

theorem network_reachable_land {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) (p : Participant) (op : Op E)
    (hop : op.HonestFeasible (n.view p)) (hgate : ∀ ss ∈ op.proofStates, n.Sendable ss) :
    (Nitro.network apps Ts).Reachable (Network.land apps n p op) :=
  h.tail ⟨p, Or.inr (Or.inl ⟨op, hop, hgate, rfl⟩)⟩

theorem network_reachable_adv {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) (p : Participant) (m : AdvMove E)
    (hm : (Ts.T p).feasible (n.view p) m) (hdgate : ∀ ss, m = .deliver ss → n.Sendable ss)
    (hnochain : ∀ caller op, m ≠ .chain caller op) (hnoland : ∀ op, m ≠ .land op) :
    (Nitro.network apps Ts).Reachable (Network.applyAdv apps n p m) :=
  h.tail ⟨p, Or.inr (Or.inr (Or.inl ⟨m, hm, hdgate, hnochain, hnoland, rfl⟩))⟩

/-- `p` deposits `x` of its own wallet into ledger channel `c`, reachable
    (D10 design decision). -/
theorem network_reachable_deposit {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) (p : Participant) (c : FixedPart)
    (e x : Coins) (hxle : x ≤ n.wallet p) :
    (Nitro.network apps Ts).Reachable (Network.deposit n p (.channel c) e x) :=
  h.tail ⟨p, Or.inr (Or.inr (Or.inr ⟨c, e, x, hxle, rfl⟩))⟩

/-- One send of a setup state (turn below the funding point, so
    `HonestSend.movesFrom` is vacuous) that funds no virtual channel and
    repeats no earlier state below the funding point
    (`HonestMove.Feasible_send`, `HonestSend.fundsCommitted_of_fundable`),
    closed by `decide`. -/
macro "honest_send" : tactic =>
  `(tactic| exact (HonestMove.Feasible_send _ _ _).mpr
    ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide),
      fun h => absurd h (by decide), by decide, by decide⟩)

end Reachability

/-! ## Threats and helpers for the `Liveness.lean` witnesses -/

/-- The adversary of `p` that every rule of `Assumptions` allows: any move of
    another participant with no forged signature of `p`, any delivery with
    no forged signature, and any tick. Transactions land within `ε = 2`, the
    least bound that `Capable.clockRuns` allows. -/
def canon (p : Participant) : Threat Nat p where
  feasible net m := match m with
    | .chain caller op => caller ≠ p ∧ ∀ ss ∈ op.proofStates, net.Unforged ss
    | .deliver ss => net.Unforged ss
    | .tick _ => True
    | .land _ => True
  ε := 2
  ε_pos := Nat.two_pos

theorem canon_ok (apps : Apps Nat) (p : Participant) : Assumptions apps p (canon p) where
  unforgeable _ _ _ h := h.2
  unforgeableDeliver _ _ h := h
  notHonest _ _ _ h := h.1
  capable _ _ _ h1 h2 := ⟨h1, h2⟩
  capableDeliver _ _ h := h
  capableTick _ _ := trivial
  clockRuns := le_refl 2

/-- One canonical threat per participant. -/
def Ts (apps : Apps Nat) : Threats Nat apps := ⟨canon, canon_ok apps⟩

/-- The adversary of the Turbo game: transfers by other participants. -/
def turboT (p : Participant) : Threat Nat p where
  feasible _ m := ∃ caller a b, caller ≠ p ∧ m = .chain caller (.transfer a b)
  ε := 1
  ε_pos := Nat.one_pos

theorem turboT_bounds (apps : Apps Nat) (p : Participant) : Bounds apps p (turboT p) where
  unforgeable _ caller op h ss hss := by
    obtain ⟨_, a, b, -, hm⟩ := h
    cases hm; (simp? [Op.proofStates] at hss says simp only [Op.proofStates, List.not_mem_nil] at hss)
  unforgeableDeliver _ _ h := by obtain ⟨_, _, _, -, hm⟩ := h; cases hm
  notHonest _ caller op h := by obtain ⟨_, _, _, hne, hm⟩ := h; cases hm; exact hne

theorem turboT_only (p : Participant) : (turboT p).TransfersOnly := by
  rintro _ _ ⟨caller, a, b, -, hm⟩; exact ⟨caller, a, b, hm⟩

theorem turboT_capable (p : Participant) : (turboT p).CapableTransfers :=
  fun _ caller a b h => ⟨caller, a, b, h, rfl⟩

/-- A held state whose voucher, if any, lists no signer. -/
theorem holds_intro {p : Participant} (net : NetworkState Nat p) (ss : SignedState Nat)
    (hsig : ∀ q ∈ ss.signers, (q = p ∧ ∃ s ∈ net.sent, s.state = ss.state) ∨
      (∃ r ∈ net.received, r.state = ss.state ∧ q ∈ r.signers))
    (hv : ∀ v, ss.state.voucher? = some v → v.signers = []) : net.Holds ss :=
  ⟨hsig, fun v h q hq => by rw [hv v h] at hq; cases hq⟩

/-- An unforged state whose voucher, if any, lists no signer. -/
theorem unforged_intro {p : Participant} (net : NetworkState Nat p) (ss : SignedState Nat)
    (hsig : p ∈ ss.signers → ∃ s ∈ net.sent, s.state = ss.state)
    (hv : ∀ v, ss.state.voucher? = some v → v.signers = []) : net.Unforged ss :=
  ⟨hsig, fun v h hp => by rw [hv v h] at hp; cases hp⟩

theorem deadlineAfter_open {p : Participant} {net : NetworkState Nat p} {c : FixedPart} {t : Nat}
    (h : net.chain.statusOf c = .open t) (δ : Time) : net.DeadlineAfter c δ :=
  fun _ _ h' => by rw [h] at h'; cases h'

/-- The genesis chain has no edge, so it is a DAG. -/
theorem g0_dag : g0.IsDAG := by
  refine ⟨fun a h => ?_⟩
  obtain ⟨b, ⟨-, e, he, -⟩, -⟩ := Relation.TransGen.head'_iff.1 h
  cases a <;> simp [Adjudicator.allocationOf, g0, Adjudicator.genesis, Adjudicator.finalOutcome,
    Adjudicator.statusOf] at he

/-- The empty ordering is a topological ordering of the genesis chain. -/
theorem g0_topo : g0.IsTopologicalOrder [] := by
  refine ⟨List.nodup_nil, fun n d hnd => ?_, fun n h => ?_⟩
  · obtain ⟨-, e, he, -⟩ := hnd
    cases n <;> simp [Adjudicator.allocationOf, g0, Adjudicator.genesis, Adjudicator.finalOutcome,
      Adjudicator.statusOf] at he
  · rcases h with h | h
    · exact absurd rfl h
    · cases n <;> simp [Adjudicator.allocationOf, g0, Adjudicator.genesis,
        Adjudicator.finalOutcome, Adjudicator.statusOf] at h

theorem g0_turbo (n : Address Nat) : g0.TurboValue n 0 := ⟨[], g0_topo, rfl⟩

/-- The genesis chain has no allocation anywhere: `status` is empty, so
    every channel reads the default open status, which has no final
    outcome. -/
theorem g0_allocationOf (n : Address Nat) : g0.allocationOf n = [] := by
  cases n <;> simp [Adjudicator.allocationOf, g0, Adjudicator.genesis, Adjudicator.finalOutcome,
    Adjudicator.statusOf]

/-- The genesis chain has no node at all, so it trivially stays in Turbo
    scope: no channel is a source (`g0_allocationOf`) and no entry exists to
    name a destination. -/
theorem g0_turboScope : g0.TurboScope := by
  refine ⟨fun c hc => absurd (g0_allocationOf (.channel c)) hc, fun n e he => ?_⟩
  rw [g0_allocationOf n] at he
  exact absurd he List.not_mem_nil

/-- The genesis chain is a `TurboOutcomeNetwork`: a DAG (`g0_dag`) in Turbo
    scope (`g0_turboScope`). -/
theorem g0_turboOutcomeNetwork : g0.IsTurboOutcomeNetwork := ⟨g0_dag, g0_turboScope⟩


/-! ## `Liveness.lean` -/

/-- `p0` sent `ssF`; `c1` is open and holds 1. -/
def netF : NetworkState Nat p0 := ⟨sDep, [], [ssF]⟩

theorem netF_holds : netF.Holds ssF :=
  holds_intro _ _ (by decide) (fun _ h => by cases h)

/-- `netF` is reachable: an adversary deposit (`Adjudicator.apply`'s `.deposit` arm does not read
    `caller`, `Adjudicator.lean:293`, so `q0` depositing reaches the same `sDep` `g0_dep` does for
    `p0`), then `p0`'s own honest `.send stF`. -/
theorem netF_reach : (Nitro.participant apps0 (canon p0)).Reachable netF :=
  participant_reachable_honest
    (participant_reachable_adv (participant_reachable_init apps0 (canon p0))
      (.chain q0 (.deposit c1.address 0 1)) ⟨by decide, fun ss h => absurd h List.not_mem_nil⟩
      (fun op h => by cases h))
    (.send stF) (by honest_send)

/-- `⟨sCon, [ssF], [ssF]⟩` is reachable: `netF_reach`, then `p0`'s own call landing (the
    explicit-time game lands a call separately from issuing it, `participant_reachable_land`),
    conclude with `ssF` (`Holds` needs `ssF` in `net.sent`, already there from the `.send`
    `netF_reach` ends with; the land also broadcasts `ssF` into `received`,
    `NetworkState.applyAdv`'s `.land` case). -/
theorem netC_reach :
    (Nitro.participant apps0 (canon p0)).Reachable (⟨sCon, [ssF], [ssF]⟩ : NetworkState Nat p0) :=
  participant_reachable_land netF_reach (.conclude c1 ssF)
    (fun ss h => by
      simp only [Op.proofStates, List.mem_singleton] at h; subst h; exact netF_holds)

/-- `directly_funded_pays`. -/
theorem directly_funded_pays.nonvacuity : ∃ (net : NetworkState Nat p0) (c : FixedPart) (o : Allocation Nat) (d : Nat) (amt : Coins),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    net.chain.finalOutcome c.address = some (.allocation o) ∧
    net.chain.DirectlyFunded c ∧ o.find (.external d) = some ⟨.external d, .alloc amt⟩ :=
  ⟨⟨sCon, [ssF], [ssF]⟩, c1, o1, 0, 1, canon_ok _ _, netC_reach, rfl, ⟨o1, rfl, by decide⟩, by decide⟩

/-- `finalizable_funded_pays`. -/
theorem finalizable_funded_pays.nonvacuity : ∃ (net : NetworkState Nat p0) (c : FixedPart) (o : Allocation Nat) (d : Nat) (amt : Coins),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    net.chain.finalOutcome c.address = some (.allocation o) ∧
    FundedFor apps0 (canon p0) c o.total net ∧
    o.find (.external d) = some ⟨.external d, .alloc amt⟩ :=
  ⟨⟨sCon, [ssF], [ssF]⟩, c1, o1, 0, 1, canon_ok _ _, netC_reach, rfl,
    .done (show o1.total ≤ _ by decide), by decide⟩

/-- `conclusion_proof_finalizable`. -/
theorem conclusion_proof_finalizable.nonvacuity : ∃ (net : NetworkState Nat p0) (c : TimedChannel (canon p0).ε) (ss : SignedState Nat)
    (Ω : Outcome Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 (c : FixedPart).appDef = consensusRules ∧ p0 ∈ (c : FixedPart).participants ∧
    net.Holds ss ∧ ConclusionProof (c : FixedPart) ss ∧ ss.state.outcome = Ω ∧
    (∀ t ∈ net.sent, t.state.channel = (c : FixedPart) → t.state.isFinal = true →
      t.state.outcome = Ω) ∧
    (net.chain.finalizedWith (c : FixedPart).address = none ∨ net.Finalized (c : FixedPart) Ω) ∧
    net.DeadlineAfter (c : FixedPart) (canon p0).ε :=
  ⟨netF, ⟨c1, by decide⟩, ssF, _, canon_ok _ _, netF_reach, rfl, by decide, netF_holds,
    by decide, rfl, by decide, .inl (by decide), deadlineAfter_open (t := 0) rfl _⟩

/-- `latest_state_finalizable`. -/
theorem latest_state_finalizable.nonvacuity : ∃ (net : NetworkState Nat p0) (c : TimedChannel (canon p0).ε) (ss : SignedState Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 (c : FixedPart).appDef = consensusRules ∧ p0 ∈ (c : FixedPart).participants ∧
    net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = (c : FixedPart) ∧
    (∀ t ∈ net.sent, t.state.channel = (c : FixedPart) →
      t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) ∧
    (∀ t ∈ net.sent, t.state.channel = (c : FixedPart) → t.state.isFinal = true →
      t.state.outcome = ss.state.outcome) ∧
    (net.Finalized (c : FixedPart) ss.state.outcome ∨
      (∃ t, net.chain.statusOf (c : FixedPart) = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf (c : FixedPart) = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧
        net.chain.now + (canon p0).ε ≤ ch.deadline)) :=
  ⟨netF, ⟨c1, by decide⟩, ssF, canon_ok _ _, netF_reach, rfl, by decide, netF_holds, by decide,
    rfl, by decide, by decide, .inr (.inl ⟨0, rfl, le_rfl⟩)⟩

/-- `c1` challenged at turn 0, deadline 2 (`g0.now + c1.challengeDuration`): reached by `p0`
    sending `stO0`, then `p0`'s own honest challenge with it (only `c1`'s own participant may
    challenge it, `Adjudicator.lean:217`, so this cannot be an adversary move the way a deposit
    can). `p0` then sends `ssO` at turn 1, the later state `late_observer_can_checkpoint`
    checkpoints with. -/
def stO0 : State Nat := ⟨c1, 0, .allocation o1, false, .opaque 0⟩
def ssO0 : SignedState Nat := ⟨stO0, [p0]⟩
def sCh0 : Adjudicator Nat := g0.setStatus c1 (.challenged 0 ⟨stO0, 4⟩)
def netO : NetworkState Nat p0 := ⟨sCh0, [ssO0], [ssO, ssO0]⟩

theorem g0_challengeO0 : g0.apply apps0 p0 (.challenge c1 [ssO0] stO0) = some sCh0 := rfl

theorem netO_reach : (Nitro.participant apps0 (canon p0)).Reachable netO :=
  participant_reachable_honest
    (participant_reachable_land
      (participant_reachable_honest (participant_reachable_init apps0 (canon p0)) (.send stO0)
        (by honest_send))
      (.challenge c1 [ssO0] stO0)
      (fun ss h => by
        simp only [Op.proofStates, List.mem_singleton] at h; subst h
        exact holds_intro _ _ (by decide) (fun _ h => by cases h)))
    (.send stO) ((HonestMove.Feasible_send _ _ _).mpr
      ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide), fun _ =>
        ⟨⟨[ssO0], stO0, fun ss h => by
          simp only [List.mem_singleton] at h; subst h
          exact holds_intro _ _ (fun q hq => .inl ⟨List.mem_singleton.1 hq, ssO0,
            List.mem_singleton_self _, rfl⟩) (fun _ h => by cases h), rfl, rfl, rfl⟩,
          [ssO], fun ss h => .inr (by rw [List.mem_singleton.1 h]; rfl), rfl⟩, by decide, by decide⟩)

/-- `late_observer_can_checkpoint`. -/
theorem late_observer_can_checkpoint.nonvacuity : ∃ (net : NetworkState Nat p0) (c : TimedChannel (canon p0).ε) (ss : SignedState Nat)
    (t : Nat) (ch : Challenge Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 (c : FixedPart).appDef = consensusRules ∧ p0 ∈ (c : FixedPart).participants ∧
    net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = (c : FixedPart) ∧
    (∀ u ∈ net.sent, u.state.channel = (c : FixedPart) →
      (u.state.turnNum < ss.state.turnNum ∨ u.state = ss.state) ∧ u.state.isFinal = false) ∧
    net.chain.statusOf (c : FixedPart) = .challenged t ch ∧ t < ss.state.turnNum ∧
    net.chain.now + (canon p0).ε ≤ ch.deadline :=
  ⟨netO, ⟨c1, by decide⟩, ssO, 0, ⟨stO0, 4⟩, canon_ok _ _, netO_reach, rfl, by decide,
    holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, by decide, rfl,
    by decide, by decide⟩

/-- `p0` concludes `c1` with `o1` directly from genesis: `conclude` needs no
    balance, only a valid conclusion proof (Nitro §3.2, "Finalization" and
    "Redistribution" are independent steps), so no deposit is needed. -/
def gCon : Adjudicator Nat := g0.setStatus c1 (.finalized 0 (.allocation o1) (.allocation o1))

theorem g0_conclude : g0.apply apps0 p0 (.conclude c1 ssF) = some gCon := rfl

theorem stF_voucher : stF.voucher? = none := rfl

/-- `c1` finalized with `o1`, reached by `p0`'s own honest `.send stF` then
    `.chain (.conclude c1 ssF)` (`Network.Sendable` gated by the prior
    send). Defined as the reachability derivation's own result, not a
    hand-written record, so `nFU_reach` needs no further unification. -/
def nFU : Network Nat :=
  Network.land apps0
    (Network.applyHonest (⟨g0, fun _ => [], fun _ => [], noDeposits⟩ : Network Nat) p0 (.send stF))
    p0 (.conclude c1 ssF)

theorem nFU_reach : (Nitro.network apps0 (Ts apps0)).Reachable nFU :=
  network_reachable_land
    (network_reachable_honest (network_reachable_init apps0 (Ts apps0) noDeposits)
      p0 (.send stF) (by honest_send)
      (fun r hr st hst => by
        injection hr with hr; subst hr
        simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
        intro v hv; rw [stF_voucher] at hv; cases hv))
    p0 (.conclude c1 ssF)
    (fun ss hss => by
      simp only [Op.proofStates, List.mem_singleton] at hss; subst hss
      exact holds_intro _ _ (by decide) (fun _ h => by cases h))
    (fun ss hss => by
      simp only [Op.proofStates, List.mem_singleton] at hss; subst hss
      refine ⟨fun q hq => ?_, fun v hv q hq => by (simp? [ssF, stF, State.voucher?] at hv says simp only [State.voucher?, ssF, stF, reduceCtorEq] at hv)⟩
      simp only [ssF, List.mem_singleton] at hq; subst hq
      exact ⟨⟨stF, [p0]⟩, by decide, rfl⟩)

theorem nFU_chain : nFU.chain = gCon := rfl

theorem nFU_views_chain (r : Participant) : (nFU.views r).chain = gCon := rfl

theorem nFU_views_p0 : nFU.views p0 = ⟨gCon, [ssF], [⟨stF, [p0]⟩]⟩ := rfl

theorem nFU_views_q0 : nFU.views q0 = ⟨gCon, [ssF], []⟩ := rfl

/-- `finalizable_unique`: both participants see `c1` finalized with `o1`. -/
theorem finalizable_unique.nonvacuity : ∃ (v : Views Nat) (n : Network Nat) (c : FixedPart) (p q : Participant)
    (Ω Ω' : Outcome Nat), (Nitro.network apps0 (Ts apps0)).Reachable n ∧ v = n.views ∧
    p ≠ q ∧ Finalizable apps0 ((Ts apps0).T p) c Ω (v p) ∧
    Finalizable apps0 ((Ts apps0).T q) c Ω' (v q) := by
  refine ⟨nFU.views, nFU, c1, p0, q0, .allocation o1, .allocation o1, nFU_reach, rfl,
    by decide, ?_, ?_⟩
  · rw [nFU_views_p0]; exact .done rfl
  · rw [nFU_views_q0]; exact .done rfl

/-- `channel_finalizability_cases`: the genesis network is reachable, and
    `c`, `p0` are universally quantified by the theorem, so no further
    content is needed. -/
theorem channel_finalizability_cases.nonvacuity : ∃ (v : Views Nat) (n : Network Nat), (Nitro.network apps0 (Ts apps0)).Reachable n ∧
    v = n.views :=
  ⟨(⟨g0, fun _ => [], fun _ => [], noDeposits⟩ : Network Nat).views, _,
    network_reachable_init apps0 (Ts apps0) noDeposits, rfl⟩


/-- `finalizable_or_two_enabled`: `p0` holds `ssF`, a consensus support of
    `stF` at turn 0, and `c1` is open at turn 0. -/
theorem finalizable_or_two_enabled.nonvacuity : ∃ (net : NetworkState Nat p0)
    (c : TimedChannel (canon p0).ε) (proof : SupportProof Nat) (cand : State Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    ((∃ vt, apps0 (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps0 (c : FixedPart).appDef = consensusRules) ∧
    p0 ∈ (c : FixedPart).participants ∧ TakeOut.ExitReady apps0 (canon p0) net c proof cand :=
  ⟨netF, ⟨c1, by decide⟩, [ssF], stF, canon_ok _ _, netF_reach, Or.inr rfl, by decide,
    fun ss h => by rw [List.mem_singleton] at h; subst h; exact netF_holds, by decide, rfl,
    by decide, deadlineAfter_open (t := 0) rfl _⟩

/-- `single_enabled_is_finalizable`: `c1` is finalized with `o1` after
    `p0`'s own conclude lands, so every play of the exit strategy keeps
    `o1` (`Run.finalized`). -/
theorem single_enabled_is_finalizable.nonvacuity : ∃ (net : NetworkState Nat p0)
    (c : TimedChannel (canon p0).ε) (proof : SupportProof Nat) (cand : State Nat) (Ω : Outcome Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    ((∃ vt, apps0 (c : FixedPart).appDef = forceMoveRules vt) ∨
      apps0 (c : FixedPart).appDef = consensusRules) ∧
    p0 ∈ (c : FixedPart).participants ∧ TakeOut.ExitReady apps0 (canon p0) net c proof cand ∧
    (∀ Ω', EnabledBy apps0 (canon p0) (TakeOut.exitStrategy apps0 c proof cand) (c : FixedPart) Ω'
      net → Ω' = Ω) :=
  ⟨⟨sCon, [ssF], [ssF]⟩, ⟨c1, by decide⟩, [ssF], stF, .allocation o1, canon_ok _ _,
    participant_reachable_land netF_reach (.conclude c1 ssF)
      (fun ss h => by
        simp only [Op.proofStates, List.mem_singleton] at h; subst h; exact netF_holds),
    Or.inr rfl, by decide,
    ⟨fun ss h => by
      rw [List.mem_singleton] at h; subst h
      exact holds_intro _ _ (by decide) (fun _ h => by cases h),
      by decide, rfl, by decide,
      fun _ _ h' => by
        cases (show sCon.statusOf c1 = .finalized 0 (.allocation o1) (.allocation o1)
          from by decide).symm.trans h'⟩,
    fun Ω' ⟨_, hrun, hf⟩ => Option.some.inj
      (hf.symm.trans (Run.finalized (net := ⟨sCon, [ssF], [ssF]⟩) (Ω := .allocation o1) rfl hrun))⟩

/-- `funding_point_universally_finalizable`: `c1` (one participant) under the
    ForceMove rules; `p0` signed the turn-0 state, reached by `p0`'s own
    honest `.send st0` from genesis. `c1` has no other participant, so
    `st0.recipients p0 = []`: no delivery is needed, and the proof below
    never reads any other participant's view. -/
def apps1 : Apps Nat := fun _ => forceMoveRules vtAll
def st0 : State Nat := ⟨c1, 0, .allocation o1, false, .opaque 0⟩

def nFP : Network Nat :=
  Network.applyHonest (⟨g0, fun _ => [], fun _ => [], noDeposits⟩ : Network Nat) p0 (.send st0)

theorem st0_voucher : st0.voucher? = none := rfl

theorem nFP_reach : (Nitro.network apps1 (Ts apps1)).Reachable nFP :=
  network_reachable_honest (network_reachable_init apps1 (Ts apps1) noDeposits) p0 (.send st0)
    (by honest_send)
    (fun r hr st hst => by
      injection hr with hr; subst hr
      simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
      intro v hv; rw [st0_voucher] at hv; cases hv)

theorem nFP_views_p0 : nFP.views p0 = ⟨g0, [], [⟨st0, [p0]⟩]⟩ := rfl

theorem nFP_views_chain (r : Participant) : (nFP.views r).chain = g0 := rfl

theorem nFP_chain : nFP.chain = g0 := rfl

theorem funding_point_universally_finalizable.nonvacuity : ∃ (v : Views Nat) (n : Network Nat) (c : FixedPart) (Ω : Outcome Nat)
    (vt : State Nat → State Nat → Bool),
    (Nitro.network apps1 (Ts apps1)).Reachable n ∧ v = n.views ∧
    apps1 c.appDef = forceMoveRules vt ∧ SetupPhaseKeepsOutcome vt c ∧
    SetupPhaseAccepted vt c ∧ 0 < c.n ∧
    AtFundingPoint v c Ω ∧ (∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) := by
  refine ⟨nFP.views, nFP, c1, .allocation o1, vtAll, nFP_reach, rfl, rfl, ?_, ?_, by decide,
    ⟨?_, ?_⟩, fun r => ?_⟩
  · intro s1 s2 h _ _; (simpa? [vtAll] using h says simpa only [vtAll, decide_eq_true_eq] using h)
  · intro s1 s2 _ _ _ _ ho _; (simp? [vtAll, ho] says simp only [vtAll, ho, decide_true])
  · intro r hr k hk
    have hr' : r = p0 := by (simpa? [c1] using hr says simpa only [c1, List.mem_cons, List.not_mem_nil, or_false] using hr)
    have hk' : k = 0 := by (simpa? [FixedPart.n, c1] using hk says simpa only [FixedPart.n, c1, List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] using hk)
    subst hr' hk'
    refine ⟨⟨st0, [p0]⟩, ?_, rfl, rfl, rfl, rfl, ⟨p0, by decide, by decide⟩⟩
    rw [nFP_views_p0]
    exact holds_intro _ _ (by decide) (fun _ h => by cases h)
  · intro r hr ss hss _
    have hr' : r = p0 := by (simpa? [c1] using hr says simpa only [c1, List.mem_cons, List.not_mem_nil, or_false] using hr)
    subst hr'
    rw [nFP_views_p0] at hss
    (simp? at hss says simp only [List.mem_cons, List.not_mem_nil, or_false] at hss); subst hss; decide
  · rw [nFP_views_chain]; exact ⟨rfl, rfl⟩

/-- `concluded_universally_finalizable`: `p0` signs `ssF` off-chain
    (`Concluded` reads `Holds`, not the chain) without calling `conclude`
    on-chain, so `c1`'s on-chain status stays `.open 0`
    (`deadlineAfter_open`, the `.inl` branch of `hchain`). -/
def nCF : Network Nat :=
  Network.applyHonest (⟨g0, fun _ => [], fun _ => [], noDeposits⟩ : Network Nat) p0 (.send stF)

theorem nCF_reach : (Nitro.network apps0 (Ts apps0)).Reachable nCF :=
  network_reachable_honest (network_reachable_init apps0 (Ts apps0) noDeposits) p0 (.send stF)
    (by honest_send)
    (fun r hr st hst => by
      injection hr with hr; subst hr
      simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
      intro v hv; rw [stF_voucher] at hv; cases hv)

theorem nCF_views_p0 : nCF.views p0 = ⟨g0, [], [ssF]⟩ := rfl

theorem nCF_views_chain (r : Participant) : (nCF.views r).chain = g0 := rfl

theorem concluded_universally_finalizable.nonvacuity : ∃ (v : Views Nat) (n : Network Nat) (c : FixedPart) (Ω : Outcome Nat),
    (Nitro.network apps0 (Ts apps0)).Reachable n ∧ v = n.views ∧
    apps0 c.appDef = consensusRules ∧ Concluded v c Ω ∧
    (∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) ∧
    (∀ p, (v p).chain.finalizedWith c.address = none ∨ (v p).Finalized c Ω) ∧
    (∀ p, 2 * ((Ts apps0).T p).ε ≤ c.challengeDuration) ∧
    (∀ p, (v p).DeadlineAfter c ((Ts apps0).T p).ε) := by
  refine ⟨nCF.views, nCF, c1, .allocation o1, nCF_reach, rfl, rfl, ?_, ?_,
    fun r => .inl (by rw [nCF_views_chain]; decide),
    fun _ => (by decide : 2 * 2 ≤ 4),
    fun r => deadlineAfter_open (t := 0) (by rw [nCF_views_chain]; rfl) _⟩
  · intro r hr
    have hr' : r = p0 := by (simpa? [c1] using hr says simpa only [c1, List.mem_cons, List.not_mem_nil, or_false] using hr)
    subst hr'
    refine ⟨ssF, ?_, by decide, rfl⟩
    rw [nCF_views_p0]; exact netF_holds
  · intro r t ht _ hfin
    by_cases hrp0 : r = p0
    · subst hrp0
      rw [nCF_views_p0] at ht
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht); subst ht; rfl
    · exfalso
      have : (nCF.views r).sent = [] := by
        rw [Network.views, Network.view]
        simp only [nCF, Network.applyHonest, HonestMove.send, if_neg hrp0]
      rw [this] at ht
      exact absurd ht List.not_mem_nil

/-- `consensus_enabled_outcomes`: the adversary concludes `c2` with the
    final state both participants signed. -/
def stF2 : State Nat := ⟨c2, 0, .allocation o1, true, .opaque 0⟩
def netC2 : NetworkState Nat p0 := ⟨g0, [⟨stF2, [q0]⟩], [⟨stF2, [p0]⟩]⟩
def mC2 : AdvMove Nat := .chain q0 (.conclude c2 ⟨stF2, [p0, q0]⟩)

/-- `netC2` is reachable: `p0` sends its own signature on `stF2`, then an adversary `.deliver`
    of `q0`'s claimed signature (never genuineness-checked for a non-`p0` signer, `Unforged`'s own
    definition cares only about `p0`'s alleged signature). -/
theorem netC2_reach : (Nitro.participant apps0 (canon p0)).Reachable netC2 :=
  participant_reachable_adv
    (participant_reachable_honest (participant_reachable_init apps0 (canon p0)) (.send stF2)
      (by honest_send))
    (.deliver ⟨stF2, [q0]⟩) (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ :
      NetworkState.Unforged _ ⟨stF2, [q0]⟩) (fun op h => by cases h)

theorem consensus_enabled_outcomes.nonvacuity : ∃ (net : NetworkState Nat p0) (c : TimedChannel (canon p0).ε) (ss : SignedState Nat)
    (Ω1 Ω2 Ω : Outcome Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 (c : FixedPart).appDef = consensusRules ∧ p0 ∈ (c : FixedPart).participants ∧
    net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = (c : FixedPart) ∧ ss.state.outcome = Ω1 ∧
    (∀ t ∈ net.sent, t.state.channel = (c : FixedPart) →
      (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
      (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2)) ∧
    ((∃ t, net.chain.statusOf (c : FixedPart) = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf (c : FixedPart) = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧
        net.chain.now + (canon p0).ε ≤ ch.deadline)) ∧
    Enabled apps0 (canon p0) (c : FixedPart) Ω net := by
  refine ⟨netC2, ⟨c2, by decide⟩, ⟨stF2, [p0, q0]⟩, .allocation o1, .allocation o1,
    .allocation o1, canon_ok _ _, netC2_reach, rfl, by decide,
    holds_intro _ _ (by decide) (fun _ h => by cases h), by decide,
    rfl, rfl, (fun t h _ => by
      simp only [netC2, List.mem_singleton] at h; subst h
      exact ⟨Or.inr (Or.inl rfl), fun _ => Or.inl rfl⟩), .inl ⟨0, rfl, le_rfl⟩, ?_⟩
  rintro ⟨σ, hfeas, hσ⟩
  have hmC2feas : (canon p0).feasible netC2 mC2 :=
    ⟨by decide, fun ss hss => by
      simp only [mC2, Op.proofStates, List.mem_singleton] at hss; subst hss
      exact unforged_intro _ _ (by decide) (fun _ h => by cases h)⟩
  have hfin1 : (netC2.applyAdv apps0 mC2).chain.finalizedWith c2.address = some (.allocation o1) :=
    rfl
  have hnow1 : (netC2.applyAdv apps0 mC2).chain.now = netC2.chain.now := rfl
  cases hm : σ netC2 with
  | react r =>
    have hnotick : ∀ op ∈ r.calls, ∀ dt, op ≠ Op.tick dt := by
      intro op hop dt heq
      have h := hfeas netC2
      rw [hm] at h
      subst heq
      exact h.1 _ hop
    obtain ⟨net2, hland, heqnow⟩ :=
      Threat.RoundSeq.landAll apps0 (canon p0) netC2.chain.now r.calls hnotick
        (netC2.applyAdv apps0 mC2)
    have hseq : Threat.RoundSeq apps0 (canon p0) netC2.chain.now (σ netC2).calls netC2 net2 := by
      rw [hm, HonestMove.calls]
      exact Threat.RoundSeq.other hmC2feas (by (simp? [mC2] says simp only [mC2, ne_eq, reduceCtorEq, not_false_eq_true, implies_true])) (by (simp? [mC2] says simp only [mC2, ne_eq, reduceCtorEq, not_false_eq_true, implies_true])) hland
    have hfin2 : net2.chain.finalizedWith c2.address = some (.allocation o1) :=
      hland.finalizedWith_mono hfin1
    have htime : net2.chain.now < netC2.chain.now + (canon p0).ε := by
      rw [heqnow, hnow1]; exact Nat.lt_add_of_pos_right (canon p0).ε_pos
    exact hσ netC2 net2 .refl ⟨hseq, htime⟩ hfin2
  | wait dt =>
    have hseq : Threat.RoundSeq apps0 (canon p0) netC2.chain.now (σ netC2).calls netC2
        (netC2.applyAdv apps0 mC2) := by
      rw [hm, HonestMove.calls_wait]
      exact Threat.RoundSeq.other hmC2feas (by (simp? [mC2] says simp only [mC2, ne_eq, reduceCtorEq, not_false_eq_true, implies_true])) (by (simp? [mC2] says simp only [mC2, ne_eq, reduceCtorEq, not_false_eq_true, implies_true])) Threat.RoundSeq.nil
    have htime : (netC2.applyAdv apps0 mC2).chain.now < netC2.chain.now + (canon p0).ε := by
      rw [hnow1]; exact Nat.lt_add_of_pos_right (canon p0).ε_pos
    exact hσ netC2 _ .refl ⟨hseq, htime⟩ hfin1

/-- `turbo_redistribution_unbeatable`. `net` is the genesis state itself: `Nitro.participant`'s own
    initial state. -/
theorem turbo_redistribution_unbeatable.nonvacuity : ∃ (net : NetworkState Nat p0) (ops : List (Participant × Op Nat)) (d : Nat) (x : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsDAG ∧ OnlyTransfers ops ∧
    x ≤ (Adjudicator.applyAll apps0 ops net.chain).balances.get (.external d) :=
  ⟨⟨g0, [], []⟩, [], 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_dag,
    fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩

theorem zero_g0 : ∀ a : Address Nat, g0.balances.get a = 0 := fun _ => rfl

/-- `deposit_bounds_value`: a deposit of 0 into the ledger channel `c1` of the empty
    chain, in the transfer-only game. `net` is the genesis state itself. Both values are
    the Turbo Value Algorithm's (`turboValueAlong_valueIn`). -/
theorem deposit_bounds_value.nonvacuity : ∃ (net : NetworkState Nat p0) (c : FixedPart) (d : Nat) (y x x' : Coins)
    (s' : Adjudicator Nat) (e : Coins),
    (turboT p0).TransfersOnly ∧ (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsTurboOutcomeNetwork ∧
    net.chain.deposit c.address e y = some s' ∧
    ValueIn apps0 (turboT p0) HonestMove.IsTransfer d net x ∧
    ValueIn apps0 (turboT p0) HonestMove.IsTransfer d { net with chain := s' } x' := by
  obtain ⟨s', hd⟩ : ∃ s', g0.deposit c1.address 0 0 = some s' := ⟨_, rfl⟩
  have ht' : s'.IsTurboOutcomeNetwork := g0_turboOutcomeNetwork.deposit hd
  obtain ⟨o', ho'⟩ := exists_valid_topo_order s' ht'.1
  exact ⟨⟨g0, [], []⟩, c1, 0, 0, _, _, s', 0, turboT_only _,
    participant_reachable_init apps0 (turboT p0), g0_turboOutcomeNetwork, hd,
    turboValueAlong_valueIn apps0 _ (turboT_only _) ⟨g0, [], []⟩ g0_turboOutcomeNetwork 0
      (g0_turbo _),
    turboValueAlong_valueIn apps0 _ (turboT_only _) ⟨s', [], []⟩ ht' 0 ⟨o', ho', rfl⟩⟩

/-- `payout_preserves_value`. `sP` is `c1` concluded with outcome `[alloc d1 0]`:
    reached by `p0` sending the final state `stP`, then honestly concluding with it (`Holds`
    needs `p0`'s own signature in `net.sent`, so the send comes first; `Adjudicator.lean:249-254`'s
    `conclude` does not read `caller`, so no deposit is needed for an all-zero outcome). Both
    steps are `p0`'s own, so `sP` is reachable under every threat. Its only allocation names
    the external `d1`, so `sP` has no edge and is a Turbo outcome network. -/
def stP : State Nat := ⟨c1, 0, .allocation [alloc d1 0], true, .opaque 0⟩
def ssP : SignedState Nat := ⟨stP, [p0]⟩
def sP : Adjudicator Nat :=
  g0.setStatus c1 (.finalized 0 (.allocation [alloc d1 0]) (.allocation [alloc d1 0]))

theorem g0_concludeP : g0.apply apps0 p0 (.conclude c1 ssP) = some sP := rfl

theorem sP_reach (T : Threat Nat p0) : (Nitro.participant apps0 T).Reachable
    (⟨sP, [ssP], [ssP]⟩ : NetworkState Nat p0) :=
  participant_reachable_land
    (participant_reachable_honest (participant_reachable_init apps0 T) (.send stP)
      (by honest_send))
    (.conclude c1 ssP)
    (fun ss h => by
      simp only [Op.proofStates, List.mem_singleton] at h; subst h
      exact holds_intro _ _ (by decide) (fun _ h => by cases h))

/-- `sP`'s only allocation is `c1`'s `[alloc d1 0]`. -/
theorem sP_allocationOf (n : Address Nat) :
    sP.allocationOf n = if n = c1.address then [alloc d1 0] else [] := by
  cases n with
  | external e =>
    rw [if_neg (fun h => by cases h)]
    rfl
  | channel c =>
    by_cases hc : c = c1
    · subst hc
      rw [if_pos (FixedPart.address_eq c1).symm]
      rfl
    · rw [if_neg (fun h => hc (by cases h; rfl))]
      simp only [Adjudicator.allocationOf, Adjudicator.finalOutcome, Adjudicator.statusOf, sP,
        Adjudicator.setStatus, g0, Adjudicator.genesis, ne_eq, decide_not, List.filter_nil,
        List.lookup_cons, beq_false_of_ne hc, List.lookup_nil, Option.getD_none,
        ChannelStatus.finalOutcome_open]

/-- `sP` has no edge: its one entry names an external destination. -/
theorem sP_dag : sP.IsDAG := by
  refine ⟨fun a h => ?_⟩
  obtain ⟨b, ⟨hext, e, he, hed⟩, -⟩ := Relation.TransGen.head'_iff.1 h
  rw [sP_allocationOf] at he
  split at he
  · rw [List.mem_singleton] at he
    subst he
    rw [← hed] at hext
    exact absurd hext (by decide)
  · exact absurd he List.not_mem_nil

/-- `sP` is in Turbo scope: its source `c1` is a ledger channel, and its one
    entry is an `alloc` to an external destination. -/
theorem sP_turboScope : sP.TurboScope := by
  refine ⟨fun c hc => ?_, fun n e he => ?_⟩
  · rw [sP_allocationOf] at hc
    split at hc
    · rename_i h
      cases h
      rfl
    · exact absurd rfl hc
  · rw [sP_allocationOf] at he
    split at he
    · rw [List.mem_singleton] at he
      subst he
      exact ⟨rfl, fun c hc => by cases hc⟩
    · exact absurd he List.not_mem_nil

theorem sP_turboOutcomeNetwork : sP.IsTurboOutcomeNetwork := ⟨sP_dag, sP_turboScope⟩

theorem payout_preserves_value.nonvacuity : ∃ (net : NetworkState Nat p0) (_d q : Nat) (a : FixedPart) (s' : Adjudicator Nat),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsTurboOutcomeNetwork ∧ net.chain.transfer a (.external q) = some s' :=
  ⟨⟨sP, [ssP], [ssP]⟩, 0, 1, c1, _, turboT_bounds _ _, turboT_only _, turboT_capable _,
    sP_reach _, sP_turboOutcomeNetwork, rfl⟩

/-- `participant_can_prevent_cycles`. `net` is the genesis state itself. -/
theorem participant_can_prevent_cycles.nonvacuity : ∃ net : NetworkState Nat p0,
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    (∀ c : FixedPart, p0 ∈ c.participants → apps0 c.appDef = consensusRules) ∧
    (∀ c : FixedPart, p0 ∈ c.participants → ∃ t, net.chain.statusOf c = .open t) ∧
    net.chain.IsDAG ∧ net.sent = [] :=
  ⟨⟨g0, [], []⟩, canon_ok _ _, participant_reachable_init apps0 (canon p0), fun _ _ => rfl,
    fun _ _ => ⟨0, rfl⟩, g0_dag, rfl⟩

/-- `turbo_value_upper_bound`. `net` is the genesis state itself. -/
theorem turbo_value_upper_bound.nonvacuity : ∃ (net : NetworkState Nat p0) (n : Address Nat) (v x : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsDAG ∧ net.chain.TurboValue n v ∧
    CanObtainIn apps0 (turboT p0) HonestMove.IsTransfer n x net :=
  ⟨⟨g0, [], []⟩, d0, 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_dag, g0_turbo _,
    .done (Nat.zero_le _)⟩

/-- `turbo_value_achievable`. `net` is the genesis state itself. -/
theorem turbo_value_achievable.nonvacuity : ∃ (net : NetworkState Nat p0) (d : Nat) (v : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsTurboOutcomeNetwork ∧ net.chain.TurboValue (.external d) v :=
  ⟨⟨g0, [], []⟩, 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_turboOutcomeNetwork, g0_turbo _⟩

/-- `turbo_value_is_value`. `net` is the genesis state itself. -/
theorem turbo_value_is_value.nonvacuity : ∃ (net : NetworkState Nat p0) (d : Nat) (v : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsTurboOutcomeNetwork ∧ net.chain.TurboValue (.external d) v :=
  ⟨⟨g0, [], []⟩, 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_turboOutcomeNetwork, g0_turbo _⟩

theorem g0_exhausted : g0.TransferExhausted := by
  intro a b s' h
  (simp? [Adjudicator.transfer, Adjudicator.finalOutcome, Adjudicator.statusOf, g0,
    Adjudicator.genesis] at h says simp only [Adjudicator.transfer, Adjudicator.finalOutcome, FixedPart.address_eq, Adjudicator.statusOf, g0, Adjudicator.genesis, List.lookup_nil, Option.getD_none, ChannelStatus.finalOutcome_open, ite_self, reduceCtorEq] at h)

/-- `turbo_order_independent`. -/
theorem turbo_order_independent.nonvacuity : ∃ (s : DAGOutcomeNetwork Nat) (ops1 ops2 : List (Participant × Op Nat)),
    OnlyTransfers ops1 ∧ OnlyTransfers ops2 ∧
    (Adjudicator.applyAll apps0 ops1 (s : Adjudicator Nat)).TransferExhausted ∧
    (Adjudicator.applyAll apps0 ops2 (s : Adjudicator Nat)).TransferExhausted :=
  ⟨⟨g0, g0_dag⟩, [], [], fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, g0_exhausted, g0_exhausted⟩

/-- `turbo_value_exists_unique`. -/
example : DAGOutcomeNetwork Nat := ⟨g0, g0_dag⟩


/-! ### Ledger constructions: `A = p0` at `0`, `B = q0` at `1`. -/

def cLWF : FixedPart := ⟨[p0, q0], 107, ⟨0⟩, 4, .ledger⟩
def cχF : FixedPart := ⟨[p0, q0], 108, ⟨0⟩, 4, .ledger⟩
/-- `wLSF.c = 5`, a real subchannel value (D10 design decision): `cLWF` holds a
    genuine deposit, not the zero balance the pre-decision model forced on
    every reachable chain. -/
def wLSF : LedgerWithSub Nat := ⟨p0, q0, 0, 1, cLWF, cχF, 0, 0, 5⟩

def stLWF : State Nat := ⟨cLWF, 0, wLSF.outcome, true, .opaque 0⟩

theorem stLWF_voucher : stLWF.voucher? = none := rfl

/-- The chain after `p0` deposits `5` into `cLWF` from genesis. -/
def gLWF : Adjudicator Nat := { balances := [(cLWF.address, 5)], held := 5, status := [], now := 0 }

theorem g0_dep_cLWF : g0.deposit cLWF.address 0 5 = some gLWF := rfl

/-- `p0`'s wallet before the deposit: exactly `5`, the amount it spends. -/
def wLWalletF : Participant → Coins := fun r => if r = p0 then 5 else 0

def nLWF0 : Network Nat := ⟨g0, fun _ => [], fun _ => [], wLWalletF⟩
def nLWF1 : Network Nat := Network.deposit nLWF0 p0 cLWF.address 0 5

theorem nLWF1_chain : nLWF1.chain = gLWF := rfl
theorem nLWF1_sent_p0 : nLWF1.sent p0 = [] := rfl
theorem nLWF1_sent_q0 : nLWF1.sent q0 = [] := rfl

theorem nLWF1_reach : (Nitro.network apps0 (Ts apps0)).Reachable nLWF1 :=
  network_reachable_deposit (network_reachable_init apps0 (Ts apps0) wLWalletF) p0 cLWF 0 5
    (by (simp? [wLWalletF] says simp only [wLWalletF, ↓reduceIte, Std.le_refl]))

theorem gLWF_balance_cLWF : gLWF.balances.get cLWF.address = 5 := rfl

/-- The unfunded base every zero-balance witness in this file reads:
    chain `g0`, no sent/received history, `noDeposits` wallet. -/
def n0G : Network Nat := ⟨g0, fun _ => [], fun _ => [], noDeposits⟩

theorem n0G_reach : (Nitro.network apps0 (Ts apps0)).Reachable n0G :=
  network_reachable_init apps0 (Ts apps0) noDeposits

theorem n0G_chain : n0G.chain = g0 := rfl

/-- `p0` and `q0` each send `st`, synchronously delivered to the other
    (a two-participant channel), giving each the other's signature with
    no adversary move. Built on an arbitrary reachable base `n0`
    (`n0G`'s zero-balance chain for every call site below except the
    funded witnesses, which build on a deposit-funded base instead). -/
def nOneCh (n0 : Network Nat) (st : State Nat) : Network Nat :=
  Network.applyHonest (Network.applyHonest n0 p0 (.send st)) q0 (.send st)

/-- A send of `p` leaves the `sent` list of another participant `q`. -/
theorem sent_after_send_other (n0 : Network Nat) {p q : Participant} (h : q ≠ p) (st : State Nat) :
    ((Network.applyHonest n0 p (.send st)).view q).sent = (n0.view q).sent := by
  show (Network.applyHonest n0 p (.react ⟨[], [st]⟩)).sent q = n0.sent q
  rw [Network.applyHonest_react_sent, if_neg h]

/-- A send of `p` adds the one signed state to `p`'s own `sent` list. -/
theorem sent_after_send_self (n0 : Network Nat) (p : Participant) (st : State Nat) :
    ((Network.applyHonest n0 p (.send st)).view p).sent = ⟨st, [p]⟩ :: (n0.view p).sent := by
  show (Network.applyHonest n0 p (.react ⟨[], [st]⟩)).sent p = _
  rw [Network.applyHonest_react_sent, if_pos rfl]
  rfl

/-- One send of `st` is feasible when `st` satisfies the signing rules against
    `prior` with no held pre-fund state and no held support (so `st` is a
    setup state), and every state `p` sent repeats a state of `prior`
    (`HonestSend.of_prior`). -/
theorem send_feasible_prior {apps : Apps Nat} {p : Participant} {net : NetworkState Nat p}
    {prior : List (SignedState Nat)} {st : State Nat}
    (hst : HonestSend prior (fun _ => False) (fun _ => False) st)
    (hcover : ∀ s ∈ net.sent, ∃ s' ∈ prior, s'.state = s.state) :
    (HonestMove.send st).Feasible apps net :=
  (HonestMove.Feasible_send _ _ _).mpr ((hst.of_prior fun s hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact .inl rfl
    · exact .inr (hcover s hs)).mono (fun _ hx => hx) (fun _ h => h) (fun _ h => h.elim))

theorem nOneCh_reach {n0 : Network Nat} {st : State Nat}
    (hr0 : (Nitro.network apps0 (Ts apps0)).Reachable n0) (hv : st.voucher? = none)
    (hstp : HonestSend (n0.sent p0) (fun _ => False) (fun _ => False) st)
    (hstq : HonestSend (n0.sent q0) (fun _ => False) (fun _ => False) st) :
    (Nitro.network apps0 (Ts apps0)).Reachable (nOneCh n0 st) :=
  network_reachable_honest
    (network_reachable_honest hr0 p0 (.send st) (send_feasible_prior hstp fun s hs => ⟨s, hs, rfl⟩)
      (fun r hr st' hst => by
        injection hr with hr; subst hr
        simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
        intro v hv'; rw [hv] at hv'; cases hv'))
    q0 (.send st)
    (send_feasible_prior hstq (by
      rw [sent_after_send_other n0 (p := p0) (q := q0) (by decide) st]
      exact fun s hs => ⟨s, hs, rfl⟩))
    (fun r hr st' hst => by
      injection hr with hr; subst hr
      simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
      intro v hv'; rw [hv] at hv'; cases hv')

theorem nOneCh_chain (n0 : Network Nat) (st : State Nat) : (nOneCh n0 st).chain = n0.chain := rfl

theorem nOneCh_views_p0 {n0 : Network Nat} {st : State Nat}
    (hst : st.channel.participants = [p0, q0]) (hsp0 : n0.sent p0 = []) (hrp0 : n0.received p0 = []) :
    (nOneCh n0 st).views p0 = ⟨n0.chain, [⟨st, [q0]⟩], [⟨st, [p0]⟩]⟩ := by
  (simp? [nOneCh, Network.views, Network.view, Network.applyHonest, HonestMove.send, State.recipients, hst,
    show p0 ≠ q0 from by decide, hsp0, hrp0] says simp only [Network.views, Network.view, nOneCh, Network.applyHonest, HonestMove.send, List.map_cons, List.map_nil, List.cons_append, List.nil_append, State.recipients, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.decide_and, show p0 ≠ q0 from by decide, decide_false, Bool.not_false, Bool.and_true, hst, List.mem_cons, List.not_mem_nil, or_self, or_false, decide_true, List.filter_cons_of_pos, List.filter_nil, Bool.and_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, hrp0, List.append_nil, ↓reduceIte, hsp0])

theorem nOneCh_views_q0 {n0 : Network Nat} {st : State Nat}
    (hst : st.channel.participants = [p0, q0]) (hsq0 : n0.sent q0 = []) (hrq0 : n0.received q0 = []) :
    (nOneCh n0 st).views q0 = ⟨n0.chain, [⟨st, [p0]⟩], [⟨st, [q0]⟩]⟩ := by
  (simp? [nOneCh, Network.views, Network.view, Network.applyHonest, HonestMove.send, State.recipients, hst,
    show p0 ≠ q0 from by decide, show q0 ≠ p0 from by decide, hsq0, hrq0] says simp only [Network.views, Network.view, nOneCh, Network.applyHonest, HonestMove.send, List.map_cons, List.map_nil, List.cons_append, List.nil_append, State.recipients, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.decide_and, decide_true, Bool.and_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil, show q0 ≠ p0 from by decide, decide_false, Bool.not_false, Bool.and_true, hst, List.mem_cons, List.not_mem_nil, or_false, or_true, List.filter_cons_of_pos, hrq0, List.append_nil, ↓reduceIte, hsq0])

theorem g0_open (c : FixedPart) : g0.statusOf c = .open 0 := rfl
theorem g0_finalizedWith (c : FixedPart) : g0.finalizedWith c.address = none := rfl

theorem nOneCh_views_chain (n0 : Network Nat) (st : State Nat) (r : Participant) :
    ((nOneCh n0 st).views r).chain = n0.chain := rfl

/-- `FinalizableBy` for the channel `c` of `nOneCh`'s one held state, on
    any base `n0` whose chain has `c` open and unfinalized, and whose
    `p0`/`q0` sent/received histories are empty (true by `rfl` for `n0G`
    and for a deposit-only funded base, `Network.deposit_sent`/
    `Network.deposit_received`). -/
theorem nOneCh_finalizable {n0 : Network Nat} {c : FixedPart} {Ω : Outcome Nat}
    (hcp : c.participants = [p0, q0]) (hdur : c.challengeDuration = 4)
    (hopen : n0.chain.statusOf c = .open 0) (hnone : n0.chain.finalizedWith c.address = none)
    (hsp0 : n0.sent p0 = []) (hrp0 : n0.received p0 = [])
    (hsq0 : n0.sent q0 = []) (hrq0 : n0.received q0 = []) :
    (nOneCh n0 (⟨c, 0, Ω, true, .opaque 0⟩ : State Nat)).views.FinalizableBy apps0 (Ts apps0) c Ω
      [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by (simpa? using hr says simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
  rcases hr' with rfl | rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 p0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by (simp? [ConclusionProof, SignedState.ByAll, hcp] says simp only [ConclusionProof, SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true, and_self])) rfl ?_
      (.inl (by rw [nOneCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nOneCh_views_chain]; exact hopen) _)
    · rw [nOneCh_views_p0 hcp hsp0 hrp0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_singleton_self _, rfl⟩
      · exact .inr ⟨_, List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩
    · rw [nOneCh_views_p0 hcp hsp0 hrp0]; intro t ht _ _; (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht); subst ht; rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 q0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by (simp? [ConclusionProof, SignedState.ByAll, hcp] says simp only [ConclusionProof, SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true, and_self])) rfl ?_
      (.inl (by rw [nOneCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nOneCh_views_chain]; exact hopen) _)
    · rw [nOneCh_views_q0 hcp hsq0 hrq0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩
      · exact .inl ⟨rfl, _, List.mem_singleton_self _, rfl⟩
    · rw [nOneCh_views_q0 hcp hsq0 hrq0]; intro t ht _ _; (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht); subst ht; rfl

/-- Two rounds of `nOneCh`: `p0` and `q0` each send `st1`, then each
    send `st2`, both synchronously delivered to the other. Built on an
    arbitrary reachable base `n0`, the same way `nOneCh` is. -/
def nTwoCh (n0 : Network Nat) (st1 st2 : State Nat) : Network Nat :=
  Network.applyHonest
    (Network.applyHonest
      (Network.applyHonest
        (Network.applyHonest n0 p0 (.send st1))
        q0 (.send st1))
      p0 (.send st2))
    q0 (.send st2)

theorem nTwoCh_reach {n0 : Network Nat} {st1 st2 : State Nat}
    (hr0 : (Nitro.network apps0 (Ts apps0)).Reachable n0)
    (hv1 : st1.voucher? = none) (hv2 : st2.voucher? = none)
    (hst1p : HonestSend (n0.sent p0) (fun _ => False) (fun _ => False) st1)
    (hst1q : HonestSend (n0.sent q0) (fun _ => False) (fun _ => False) st1)
    (hst2p : HonestSend (⟨st1, [p0]⟩ :: n0.sent p0) (fun _ => False) (fun _ => False) st2)
    (hst2q : HonestSend (⟨st1, [q0]⟩ :: n0.sent q0) (fun _ => False) (fun _ => False) st2) :
    (Nitro.network apps0 (Ts apps0)).Reachable (nTwoCh n0 st1 st2) :=
  have hp1 : ((Network.applyHonest (Network.applyHonest n0 p0 (.send st1)) q0 (.send st1)).view
      p0).sent = ⟨st1, [p0]⟩ :: n0.sent p0 := by
    rw [sent_after_send_other _ (p := q0) (q := p0) (by decide), sent_after_send_self]
    rfl
  have hq1 : ((Network.applyHonest (Network.applyHonest (Network.applyHonest n0 p0 (.send st1))
      q0 (.send st1)) p0 (.send st2)).view q0).sent = ⟨st1, [q0]⟩ :: n0.sent q0 := by
    rw [sent_after_send_other _ (p := p0) (q := q0) (by decide), sent_after_send_self,
      sent_after_send_other _ (p := p0) (q := q0) (by decide)]
    rfl
  network_reachable_honest
    (network_reachable_honest
      (network_reachable_honest
        (network_reachable_honest hr0 p0 (.send st1)
          (send_feasible_prior hst1p fun s hs => ⟨s, hs, rfl⟩)
          (fun r hr st' hst => by
            injection hr with hr; subst hr
            simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
            intro v hv'; rw [hv1] at hv'; cases hv'))
        q0 (.send st1)
        (send_feasible_prior hst1q (by
          rw [sent_after_send_other n0 (p := p0) (q := q0) (by decide) st1]
          exact fun s hs => ⟨s, hs, rfl⟩))
        (fun r hr st' hst => by
          injection hr with hr; subst hr
          simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
          intro v hv'; rw [hv1] at hv'; cases hv'))
      p0 (.send st2) (send_feasible_prior hst2p (by rw [hp1]; exact fun s hs => ⟨s, hs, rfl⟩))
      (fun r hr st' hst => by
        injection hr with hr; subst hr
        simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
        intro v hv'; rw [hv2] at hv'; cases hv'))
    q0 (.send st2) (send_feasible_prior hst2q (by rw [hq1]; exact fun s hs => ⟨s, hs, rfl⟩))
    (fun r hr st' hst => by
      injection hr with hr; subst hr
      simp only [Reaction.sends, List.mem_singleton] at hst; subst hst
      intro v hv'; rw [hv2] at hv'; cases hv')

theorem nTwoCh_chain (n0 : Network Nat) (st1 st2 : State Nat) :
    (nTwoCh n0 st1 st2).chain = n0.chain := rfl

theorem nTwoCh_views_p0 {n0 : Network Nat} {st1 st2 : State Nat}
    (hst1 : st1.channel.participants = [p0, q0]) (hst2 : st2.channel.participants = [p0, q0])
    (hsp0 : n0.sent p0 = []) (hrp0 : n0.received p0 = []) :
    (nTwoCh n0 st1 st2).views p0 =
      ⟨n0.chain, [⟨st2, [q0]⟩, ⟨st1, [q0]⟩], [⟨st2, [p0]⟩, ⟨st1, [p0]⟩]⟩ := by
  (simp? [nTwoCh, Network.views, Network.view, Network.applyHonest, HonestMove.send, State.recipients, hst1, hst2,
    show p0 ≠ q0 from by decide, hsp0, hrp0] says simp only [Network.views, Network.view, nTwoCh, Network.applyHonest, HonestMove.send, List.map_cons, List.map_nil, List.cons_append, List.nil_append, State.recipients, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.decide_and, show p0 ≠ q0 from by decide, decide_false, Bool.not_false, Bool.and_true, hst2, List.mem_cons, List.not_mem_nil, or_self, or_false, decide_true, List.filter_cons_of_pos, List.filter_nil, Bool.and_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, hst1, hrp0, List.append_nil, ↓reduceIte, hsp0])

theorem nTwoCh_views_q0 {n0 : Network Nat} {st1 st2 : State Nat}
    (hst1 : st1.channel.participants = [p0, q0]) (hst2 : st2.channel.participants = [p0, q0])
    (hsq0 : n0.sent q0 = []) (hrq0 : n0.received q0 = []) :
    (nTwoCh n0 st1 st2).views q0 =
      ⟨n0.chain, [⟨st2, [p0]⟩, ⟨st1, [p0]⟩], [⟨st2, [q0]⟩, ⟨st1, [q0]⟩]⟩ := by
  (simp? [nTwoCh, Network.views, Network.view, Network.applyHonest, HonestMove.send, State.recipients, hst1, hst2,
    show p0 ≠ q0 from by decide, show q0 ≠ p0 from by decide, hsq0, hrq0] says simp only [Network.views, Network.view, nTwoCh, Network.applyHonest, HonestMove.send, List.map_cons, List.map_nil, List.cons_append, List.nil_append, State.recipients, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.decide_and, decide_true, Bool.and_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil, show q0 ≠ p0 from by decide, decide_false, Bool.not_false, Bool.and_true, hst2, List.mem_cons, List.not_mem_nil, or_false, or_true, List.filter_cons_of_pos, hst1, hrq0, List.append_nil, ↓reduceIte, hsq0])


theorem nTwoCh_views_chain (n0 : Network Nat) (st1 st2 : State Nat) (r : Participant) :
    ((nTwoCh n0 st1 st2).views r).chain = n0.chain := rfl

/-- `FinalizableBy` for the channel `c` of `nTwoCh`'s first-sent state
    (sent first, so found second — via `List.mem_cons_of_mem` — in each
    participant's accumulated `sent`/`received`), on any base `n0` with
    `c` open and unfinalized (see `nOneCh_finalizable`). -/
theorem nTwoCh_finalizable_fst {n0 : Network Nat} {c : FixedPart} {Ω : Outcome Nat} {st2 : State Nat}
    (hcp : c.participants = [p0, q0]) (hst2p : st2.channel.participants = [p0, q0])
    (hne : st2.channel ≠ c) (hdur : c.challengeDuration = 4)
    (hopen : n0.chain.statusOf c = .open 0) (hnone : n0.chain.finalizedWith c.address = none)
    (hsp0 : n0.sent p0 = []) (hrp0 : n0.received p0 = [])
    (hsq0 : n0.sent q0 = []) (hrq0 : n0.received q0 = []) :
    (nTwoCh n0 (⟨c, 0, Ω, true, .opaque 0⟩ : State Nat) st2).views.FinalizableBy apps0
      (Ts apps0) c Ω [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by (simpa? using hr says simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
  rcases hr' with rfl | rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 p0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by (simp? [ConclusionProof, SignedState.ByAll, hcp] says simp only [ConclusionProof, SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true, and_self])) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_p0 hcp hst2p hsp0 hrp0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
      · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl,
          List.mem_cons_self ..⟩
    · rw [nTwoCh_views_p0 hcp hst2p hsp0 hrp0]
      intro t ht hcc _
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · exact absurd hcc hne
      · rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 q0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by (simp? [ConclusionProof, SignedState.ByAll, hcp] says simp only [ConclusionProof, SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true, and_self])) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_q0 hcp hst2p hsq0 hrq0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl,
          List.mem_cons_self ..⟩
      · exact .inl ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
    · rw [nTwoCh_views_q0 hcp hst2p hsq0 hrq0]
      intro t ht hcc _
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · exact absurd hcc hne
      · rfl

/-- `FinalizableBy` for the channel `c` of `nTwoCh`'s second-sent state
    (sent last, so found first — via `List.mem_cons_self` — in each
    participant's accumulated `sent`/`received`), on any base `n0` with
    `c` open and unfinalized. -/
theorem nTwoCh_finalizable_snd {n0 : Network Nat} {c : FixedPart} {Ω : Outcome Nat} {st1 : State Nat}
    (hcp : c.participants = [p0, q0]) (hst1p : st1.channel.participants = [p0, q0])
    (hne : st1.channel ≠ c) (hdur : c.challengeDuration = 4)
    (hopen : n0.chain.statusOf c = .open 0) (hnone : n0.chain.finalizedWith c.address = none)
    (hsp0 : n0.sent p0 = []) (hrp0 : n0.received p0 = [])
    (hsq0 : n0.sent q0 = []) (hrq0 : n0.received q0 = []) :
    (nTwoCh n0 st1 (⟨c, 0, Ω, true, .opaque 0⟩ : State Nat)).views.FinalizableBy apps0
      (Ts apps0) c Ω [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by (simpa? using hr says simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
  rcases hr' with rfl | rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 p0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by (simp? [ConclusionProof, SignedState.ByAll, hcp] says simp only [ConclusionProof, SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true, and_self])) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_p0 hst1p hcp hsp0 hrp0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_cons_self .., rfl⟩
      · exact .inr ⟨_, List.mem_cons_self .., rfl, List.mem_cons_self ..⟩
    · rw [nTwoCh_views_p0 hst1p hcp hsp0 hrp0]
      intro t ht hcc _
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · rfl
      · exact absurd hcc hne
  · refine conclude_strategy apps0 _ (canon_ok apps0 q0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by (simp? [ConclusionProof, SignedState.ByAll, hcp] says simp only [ConclusionProof, SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true, and_self])) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_q0 hst1p hcp hsq0 hrq0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_cons_self .., rfl, List.mem_cons_self ..⟩
      · exact .inl ⟨rfl, _, List.mem_cons_self .., rfl⟩
    · rw [nTwoCh_views_q0 hst1p hcp hsq0 hrq0]
      intro t ht hcc _
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · rfl
      · exact absurd hcc hne

/-- `FinalizableBy` for the channel `c` of `nTwoCh`'s second-sent state,
    when that state is NOT final (`isFinal = false`): via
    `latest_state_finalizable` (Liveness.lean) on the open channel, not
    `conclude_strategy`, so no participant's `sent` ever carries an
    `isFinal = true` state of `c`. On any base `n0` with `c` open. -/
theorem nTwoCh_finalizable_latest_snd {n0 : Network Nat} {c : FixedPart} {Ω : Outcome Nat} {st1 : State Nat}
    (hcp : c.participants = [p0, q0]) (hst1p : st1.channel.participants = [p0, q0])
    (hne : st1.channel ≠ c) (hdur : c.challengeDuration = 4)
    (hopen : n0.chain.statusOf c = .open 0)
    (hsp0 : n0.sent p0 = []) (hrp0 : n0.received p0 = [])
    (hsq0 : n0.sent q0 = []) (hrq0 : n0.received q0 = [])
    (hreach : (Nitro.network apps0 (Ts apps0)).Reachable
      (nTwoCh n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat))) :
    (nTwoCh n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat)).views.FinalizableBy apps0
      (Ts apps0) c Ω [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by (simpa? using hr says simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
  rcases hr' with rfl | rfl
  · refine latest_state_finalizable apps0 ((Ts apps0).T p0) (canon_ok apps0 p0)

      ⟨(nTwoCh n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat)).views p0, (Nitro.network_views_participant_reachable ⟨_, hreach⟩ p0)⟩
      ⟨c, by unfold FixedPart.IsTimed; rw [hdur]; decide⟩
      ⟨(⟨c, 0, Ω, false, .opaque 0⟩ : State Nat), [p0, q0]⟩ rfl (by rw [hcp]; decide) ?_
      (by (simp? [SignedState.ByAll, hcp] says simp only [SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true])) rfl ?_ ?_
      (.inr (.inl ⟨0, by rw [nTwoCh_views_chain]; exact hopen, le_rfl⟩))
    · simp only [@nTwoCh_views_p0 n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat) hst1p hcp hsp0 hrp0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_cons_self .., rfl⟩
      · exact .inr ⟨_, List.mem_cons_self .., rfl,
          List.mem_cons_self ..⟩
    · simp only [@nTwoCh_views_p0 n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat) hst1p hcp hsp0 hrp0]
      intro t ht hcc
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · right; rfl
      · exact absurd hcc hne
    · simp only [@nTwoCh_views_p0 n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat) hst1p hcp hsp0 hrp0]
      intro t ht hcc hfin
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · cases hfin
      · exact absurd hcc hne
  · refine latest_state_finalizable apps0 ((Ts apps0).T q0) (canon_ok apps0 q0)

      ⟨(nTwoCh n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat)).views q0, (Nitro.network_views_participant_reachable ⟨_, hreach⟩ q0)⟩
      ⟨c, by unfold FixedPart.IsTimed; rw [hdur]; decide⟩
      ⟨(⟨c, 0, Ω, false, .opaque 0⟩ : State Nat), [p0, q0]⟩ rfl (by rw [hcp]; decide) ?_
      (by (simp? [SignedState.ByAll, hcp] says simp only [SignedState.ByAll, hcp, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true])) rfl ?_ ?_
      (.inr (.inl ⟨0, by rw [nTwoCh_views_chain]; exact hopen, le_rfl⟩))
    · simp only [@nTwoCh_views_q0 n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat) hst1p hcp hsq0 hrq0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_cons_self .., rfl,
          List.mem_cons_self ..⟩
      · exact .inl ⟨rfl, _, List.mem_cons_self .., rfl⟩
    · simp only [@nTwoCh_views_q0 n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat) hst1p hcp hsq0 hrq0]
      intro t ht hcc
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · right; rfl
      · exact absurd hcc hne
    · simp only [@nTwoCh_views_q0 n0 st1 (⟨c, 0, Ω, false, .opaque 0⟩ : State Nat) hst1p hcp hsq0 hrq0]
      intro t ht hcc hfin
      (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · cases hfin
      · exact absurd hcc hne

/-- `gLWF`'s `status` is `[]`, the same as `g0`'s: a deposit only touches
    `balances`/`held` (`Network.deposit`'s doc comment), so every channel
    reads open and unfinalized on `gLWF`, for any `c`, not only `cLWF`. -/
theorem gLWF_open (c : FixedPart) : gLWF.statusOf c = .open 0 := rfl
theorem gLWF_finalizedWith (c : FixedPart) : gLWF.finalizedWith c.address = none := rfl
theorem gLWF_finalOutcome (c : FixedPart) : gLWF.finalOutcome c.address = none := rfl

/-- `ledger_topup_reorder_safe`. -/
theorem ledger_topup_reorder_safe.nonvacuity : ∃ A B χ : Address Nat, A ≠ B ∧ A ≠ χ ∧ B ≠ χ :=
  ⟨d0, d1, c1.address, by decide, by decide, by decide⟩

/-- `ledger_topup_deposit_funds`. -/
theorem ledger_topup_deposit_funds.nonvacuity : ∃ (s s' : Adjudicator Nat) (L : FixedPart) (A B χ : Address Nat) (a b c a' : Coins),
    A ≠ B ∧ A ≠ χ ∧ B ≠ χ ∧ s.balances.get L.address = a + b + c ∧
    s.deposit L.address (a + b + c) a' = some s' :=
  ⟨g0, _, c1, d0, d1, c3.address, 0, 0, 0, 0, by decide, by decide, by decide, rfl, rfl⟩


/-- `ledger_partial_withdrawal`, funded (D10 design decision): `cLWF` holds a
    concluded (`isFinal = true`) state so `Concluded` and `hsent` hold;
    `cL2F` holds a non-final (`isFinal = false`) latest state so
    `hL'sent` holds and `hL'out` goes through
    `nTwoCh_finalizable_latest_snd`, not `conclude_strategy`. `a = b = c
    = 1`, `a' = 2`: `a + b + c + a' = 5`, `cLWF`'s on-chain balance. -/
def cL2F : FixedPart := ⟨[p0, q0], 109, ⟨0⟩, 4, .ledger⟩
def ΩPWLF : Outcome Nat := .allocation [alloc cL2F.address 3, alloc d0 2]
def ΩPWLF' : Outcome Nat := .allocation [alloc d0 1, alloc d1 1, alloc c3.address 1]
def stPWLF : State Nat := ⟨cLWF, 0, ΩPWLF, true, .opaque 0⟩
def stPWLF' : State Nat := ⟨cL2F, 0, ΩPWLF', false, .opaque 0⟩
theorem stPWLF_voucher : stPWLF.voucher? = none := rfl
theorem stPWLF'_voucher : stPWLF'.voucher? = none := rfl
theorem cLWF_ne_cL2F : cLWF ≠ cL2F := by decide

def nPWF : Network Nat := nTwoCh nLWF1 stPWLF stPWLF'
theorem nPWF_reach : (Nitro.network apps0 (Ts apps0)).Reachable nPWF :=
  nTwoCh_reach nLWF1_reach stPWLF_voucher stPWLF'_voucher
    (by rw [nLWF1_sent_p0]; exact ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide),
      fun h => absurd h (by decide), by decide, by decide⟩)
    (by rw [nLWF1_sent_q0]; exact ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide),
      fun h => absurd h (by decide), by decide, by decide⟩)
    (by rw [nLWF1_sent_p0]; exact ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide),
      fun h => absurd h (by decide), by decide, by decide⟩)
    (by rw [nLWF1_sent_q0]; exact ⟨by decide, by decide, HonestSend.fundsCommitted_of_fundable (by decide),
      fun h => absurd h (by decide), by decide, by decide⟩)

theorem ledger_partial_withdrawal.nonvacuity : ∃ (v : Views Nat) (n : Network Nat) (A B : Participant) (dA dB : Nat)
    (L L' : LedgerChannel) (hL'c : (L' : FixedPart).RunsConsensus apps0) (χ : FixedPart)
    (a b c a' : Coins),
    (Nitro.network apps0 (Ts apps0)).Reachable n ∧ v = n.views ∧
    (L : FixedPart).participants = [A, B] ∧ (L' : FixedPart).participants = [A, B] ∧
    (L : FixedPart) ≠ (L' : FixedPart) ∧
    v.HoldsBalance (L : FixedPart).address (a + b + c + a') ∧
    Concluded v (L : FixedPart)
      (.allocation [alloc (L' : FixedPart).address (a + b + c), alloc (.external dA) a']) ∧
    (∀ p, ∀ t ∈ (v p).sent, t.state.channel = (L : FixedPart) → t.state.isFinal = true →
      t.state.outcome =
        .allocation [alloc (L' : FixedPart).address (a + b + c), alloc (.external dA) a']) ∧
    (∀ p, (v p).chain.finalizedWith (L : FixedPart).address = none) ∧
    (∀ p, 2 * ((Ts apps0).T p).ε ≤ (L : FixedPart).challengeDuration ∧
      2 * ((Ts apps0).T p).ε ≤ (L' : FixedPart).challengeDuration) ∧
    (∀ p, (v p).DeadlineAfter (L : FixedPart) ((Ts apps0).T p).ε ∧
      (v p).DeadlineAfter (L' : FixedPart) (2 * ((Ts apps0).T p).ε)) ∧
    (∀ p, (v p).chain.finalOutcome (L' : FixedPart).address = none) ∧
    (∀ p, ∀ t ∈ (v p).sent, t.state.channel = (L' : FixedPart) → t.state.isFinal = false) ∧
    v.FinalizableBy apps0 (Ts apps0) (L' : FixedPart)
      (.allocation [alloc (.external dA) a, alloc (.external dB) b, alloc χ.address c]) [A, B] := by
  refine ⟨nPWF.views, nPWF, p0, q0, 0, 1, ⟨cLWF, rfl⟩, ⟨cL2F, rfl⟩, rfl, c3, 1, 1, 1, 2,
    nPWF_reach, rfl, rfl, rfl, cLWF_ne_cL2F, ?_, ?_, ?_,
    fun r => by simp only [nPWF, nTwoCh_views_chain, nLWF1_chain]; exact gLWF_finalizedWith _,
    fun _ => ⟨(by decide : 2 * 2 ≤ 4), (by decide : 2 * 2 ≤ 4)⟩, ?_,
    fun r => by simp only [nPWF, nTwoCh_views_chain, nLWF1_chain]; exact gLWF_finalOutcome _, ?_,
    nTwoCh_finalizable_latest_snd rfl rfl cLWF_ne_cL2F rfl rfl rfl rfl rfl rfl nPWF_reach⟩
  · intro r; simp only [nPWF, nTwoCh_views_chain, nLWF1_chain]; exact gLWF_balance_cLWF
  · intro r hr
    have hr' : r = p0 ∨ r = q0 := by simp only [cLWF] at hr; (simpa? using hr says simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
    rcases hr' with rfl | rfl
    · refine ⟨⟨stPWLF, [p0, q0]⟩, ?_, by decide, rfl⟩
      simp only [nPWF]; rw [nTwoCh_views_p0 rfl rfl rfl rfl]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
      · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl,
          List.mem_cons_self ..⟩
    · refine ⟨⟨stPWLF, [p0, q0]⟩, ?_, by decide, rfl⟩
      simp only [nPWF]; rw [nTwoCh_views_q0 rfl rfl rfl rfl]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; (simp? at hq says simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl,
          List.mem_cons_self ..⟩
      · exact .inl ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
  · intro r t ht hcc _
    by_cases hrp0 : r = p0
    · subst hrp0; simp only [nPWF] at ht; rw [nTwoCh_views_p0 rfl rfl rfl rfl] at ht; (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · exact absurd hcc cLWF_ne_cL2F.symm
      · rfl
    · by_cases hrq0 : r = q0
      · subst hrq0; simp only [nPWF] at ht; rw [nTwoCh_views_q0 rfl rfl rfl rfl] at ht; (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
        rcases ht with rfl | rfl
        · exact absurd hcc cLWF_ne_cL2F.symm
        · rfl
      · exfalso
        have : (nPWF.views r).sent = [] := by
          rw [Network.views, Network.view]
          simp only [nPWF, nTwoCh, nLWF1, nLWF0, Network.deposit_sent, Network.applyHonest,
            HonestMove.send, if_neg hrp0, if_neg hrq0]
        rw [this] at ht; exact absurd ht List.not_mem_nil
  · intro r; simp only [nPWF]
    refine ⟨deadlineAfter_open (by rw [nTwoCh_views_chain, nLWF1_chain]; exact gLWF_open cLWF) _,
      deadlineAfter_open (by rw [nTwoCh_views_chain, nLWF1_chain]; exact gLWF_open cL2F) _⟩
  · intro r t ht hcc
    by_cases hrp0 : r = p0
    · subst hrp0; simp only [nPWF] at ht; rw [nTwoCh_views_p0 rfl rfl rfl rfl] at ht; (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl
      · rfl
      · exact absurd hcc cLWF_ne_cL2F
    · by_cases hrq0 : r = q0
      · subst hrq0; simp only [nPWF] at ht; rw [nTwoCh_views_q0 rfl rfl rfl rfl] at ht; (simp? at ht says simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
        rcases ht with rfl | rfl
        · rfl
        · exact absurd hcc cLWF_ne_cL2F
      · exfalso
        have : (nPWF.views r).sent = [] := by
          rw [Network.views, Network.view]
          simp only [nPWF, nTwoCh, nLWF1, nLWF0, Network.deposit_sent, Network.applyHonest,
            HonestMove.send, if_neg hrp0, if_neg hrq0]
        rw [this] at ht; exact absurd ht List.not_mem_nil
/-! ### SATP: a route of two peers (`p0` Alice, `q0` Bob) and of three. -/

def apps2 : Apps Nat := fun id => if id = ⟨1⟩ then satpVirtualRules else consensusRules
def Lr : FixedPart := ⟨[p0, q0], 10, ⟨0⟩, 4, .ledger⟩
def Vr : FixedPart := ⟨[p0, q0], 11, ⟨1⟩, 4, .virtual⟩
def r2 : Route Nat := ⟨[p0, q0], [Lr], Vr, 1, 0, fun p => p.key⟩
def vch : Voucher := ⟨Vr, 0, 0, 0, []⟩
def stV : State Nat :=
  ⟨Vr, 1, originalOutcome 0 1 1 0, false, .satpVirtual ⟨.none, vch⟩⟩

theorem r2_wf : r2.WellFormed apps2 := by
  refine ⟨rfl, by decide, by decide, by decide, fun i L h => ?_, rfl, rfl, fun i L h => ?_⟩
  · rcases i with _ | i
    · (simp? [r2] at h says simp only [r2, List.length_cons, List.length_nil, zero_add, zero_lt_one, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h); subst h; exact ⟨p0, q0, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
    · (simp? [r2] at h says simp only [r2, List.length_cons, List.length_nil, zero_add, add_lt_iff_neg_right, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h)
  · rcases i with _ | i
    · (simp? [r2] at h says simp only [r2, List.length_cons, List.length_nil, zero_add, zero_lt_one, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h); subst h; decide
    · (simp? [r2] at h says simp only [r2, List.length_cons, List.length_nil, zero_add, add_lt_iff_neg_right, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h)

/-- `satp_outcome_change_keeps_total`. -/
theorem satp_outcome_change_keeps_total.nonvacuity : ∃ (c : FixedPart) (alice bob : Participant) (proof : SupportProof Nat)
    (candidate : State Nat) (s0 : SignedState Nat),
    validateOutcomeChange c alice bob proof candidate = true ∧ proof.head? = some s0 :=
  ⟨Vr, p0, q0, [⟨stV, [p0, q0]⟩], stV, _, by decide, rfl⟩

def signed2 : List (Participant × State Nat) := [(p0, stV), (q0, stV)]
def sV1 : Adjudicator Nat := g0.setStatus Vr (.challenged 1 ⟨stV, 0 + 4⟩)
def sV2 : Adjudicator Nat := sV1.tick 4

theorem sV_reach : ReachableSigned apps2 signed2 sV2 := by
  refine .tail (.single (.mk p0 (.challenge Vr [⟨stV, [p0, q0]⟩] stV) g0 sV1 ?_ rfl))
    (.mk p0 (.tick 4) sV1 sV2 (fun _ h => by cases h) rfl)
  intro ss hss
  simp only [Op.proofStates, List.mem_singleton] at hss; subst hss
  exact ⟨by decide, fun v hv => by cases hv; intro q hq; cases hq⟩

/-- `satp_lemma_3_1`. -/
theorem satp_lemma_3_1.nonvacuity : ∃ (r : Route Nat) (alice bob : Participant) (signed : List (Participant × State Nat))
    (s : Adjudicator Nat) (Ω : Outcome Nat),
    r.WellFormed apps2 ∧ apps2 r.V.appDef = satpVirtualRules ∧ r.peers.head? = some alice ∧
    r.peers.getLast? = some bob ∧
    (∀ st : State Nat, (∀ q ∈ r.V.participants, (q, st) ∈ signed) → st.channel = r.V →
      (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (st.isFinal = true ∧ ∃ a b, PairOutcome (r.dest alice) (r.dest bob) st.outcome a b ∧
        a + b = r.a0 + r.b0)) ∧
    ReachableSigned apps2 signed s ∧ s.finalOutcome r.V.address = some Ω := by
  refine ⟨r2, p0, q0, signed2, sV2, _, r2_wf, rfl, rfl, rfl, fun st hall _ => ?_, sV_reach, rfl⟩
  have := hall p0 (by decide)
  (simp? [signed2, p0, q0] at this says simp only [signed2, p0, q0, List.mem_cons, Prod.mk.injEq, true_and, Participant.mk.injEq, zero_ne_one, false_and, List.not_mem_nil, or_self, or_false] at this)
  subst this
  exact .inl ⟨by decide, rfl⟩

/-- `satp_peers_can_finalize`. `netV` is reachable the same way `netC2` is: `p0`'s own send,
    then an adversary deliver of `q0`'s claimed signature. -/
def netV : NetworkState Nat p0 := ⟨g0, [⟨stV, [q0]⟩], [⟨stV, [p0]⟩]⟩

theorem netV_reach : (Nitro.participant apps2 (canon p0)).Reachable netV :=
  participant_reachable_adv
    (participant_reachable_honest (participant_reachable_init apps2 (canon p0)) (.send stV)
      (by honest_send))
    (.deliver ⟨stV, [q0]⟩) (⟨fun h => absurd h (by decide),
      fun v h hp => by cases h; exact absurd hp (by decide)⟩ :
      NetworkState.Unforged _ ⟨stV, [q0]⟩) (fun op h => by cases h)

theorem satp_peers_can_finalize.nonvacuity : ∃ (r : Route Nat) (alice bob : Participant) (net : NetworkState Nat p0)
    (s1 : SignedState Nat),
    Assumptions apps2 p0 (canon p0) ∧ r.WellFormed apps2 ∧ apps2 r.V.appDef = satpVirtualRules ∧
    p0 ∈ r.peers ∧ r.peers.head? = some alice ∧ r.peers.getLast? = some bob ∧
    2 * (canon p0).ε ≤ r.V.challengeDuration ∧
    (Nitro.participant apps2 (canon p0)).Reachable net ∧ net.Holds s1 ∧ s1.ByAll ∧
    s1.state.channel = r.V ∧ s1.state.turnNum = 1 ∧
    s1.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0 ∧
    (∀ t ∈ net.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧
        t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0)) ∧
    (∃ t, net.chain.statusOf r.V = .open t ∧ t ≤ 1) :=
  ⟨r2, p0, q0, netV, ⟨stV, [p0, q0]⟩, canon_ok _ _, r2_wf, rfl, by decide, rfl, rfl, by decide,
    netV_reach, holds_intro _ _ (by decide) (fun v hv => by cases hv; rfl), by decide, rfl, rfl,
    rfl, fun t ht _ => by (simp? [netV] at ht says simp only [netV, List.mem_cons, List.not_mem_nil, or_false] at ht); subst ht; exact .inl ⟨by decide, rfl⟩,
    ⟨0, rfl, by decide⟩⟩

/-- Three peers `p0`, `q0`, `w0`; `q0` is the intermediary. -/
def w0 : Participant := ⟨2⟩
def Lm3 : FixedPart := ⟨[p0, q0], 20, ⟨0⟩, 4, .ledger⟩
def Lp3 : FixedPart := ⟨[q0, w0], 21, ⟨0⟩, 4, .ledger⟩
def V3 : FixedPart := ⟨[p0, q0, w0], 22, ⟨1⟩, 4, .virtual⟩
def r3 : Route Nat := ⟨[p0, q0, w0], [Lm3, Lp3], V3, 1, 1, fun p => p.key⟩

theorem r3_wf : r3.WellFormed apps2 := by
  refine ⟨rfl, by decide, by decide, by decide, fun i L h => ?_, rfl, rfl, fun i L h => ?_⟩
  · rcases i with _ | _ | i
    · (simp? [r3] at h says simp only [r3, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h); subst h; exact ⟨p0, q0, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
    · (simp? [r3] at h says simp only [r3, zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq] at h); subst h; exact ⟨q0, w0, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
    · (simp? [r3] at h says simp only [r3, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] at h)
  · rcases i with _ | _ | i
    · (simp? [r3] at h says simp only [r3, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h); subst h; decide
    · (simp? [r3] at h says simp only [r3, zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq] at h); subst h; decide
    · (simp? [r3] at h says simp only [r3, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] at h)

def om3 : Allocation Nat := [alloc (.external 0) 0, alloc (.external 1) 0, r3.guarantee p0 q0]
def op3 : Allocation Nat := [alloc (.external 1) 0, alloc (.external 2) 0, r3.guarantee q0 w0]
def Sm : State Nat := ⟨Lm3, 1, .allocation om3, false, .opaque 0⟩
def Sp : State Nat := ⟨Lp3, 1, .allocation op3, false, .opaque 0⟩
def V0 : State Nat := ⟨V3, 0, originalOutcome 0 2 1 1, false, .satpVirtual ⟨.none, ⟨V3, 0, 0, 0, []⟩⟩⟩

/-- `q0` holds the all-signed pre-fund state of `V3` once it sent its own
    signature on `V0` and received `V0` signed by every participant of `V3`. -/
theorem prefund_V3 {net : NetworkState Nat q0} (hs : (⟨V0, [q0]⟩ : SignedState Nat) ∈ net.sent)
    (hr : (⟨V0, [p0, q0, w0]⟩ : SignedState Nat) ∈ net.received) : net.HoldsPrefund V3 := by
  refine ⟨⟨V0, [p0, q0, w0]⟩, holds_intro _ _ (fun q hq => ?_) (fun v hv => ?_), by decide, rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact .inr ⟨_, hr, rfl, List.mem_cons_self⟩
    · exact .inl ⟨rfl, _, hs, rfl⟩
    · exact .inr ⟨_, hr, rfl, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · cases hv
    rfl

/-- `q0`'s view: `q0` received the all-signed pre-fund state of `V3`, delivered right
    after `q0`'s own send of it and before `q0` sends either ledger state. `q0` signs a
    ledger state that funds `V3` only then (`HonestSend.fundsCommitted`).
    The same states without the delivery are the counterexample
    `net3` of `docs/counterexamples/satp_theorem_3_2.lean`, on the unrestricted machine. -/
def net3R : NetworkState Nat q0 :=
  ⟨g0, [⟨Sm, [p0]⟩, ⟨Sp, [w0]⟩, ⟨V0, [p0, q0, w0]⟩], [⟨Sm, [q0]⟩, ⟨Sp, [q0]⟩, ⟨V0, [q0]⟩]⟩

theorem net3R_reach : (Nitro.participant apps2 (canon q0)).Reachable net3R :=
  participant_reachable_adv
    (participant_reachable_adv
      (participant_reachable_honest
        (participant_reachable_honest
          (participant_reachable_adv
            (participant_reachable_honest (participant_reachable_init apps2 (canon q0)) (.send V0)
              (by honest_send))
            (.deliver ⟨V0, [p0, q0, w0]⟩)
            (⟨fun _ => ⟨⟨V0, [q0]⟩, by (simp? says simp only [NetworkState.applyHonest_send, List.mem_cons, List.not_mem_nil, or_false]), rfl⟩,
              fun v h hp => by
                (simp? [V0, State.voucher?] at h says simp only [State.voucher?, V0, Option.some.injEq] at h); subst h; exact absurd hp List.not_mem_nil⟩ :
              NetworkState.Unforged _ ⟨V0, [p0, q0, w0]⟩)
            (fun op h => by cases h))
          (.send Sp) ((HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
            fundsCommitted_one V3 (by decide) (prefund_V3 (by decide) (by decide)),
            fun h => absurd h (by decide), by decide, by decide⟩))
        (.send Sm) ((HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
          fundsCommitted_one V3 (by decide) (prefund_V3 (by decide) (by decide)),
          fun h => absurd h (by decide), by decide, by decide⟩))
      (.deliver ⟨Sp, [w0]⟩)
      (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ : NetworkState.Unforged _ ⟨Sp, [w0]⟩)
      (fun op h => by cases h))
    (.deliver ⟨Sm, [p0]⟩)
    (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ : NetworkState.Unforged _ ⟨Sm, [p0]⟩)
    (fun op h => by cases h)

theorem net3R_latest_m : HoldsLatestLedger net3R Lm3 om3 :=
  ⟨⟨Sm, [p0, q0]⟩, holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, rfl, rfl,
    by decide, .inl ⟨0, rfl, by decide⟩⟩

theorem net3R_latest_p : HoldsLatestLedger net3R Lp3 op3 :=
  ⟨⟨Sp, [q0, w0]⟩, holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, rfl, rfl,
    by decide, .inl ⟨0, rfl, by decide⟩⟩

theorem net3R_virtualSetup : HoldsVirtualSetup net3R r3 p0 w0 true :=
  ⟨fun t ht hc => by
      (simp? [net3R] at ht says simp only [net3R, List.mem_cons, List.not_mem_nil, or_false] at ht)
      rcases ht with rfl | rfl | rfl <;>
        first | exact ⟨rfl, rfl, .inl rfl⟩ | exact absurd hc (by decide),
    ⟨V0, [q0]⟩, by (simp? [net3R] says simp only [net3R, List.mem_cons, SignedState.mk.injEq, and_true, List.not_mem_nil, or_false, or_true]), rfl, rfl⟩

/-- `satp_theorem_3_2`. -/
theorem satp_theorem_3_2.nonvacuity : ∃ (r : Route Nat) (alice bob P Pprev Pnext : Participant) (i : Nat)
    (Lm Lp : TimedChannel (canon P).ε) (om : r.Round2Ledger Pprev P P r.b0)
    (op : r.Round2Ledger P Pnext P r.a0) (net : NetworkState Nat P),
    Assumptions apps2 P (canon P) ∧ r.WellFormed apps2 ∧ apps2 r.V.appDef = satpVirtualRules ∧
    r.peers.head? = some alice ∧ r.peers.getLast? = some bob ∧ 1 ≤ i ∧ i + 1 < r.peers.length ∧
    r.peers[i]? = some P ∧ r.peers[i - 1]? = some Pprev ∧ r.peers[i + 1]? = some Pnext ∧
    r.ledgers[i - 1]? = some (Lm : FixedPart) ∧ r.ledgers[i]? = some (Lp : FixedPart) ∧
    r.V.IsTimed (canon P).ε ∧
    (Nitro.participant apps2 (canon P)).Reachable net ∧
    HoldsLatestLedger net (Lm : FixedPart) om.outcome ∧ HoldsLatestLedger net (Lp : FixedPart) op.outcome ∧
    HoldsVirtualSetup net r alice bob true ∧
    (net.DeadlineAfter (Lm : FixedPart) (canon P).ε ∧
      net.DeadlineAfter (Lp : FixedPart) (canon P).ε ∧ net.DeadlineAfter r.V (canon P).ε) ∧
    (net.chain.finalizedWith (Lm : FixedPart).address = none ∧
      net.chain.finalizedWith (Lp : FixedPart).address = none ∧
      net.chain.finalizedWith r.V.address = none) :=
  ⟨r3, p0, w0, q0, p0, w0, 1, ⟨Lm3, by decide⟩, ⟨Lp3, by decide⟩,
    ⟨om3, 1, by unfold Route.LedgerAfterRound2; decide⟩, ⟨op3, 1, by unfold Route.LedgerAfterRound2; decide⟩,
    net3R, canon_ok _ _, r3_wf, rfl, rfl, rfl, le_rfl, by decide, rfl, rfl, rfl, rfl, rfl, by decide,
    net3R_reach, net3R_latest_m, net3R_latest_p, net3R_virtualSetup,
    ⟨deadlineAfter_open (t := 0) rfl _, deadlineAfter_open (t := 0) rfl _,
      deadlineAfter_open (t := 0) rfl _⟩, by decide, by decide, by decide⟩

/-- `satp_intermediary_before_round2`. `netB` is reachable the same way `net3R` is, with two
    sends and two delivers instead of three and three. -/
def omB : Allocation Nat := [alloc (.external 1) 1]
def SmB : State Nat := ⟨Lm3, 1, .allocation omB, false, .opaque 0⟩
def SpB : State Nat := ⟨Lp3, 1, .allocation omB, false, .opaque 0⟩
def netB : NetworkState Nat q0 := ⟨g0, [⟨SmB, [p0]⟩, ⟨SpB, [w0]⟩], [⟨SmB, [q0]⟩, ⟨SpB, [q0]⟩]⟩

theorem netB_reach : (Nitro.participant apps2 (canon q0)).Reachable netB :=
  participant_reachable_adv
    (participant_reachable_adv
      (participant_reachable_honest
        (participant_reachable_honest (participant_reachable_init apps2 (canon q0)) (.send SpB)
          (by honest_send))
        (.send SmB) (by honest_send))
      (.deliver ⟨SpB, [w0]⟩)
      (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ :
        NetworkState.Unforged _ ⟨SpB, [w0]⟩)
      (fun op h => by cases h))
    (.deliver ⟨SmB, [p0]⟩)
    (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ : NetworkState.Unforged _ ⟨SmB, [p0]⟩)
    (fun op h => by cases h)

theorem satp_intermediary_before_round2.nonvacuity : ∃ (r : Route Nat) (P : Participant) (i : Nat) (Lm Lp : TimedChannel (canon P).ε)
    (om op : Allocation Nat) (balm balp : Coins) (net : NetworkState Nat P),
    Assumptions apps2 P (canon P) ∧ r.WellFormed apps2 ∧ 1 ≤ i ∧ i + 1 < r.peers.length ∧
    r.peers[i]? = some P ∧ r.ledgers[i - 1]? = some (Lm : FixedPart) ∧
    r.ledgers[i]? = some (Lp : FixedPart) ∧
    r.LedgerBeforeRound2 om P balm ∧ r.LedgerBeforeRound2 op P balp ∧
    (Nitro.participant apps2 (canon P)).Reachable net ∧
    HoldsLatestLedger net (Lm : FixedPart) om ∧ HoldsLatestLedger net (Lp : FixedPart) op ∧
    (net.DeadlineAfter (Lm : FixedPart) (canon P).ε ∧
      net.DeadlineAfter (Lp : FixedPart) (canon P).ε) ∧
    (net.chain.finalizedWith (Lm : FixedPart).address = none ∧
      net.chain.finalizedWith (Lp : FixedPart).address = none) :=
  ⟨r3, q0, 1, ⟨Lm3, by decide⟩, ⟨Lp3, by decide⟩, omB, omB, 1, 1, netB, canon_ok _ _, r3_wf, le_rfl,
    by decide, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, netB_reach,
    ⟨⟨SmB, [p0, q0]⟩, holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, rfl, rfl,
      by decide, .inl ⟨0, rfl, by decide⟩⟩,
    ⟨⟨SpB, [q0, w0]⟩, holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, rfl, rfl,
      by decide, .inl ⟨0, rfl, by decide⟩⟩,
    ⟨deadlineAfter_open (t := 0) rfl _, deadlineAfter_open (t := 0) rfl _⟩, by decide⟩

/-- `satp_end_user_recovers`: Alice `p0` in the two-peer route; `V` is finalized with
    `(A : 1, B : 0)` by TIMEOUT, not an explicit final state: `p0` challenges `Vr` with its own
    setup state `V0r` (turn 0, not final — `originalOutcome 0 1 1 0` computes to exactly `ΩV`,
    `SATP.lean:111-112`), then waits out the deadline (`timeout_finalizes`, `Safety.lean:986-989`).
    This keeps every `Vr`-channel state `p0` ever sends non-final, as `HoldsVirtualSetup` requires;
    an explicit final conclude would need `p0` to sign a final state, breaking that. -/
def o0 : Allocation Nat := [alloc (.external 0) 0, alloc (.external 1) 0, r2.guarantee p0 q0]
def S0 : State Nat := ⟨Lr, 1, .allocation o0, false, .opaque 0⟩
def V0r : State Nat := ⟨Vr, 0, originalOutcome 0 1 1 0, false, .satpVirtual ⟨.none, vch⟩⟩
def ΩV : Outcome Nat := .allocation [alloc (.external 0) 1, alloc (.external 1) 0]
def sE : Adjudicator Nat := (g0.setStatus Vr (.challenged 0 ⟨V0r, 0 + Vr.challengeDuration⟩)).tick 4
def netE : NetworkState Nat p0 :=
  ⟨sE, [⟨V0r, [p0, q0]⟩, ⟨S0, [q0]⟩, ⟨V0r, [q0]⟩], [⟨S0, [p0]⟩, ⟨V0r, [p0]⟩]⟩

theorem netE_reach : (Nitro.participant apps2 (canon p0)).Reachable netE :=
  participant_reachable_honest
    (participant_reachable_land
      (participant_reachable_adv
        (participant_reachable_honest
          (participant_reachable_adv
            (participant_reachable_honest (participant_reachable_init apps2 (canon p0))
              (.send V0r) (by honest_send))
            (.deliver ⟨V0r, [q0]⟩) (by
              refine ⟨fun h => absurd h (by decide), fun v h hp => ?_⟩
              cases h; exact absurd hp (by decide)) (fun op h => by cases h))
          (.send S0) ((HonestMove.Feasible_send _ _ _).mpr ⟨by decide, by decide,
            fundsCommitted_one Vr (by decide)
              ⟨⟨V0r, [p0, q0]⟩, holds_intro _ _ (fun q hq => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl
                · exact .inl ⟨rfl, _, List.mem_cons_self, rfl⟩
                · exact .inr ⟨_, List.mem_cons_self, rfl, List.mem_cons_self⟩)
                (fun _ h => by cases h; rfl), by decide,
                rfl, rfl⟩, fun h => absurd h (by decide), by decide, by decide⟩))
        (.deliver ⟨S0, [q0]⟩) (by
          refine ⟨fun h => absurd h (by decide), fun v h => ?_⟩
          cases h) (fun op h => by cases h))
      (.challenge Vr [⟨V0r, [p0, q0]⟩] V0r)
      (fun ss h => by
        simp only [Op.proofStates, List.mem_singleton] at h; subst h
        refine ⟨fun q hq => ?_, fun v hv => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact .inl ⟨rfl, ⟨V0r, [p0]⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
          · exact .inr ⟨⟨V0r, [q0]⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
              List.mem_cons_self⟩
        · cases hv
          exact fun q hq => absurd hq List.not_mem_nil))
    (.wait 4) trivial

theorem satp_end_user_recovers.nonvacuity : ∃ (r : Route Nat) (alice bob P P1 : Participant) (L0 : TimedChannel (canon P).ε)
    (o : r.Round2Ledger P P1 P r.a0) (a b : Coins) (net : NetworkState Nat P),
    Assumptions apps2 P (canon P) ∧ r.WellFormed apps2 ∧ apps2 r.V.appDef = satpVirtualRules ∧
    r.peers.head? = some alice ∧ r.peers.getLast? = some bob ∧ P = alice ∧ r.peers[1]? = some P1 ∧
    r.ledgers[0]? = some (L0 : FixedPart) ∧
    r.V.IsTimed (canon P).ε ∧
    (Nitro.participant apps2 (canon P)).Reachable net ∧
    HoldsLatestLedger net (L0 : FixedPart) o.outcome ∧
    HoldsVirtualSetup net r alice bob true ∧ a + b = r.a0 + r.b0 ∧
    net.chain.finalOutcome r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]) ∧
    net.DeadlineAfter (L0 : FixedPart) (canon P).ε ∧
    net.chain.finalizedWith (L0 : FixedPart).address = none := by
  refine ⟨r2, p0, q0, p0, q0, ⟨Lr, by decide⟩, ⟨o0, 1, by unfold Route.LedgerAfterRound2; decide⟩, 1, 0, netE,
    canon_ok _ _, r2_wf, rfl, rfl, rfl, rfl, rfl, rfl, by decide, netE_reach,
    ⟨⟨S0, [p0, q0]⟩, ?_, by decide, rfl, rfl, rfl, ?_, ?_⟩, ⟨?_, ?_⟩, rfl, by decide, ?_, by decide⟩
  · refine ⟨fun q hq => ?_, fun v hv => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, ⟨S0, [p0]⟩, List.mem_cons_self, rfl⟩
      · exact .inr ⟨⟨S0, [q0]⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl, List.mem_cons_self⟩
    · (simp? [S0, State.voucher?] at hv says simp only [State.voucher?, S0, reduceCtorEq] at hv)
  · intro t ht hc
    simp only [netE, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨Or.inr rfl, rfl⟩
    · exact absurd hc (by decide)
  · exact .inl ⟨0, rfl, by decide⟩
  · intro t ht hc
    simp only [netE, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact absurd hc (by decide)
    · exact ⟨rfl, rfl, .inl rfl⟩
  · exact ⟨⟨V0r, [p0]⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl⟩
  · exact deadlineAfter_open (t := 0) rfl _

/-- `satp_reclaim_credits_intermediary`. -/
def sRC : Adjudicator Nat :=
  { g0 with status := [(V3, .finalized 0 (.allocation [alloc (.external 0) 1, alloc (.external 2) 1])
      (.allocation [alloc (.external 0) 1, alloc (.external 2) 1])),
    (Lm3, .finalized 0 (.allocation om3) (.allocation om3)),
    (Lp3, .finalized 0 (.allocation op3) (.allocation op3))] }

theorem satp_reclaim_credits_intermediary.nonvacuity : ∃ (s : Adjudicator Nat) (r : Route Nat) (alice bob P Pprev Pnext : Participant)
    (Lm Lp : FixedPart) (om op : Allocation Nat) (a b : Coins),
    (r.dest P ≠ r.dest Pprev ∧ r.dest P ≠ r.dest Pnext ∧ r.dest Pprev ≠ r.dest Pnext) ∧
    Lm.kind = .ledger ∧ Lp.kind = .ledger ∧ r.V.kind = .virtual ∧
    s.finalizedWith r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]) ∧
    s.finalOutcome Lm.address = some (.allocation om) ∧
    s.finalOutcome Lp.address = some (.allocation op) ∧
    om.find r.V.address = some (r.guarantee Pprev P) ∧ op.find r.V.address = some (r.guarantee P Pnext) ∧
    Lm ≠ Lp ∧
    (om.find (.external (r.dest Pprev)) ≠ none ∧ om.find (.external (r.dest P)) ≠ none) ∧
    (op.find (.external (r.dest P)) ≠ none ∧ op.find (.external (r.dest Pnext)) ≠ none) ∧
    a + b = r.a0 + r.b0 :=
  ⟨sRC, r3, p0, w0, q0, p0, w0, Lm3, Lp3, om3, op3, 1, 1, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

/-! ## Fixtures for the open witnesses of `Lemmas.lean`, `Liveness.lean`,
    `Reachable.lean`, `SATP.lean`, `Strategy.lean` and `Value.lean`. -/

/-- A two-participant channel for the `validChallenge`/`validResponse`
    witnesses below. -/
def cS : FixedPart := ⟨[p0, q0], 8, ⟨0⟩, 4, .virtual⟩

/-- The start-state voucher: unused fields, type `.none`. -/
def vS : Voucher := ⟨cS, 0, 0, 0, []⟩

/-- The start state of `cS`: signed by both participants, funded total 5. -/
def stS : State Nat := ⟨cS, 1, .allocation [alloc d0 3, alloc d1 2], false, .satpVirtual ⟨VType.none, vS⟩⟩
def ssS : SignedState Nat := ⟨stS, [p0, q0]⟩

/-- The challenge voucher: `p0` (alice) and `q0` (bob) both sign, same total. -/
def vCh : Voucher := ⟨cS, 0, 3, 2, [p0, q0]⟩

/-- The challenge state: `p0` (alice) signs, type `A`. -/
def stCh : State Nat := ⟨cS, 2, .allocation [alloc d0 3, alloc d1 2], false, .satpVirtual ⟨VType.A, vCh⟩⟩
def ssCh : SignedState Nat := ⟨stCh, [p0]⟩

theorem validChallenge_cS : validChallenge cS p0 q0 ssS ssCh = true := by decide

/-- The response voucher: a later version, same total. -/
def vRe : Voucher := ⟨cS, 1, 3, 2, [p0, q0]⟩

/-- The response state: `q0` (bob) signs, as `dc.type = .A` requires. -/
def stRe : State Nat := ⟨cS, 3, .allocation [alloc d0 3, alloc d1 2], false, .satpVirtual ⟨VType.AB, vRe⟩⟩
def ssRe : SignedState Nat := ⟨stRe, [p0, q0]⟩

theorem validResponse_cS : validResponse cS p0 q0 ssS ssCh ssRe = true := by decide

end ArmadaLean.Nitro.NonVacuity
