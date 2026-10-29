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

namespace ArmadaLean.Nitro.NonVacuity

open ArmadaLean.Nitro

/-! ## Shared values -/

def p0 : Participant := ⟨0⟩
def q0 : Participant := ⟨1⟩
/-- A one-participant channel; challenge duration 2. -/
def c1 : FixedPart := ⟨[p0], 0, ⟨0⟩, 2, .ledger⟩
/-- A second one-participant channel. -/
def c3 : FixedPart := ⟨[p0], 3, ⟨0⟩, 2, .ledger⟩
/-- A two-participant channel. -/
def c2 : FixedPart := ⟨[p0, q0], 1, ⟨0⟩, 2, .ledger⟩
def apps0 : Apps Nat := fun _ => consensusRules
def d0 : Address Nat := .external 0
def d1 : Address Nat := .external 1
def o1 : Allocation Nat := [alloc d0 1]
def g0 : Adjudicator Nat := Adjudicator.genesis

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

def cL : FixedPart := ⟨[p0], 5, ⟨0⟩, 2, .ledger⟩
def cV : FixedPart := ⟨[p0], 6, ⟨0⟩, 2, .virtual⟩
def oL : Allocation Nat := [alloc d0 0, alloc d1 0, ⟨cV.address, .guarantee 1 [d0, d1]⟩]
def oV : Allocation Nat := [alloc d0 1, alloc d1 0]
def sR : Adjudicator Nat :=
  { balances := [], held := 0,
    status := [(cL, .finalized 0 (.allocation oL) (.allocation oL)),
      (cV, .finalized 0 (.allocation oV) (.allocation oV))], now := 0 }

/-! ## `Safety.lean` -/

/-- `channel_address_inj`. -/
example : ∃ c c' : FixedPart, (c.address : Address Nat) = c'.address := ⟨c1, c1, rfl⟩

/-- `balances_absent_zero`. -/
example : ∃ (b : Balances Nat) (a : Address Nat), ∀ e ∈ b, e.1 ≠ a :=
  ⟨[], d0, fun _ h => absurd h (List.not_mem_nil)⟩

/-- `held_eq_channel_balances`. -/
example : ∃ s : Adjudicator Nat, Reachable apps0 s := ⟨g0, .refl⟩

/-- `deposit_effects`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (e x : Coins) (s' : Adjudicator Nat),
    s.deposit c.address e x = some s' := ⟨g0, c1, 0, 1, _, rfl⟩

/-- `deposit_requires_expectedHeld`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (e : Coins), s.balances.get c.address ≠ e :=
  ⟨g0, c1, 1, by decide⟩

/-- `deposit_respects_funding_order`. -/
example : ∃ (s s' : Adjudicator Nat) (caller : Participant) (c : FixedPart) (o : Allocation Nat)
    (k : Nat) (e : Entry Nat), Reachable apps0 s ∧ o.dedup = o ∧ o[k]? = some e ∧
    s.apply apps0 caller (.deposit c.address (o.aheadOf k) e.amount) = some s' :=
  ⟨g0, sDep, p0, c1, o1, 0, alloc d0 1, .refl, by decide, by decide, rfl⟩

/-- `deposit_can_happen`. -/
example : ∃ (c : FixedPart), c.kind = .ledger := ⟨c1, by decide⟩

/-- `deposits_in_order_succeed`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart), c.kind = .ledger ∧
    s.balances.get c.address = 0 :=
  ⟨g0, c1, by decide, by decide⟩

/-- `held_falls_only_by_payout`. -/
example : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat),
    Reachable apps0 s ∧ s.apply apps0 caller op = some s' ∧ s'.held < s.held :=
  ⟨sCon, _, p0, .transfer c1 d0, sCon_reach, rfl, by decide⟩

/-- `channel_balance_falls_only_by_redistribution`. -/
example : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat) (c : FixedPart),
    s.apply apps0 caller op = some s' ∧ s'.balances.get c.address < s.balances.get c.address :=
  ⟨sCon, _, p0, .transfer c1 d0, c1, rfl, by decide⟩

/-- `paid_out_monotone`. -/
example : ∃ s s' : Adjudicator Nat, Step apps0 s s' := ⟨g0, sDep, .mk _ _ _ _ g0_dep⟩

/-- `payout_priority_formula`. -/
example : ∃ (o : Allocation Nat) (k : Nat) (e : Entry Nat), o[k]? = some e :=
  ⟨o1, 0, alloc d0 1, by decide⟩

/-- `payout_earlier_paid_in_full`. -/
example : ∃ (held : Coins) (o : Allocation Nat) (i j : Nat) (ei ej : Entry Nat) (pi pj : Coins),
    o[i]? = some ei ∧ o[j]? = some ej ∧ i < j ∧ (o.payout held)[i]? = some (ei.dest, pi) ∧
    (o.payout held)[j]? = some (ej.dest, pj) ∧ 0 < pj :=
  ⟨2, [alloc d0 1, alloc d1 1], 0, 1, alloc d0 1, alloc d1 1, 1, 1, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- `affords_when_fully_funded`. -/
example : ∃ (held : Coins) (o : Allocation Nat), o.total ≤ held := ⟨1, o1, by decide⟩

/-- `transfer_effects`. -/
example : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (s' : Adjudicator Nat),
    Reachable apps0 s ∧ s.transfer a b = some s' := ⟨sCon, c1, d0, _, sCon_reach, rfl⟩

/-- `transfer_can_happen`. -/
example : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (o : Allocation Nat) (amt : Coins),
    a.kind = .ledger ∧ b.fundable = true ∧
    s.finalOutcome a.address = some (.allocation o) ∧ o.find b = some ⟨b, .alloc amt⟩ :=
  ⟨sCon, c1, d0, o1, 1, by decide, by decide, by decide, by decide⟩

/-- `transfer_fails_otherwise`. -/
example : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat),
    ∀ o, s.finalOutcome a.address = some (.allocation o) → ∀ amt, o.find b ≠ some ⟨b, .alloc amt⟩ :=
  ⟨g0, c1, d0, fun o h => by simp [g0, Adjudicator.genesis, Adjudicator.statusOf] at h⟩

/-- `transfer_zero_moves_nothing`. -/
example : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (s' : Adjudicator Nat),
    s.transfer a b = some s' ∧
    ∀ o, s.finalOutcome a.address = some (.allocation o) → o.paidTo (s.balances.get a.address) b = 0 :=
  ⟨sCon.setStatus c1 (.finalized 0 (.allocation [alloc d0 0]) (.allocation [alloc d0 0])), c1, d0, _,
    rfl, fun o h => by
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus,
        if_true, ChannelStatus.finalOutcome_finalized, Option.some.injEq, Outcome.allocation.injEq] at h
      subst h; decide⟩

/-- `transfer_requires_finalized`. -/
example : ∃ (s : Adjudicator Nat) (a : FixedPart) (b : Address Nat) (s' : Adjudicator Nat),
    s.transfer a b = some s' := ⟨sCon, c1, d0, _, rfl⟩

/-- `redistribution_ignores_caller`. -/
example : ∃ op : Op Nat, op.isRedistribution = true := ⟨.transfer c1 d0, rfl⟩

/-- `redistribution_conserves_total`. -/
example : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat),
    Reachable apps0 s ∧ op.isRedistribution = true ∧ s.apply apps0 caller op = some s' :=
  ⟨sCon, _, p0, .transfer c1 d0, sCon_reach, rfl, rfl⟩

/-- `FinalizedTwoWays.mono`. -/
example : ∃ (s s' : Adjudicator Nat) (c : FixedPart) (Ω Ω' : Outcome Nat),
    FinalizedTwoWays apps0 s c Ω ∧ s.now ≤ s'.now ∧ Redistributed Ω Ω' :=
  ⟨sCon, sCon, c1, _, _, ⟨sDep, sCon, p0, sDep_reach, .inl ⟨ssF, sDep_con, by decide, .refl⟩⟩,
    le_rfl, .refl⟩

/-- `statusOrigin_of_eq`. -/
example : ∃ (s s' : Adjudicator Nat) (c : FixedPart),
    StatusOrigin apps0 s c ∧ s'.statusOf c = s.statusOf c ∧ s.now ≤ s'.now :=
  ⟨g0, g0, c1, trivial, rfl, le_rfl⟩

/-- `statusOrigin_redistribute`. -/
example : ∃ (s s' : Adjudicator Nat) (c : FixedPart) (Ω Ω' : Outcome Nat),
    StatusOrigin apps0 s c ∧ (s.statusOf c).finalOutcome s.now = some Ω ∧ Redistributed Ω Ω' ∧
    s.now ≤ s'.now ∧ s'.statusOf c = (s.statusOf c).withOutcome Ω' :=
  ⟨sCon, sCon, c1, _, _, ⟨sDep, sCon, p0, sDep_reach, .inl ⟨ssF, sDep_con, by decide, .refl⟩⟩,
    rfl, .refl, le_rfl, rfl⟩

/-- `statusOrigin_step`. -/
example : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat),
    Reachable apps0 s ∧ (∀ c, StatusOrigin apps0 s c) ∧ s.apply apps0 caller op = some s' :=
  ⟨g0, sDep, p0, _, .refl, fun _ => trivial, g0_dep⟩

/-- `statusOrigin_reachable`. -/
example : ∃ s : Adjudicator Nat, Reachable apps0 s := ⟨g0, .refl⟩

/-- `finalized_two_ways`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (Ω : Outcome Nat),
    Reachable apps0 s ∧ s.finalOutcome c.address = some Ω := ⟨sCon, c1, _, sCon_reach, rfl⟩

/-- `finalized_permanent`. -/
example : ∃ (s s' : Adjudicator Nat) (c : FixedPart), Step apps0 s s' ∧ s.mode c = .finalized :=
  ⟨sCon, _, c1, .mk p0 (.tick 1) _ _ rfl, by decide⟩

/-- `finalized_outcome_only_redistributed`. -/
example : ∃ (s s' : Adjudicator Nat) (c : FixedPart) (Ω : Outcome Nat),
    Step apps0 s s' ∧ s.finalOutcome c.address = some Ω :=
  ⟨sCon, _, c1, _, .mk p0 (.tick 1) _ _ rfl, rfl⟩

/-- A challenge of the open channel `c1` with the state `stO` signed by `p0`. -/
def stO : State Nat := ⟨c1, 1, .allocation o1, false, .opaque 0⟩
def ssO : SignedState Nat := ⟨stO, [p0]⟩

/-- `challenge_requires`. -/
example : ∃ (s : Adjudicator Nat) (challenger : Participant) (c : FixedPart)
    (proof : SupportProof Nat) (candidate : State Nat) (s' : Adjudicator Nat),
    s.challenge apps0 challenger c proof candidate = some s' := ⟨g0, p0, c1, [ssO], stO, _, rfl⟩

/-- `challenge_fails_when_finalized`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart), s.mode c = .finalized := ⟨sCon, c1, by decide⟩

/-- The status of `c1` after the challenge with `stO`. -/
def sCh : Adjudicator Nat := g0.setStatus c1 (.challenged 1 ⟨stO, 2⟩)

/-- `rechallenge_equal_turn_fails`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (candidate : State Nat),
    s.mode c = .challenge ∧ candidate.turnNum ≤ (s.statusOf c).turnNumRecord :=
  ⟨sCh, c1, stO, by decide, by decide⟩

/-- `challenge_can_happen`. -/
example : ∃ (s : Adjudicator Nat) (challenger : Participant) (c : FixedPart)
    (proof : SupportProof Nat) (candidate : State Nat),
    challenger ∈ c.participants ∧ (apps0 c.appDef).supports c proof candidate = true ∧
    candidate.channel = c ∧
    ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
     (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum)) :=
  ⟨g0, p0, c1, [ssO], stO, by decide, by decide, rfl, .inl ⟨by decide, by decide⟩⟩

/-- `challenge_effects`. -/
example : ∃ (s : Adjudicator Nat) (challenger : Participant) (c : FixedPart)
    (proof : SupportProof Nat) (candidate : State Nat) (s' : Adjudicator Nat),
    s.challenge apps0 challenger c proof candidate = some s' ∧ 0 < c.challengeDuration :=
  ⟨g0, p0, c1, [ssO], stO, _, rfl, by decide⟩

/-- `checkpoint_requires`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (proof : SupportProof Nat) (candidate : State Nat)
    (s' : Adjudicator Nat), s.checkpoint apps0 c proof candidate = some s' :=
  ⟨g0, c1, [ssO], stO, _, rfl⟩

/-- `checkpoint_can_happen`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (proof : SupportProof Nat) (candidate : State Nat),
    s.mode c ≠ .finalized ∧ (apps0 c.appDef).supports c proof candidate = true ∧
    candidate.channel = c ∧ (s.statusOf c).turnNumRecord < candidate.turnNum :=
  ⟨g0, c1, [ssO], stO, by decide, by decide, rfl, by decide⟩

/-- `turnNumRecord_monotone`. -/
example : ∃ s s' : Adjudicator Nat, Step apps0 s s' := ⟨g0, sDep, .mk _ _ _ _ g0_dep⟩

/-- `conclude_requires`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat) (s' : Adjudicator Nat),
    s.conclude c ss = some s' := ⟨sDep, c1, ssF, _, rfl⟩

/-- `conclude_needs_all`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat) (s' : Adjudicator Nat)
    (p : Participant), s.conclude c ss = some s' ∧ p ∈ c.participants :=
  ⟨sDep, c1, ssF, _, p0, rfl, by decide⟩

/-- `conclude_can_happen`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat),
    s.mode c ≠ .finalized ∧ ConclusionProof c ss := ⟨sDep, c1, ssF, by decide, by decide⟩

/-- `conclude_moves_no_value`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (ss : SignedState Nat) (s' : Adjudicator Nat),
    s.conclude c ss = some s' := ⟨sDep, c1, ssF, _, rfl⟩

/-- `timeout_finalizes`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (t : Nat) (ch : Challenge Nat),
    s.statusOf c = .challenged t ch ∧ ch.deadline ≤ s.now :=
  ⟨sCh.tick 2, c1, 1, ⟨stO, 2⟩, by decide, by decide⟩

/-- `challenge_in_progress_before_deadline`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart) (t : Nat) (ch : Challenge Nat),
    s.statusOf c = .challenged t ch ∧ s.now < ch.deadline :=
  ⟨sCh, c1, 1, ⟨stO, 2⟩, by decide, by decide⟩

/-- `failed_op_no_effect`. -/
example : ∃ (caller : Participant) (op : Op Nat) (s : Adjudicator Nat),
    s.apply apps0 caller op = none := ⟨p0, .transfer c1 d0, g0, rfl⟩

/-- `funding_decoupled_from_rules`. -/
example : ∃ op : Op Nat, op.isRedistribution = false ∧ ∀ a e x, op ≠ .deposit a e x :=
  ⟨.tick 0, rfl, fun _ _ _ h => by cases h⟩

/-- A ForceMove run of one state for `c1` (one participant). -/
def vtAll : State Nat → State Nat → Bool := fun s1 s2 => decide (s2.outcome = s1.outcome)

/-- `forceMove_supports_valid_run`. -/
example : ∃ (vt : State Nat → State Nat → Bool) (c : FixedPart) (proof : SupportProof Nat)
    (candidate : State Nat), (forceMoveRules vt).supports c proof candidate = true :=
  ⟨vtAll, c1, [⟨stO, [p0]⟩], stO, by decide⟩

/-- `forceMove_conclude_keeps_outcome`: two moves in the two-party channel
    `c2`, the first by `p0` at turn 0, the second by `q0` at turn 1. -/
def stM0 : State Nat := ⟨c2, 0, .allocation o1, false, .opaque 0⟩
def stM1 : State Nat := ⟨c2, 1, .allocation o1, false, .opaque 0⟩

example : ∃ (vt : State Nat → State Nat → Bool) (c : FixedPart) (proof : SupportProof Nat)
    (candidate : State Nat) (i : Nat) (m1 m2 : SignedState Nat),
    (forceMoveRules vt).supports c proof candidate = true ∧ proof[i]? = some m1 ∧
    proof[i + 1]? = some m2 :=
  ⟨vtAll, c2, [⟨stM0, [p0]⟩, ⟨stM1, [q0]⟩], stM1, 0, ⟨stM0, [p0]⟩, ⟨stM1, [q0]⟩,
    by decide, by decide, by decide⟩

/-- `mover_determined_by_turn`. -/
example : ∃ s t : State Nat, s.channel = t.channel ∧ s.turnNum = t.turnNum := ⟨stO, stO, rfl, rfl⟩

/-- `reclaim_requires`. -/
example : ∃ (s : Adjudicator Nat) (l v : FixedPart) (s' : Adjudicator Nat),
    s.reclaim l v = some s' := ⟨sR, cL, cV, _, rfl⟩

/-- `reclaim_effects`. -/
example : ∃ (s : Adjudicator Nat) (l v : FixedPart) (s' : Adjudicator Nat) (oL oV : Allocation Nat)
    (x : Coins) (left right : Address Nat),
    s.finalOutcome l.address = some (.allocation oL) ∧
    s.finalizedWith v.address = some (.allocation oV) ∧
    oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧ left ≠ right ∧
    left ≠ v.address ∧ right ≠ v.address ∧ l ≠ v ∧ oL.dedup = oL ∧ s.reclaim l v = some s' :=
  ⟨sR, cL, cV, _, oL, oV, 1, d0, d1, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, rfl⟩

/-- `reclaim_can_happen`. -/
example : ∃ (s : Adjudicator Nat) (l v : FixedPart) (oL oV : Allocation Nat) (x : Coins)
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

example : ∃ (s : Adjudicator Nat) (l v : FixedPart) (oL oV : Allocation Nat) (x : Coins)
    (left right : Address Nat),
    s.finalOutcome l.address = some (.allocation oL) ∧
    s.finalizedWith v.address = some (.allocation oV) ∧
    oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧
    ((oL.remove v.address).find left = none ∨ (oL.remove v.address).find right = none ∨
      oV.amountAt 0 + oV.amountAt 1 ≠ x) :=
  ⟨sR2, cL, cV, oL2, oV, 2, d0, d1, by decide, by decide, by decide, by decide⟩

/-- `mode_of_absent`. -/
example : ∃ (s : Adjudicator Nat) (c : FixedPart), ∀ e ∈ s.status, e.1 ≠ c :=
  ⟨g0, c1, fun _ h => absurd h List.not_mem_nil⟩

/-- `held_changes_only_by_deposit_payout`. -/
example : ∃ (s s' : Adjudicator Nat) (caller : Participant) (op : Op Nat),
    s.apply apps0 caller op = some s' ∧ s'.held ≠ s.held :=
  ⟨g0, sDep, p0, _, g0_dep, by decide⟩

/-! ## Chain facts used by the strategies below -/

section Chain

variable {E : Type} [DecidableEq E]

/-- `Adjudicator.finalizedWith_apply` (`Lemmas.lean`): the outcome of
    finalization never changes. -/
alias finalizedWith_apply := Adjudicator.finalizedWith_apply

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
  | tick dt => simp at h; subst h; rfl
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

theorem applyAdv_now_le (apps : Apps E) {p : Participant} (m : AdvMove E) (n : NetworkState E p) :
    n.chain.now ≤ (n.applyAdv apps m).chain.now := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases h : n.chain.apply apps caller op with
    | none => exact le_rfl
    | some s' => exact Adjudicator.apply_now_le h
  | deliver ss => exact le_rfl
  | tick dt => simp [NetworkState.applyAdv]

theorem applyAdv_sent (apps : Apps E) {p : Participant} (m : AdvMove E) (n : NetworkState E p) :
    (n.applyAdv apps m).sent = n.sent := by
  cases m with
  | chain caller op => simp only [NetworkState.applyAdv]; cases n.chain.apply apps caller op <;> rfl
  | deliver ss => rfl
  | tick dt => rfl

theorem FeasibleSeq.now_le {apps : Apps E} {p : Participant} {T : Threat E p}
    {n n' : NetworkState E p} {advs : List (AdvMove E)} (h : T.FeasibleSeq apps n advs n') :
    n.chain.now ≤ n'.chain.now := by
  induction h with
  | nil => exact le_rfl
  | cons _ _ ih => exact le_trans (applyAdv_now_le _ _ _) ih

theorem FeasibleSeq.sent_eq {apps : Apps E} {p : Participant} {T : Threat E p}
    {n n' : NetworkState E p} {advs : List (AdvMove E)} (h : T.FeasibleSeq apps n advs n') :
    n'.sent = n.sent := by
  induction h with
  | nil => rfl
  | cons _ _ ih => rw [ih, applyAdv_sent]

/-- An invariant of the adversary's steps that holds while the clock is
    below `t1` holds at the end of a prefix that ends below `t1`. -/
theorem FeasibleSeq.inv {apps : Apps E} {p : Participant} {T : Threat E p}
    (P : NetworkState E p → Prop) (t1 : Time)
    (hstep : ∀ n m, T.feasible n m → P n → (n.applyAdv apps m).chain.now < t1 →
      P (n.applyAdv apps m))
    {n n' : NetworkState E p} {advs : List (AdvMove E)} (h : T.FeasibleSeq apps n advs n')
    (hP : P n) (ht : n'.chain.now < t1) : P n' := by
  induction h with
  | nil => exact hP
  | cons hm hrest ih =>
    exact ih (hstep _ _ hm hP (lt_of_le_of_lt (FeasibleSeq.now_le hrest) ht)) ht

/-- An invariant of the adversary's steps holds at the end of a prefix. -/
theorem FeasibleSeq.inv0 {apps : Apps E} {p : Participant} {T : Threat E p}
    (P : NetworkState E p → Prop) (hstep : ∀ n m, T.feasible n m → P n → P (n.applyAdv apps m))
    {n n' : NetworkState E p} {advs : List (AdvMove E)} (h : T.FeasibleSeq apps n advs n')
    (hP : P n) : P n' := by
  induction h with
  | nil => exact hP
  | cons hm _ ih => exact ih (hstep _ _ hm hP)

/-- Applying a chain operation, as `applyAdv` and `applyHonest` do. -/
theorem chain_applyAdv (apps : Apps E) {p : Participant} (caller : Participant) (op : Op E)
    (n : NetworkState E p) :
    (n.applyAdv apps (.chain caller op)).chain = (n.chain.apply apps caller op).getD n.chain := by
  simp only [NetworkState.applyAdv]; cases n.chain.apply apps caller op <;> rfl

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
  · exact .inl (finalizedWith_apply h hf)
  · by_cases hon : opOn op c
    · obtain ⟨t, ht⟩ := ho
      cases op with
      | deposit a e x => exact absurd hon id
      | tick dt => exact absurd hon id
      | transfer a b =>
        simp only [opOn] at hon; subst a
        obtain ⟨o, _, _, hfo, -⟩ := Adjudicator.transfer_some h
        simp [ht] at hfo
      | reclaim l v =>
        simp only [opOn] at hon; subst l
        obtain ⟨_, _, _, _, _, hL, -⟩ := Adjudicator.reclaim_some h
        simp [ht] at hL
      | challenge c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        refine .inr (.inr ⟨cand.turnNum, ⟨cand, s.now + c.challengeDuration⟩, by simp, ?_⟩)
        show t0 + ε ≤ s.now + c.challengeDuration
        exact Nat.add_le_add ht0 hdur
      | checkpoint c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        exact .inr (.inl ⟨cand.turnNum, by simp⟩)
      | conclude c' ss' =>
        simp only [opOn] at hon; subst c'
        obtain ⟨⟨-, hch, hfin, hall⟩, rfl⟩ := Adjudicator.conclude_some h
        obtain ⟨x, hx, hst⟩ := hU ss' (List.mem_singleton_self _) (hall p (hch ▸ hp))
        have := hsent x hx (by rw [hst]; exact hch) (by rw [hst]; exact hfin)
        rw [hst] at this
        exact .inl (by simp [this])
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
        simp [ht, hnexp] at hfo
      | reclaim l v =>
        simp only [opOn] at hon; subst l
        obtain ⟨_, _, _, _, _, hL, -⟩ := Adjudicator.reclaim_some h
        simp [ht, hnexp] at hL
      | challenge c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        refine .inr (.inr ⟨cand.turnNum, ⟨cand, s.now + c.challengeDuration⟩, by simp, ?_⟩)
        show t0 + ε ≤ s.now + c.challengeDuration
        exact Nat.add_le_add ht0 hdur
      | checkpoint c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        exact .inr (.inl ⟨cand.turnNum, by simp⟩)
      | conclude c' ss' =>
        simp only [opOn] at hon; subst c'
        obtain ⟨⟨-, hch, hfin, hall⟩, rfl⟩ := Adjudicator.conclude_some h
        obtain ⟨x, hx, hst⟩ := hU ss' (List.mem_singleton_self _) (hall p (hch ▸ hp))
        have := hsent x hx (by rw [hst]; exact hch) (by rw [hst]; exact hfin)
        rw [hst] at this
        exact .inl (by simp [this])
    · exact .inr (.inr (by rw [statusOf_apply_of_not_on h hon]; exact hc))

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
      | finalized t f o => rw [hs] at hn; simp at hn
    · exact .inl hn
  refine .move (.chain (.conclude c ss)) hal
    (by simpa [HonestMove.Feasible, Op.proofStates] using hh) fun advs n' ⟨hseq, htime⟩ => .done ?_
  have hK : n'.sent = net.sent ∧ net.chain.now ≤ n'.chain.now ∧
      ConcludeInv c Ω (net.chain.now + T.ε) n'.chain := by
    refine FeasibleSeq.inv (fun n => n.sent = net.sent ∧ net.chain.now ≤ n.chain.now ∧
      ConcludeInv c Ω (net.chain.now + T.ε) n.chain) (net.chain.now + T.ε) ?_ hseq
      ⟨rfl, le_rfl, hK0⟩ htime
    intro n m hm ⟨hs0, ht0, hk⟩ hlt
    refine ⟨by rw [applyAdv_sent]; exact hs0, le_trans ht0 (applyAdv_now_le _ _ _), ?_⟩
    cases m with
    | deliver ss' => exact hk
    | tick dt =>
      have happ : n.chain.apply apps p (.tick dt) = some (n.chain.tick dt) := rfl
      exact concludeInv_apply happ n.sent hp (by simp [Op.proofStates]) (hs0 ▸ hsent) hdur ht0
        hlt hk
    | chain caller op =>
      rw [chain_applyAdv]
      cases happ : n.chain.apply apps caller op with
      | none => exact hk
      | some s' =>
        rw [chain_applyAdv, happ] at hlt
        exact concludeInv_apply happ n.sent hp
          (fun ss' hss' => (B.unforgeable n caller op hm ss' hss').1) (hs0 ▸ hsent) hdur ht0 hlt hk
  obtain ⟨-, -, hk⟩ := hK
  show (n'.applyHonest apps (.chain (.conclude c ss))).chain.finalizedWith c.address = some Ω
  simp only [NetworkState.applyHonest]
  rcases hk with hf | ⟨t, ho⟩ | ⟨t, ch, ht, hd⟩
  · cases happ : n'.chain.apply apps p (.conclude c ss) with
    | none => simpa using hf
    | some s' => simpa using finalizedWith_apply happ hf
  · have hm : n'.chain.mode c ≠ .finalized := by rw [Adjudicator.mode_eq, ho]; simp
    rw [Adjudicator.apply_conclude, (conclude_can_happen _ _ _ hm hproof).1]
    simp [hΩ]
  · have hm : n'.chain.mode c ≠ .finalized := by
      rw [Adjudicator.mode_eq, ht]
      simp only [ChannelStatus.mode_challenged, ne_eq]
      split
      · rename_i h'; exact absurd (lt_of_le_of_lt (le_trans hd h') htime) (lt_irrefl _)
      · simp
    rw [Adjudicator.apply_conclude, (conclude_can_happen _ _ _ hm hproof).1]
    simp [hΩ]

/-- The chain part of the invariant of `wait_strategy`. -/
def WaitInv (c : FixedPart) (T0 : Nat) (ch : Challenge E) (s : Adjudicator E) : Prop :=
  s.statusOf c = .challenged T0 ch ∨ s.finalizedWith c.address = some ch.state.outcome

theorem waitInv_apply {apps : Apps E} {caller p : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') {c : FixedPart} {T0 : Nat}
    {ch : Challenge E} (sent : List (SignedState E)) (hc : apps c.appDef = consensusRules)
    (hp : p ∈ c.participants)
    (hU : ∀ ss ∈ op.proofStates, p ∈ ss.signers → ∃ x ∈ sent, x.state = ss.state)
    (hsent : ∀ t ∈ sent, t.state.channel = c → t.state.turnNum ≤ T0 ∧ t.state.isFinal = false)
    (hk : WaitInv c T0 ch s) : WaitInv c T0 ch s' := by
  rcases hk with hst | hf
  · -- a supported candidate of `c` is a state `p` sent, so its turn is at most `T0`
    have hsupp : ∀ proof cand, (∀ ss ∈ proof, p ∈ ss.signers → ∃ x ∈ sent, x.state = ss.state) →
        (apps c.appDef).supports c proof cand = true → cand.turnNum ≤ T0 := by
      intro proof cand hU' hs
      rw [hc] at hs
      match proof, hs with
      | [ss], hs =>
        simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hss, hch⟩, hall⟩ := hs
        obtain ⟨x, hx, hxs⟩ := hU' ss (List.mem_singleton_self _) (hall p (hch ▸ hp))
        rw [← hss, ← hxs]
        exact (hsent x hx (by rw [hxs]; exact hch)).1
    by_cases hon : opOn op c
    · cases op with
      | deposit a e x => exact absurd hon id
      | tick dt => exact absurd hon id
      | transfer a b =>
        simp only [opOn] at hon; subst a
        obtain ⟨_, _, _, _, _, _, _, _, hs, hn, _, _⟩ := Adjudicator.transfer_some h
        refine .inr ?_
        rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.statusOf_of_status hs]
        simp [hst]
      | reclaim l v =>
        simp only [opOn] at hon; subst l
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := Adjudicator.reclaim_some h
        exact .inr (by simp [hst])
      | challenge c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨⟨-, hs, -, hm⟩, rfl⟩ := Adjudicator.challenge_some h
        have := hsupp proof cand hU hs
        rw [Adjudicator.mode_eq, hst] at hm
        simp only [ChannelStatus.mode_challenged, ChannelStatus.turnNumRecord_challenged] at hm
        rcases hm with ⟨hm, -⟩ | ⟨-, hlt⟩
        · split at hm <;> cases hm
        · omega
      | checkpoint c' proof cand =>
        simp only [opOn] at hon; subst c'
        obtain ⟨⟨-, hs, -, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
        have := hsupp proof cand hU hs
        rw [hst] at hlt; simp at hlt; omega
      | conclude c' ss' =>
        simp only [opOn] at hon; subst c'
        obtain ⟨⟨-, hch, hfin, hall⟩, rfl⟩ := Adjudicator.conclude_some h
        obtain ⟨x, hx, hxs⟩ := hU ss' (List.mem_singleton_self _) (hall p (hch ▸ hp))
        have := (hsent x hx (by rw [hxs]; exact hch)).2
        rw [hxs, hfin] at this; cases this
    · exact .inl (by rw [statusOf_apply_of_not_on h hon]; exact hst)
  · exact .inr (finalizedWith_apply h hf)

/-- The strategy "wait until the deadline". `c` is challenged with `ch`, and
    `p` signed no state of `c` above the record and no final state. -/
theorem wait_strategy (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (allowed : HonestMove E → Prop) (net : NetworkState E p)
    (c : FixedPart) (T0 : Nat) (ch : Challenge E)
    (hal : allowed (.wait (ch.deadline - net.chain.now))) (hc : apps c.appDef = consensusRules)
    (hp : p ∈ c.participants) (hst : net.chain.statusOf c = .challenged T0 ch)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.turnNum ≤ T0 ∧ t.state.isFinal = false) :
    UnbeatableIn apps T allowed (fun n => n.Finalized c ch.state.outcome) net := by
  refine .move (.wait (ch.deadline - net.chain.now)) hal trivial fun advs n' ⟨hseq, _⟩ => .done ?_
  have hK : n'.sent = net.sent ∧ WaitInv c T0 ch n'.chain := by
    refine FeasibleSeq.inv0 (fun n => n.sent = net.sent ∧ WaitInv c T0 ch n.chain) ?_ hseq
      ⟨rfl, .inl hst⟩
    intro n m hm ⟨hs0, hk⟩
    refine ⟨by rw [applyAdv_sent]; exact hs0, ?_⟩
    cases m with
    | deliver ss' => exact hk
    | tick dt =>
      have happ : n.chain.apply apps p (.tick dt) = some (n.chain.tick dt) := rfl
      exact waitInv_apply happ n.sent hc hp (by simp [Op.proofStates]) (hs0 ▸ hsent) hk
    | chain caller op =>
      rw [chain_applyAdv]
      cases happ : n.chain.apply apps caller op with
      | none => exact hk
      | some s' =>
        exact waitInv_apply happ n.sent hc hp
          (fun ss' hss' => (B.unforgeable n caller op hm ss' hss').1) (hs0 ▸ hsent) hk
  obtain ⟨-, hk⟩ := hK
  have hle := FeasibleSeq.now_le hseq
  show (n'.chain.tick (ch.deadline - net.chain.now)).finalizedWith c.address = some ch.state.outcome
  rcases hk with hst' | hf
  · simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf,
      hst', Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged]
    rw [if_pos (le_trans le_add_tsub (Nat.add_le_add_right hle _))]
  · simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf,
      Adjudicator.tick_now] at hf ⊢
    exact ChannelStatus.finalizedWith_mono hf (Nat.le_add_right _ _)

/-- With no coins anywhere and no deposit, no operation creates coins. -/
theorem zeroBal_apply {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    (h : s.apply apps caller op = some s') (hop : ∀ a e x, op ≠ .deposit a e x)
    (hz : ∀ a, s.balances.get a = 0) : ∀ a, s'.balances.get a = 0 := by
  intro a'
  cases op with
  | deposit a e x => exact absurd rfl (hop a e x)
  | tick dt => simp at h; subst h; exact hz a'
  | transfer a b =>
    obtain ⟨o, _, x, -, -, hx, hb, -⟩ := Adjudicator.transfer_some h
    have hx0 : x = 0 := by
      have := Allocation.paidTo_le_held (s.balances.get a.address) o b
      rw [hz] at this; rw [hx, hz]; exact Nat.le_zero.1 this
    rw [hb]; simp [hx0, hz]
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := Adjudicator.reclaim_some h; simp [hz]
  | challenge c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.challenge_some h; simp [hz]
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.checkpoint_some h; simp [hz]
  | conclude c ss => obtain ⟨_, rfl⟩ := Adjudicator.conclude_some h; simp [hz]

/-- The empty round: the adversary does nothing. -/
theorem round_nil (apps : Apps E) {p : Participant} (T : Threat E p) (n : NetworkState E p) :
    T.Round apps n [] n := ⟨.nil, Nat.lt_add_of_pos_right T.ε_pos⟩

/-- With no coins anywhere, `p` obtains nothing at `d`: the value is 0. -/
theorem value_zero (apps : Apps E) {p : Participant} (T : Threat E p) (net : NetworkState E p)
    (hz : ∀ a, net.chain.balances.get a = 0) (d : E) : Value apps T d net 0 := by
  refine ⟨.done (Nat.zero_le _), fun y hy => ?_⟩
  suffices H : ∀ n, UnbeatableIn apps T (fun _ => True)
      (fun net' => y ≤ net'.chain.balances.get (.external d)) n →
      (∀ a, n.chain.balances.get a = 0) → y ≤ 0 from H net hy hz
  intro n hn
  induction hn with
  | done hg => intro hz'; rw [hz'] at hg; exact hg
  | @move n m _ hfeas _ ih =>
    intro hz'
    refine ih [] n (round_nil apps T n) ?_
    cases m with
    | chain op =>
      simp only [NetworkState.applyHonest]
      cases happ : n.chain.apply apps p op with
      | none => exact hz'
      | some s' =>
        refine zeroBal_apply happ (fun a e x hd => ?_) hz'
        subst hd; exact hfeas
    | send st => exact hz'
    | wait dt => exact hz'

/-- The outcome of finalization survives every adversary move. -/
theorem finalizedWith_applyAdv (apps : Apps E) {p : Participant} (m : AdvMove E)
    (n : NetworkState E p) {c : FixedPart} {f : Outcome E}
    (hf : n.chain.finalizedWith c.address = some f) :
    (n.applyAdv apps m).chain.finalizedWith c.address = some f := by
  cases m with
  | chain caller op =>
    rw [chain_applyAdv]
    cases happ : n.chain.apply apps caller op with
    | none => exact hf
    | some s' => exact finalizedWith_apply happ hf
  | deliver ss => exact hf
  | tick dt => exact finalizedWith_apply (show n.chain.apply apps p (.tick dt) = _ from rfl) hf

/-- The outcome of finalization survives every honest move. -/
theorem finalizedWith_applyHonest (apps : Apps E) {p : Participant} (m : HonestMove E)
    (n : NetworkState E p) {c : FixedPart} {f : Outcome E}
    (hf : n.chain.finalizedWith c.address = some f) :
    (n.applyHonest apps m).chain.finalizedWith c.address = some f := by
  cases m with
  | chain op =>
    show ((n.chain.apply apps p op).getD n.chain).finalizedWith c.address = some f
    cases happ : n.chain.apply apps p op with
    | none => exact hf
    | some s' => exact finalizedWith_apply happ hf
  | send st => exact hf
  | wait dt => exact finalizedWith_apply (show n.chain.apply apps p (.tick dt) = _ from rfl) hf

/-- A channel finalized with `Ω` is never finalized with another outcome:
    `p` prevents it by waiting. -/
theorem prevents_other_outcome (apps : Apps E) {p : Participant} (T : Threat E p)
    (net : NetworkState E p) (c : FixedPart) (Ω Ω' : Outcome E) (hf : net.Finalized c Ω)
    (hne : Ω' ≠ Ω) : Prevents apps T (fun n => n.Finalized c Ω') net := by
  refine ⟨fun _ => .wait 0, fun _ => trivial, fun n1 advs n2 hrun hround => ?_⟩
  have h1 : n1.Finalized c Ω := by
    clear hround
    induction hrun with
    | refl => exact hf
    | round _ hr ih =>
      exact finalizedWith_applyHonest apps _ _
        (FeasibleSeq.inv0 (fun n => n.Finalized c Ω)
          (fun n m _ h => finalizedWith_applyAdv apps m n h) hr.1 ih)
  have h2 := FeasibleSeq.inv0 (fun n => n.Finalized c Ω)
    (fun n m _ h => finalizedWith_applyAdv apps m n h) hround.1 h1
  intro h3
  simp only [NetworkState.Finalized] at h2 h3
  rw [h2] at h3; exact hne (Option.some.inj h3).symm

end Game

/-! ## Reachability helpers (`ArmadaLean/Machine.lean`, `ArmadaLean/Nitro/Reachable.lean`)

    Every witness below that supports a theorem taking `(Nitro.participant apps T).Reachable net`
    or `(Nitro.network apps Ts).Reachable n` proves it by a short chain of these three helpers per
    machine, mirroring the real move sequence that reaches the witness state: one honest move, one
    adversary move, or the genesis state itself. -/

section Reachability

variable {E : Type} [DecidableEq E]

theorem participant_reachable_init {p : Participant} (apps : Apps E) (T : Threat E p) :
    (Nitro.participant apps T).Reachable (⟨Adjudicator.genesis, [], []⟩ : NetworkState E p) :=
  ⟨_, rfl, .refl⟩

theorem participant_reachable_honest {apps : Apps E} {p : Participant} {T : Threat E p}
    {net : NetworkState E p} (h : (Nitro.participant apps T).Reachable net) (m : HonestMove E)
    (hm : m.Feasible net) : (Nitro.participant apps T).Reachable (net.applyHonest apps m) :=
  h.tail (Or.inl ⟨m, hm, rfl⟩)

theorem participant_reachable_adv {apps : Apps E} {p : Participant} {T : Threat E p}
    {net : NetworkState E p} (h : (Nitro.participant apps T).Reachable net) (m : AdvMove E)
    (hm : T.feasible net m) : (Nitro.participant apps T).Reachable (net.applyAdv apps m) :=
  h.tail (Or.inr ⟨m, hm, rfl⟩)

theorem network_reachable_init (apps : Apps E) (Ts : Threats E apps) :
    (Nitro.network apps Ts).Reachable
      (⟨Adjudicator.genesis, fun _ => [], fun _ => []⟩ : Network E) :=
  ⟨_, rfl, .refl⟩

theorem network_reachable_honest {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) (p : Participant) (m : HonestMove E)
    (hm : m.Feasible (n.view p))
    (hgate : ∀ op, m = .chain op → ∀ ss ∈ op.proofStates, n.Sendable ss)
    (hvgate : ∀ st, m = .send st → n.VoucherSendable st) :
    (Nitro.network apps Ts).Reachable (Network.applyHonest apps n p m) :=
  h.tail ⟨p, Or.inl ⟨m, hm, hgate, hvgate, rfl⟩⟩

theorem network_reachable_adv {apps : Apps E} {Ts : Threats E apps} {n : Network E}
    (h : (Nitro.network apps Ts).Reachable n) (p : Participant) (m : AdvMove E)
    (hm : (Ts.T p).feasible (n.view p) m) (hdgate : ∀ ss, m = .deliver ss → n.Sendable ss)
    (hnochain : ∀ caller op, m ≠ .chain caller op) :
    (Nitro.network apps Ts).Reachable (Network.applyAdv apps n p m) :=
  h.tail ⟨p, Or.inr ⟨m, hm, hdgate, hnochain, rfl⟩⟩

end Reachability

/-! ## Threats and helpers for the `Liveness.lean` witnesses -/

/-- The adversary of `p` that every rule of `Assumptions` allows: any move of
    another participant with no forged signature of `p`, any delivery with
    no forged signature, and any tick. Transactions land within `ε = 1`. -/
def canon (p : Participant) : Threat Nat p where
  feasible net m := match m with
    | .chain caller op => caller ≠ p ∧ ∀ ss ∈ op.proofStates, net.Unforged ss
    | .deliver ss => net.Unforged ss
    | .tick _ => True
  ε := 1
  ε_pos := Nat.one_pos

theorem canon_ok (apps : Apps Nat) (p : Participant) : Assumptions apps p (canon p) where
  unforgeable _ _ _ h := h.2
  unforgeableDeliver _ _ h := h
  notHonest _ _ _ h := h.1
  capable _ _ _ h1 h2 := ⟨h1, h2⟩
  capableDeliver _ _ h := h
  capableTick _ _ := trivial

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
    cases hm; simp [Op.proofStates] at hss
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
      (.chain q0 (.deposit c1.address 0 1)) ⟨by decide, fun ss h => absurd h List.not_mem_nil⟩)
    (.send stF) trivial

/-- `⟨sCon, [], [ssF]⟩` is reachable: `netF_reach`, then `p0`'s own honest conclude with `ssF`
    (`Holds` needs `ssF` in `net.sent`, already there from the `.send` `netF_reach` ends with). -/
theorem netC_reach :
    (Nitro.participant apps0 (canon p0)).Reachable (⟨sCon, [], [ssF]⟩ : NetworkState Nat p0) :=
  participant_reachable_honest netF_reach (.chain (.conclude c1 ssF))
    (fun ss h => by
      simp only [Op.proofStates, List.mem_singleton] at h; subst h; exact netF_holds)

/-- `directly_funded_pays`. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (o : Allocation Nat) (d : Nat) (amt : Coins),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    net.chain.finalOutcome c.address = some (.allocation o) ∧
    net.chain.DirectlyFunded c ∧ o.find (.external d) = some ⟨.external d, .alloc amt⟩ :=
  ⟨⟨sCon, [], [ssF]⟩, c1, o1, 0, 1, canon_ok _ _, netC_reach, rfl, ⟨o1, rfl, by decide⟩, by decide⟩

/-- `finalizable_funded_pays`. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (o : Allocation Nat) (d : Nat) (amt : Coins),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    net.chain.finalOutcome c.address = some (.allocation o) ∧
    FundedFor apps0 (canon p0) c o.total net ∧
    o.find (.external d) = some ⟨.external d, .alloc amt⟩ :=
  ⟨⟨sCon, [], [ssF]⟩, c1, o1, 0, 1, canon_ok _ _, netC_reach, rfl,
    .done (show o1.total ≤ _ by decide), by decide⟩

/-- `conclusion_proof_finalizable`. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (ss : SignedState Nat) (Ω : Outcome Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 c.appDef = consensusRules ∧ p0 ∈ c.participants ∧
    net.Holds ss ∧ ConclusionProof c ss ∧ ss.state.outcome = Ω ∧
    (∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) ∧
    (net.chain.finalizedWith c.address = none ∨ net.Finalized c Ω) ∧
    2 * (canon p0).ε ≤ c.challengeDuration ∧ net.DeadlineAfter c (canon p0).ε :=
  ⟨netF, c1, ssF, _, canon_ok _ _, netF_reach, rfl, by decide, netF_holds, by decide, rfl,
    by decide, .inl (by decide), by decide, deadlineAfter_open (t := 0) rfl _⟩

/-- `latest_state_finalizable`. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (ss : SignedState Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 c.appDef = consensusRules ∧ p0 ∈ c.participants ∧
    net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = c ∧
    (∀ t ∈ net.sent, t.state.channel = c →
      t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state) ∧
    (∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = ss.state.outcome) ∧
    2 * (canon p0).ε ≤ c.challengeDuration ∧
    (net.Finalized c ss.state.outcome ∨
      (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + (canon p0).ε ≤ ch.deadline)) :=
  ⟨netF, c1, ssF, canon_ok _ _, netF_reach, rfl, by decide, netF_holds, by decide, rfl, by decide,
    by decide, by decide, .inr (.inl ⟨0, rfl, le_rfl⟩)⟩

/-- `c1` challenged at turn 0, deadline 2 (`g0.now + c1.challengeDuration`): reached by `p0`
    sending `stO0`, then `p0`'s own honest challenge with it (only `c1`'s own participant may
    challenge it, `Adjudicator.lean:217`, so this cannot be an adversary move the way a deposit
    can). `p0` then sends `ssO` at turn 1, the later state `late_observer_can_checkpoint`
    checkpoints with. -/
def stO0 : State Nat := ⟨c1, 0, .allocation o1, false, .opaque 0⟩
def ssO0 : SignedState Nat := ⟨stO0, [p0]⟩
def sCh0 : Adjudicator Nat := g0.setStatus c1 (.challenged 0 ⟨stO0, 2⟩)
def netO : NetworkState Nat p0 := ⟨sCh0, [], [ssO, ssO0]⟩

theorem g0_challengeO0 : g0.apply apps0 p0 (.challenge c1 [ssO0] stO0) = some sCh0 := rfl

theorem netO_reach : (Nitro.participant apps0 (canon p0)).Reachable netO :=
  participant_reachable_honest
    (participant_reachable_honest
      (participant_reachable_honest (participant_reachable_init apps0 (canon p0)) (.send stO0)
        trivial)
      (.chain (.challenge c1 [ssO0] stO0))
      (fun ss h => by
        simp only [Op.proofStates, List.mem_singleton] at h; subst h
        exact holds_intro _ _ (by decide) (fun _ h => by cases h)))
    (.send stO) trivial

/-- `late_observer_can_checkpoint`. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (ss : SignedState Nat) (t : Nat)
    (ch : Challenge Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 c.appDef = consensusRules ∧ p0 ∈ c.participants ∧
    net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = c ∧
    (∀ u ∈ net.sent, u.state.channel = c →
      (u.state.turnNum < ss.state.turnNum ∨ u.state = ss.state) ∧ u.state.isFinal = false) ∧
    net.chain.statusOf c = .challenged t ch ∧ t < ss.state.turnNum ∧
    net.chain.now + (canon p0).ε ≤ ch.deadline ∧ 2 * (canon p0).ε ≤ c.challengeDuration :=
  ⟨netO, c1, ssO, 0, ⟨stO0, 2⟩, canon_ok _ _, netO_reach, rfl, by decide,
    holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, by decide, rfl, by decide,
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
  Network.applyHonest apps0
    (Network.applyHonest apps0 (⟨g0, fun _ => [], fun _ => []⟩ : Network Nat) p0 (.send stF))
    p0 (.chain (.conclude c1 ssF))

theorem nFU_reach : (Nitro.network apps0 (Ts apps0)).Reachable nFU :=
  network_reachable_honest
    (network_reachable_honest (network_reachable_init apps0 (Ts apps0))
      p0 (.send stF) trivial (fun op h => by cases h)
      (fun st h => by
        injection h with h; subst h; intro v hv; rw [stF_voucher] at hv; cases hv))
    p0 (.chain (.conclude c1 ssF))
    (fun ss hss => by
      simp only [Op.proofStates, List.mem_singleton] at hss; subst hss
      exact holds_intro _ _ (by decide) (fun _ h => by cases h))
    (fun op h => by
      injection h with h; subst h
      intro ss hss; simp only [Op.proofStates, List.mem_singleton] at hss; subst hss
      refine ⟨fun q hq => ?_, fun v hv q hq => by simp [ssF, stF, State.voucher?] at hv⟩
      simp only [ssF, List.mem_singleton] at hq; subst hq
      exact ⟨⟨stF, [p0]⟩, by decide, rfl⟩)
    (fun st h => by cases h)

theorem nFU_chain : nFU.chain = gCon := rfl

theorem nFU_views_chain (r : Participant) : (nFU.views r).chain = gCon := rfl

theorem nFU_views_p0 : nFU.views p0 = ⟨gCon, [], [⟨stF, [p0]⟩]⟩ := rfl

theorem nFU_views_q0 : nFU.views q0 = ⟨gCon, [ssF], []⟩ := rfl

/-- `finalizable_unique`: both participants see `c1` finalized with `o1`. -/
example : ∃ (v : Views Nat) (n : Network Nat) (c : FixedPart) (p q : Participant)
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
example : ∃ (v : Views Nat) (n : Network Nat), (Nitro.network apps0 (Ts apps0)).Reachable n ∧
    v = n.views :=
  ⟨(⟨g0, fun _ => [], fun _ => []⟩ : Network Nat).views, _,
    network_reachable_init apps0 (Ts apps0), rfl⟩


/-- `finalizable_or_two_enabled`. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    p0 ∈ c.participants ∧
    (∃ proof candidate, (∀ ss ∈ proof, net.Holds ss) ∧
      (apps0 c.appDef).supports c proof candidate = true ∧ candidate.channel = c) ∧
    2 * (canon p0).ε ≤ c.challengeDuration :=
  ⟨netF, c1, canon_ok _ _, netF_reach, by decide,
    ⟨[ssF], stF, fun ss h => by rw [List.mem_singleton] at h; subst h; exact netF_holds,
      by decide, rfl⟩, by decide⟩

/-- `single_enabled_is_finalizable`: `c1` is finalized with `o1`, so `o1`
    is enabled and is the only enabled outcome. `net` is `⟨sCon, [], [ssF]⟩`: `netC_reach`. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (Ω : Outcome Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    p0 ∈ c.participants ∧
    (∀ t ∈ net.sent, t.state.channel = c → ∃ proof, (∀ ss ∈ proof, net.Holds ss) ∧
      (apps0 c.appDef).supports c proof t.state = true) ∧
    2 * (canon p0).ε ≤ c.challengeDuration ∧ Enabled apps0 (canon p0) c Ω net ∧
    (∀ Ω', Enabled apps0 (canon p0) c Ω' net → Ω' = Ω) :=
  ⟨⟨sCon, [], [ssF]⟩, c1, .allocation o1, canon_ok _ _, netC_reach, by decide,
    (fun t h _ => by
      rw [List.mem_singleton] at h; subst h
      exact ⟨[ssF], fun ss h' => by rw [List.mem_singleton] at h'; subst h'; exact netF_holds,
        by decide⟩),
    by decide, fun ⟨_, _, hσ⟩ => hσ _ [] _ .refl (round_nil _ _ _) rfl,
    fun Ω' hen => by
      by_contra hne
      exact hen (prevents_other_outcome _ _ _ _ _ _ rfl hne)⟩

/-- `funding_point_universally_finalizable`: `c1` (one participant) under the
    ForceMove rules; `p0` signed the turn-0 state, reached by `p0`'s own
    honest `.send st0` from genesis. `c1` has no other participant, so
    `st0.recipients p0 = []`: no delivery is needed, and the proof below
    never reads any other participant's view. -/
def apps1 : Apps Nat := fun _ => forceMoveRules vtAll
def st0 : State Nat := ⟨c1, 0, .allocation o1, false, .opaque 0⟩

def nFP : Network Nat :=
  Network.applyHonest apps1 (⟨g0, fun _ => [], fun _ => []⟩ : Network Nat) p0 (.send st0)

theorem st0_voucher : st0.voucher? = none := rfl

theorem nFP_reach : (Nitro.network apps1 (Ts apps1)).Reachable nFP :=
  network_reachable_honest (network_reachable_init apps1 (Ts apps1)) p0 (.send st0) trivial
    (fun op h => by cases h)
    (fun st h => by
      injection h with h; subst h; intro v hv; rw [st0_voucher] at hv; cases hv)

theorem nFP_views_p0 : nFP.views p0 = ⟨g0, [], [⟨st0, [p0]⟩]⟩ := rfl

theorem nFP_views_chain (r : Participant) : (nFP.views r).chain = g0 := rfl

theorem nFP_chain : nFP.chain = g0 := rfl

example : ∃ (v : Views Nat) (n : Network Nat) (c : FixedPart) (Ω : Outcome Nat)
    (vt : State Nat → State Nat → Bool),
    (Nitro.network apps1 (Ts apps1)).Reachable n ∧ v = n.views ∧
    apps1 c.appDef = forceMoveRules vt ∧ SetupPhaseKeepsOutcome vt c ∧
    SetupPhaseAccepted vt c ∧ 0 < c.n ∧ (∀ p, 2 * ((Ts apps1).T p).ε ≤ c.challengeDuration) ∧
    AtFundingPoint v c Ω ∧ (∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) := by
  refine ⟨nFP.views, nFP, c1, .allocation o1, vtAll, nFP_reach, rfl, rfl, ?_, ?_, by decide,
    fun _ => (by decide : 2 * 1 ≤ 2), ⟨?_, ?_⟩, fun r => ?_⟩
  · intro s1 s2 h _ _; simpa [vtAll] using h
  · intro s1 s2 _ _ _ _ ho _; simp [vtAll, ho]
  · intro r hr k hk
    have hr' : r = p0 := by simpa [c1] using hr
    have hk' : k = 0 := by simpa [FixedPart.n, c1] using hk
    subst hr' hk'
    refine ⟨⟨st0, [p0]⟩, ?_, rfl, rfl, rfl, rfl, ⟨p0, by decide, by decide⟩⟩
    rw [nFP_views_p0]
    exact holds_intro _ _ (by decide) (fun _ h => by cases h)
  · intro r hr ss hss _
    have hr' : r = p0 := by simpa [c1] using hr
    subst hr'
    rw [nFP_views_p0] at hss
    simp at hss; subst hss; decide
  · rw [nFP_views_chain]; exact ⟨rfl, rfl⟩

/-- `concluded_universally_finalizable`: `p0` signs `ssF` off-chain
    (`Concluded` reads `Holds`, not the chain) without calling `conclude`
    on-chain, so `c1`'s on-chain status stays `.open 0`
    (`deadlineAfter_open`, the `.inl` branch of `hchain`). -/
def nCF : Network Nat :=
  Network.applyHonest apps0 (⟨g0, fun _ => [], fun _ => []⟩ : Network Nat) p0 (.send stF)

theorem nCF_reach : (Nitro.network apps0 (Ts apps0)).Reachable nCF :=
  network_reachable_honest (network_reachable_init apps0 (Ts apps0)) p0 (.send stF) trivial
    (fun op h => by cases h)
    (fun st h => by
      injection h with h; subst h; intro v hv; rw [stF_voucher] at hv; cases hv)

theorem nCF_views_p0 : nCF.views p0 = ⟨g0, [], [ssF]⟩ := rfl

theorem nCF_views_chain (r : Participant) : (nCF.views r).chain = g0 := rfl

example : ∃ (v : Views Nat) (n : Network Nat) (c : FixedPart) (Ω : Outcome Nat),
    (Nitro.network apps0 (Ts apps0)).Reachable n ∧ v = n.views ∧
    apps0 c.appDef = consensusRules ∧ Concluded v c Ω ∧
    (∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω) ∧
    (∀ p, (v p).chain.finalizedWith c.address = none ∨ (v p).Finalized c Ω) ∧
    (∀ p, 2 * ((Ts apps0).T p).ε ≤ c.challengeDuration) ∧
    (∀ p, (v p).DeadlineAfter c ((Ts apps0).T p).ε) := by
  refine ⟨nCF.views, nCF, c1, .allocation o1, nCF_reach, rfl, rfl, ?_, ?_,
    fun r => .inl (by rw [nCF_views_chain]; decide),
    fun _ => (by decide : 2 * 1 ≤ 2),
    fun r => deadlineAfter_open (t := 0) (by rw [nCF_views_chain]; rfl) _⟩
  · intro r hr
    have hr' : r = p0 := by simpa [c1] using hr
    subst hr'
    refine ⟨ssF, ?_, by decide, rfl⟩
    rw [nCF_views_p0]; exact netF_holds
  · intro r t ht _ hfin
    by_cases hrp0 : r = p0
    · subst hrp0
      rw [nCF_views_p0] at ht
      simp at ht; subst ht; rfl
    · exfalso
      have : (nCF.views r).sent = [] := by
        rw [Network.views, Network.view]
        simp only [nCF, Network.applyHonest, if_neg hrp0]
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
      trivial)
    (.deliver ⟨stF2, [q0]⟩) (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ :
      NetworkState.Unforged _ ⟨stF2, [q0]⟩)

example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (ss : SignedState Nat)
    (Ω1 Ω2 Ω : Outcome Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    apps0 c.appDef = consensusRules ∧ p0 ∈ c.participants ∧
    net.Holds ss ∧ ss.ByAll ∧ ss.state.channel = c ∧ ss.state.outcome = Ω1 ∧
    (∀ t ∈ net.sent, t.state.channel = c →
      (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
      (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2)) ∧
    2 * (canon p0).ε ≤ c.challengeDuration ∧
    ((∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.chain.now + (canon p0).ε ≤ ch.deadline)) ∧
    Enabled apps0 (canon p0) c Ω net := by
  refine ⟨netC2, c2, ⟨stF2, [p0, q0]⟩, .allocation o1, .allocation o1, .allocation o1,
    canon_ok _ _, netC2_reach, rfl, by decide,
    holds_intro _ _ (by decide) (fun _ h => by cases h), by decide,
    rfl, rfl, by decide, by decide, .inl ⟨0, rfl, le_rfl⟩, ?_⟩
  rintro ⟨σ, -, hσ⟩
  refine hσ netC2 [mC2] _ .refl ⟨.cons ⟨by decide, fun ss hss => ?_⟩ .nil, by decide⟩ rfl
  simp only [Op.proofStates, List.mem_singleton] at hss; subst hss
  exact unforged_intro _ _ (by decide) (fun _ h => by cases h)

/-- `turbo_redistribution_unbeatable`. `net` is the genesis state itself: `Nitro.participant`'s own
    initial state. -/
example : ∃ (net : NetworkState Nat p0) (ops : List (Participant × Op Nat)) (d : Nat) (x : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsDAG ∧ OnlyTransfers ops ∧
    x ≤ (Adjudicator.applyAll apps0 ops net.chain).balances.get (.external d) :=
  ⟨⟨g0, [], []⟩, [], 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_dag,
    fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩

theorem zero_g0 : ∀ a : Address Nat, g0.balances.get a = 0 := fun _ => rfl

/-- `deposit_bounds_value`: a deposit of 0 into an empty chain. `net` is the genesis state
    itself. -/
example : ∃ (net : NetworkState Nat p0) (c : FixedPart) (d : Nat) (y x x' : Coins)
    (s' : Adjudicator Nat) (e : Coins),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    net.chain.deposit c.address e y = some s' ∧
    Value apps0 (canon p0) d net x ∧ Value apps0 (canon p0) d { net with chain := s' } x' := by
  refine ⟨⟨g0, [], []⟩, c1, 0, 0, 0, 0, _, 0, canon_ok _ _,
    participant_reachable_init apps0 (canon p0), rfl, value_zero _ _ _ zero_g0 0,
    value_zero _ _ _ (fun a => ?_) 0⟩
  show Balances.get (((c1.address : Address Nat), 0 + 0) :: []) a = 0
  rw [Balances.get_cons]; split <;> rfl

/-- `payout_to_other_affects_only_owner`. `sP` is `c1` concluded with outcome `[alloc d1 0]`:
    reached by `p0` sending the final state `stP`, then honestly concluding with it (`Holds`
    needs `p0`'s own signature in `net.sent`, so the send comes first; `Adjudicator.lean:249-254`'s
    `conclude` does not read `caller`, so no deposit is needed for an all-zero outcome). -/
def stP : State Nat := ⟨c1, 0, .allocation [alloc d1 0], true, .opaque 0⟩
def ssP : SignedState Nat := ⟨stP, [p0]⟩
def sP : Adjudicator Nat :=
  g0.setStatus c1 (.finalized 0 (.allocation [alloc d1 0]) (.allocation [alloc d1 0]))

theorem g0_concludeP : g0.apply apps0 p0 (.conclude c1 ssP) = some sP := rfl

theorem sP_reach : (Nitro.participant apps0 (canon p0)).Reachable
    (⟨sP, [], [ssP]⟩ : NetworkState Nat p0) :=
  participant_reachable_honest
    (participant_reachable_honest (participant_reachable_init apps0 (canon p0)) (.send stP) trivial)
    (.chain (.conclude c1 ssP))
    (fun ss h => by
      simp only [Op.proofStates, List.mem_singleton] at h; subst h
      exact holds_intro _ _ (by decide) (fun _ h => by cases h))

example : ∃ (net : NetworkState Nat p0) (d q : Nat) (a : FixedPart) (s' : Adjudicator Nat),
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    q ≠ d ∧ net.chain.transfer a (.external q) = some s' :=
  ⟨⟨sP, [], [ssP]⟩, 0, 1, c1, _, canon_ok _ _, sP_reach, by decide, rfl⟩

/-- `participant_can_prevent_cycles`. `net` is the genesis state itself. -/
example : ∃ net : NetworkState Nat p0,
    Assumptions apps0 p0 (canon p0) ∧ (Nitro.participant apps0 (canon p0)).Reachable net ∧
    (∀ c : FixedPart, p0 ∈ c.participants → apps0 c.appDef = consensusRules) ∧
    (∀ c : FixedPart, p0 ∈ c.participants → ∃ t, net.chain.statusOf c = .open t) ∧
    net.chain.IsDAG ∧ net.sent = [] :=
  ⟨⟨g0, [], []⟩, canon_ok _ _, participant_reachable_init apps0 (canon p0), fun _ _ => rfl,
    fun _ _ => ⟨0, rfl⟩, g0_dag, rfl⟩

/-- `turbo_value_upper_bound`. `net` is the genesis state itself. -/
example : ∃ (net : NetworkState Nat p0) (n : Address Nat) (v x : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsDAG ∧ net.chain.TurboValue n v ∧
    CanObtainIn apps0 (turboT p0) HonestMove.IsTransfer n x net :=
  ⟨⟨g0, [], []⟩, d0, 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_dag, g0_turbo _, .done (Nat.zero_le _)⟩

/-- `turbo_value_achievable`. `net` is the genesis state itself. -/
example : ∃ (net : NetworkState Nat p0) (d : Nat) (v : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsDAG ∧ net.chain.TurboValue (.external d) v :=
  ⟨⟨g0, [], []⟩, 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_dag, g0_turbo _⟩

/-- `turbo_value_is_value`. `net` is the genesis state itself. -/
example : ∃ (net : NetworkState Nat p0) (d : Nat) (v : Coins),
    Bounds apps0 p0 (turboT p0) ∧ (turboT p0).TransfersOnly ∧ (turboT p0).CapableTransfers ∧
    (Nitro.participant apps0 (turboT p0)).Reachable net ∧
    net.chain.IsDAG ∧ net.chain.TurboValue (.external d) v :=
  ⟨⟨g0, [], []⟩, 0, 0, turboT_bounds _ _, turboT_only _, turboT_capable _,
    participant_reachable_init apps0 (turboT p0), g0_dag, g0_turbo _⟩

theorem g0_exhausted : g0.TransferExhausted := by
  intro a b s' h
  simp [Adjudicator.transfer, Adjudicator.finalOutcome, Adjudicator.statusOf, g0,
    Adjudicator.genesis] at h

/-- `turbo_order_independent`. -/
example : ∃ (s : Adjudicator Nat) (ops1 ops2 : List (Participant × Op Nat)),
    s.IsDAG ∧ OnlyTransfers ops1 ∧ OnlyTransfers ops2 ∧
    (Adjudicator.applyAll apps0 ops1 s).TransferExhausted ∧
    (Adjudicator.applyAll apps0 ops2 s).TransferExhausted :=
  ⟨g0, [], [], g0_dag, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    g0_exhausted, g0_exhausted⟩

/-- `turbo_value_exists_unique`. -/
example : ∃ s : Adjudicator Nat, s.IsDAG := ⟨g0, g0_dag⟩

/-! ### Ledger constructions: `A = p0` at `0`, `B = q0` at `1`. -/

def cLW : FixedPart := ⟨[p0, q0], 7, ⟨0⟩, 2, .ledger⟩
def cχ : FixedPart := ⟨[p0, q0], 8, ⟨0⟩, 2, .ledger⟩
def wLS : LedgerWithSub Nat := ⟨p0, q0, 0, 1, cLW, cχ, 0, 0, 0⟩

/-- `ledger_offload_funds_subchannel`: `p0` and `q0` each send `stLW`
    (channel `cLW`, two participants); the new synchronous network
    delivers each to the other, so both hold the other's signature
    without any further adversary move (`State.recipients`). The chain
    stays `g0`: `cLW`'s `FinalizableBy` reads `conclude_strategy`, which
    needs the channel open and the state held, not already concluded. -/
def stLW : State Nat := ⟨cLW, 0, wLS.outcome, true, .opaque 0⟩

theorem stLW_voucher : stLW.voucher? = none := rfl

def nLW : Network Nat :=
  Network.applyHonest apps0
    (Network.applyHonest apps0 (⟨g0, fun _ => [], fun _ => []⟩ : Network Nat) p0 (.send stLW))
    q0 (.send stLW)

theorem nLW_reach : (Nitro.network apps0 (Ts apps0)).Reachable nLW :=
  network_reachable_honest
    (network_reachable_honest (network_reachable_init apps0 (Ts apps0)) p0 (.send stLW) trivial
      (fun op h => by cases h)
      (fun st h => by
        injection h with h; subst h; intro v hv; rw [stLW_voucher] at hv; cases hv))
    q0 (.send stLW) trivial (fun op h => by cases h)
    (fun st h => by
      injection h with h; subst h; intro v hv; rw [stLW_voucher] at hv; cases hv)

theorem nLW_views_p0 : nLW.views p0 = ⟨g0, [⟨stLW, [q0]⟩], [⟨stLW, [p0]⟩]⟩ := rfl
theorem nLW_views_q0 : nLW.views q0 = ⟨g0, [⟨stLW, [p0]⟩], [⟨stLW, [q0]⟩]⟩ := rfl
theorem nLW_views_chain (r : Participant) : (nLW.views r).chain = g0 := rfl

theorem g0_cLW_open : g0.statusOf cLW = .open 0 := rfl

theorem nLW_finalizable : nLW.views.FinalizableBy apps0 (Ts apps0) cLW wLS.outcome [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by simpa using hr
  have hnone : g0.finalizedWith cLW.address = none := by
    simp [Adjudicator.finalizedWith, g0_cLW_open]
  rcases hr' with rfl | rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 p0).toBounds _ _ cLW
      ⟨stLW, [p0, q0]⟩ wLS.outcome trivial (by decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, stLW, cLW]) rfl ?_
      (.inl (by rw [nLW_views_chain]; exact hnone)) (by decide)
      (deadlineAfter_open (net := nLW.views p0) (by rw [nLW_views_chain]; exact g0_cLW_open) _)
    · rw [nLW_views_p0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_singleton_self _, rfl⟩
      · exact .inr ⟨_, List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩
    · rw [nLW_views_p0]; intro t ht _ _; simp at ht; subst ht; rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 q0).toBounds _ _ cLW
      ⟨stLW, [p0, q0]⟩ wLS.outcome trivial (by decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, stLW, cLW]) rfl ?_
      (.inl (by rw [nLW_views_chain]; exact hnone)) (by decide)
      (deadlineAfter_open (net := nLW.views q0) (by rw [nLW_views_chain]; exact g0_cLW_open) _)
    · rw [nLW_views_q0]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩
      · exact .inl ⟨rfl, _, List.mem_singleton_self _, rfl⟩
    · rw [nLW_views_q0]; intro t ht _ _; simp at ht; subst ht; rfl

example : ∃ (v : Views Nat) (n : Network Nat) (w : LedgerWithSub Nat),
    (Nitro.network apps0 (Ts apps0)).Reachable n ∧ v = n.views ∧
    w.Holds apps0 (Ts apps0) v ∧
    (∀ p, (v p).chain.finalOutcome w.χ.address = none) ∧
    (∀ p, ∀ t ∈ (v p).sent, t.state.channel = w.χ → t.state.isFinal = false) := by
  refine ⟨nLW.views, nLW, wLS, nLW_reach, rfl, ⟨rfl, rfl, fun r => ?_, nLW_finalizable⟩,
    fun r => by rw [nLW_views_chain]; rfl, fun r t ht hc => ?_⟩
  · rw [nLW_views_chain]; exact zero_g0 _
  · by_cases hrp0 : r = p0
    · subst hrp0; rw [nLW_views_p0] at ht; simp at ht; subst ht
      simp [stLW, cLW, wLS, cχ] at hc
    · by_cases hrq0 : r = q0
      · subst hrq0; rw [nLW_views_q0] at ht; simp at ht; subst ht
        simp [stLW, cLW, wLS, cχ] at hc
      · exfalso
        have : (nLW.views r).sent = [] := by
          rw [Network.views, Network.view]
          simp only [nLW, Network.applyHonest, if_neg hrp0, if_neg hrq0]
        rw [this] at ht
        exact absurd ht List.not_mem_nil

/-- `p0` and `q0` each send `st`, synchronously delivered to the other
    (a two-participant channel), giving each the other's signature with
    no adversary move. -/
def nOneCh (st : State Nat) : Network Nat :=
  Network.applyHonest apps0
    (Network.applyHonest apps0 (⟨g0, fun _ => [], fun _ => []⟩ : Network Nat) p0 (.send st))
    q0 (.send st)

theorem nOneCh_reach {st : State Nat} (hv : st.voucher? = none) :
    (Nitro.network apps0 (Ts apps0)).Reachable (nOneCh st) :=
  network_reachable_honest
    (network_reachable_honest (network_reachable_init apps0 (Ts apps0)) p0 (.send st) trivial
      (fun op h => by cases h)
      (fun st' h => by injection h with h; subst h; intro v hv'; rw [hv] at hv'; cases hv'))
    q0 (.send st) trivial (fun op h => by cases h)
    (fun st' h => by injection h with h; subst h; intro v hv'; rw [hv] at hv'; cases hv')

theorem nOneCh_chain (st : State Nat) : (nOneCh st).chain = g0 := rfl

theorem nOneCh_views_p0 {st : State Nat} (hst : st.channel.participants = [p0, q0]) :
    (nOneCh st).views p0 = ⟨g0, [⟨st, [q0]⟩], [⟨st, [p0]⟩]⟩ := by
  simp [nOneCh, Network.views, Network.view, Network.applyHonest, State.recipients, hst,
    show p0 ≠ q0 from by decide]

theorem nOneCh_views_q0 {st : State Nat} (hst : st.channel.participants = [p0, q0]) :
    (nOneCh st).views q0 = ⟨g0, [⟨st, [p0]⟩], [⟨st, [q0]⟩]⟩ := by
  simp [nOneCh, Network.views, Network.view, Network.applyHonest, State.recipients, hst,
    show p0 ≠ q0 from by decide, show q0 ≠ p0 from by decide]

theorem g0_open (c : FixedPart) : g0.statusOf c = .open 0 := rfl
theorem g0_finalizedWith (c : FixedPart) : g0.finalizedWith c.address = none := rfl

theorem nOneCh_views_chain (st : State Nat) (r : Participant) : ((nOneCh st).views r).chain = g0 :=
  rfl

/-- `FinalizableBy` for the channel `c` of `nOneCh`'s one held state. -/
theorem nOneCh_finalizable {c : FixedPart} {Ω : Outcome Nat} (hcp : c.participants = [p0, q0])
    (hdur : c.challengeDuration = 2) :
    (nOneCh (⟨c, 0, Ω, true, .opaque 0⟩ : State Nat)).views.FinalizableBy apps0 (Ts apps0) c Ω
      [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by simpa using hr
  have hnone := g0_finalizedWith c
  have hopen := g0_open c
  rcases hr' with rfl | rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 p0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, hcp]) rfl ?_
      (.inl (by rw [nOneCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nOneCh_views_chain]; exact hopen) _)
    · rw [nOneCh_views_p0 hcp]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_singleton_self _, rfl⟩
      · exact .inr ⟨_, List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩
    · rw [nOneCh_views_p0 hcp]; intro t ht _ _; simp at ht; subst ht; rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 q0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, hcp]) rfl ?_
      (.inl (by rw [nOneCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nOneCh_views_chain]; exact hopen) _)
    · rw [nOneCh_views_q0 hcp]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩
      · exact .inl ⟨rfl, _, List.mem_singleton_self _, rfl⟩
    · rw [nOneCh_views_q0 hcp]; intro t ht _ _; simp at ht; subst ht; rfl

/-- Two rounds of `nOneCh`: `p0` and `q0` each send `st1`, then each
    send `st2`, both synchronously delivered to the other. -/
def nTwoCh (st1 st2 : State Nat) : Network Nat :=
  Network.applyHonest apps0
    (Network.applyHonest apps0
      (Network.applyHonest apps0
        (Network.applyHonest apps0 (⟨g0, fun _ => [], fun _ => []⟩ : Network Nat) p0 (.send st1))
        q0 (.send st1))
      p0 (.send st2))
    q0 (.send st2)

theorem nTwoCh_reach {st1 st2 : State Nat} (hv1 : st1.voucher? = none) (hv2 : st2.voucher? = none) :
    (Nitro.network apps0 (Ts apps0)).Reachable (nTwoCh st1 st2) :=
  network_reachable_honest
    (network_reachable_honest
      (network_reachable_honest
        (network_reachable_honest (network_reachable_init apps0 (Ts apps0)) p0 (.send st1) trivial
          (fun op h => by cases h)
          (fun st' h => by injection h with h; subst h; intro v hv'; rw [hv1] at hv'; cases hv'))
        q0 (.send st1) trivial (fun op h => by cases h)
        (fun st' h => by injection h with h; subst h; intro v hv'; rw [hv1] at hv'; cases hv'))
      p0 (.send st2) trivial (fun op h => by cases h)
      (fun st' h => by injection h with h; subst h; intro v hv'; rw [hv2] at hv'; cases hv'))
    q0 (.send st2) trivial (fun op h => by cases h)
    (fun st' h => by injection h with h; subst h; intro v hv'; rw [hv2] at hv'; cases hv')

theorem nTwoCh_chain (st1 st2 : State Nat) : (nTwoCh st1 st2).chain = g0 := rfl

theorem nTwoCh_views_p0 {st1 st2 : State Nat} (hst1 : st1.channel.participants = [p0, q0])
    (hst2 : st2.channel.participants = [p0, q0]) :
    (nTwoCh st1 st2).views p0 = ⟨g0, [⟨st2, [q0]⟩, ⟨st1, [q0]⟩], [⟨st2, [p0]⟩, ⟨st1, [p0]⟩]⟩ := by
  simp [nTwoCh, Network.views, Network.view, Network.applyHonest, State.recipients, hst1, hst2,
    show p0 ≠ q0 from by decide]

theorem nTwoCh_views_q0 {st1 st2 : State Nat} (hst1 : st1.channel.participants = [p0, q0])
    (hst2 : st2.channel.participants = [p0, q0]) :
    (nTwoCh st1 st2).views q0 = ⟨g0, [⟨st2, [p0]⟩, ⟨st1, [p0]⟩], [⟨st2, [q0]⟩, ⟨st1, [q0]⟩]⟩ := by
  simp [nTwoCh, Network.views, Network.view, Network.applyHonest, State.recipients, hst1, hst2,
    show p0 ≠ q0 from by decide, show q0 ≠ p0 from by decide]


theorem nTwoCh_views_chain (st1 st2 : State Nat) (r : Participant) :
    ((nTwoCh st1 st2).views r).chain = g0 := rfl

/-- `FinalizableBy` for the channel `c` of `nTwoCh`'s first-sent state
    (sent first, so found second — via `List.mem_cons_of_mem` — in each
    participant's accumulated `sent`/`received`). -/
theorem nTwoCh_finalizable_fst {c : FixedPart} {Ω : Outcome Nat} {st2 : State Nat}
    (hcp : c.participants = [p0, q0]) (hst2p : st2.channel.participants = [p0, q0])
    (hne : st2.channel ≠ c) (hdur : c.challengeDuration = 2) :
    (nTwoCh (⟨c, 0, Ω, true, .opaque 0⟩ : State Nat) st2).views.FinalizableBy apps0
      (Ts apps0) c Ω [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by simpa using hr
  have hnone := g0_finalizedWith c
  have hopen := g0_open c
  rcases hr' with rfl | rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 p0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, hcp]) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_p0 hcp hst2p]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
      · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl,
          List.mem_cons_self ..⟩
    · rw [nTwoCh_views_p0 hcp hst2p]
      intro t ht hcc _
      simp at ht
      rcases ht with rfl | rfl
      · exact absurd hcc hne
      · rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 q0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, hcp]) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_q0 hcp hst2p]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl,
          List.mem_cons_self ..⟩
      · exact .inl ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
    · rw [nTwoCh_views_q0 hcp hst2p]
      intro t ht hcc _
      simp at ht
      rcases ht with rfl | rfl
      · exact absurd hcc hne
      · rfl

/-- `FinalizableBy` for the channel `c` of `nTwoCh`'s second-sent state
    (sent last, so found first — via `List.mem_cons_self` — in each
    participant's accumulated `sent`/`received`). -/
theorem nTwoCh_finalizable_snd {c : FixedPart} {Ω : Outcome Nat} {st1 : State Nat}
    (hcp : c.participants = [p0, q0]) (hst1p : st1.channel.participants = [p0, q0])
    (hne : st1.channel ≠ c) (hdur : c.challengeDuration = 2) :
    (nTwoCh st1 (⟨c, 0, Ω, true, .opaque 0⟩ : State Nat)).views.FinalizableBy apps0
      (Ts apps0) c Ω [p0, q0] := by
  intro r hr
  have hr' : r = p0 ∨ r = q0 := by simpa using hr
  have hnone := g0_finalizedWith c
  have hopen := g0_open c
  rcases hr' with rfl | rfl
  · refine conclude_strategy apps0 _ (canon_ok apps0 p0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, hcp]) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_p0 hst1p hcp]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, _, List.mem_cons_self .., rfl⟩
      · exact .inr ⟨_, List.mem_cons_self .., rfl, List.mem_cons_self ..⟩
    · rw [nTwoCh_views_p0 hst1p hcp]
      intro t ht hcc _
      simp at ht
      rcases ht with rfl | rfl
      · rfl
      · exact absurd hcc hne
  · refine conclude_strategy apps0 _ (canon_ok apps0 q0).toBounds _ _ c
      ⟨(⟨c, 0, Ω, true, .opaque 0⟩ : State Nat), [p0, q0]⟩ Ω trivial (by rw [hcp]; decide) ?_
      (by simp [ConclusionProof, SignedState.ByAll, hcp]) rfl ?_
      (.inl (by rw [nTwoCh_views_chain]; exact hnone)) (by rw [hdur]; decide)
      (deadlineAfter_open (by rw [nTwoCh_views_chain]; exact hopen) _)
    · rw [nTwoCh_views_q0 hst1p hcp]
      refine holds_intro _ _ ?_ (fun _ h => by cases h)
      intro q hq; simp at hq
      rcases hq with rfl | rfl
      · exact .inr ⟨_, List.mem_cons_self .., rfl, List.mem_cons_self ..⟩
      · exact .inl ⟨rfl, _, List.mem_cons_self .., rfl⟩
    · rw [nTwoCh_views_q0 hst1p hcp]
      intro t ht hcc _
      simp at ht
      rcases ht with rfl | rfl
      · rfl
      · exact absurd hcc hne

/-- `subchannel_open_value_preserving`: `v` holds `cLW` (zero outcome)
    and `cχ` (zero outcome) each by two sends; `v'` holds `cLW` (`wLS`'s
    3-entry outcome, i.e. `stLW`) and `cχ` (zero outcome) each by two
    sends, from a separate genesis start. -/
def stL1 : State Nat := ⟨cLW, 0, .allocation [alloc d0 0, alloc d1 0], true, .opaque 0⟩
def stX1 : State Nat := ⟨cχ, 0, .allocation [alloc d0 0, alloc d1 0], true, .opaque 0⟩
theorem stL1_voucher : stL1.voucher? = none := rfl
theorem stX1_voucher : stX1.voucher? = none := rfl
theorem cLW_ne_cχ : cLW ≠ cχ := by decide

def nOpen : Network Nat := nTwoCh stL1 stX1
theorem nOpen_reach : (Nitro.network apps0 (Ts apps0)).Reachable nOpen :=
  nTwoCh_reach stL1_voucher stX1_voucher

def nOpen' : Network Nat := nTwoCh stLW stX1
theorem nOpen'_reach : (Nitro.network apps0 (Ts apps0)).Reachable nOpen' :=
  nTwoCh_reach stLW_voucher stX1_voucher

example : ∃ (v v' : Views Nat) (n n' : Network Nat) (A B : Participant) (dA dB : Nat)
    (L χ : FixedPart) (a b a' b' : Coins),
    (Nitro.network apps0 (Ts apps0)).Reachable n ∧ v = n.views ∧
    (Nitro.network apps0 (Ts apps0)).Reachable n' ∧ v' = n'.views ∧
    a' ≤ a ∧ b' ≤ b ∧ IsLedgerChannel apps0 L ∧
    L.participants = [A, B] ∧ χ.participants = [A, B] ∧
    v.HoldsBalance L.address (a + b) ∧ v'.HoldsBalance L.address (a + b) ∧
    v.FinalizableBy apps0 (Ts apps0) L
      (.allocation [alloc (.external dA) a, alloc (.external dB) b]) [A, B] ∧
    v.FinalizableBy apps0 (Ts apps0) χ
      (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B] ∧
    v'.FinalizableBy apps0 (Ts apps0) L
      (.allocation [alloc (.external dA) (a - a'), alloc (.external dB) (b - b'),
        alloc χ.address (a' + b')]) [A, B] ∧
    v'.FinalizableBy apps0 (Ts apps0) χ
      (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B] ∧
    (∀ p, p = A ∨ p = B → (v p).chain = (v' p).chain) := by
  refine ⟨nOpen.views, nOpen'.views, nOpen, nOpen', p0, q0, 0, 1, cLW, cχ, 0, 0, 0, 0,
    nOpen_reach, rfl, nOpen'_reach, rfl, le_rfl, le_rfl, rfl, rfl, rfl, ?_, ?_,
    nTwoCh_finalizable_fst rfl rfl cLW_ne_cχ.symm rfl, nTwoCh_finalizable_snd rfl rfl cLW_ne_cχ rfl,
    nTwoCh_finalizable_fst rfl rfl cLW_ne_cχ.symm rfl, nTwoCh_finalizable_snd rfl rfl cLW_ne_cχ rfl,
    fun r _ => by simp only [nOpen, nOpen', nTwoCh_views_chain]⟩
  · intro r; simp only [nOpen, nTwoCh_views_chain]; exact zero_g0 _
  · intro r; simp only [nOpen', nTwoCh_views_chain]; exact zero_g0 _

/-- `subchannel_close_value_preserving`: `v` reuses `nOpen'` (`cLW` holds
    `wLS.outcome`, `cχ` holds the zero outcome); `v'` holds `cLW` with the
    zero outcome by itself, from a separate genesis start. -/
def nClose' : Network Nat := nOneCh stL1
theorem nClose'_reach : (Nitro.network apps0 (Ts apps0)).Reachable nClose' :=
  nOneCh_reach stL1_voucher

example : ∃ (v v' : Views Nat) (n n' : Network Nat) (w : LedgerWithSub Nat) (a' b' : Coins),
    (Nitro.network apps0 (Ts apps0)).Reachable n ∧ v = n.views ∧
    (Nitro.network apps0 (Ts apps0)).Reachable n' ∧ v' = n'.views ∧
    a' + b' = w.c ∧ w.Holds apps0 (Ts apps0) v ∧
    v.FinalizableBy apps0 (Ts apps0) w.χ
      (.allocation [alloc (.external w.dA) a', alloc (.external w.dB) b']) [w.A, w.B] ∧
    v'.FinalizableBy apps0 (Ts apps0) w.L
      (.allocation [alloc (.external w.dA) (w.a + a'), alloc (.external w.dB) (w.b + b')])
      [w.A, w.B] ∧
    v'.HoldsBalance w.L.address (w.a + w.b + w.c) ∧
    (∀ p, p = w.A ∨ p = w.B → (v p).chain = (v' p).chain) := by
  refine ⟨nOpen'.views, nClose'.views, nOpen', nClose', wLS, 0, 0,
    nOpen'_reach, rfl, nClose'_reach, rfl, rfl,
    ⟨rfl, rfl, ?_, nTwoCh_finalizable_fst rfl rfl cLW_ne_cχ.symm rfl⟩,
    nTwoCh_finalizable_snd rfl rfl cLW_ne_cχ rfl, nOneCh_finalizable rfl rfl, ?_,
    fun r _ => by simp only [nOpen', nClose', nTwoCh_views_chain, nOneCh_views_chain]⟩
  · intro r; simp only [nOpen', nTwoCh_views_chain]; exact zero_g0 _
  · intro r; simp only [nClose', nOneCh_views_chain]; exact zero_g0 _

/-- `ledger_topup_reorder_safe`. -/
example : ∃ A B χ : Address Nat, A ≠ B ∧ A ≠ χ ∧ B ≠ χ :=
  ⟨d0, d1, c1.address, by decide, by decide, by decide⟩

/-- `ledger_topup_deposit_funds`. -/
example : ∃ (s s' : Adjudicator Nat) (L : FixedPart) (A B χ : Address Nat) (a b c a' : Coins),
    A ≠ B ∧ A ≠ χ ∧ B ≠ χ ∧ s.balances.get L.address = a + b + c ∧
    s.deposit L.address (a + b + c) a' = some s' :=
  ⟨g0, _, c1, d0, d1, c3.address, 0, 0, 0, 0, by decide, by decide, by decide, rfl, rfl⟩

/-! ### SATP: a route of two peers (`p0` Alice, `q0` Bob) and of three. -/

def apps2 : Apps Nat := fun id => if id = ⟨1⟩ then satpVirtualRules else consensusRules
def Lr : FixedPart := ⟨[p0, q0], 10, ⟨0⟩, 2, .ledger⟩
def Vr : FixedPart := ⟨[p0, q0], 11, ⟨1⟩, 2, .virtual⟩
def r2 : Route Nat := ⟨[p0, q0], [Lr], Vr, 1, 0, fun p => p.key⟩
def vch : Voucher := ⟨Vr, 0, 0, 0, []⟩
def stV : State Nat :=
  ⟨Vr, 1, originalOutcome 0 1 1 0, false, .satpVirtual ⟨.none, vch⟩⟩

theorem r2_wf : r2.WellFormed apps2 := by
  refine ⟨rfl, by decide, by decide, by decide, fun i L h => ?_, rfl, rfl, fun i L h => ?_⟩
  · rcases i with _ | i
    · simp [r2] at h; subst h; exact ⟨p0, q0, rfl, rfl, rfl, rfl, rfl⟩
    · simp [r2] at h
  · rcases i with _ | i
    · simp [r2] at h; subst h; decide
    · simp [r2] at h

/-- `satp_outcome_change_keeps_total`. -/
example : ∃ (c : FixedPart) (alice bob : Participant) (proof : SupportProof Nat)
    (candidate : State Nat) (s0 : SignedState Nat),
    validateOutcomeChange c alice bob proof candidate = true ∧ proof.head? = some s0 :=
  ⟨Vr, p0, q0, [⟨stV, [p0, q0]⟩], stV, _, by decide, rfl⟩

def signed2 : List (Participant × State Nat) := [(p0, stV), (q0, stV)]
def sV1 : Adjudicator Nat := g0.setStatus Vr (.challenged 1 ⟨stV, 0 + 2⟩)
def sV2 : Adjudicator Nat := sV1.tick 2

theorem sV_reach : ReachableSigned apps2 signed2 sV2 := by
  refine .tail (.single (.mk p0 (.challenge Vr [⟨stV, [p0, q0]⟩] stV) g0 sV1 ?_ rfl))
    (.mk p0 (.tick 2) sV1 sV2 (fun _ h => by cases h) rfl)
  intro ss hss
  simp only [Op.proofStates, List.mem_singleton] at hss; subst hss
  exact ⟨by decide, fun v hv => by cases hv; intro q hq; cases hq⟩

/-- `satp_lemma_3_1`. -/
example : ∃ (r : Route Nat) (alice bob : Participant) (signed : List (Participant × State Nat))
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
  simp [signed2, p0, q0] at this
  subst this
  exact .inl ⟨by decide, rfl⟩

/-- `satp_peers_can_finalize`. `netV` is reachable the same way `netC2` is: `p0`'s own send,
    then an adversary deliver of `q0`'s claimed signature. -/
def netV : NetworkState Nat p0 := ⟨g0, [⟨stV, [q0]⟩], [⟨stV, [p0]⟩]⟩

theorem netV_reach : (Nitro.participant apps2 (canon p0)).Reachable netV :=
  participant_reachable_adv
    (participant_reachable_honest (participant_reachable_init apps2 (canon p0)) (.send stV)
      trivial)
    (.deliver ⟨stV, [q0]⟩) (⟨fun h => absurd h (by decide),
      fun v h hp => by cases h; exact absurd hp (by decide)⟩ :
      NetworkState.Unforged _ ⟨stV, [q0]⟩)

example : ∃ (r : Route Nat) (alice bob : Participant) (net : NetworkState Nat p0)
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
    rfl, fun t ht _ => by simp [netV] at ht; subst ht; exact .inl ⟨by decide, rfl⟩,
    ⟨0, rfl, by decide⟩⟩

/-- Three peers `p0`, `q0`, `w0`; `q0` is the intermediary. -/
def w0 : Participant := ⟨2⟩
def Lm3 : FixedPart := ⟨[p0, q0], 20, ⟨0⟩, 2, .ledger⟩
def Lp3 : FixedPart := ⟨[q0, w0], 21, ⟨0⟩, 2, .ledger⟩
def V3 : FixedPart := ⟨[p0, q0, w0], 22, ⟨1⟩, 2, .virtual⟩
def r3 : Route Nat := ⟨[p0, q0, w0], [Lm3, Lp3], V3, 1, 1, fun p => p.key⟩

theorem r3_wf : r3.WellFormed apps2 := by
  refine ⟨rfl, by decide, by decide, by decide, fun i L h => ?_, rfl, rfl, fun i L h => ?_⟩
  · rcases i with _ | _ | i
    · simp [r3] at h; subst h; exact ⟨p0, q0, rfl, rfl, rfl, rfl, rfl⟩
    · simp [r3] at h; subst h; exact ⟨q0, w0, rfl, rfl, rfl, rfl, rfl⟩
    · simp [r3] at h
  · rcases i with _ | _ | i
    · simp [r3] at h; subst h; decide
    · simp [r3] at h; subst h; decide
    · simp [r3] at h

def om3 : Allocation Nat := [alloc (.external 0) 0, alloc (.external 1) 0, r3.guarantee p0 q0]
def op3 : Allocation Nat := [alloc (.external 1) 0, alloc (.external 2) 0, r3.guarantee q0 w0]
def Sm : State Nat := ⟨Lm3, 1, .allocation om3, false, .opaque 0⟩
def Sp : State Nat := ⟨Lp3, 1, .allocation op3, false, .opaque 0⟩
def V0 : State Nat := ⟨V3, 0, originalOutcome 0 2 1 1, false, .satpVirtual ⟨.none, ⟨V3, 0, 0, 0, []⟩⟩⟩
def net3 : NetworkState Nat q0 :=
  ⟨g0, [⟨Sm, [p0]⟩, ⟨Sp, [w0]⟩], [⟨Sm, [q0]⟩, ⟨Sp, [q0]⟩, ⟨V0, [q0]⟩]⟩

theorem net3_latest_m : HoldsLatestLedger net3 Lm3 om3 :=
  ⟨⟨Sm, [p0, q0]⟩, holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, rfl, rfl,
    by decide, .inl ⟨0, rfl, by decide⟩⟩

theorem net3_latest_p : HoldsLatestLedger net3 Lp3 op3 :=
  ⟨⟨Sp, [q0, w0]⟩, holds_intro _ _ (by decide) (fun _ h => by cases h), by decide, rfl, rfl, rfl,
    by decide, .inl ⟨0, rfl, by decide⟩⟩

/-- `net3` is reachable: `q0`'s own three honest sends (`V0`, then `Sp`, then `Sm`, the order
    `.send` prepends into `net3`'s own `sent`), then two adversary delivers of `p0`'s and `w0`'s
    claimed signatures (delivered in reverse order, for the same prepend reason). -/
theorem net3_reach : (Nitro.participant apps2 (canon q0)).Reachable net3 :=
  participant_reachable_adv
    (participant_reachable_adv
      (participant_reachable_honest
        (participant_reachable_honest
          (participant_reachable_honest (participant_reachable_init apps2 (canon q0)) (.send V0)
            trivial)
          (.send Sp) trivial)
        (.send Sm) trivial)
      (.deliver ⟨Sp, [w0]⟩)
      (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ : NetworkState.Unforged _ ⟨Sp, [w0]⟩))
    (.deliver ⟨Sm, [p0]⟩)
    (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ : NetworkState.Unforged _ ⟨Sm, [p0]⟩)

/-- `satp_theorem_3_2`. -/
example : ∃ (r : Route Nat) (alice bob P Pprev Pnext : Participant) (i : Nat) (Lm Lp : FixedPart)
    (om op : Allocation Nat) (balm balp : Coins) (net : NetworkState Nat P),
    Assumptions apps2 P (canon P) ∧ r.WellFormed apps2 ∧ apps2 r.V.appDef = satpVirtualRules ∧
    r.peers.head? = some alice ∧ r.peers.getLast? = some bob ∧ 1 ≤ i ∧ i + 1 < r.peers.length ∧
    r.peers[i]? = some P ∧ r.peers[i - 1]? = some Pprev ∧ r.peers[i + 1]? = some Pnext ∧
    r.ledgers[i - 1]? = some Lm ∧ r.ledgers[i]? = some Lp ∧
    (2 * (canon P).ε ≤ Lm.challengeDuration ∧ 2 * (canon P).ε ≤ Lp.challengeDuration ∧
      2 * (canon P).ε ≤ r.V.challengeDuration) ∧
    r.LedgerAfterRound2 om Pprev P P balm r.b0 ∧ r.LedgerAfterRound2 op P Pnext P balp r.a0 ∧
    (Nitro.participant apps2 (canon P)).Reachable net ∧
    HoldsLatestLedger net Lm om ∧ HoldsLatestLedger net Lp op ∧
    HoldsVirtualSetup net r alice bob true ∧
    (net.DeadlineAfter Lm (canon P).ε ∧ net.DeadlineAfter Lp (canon P).ε ∧
      net.DeadlineAfter r.V (canon P).ε) ∧
    (net.chain.finalizedWith Lm.address = none ∧ net.chain.finalizedWith Lp.address = none ∧
      net.chain.finalizedWith r.V.address = none) :=
  ⟨r3, p0, w0, q0, p0, w0, 1, Lm3, Lp3, om3, op3, 1, 1, net3, canon_ok _ _, r3_wf, rfl, rfl, rfl,
    le_rfl, by decide, rfl, rfl, rfl, rfl, rfl, ⟨by decide, by decide, by decide⟩,
    by unfold Route.LedgerAfterRound2; decide, by unfold Route.LedgerAfterRound2; decide,
    net3_reach, net3_latest_m, net3_latest_p,
    ⟨fun t ht hc => by
        simp [net3] at ht
        rcases ht with rfl | rfl | rfl <;>
          first | exact ⟨rfl, rfl, .inl rfl⟩ | exact absurd hc (by decide),
      ⟨⟨V0, [q0]⟩, by simp [net3], rfl, rfl⟩⟩,
    ⟨deadlineAfter_open (t := 0) rfl _, deadlineAfter_open (t := 0) rfl _,
      deadlineAfter_open (t := 0) rfl _⟩, by decide⟩

/-- `satp_intermediary_before_round2`. `netB` is reachable the same way `net3` is, with two sends
    and two delivers instead of three and two. -/
def omB : Allocation Nat := [alloc (.external 1) 1]
def SmB : State Nat := ⟨Lm3, 1, .allocation omB, false, .opaque 0⟩
def SpB : State Nat := ⟨Lp3, 1, .allocation omB, false, .opaque 0⟩
def netB : NetworkState Nat q0 := ⟨g0, [⟨SmB, [p0]⟩, ⟨SpB, [w0]⟩], [⟨SmB, [q0]⟩, ⟨SpB, [q0]⟩]⟩

theorem netB_reach : (Nitro.participant apps2 (canon q0)).Reachable netB :=
  participant_reachable_adv
    (participant_reachable_adv
      (participant_reachable_honest
        (participant_reachable_honest (participant_reachable_init apps2 (canon q0)) (.send SpB)
          trivial)
        (.send SmB) trivial)
      (.deliver ⟨SpB, [w0]⟩)
      (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ :
        NetworkState.Unforged _ ⟨SpB, [w0]⟩))
    (.deliver ⟨SmB, [p0]⟩)
    (⟨fun h => absurd h (by decide), fun v h => by cases h⟩ : NetworkState.Unforged _ ⟨SmB, [p0]⟩)

example : ∃ (r : Route Nat) (P : Participant) (i : Nat) (Lm Lp : FixedPart)
    (om op : Allocation Nat) (balm balp : Coins) (net : NetworkState Nat P),
    Assumptions apps2 P (canon P) ∧ r.WellFormed apps2 ∧ 1 ≤ i ∧ i + 1 < r.peers.length ∧
    r.peers[i]? = some P ∧ r.ledgers[i - 1]? = some Lm ∧ r.ledgers[i]? = some Lp ∧
    (2 * (canon P).ε ≤ Lm.challengeDuration ∧ 2 * (canon P).ε ≤ Lp.challengeDuration) ∧
    r.LedgerBeforeRound2 om P balm ∧ r.LedgerBeforeRound2 op P balp ∧
    (Nitro.participant apps2 (canon P)).Reachable net ∧
    HoldsLatestLedger net Lm om ∧ HoldsLatestLedger net Lp op ∧
    (net.DeadlineAfter Lm (canon P).ε ∧ net.DeadlineAfter Lp (canon P).ε) ∧
    (net.chain.finalizedWith Lm.address = none ∧ net.chain.finalizedWith Lp.address = none) :=
  ⟨r3, q0, 1, Lm3, Lp3, omB, omB, 1, 1, netB, canon_ok _ _, r3_wf, le_rfl, by decide, rfl, rfl, rfl,
    ⟨by decide, by decide⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, netB_reach,
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
def sE : Adjudicator Nat := (g0.setStatus Vr (.challenged 0 ⟨V0r, 0 + Vr.challengeDuration⟩)).tick 2
def netE : NetworkState Nat p0 :=
  ⟨sE, [⟨S0, [q0]⟩, ⟨V0r, [q0]⟩], [⟨S0, [p0]⟩, ⟨V0r, [p0]⟩]⟩

theorem netE_reach : (Nitro.participant apps2 (canon p0)).Reachable netE :=
  participant_reachable_honest
    (participant_reachable_honest
      (participant_reachable_adv
        (participant_reachable_honest
          (participant_reachable_adv
            (participant_reachable_honest (participant_reachable_init apps2 (canon p0))
              (.send V0r) trivial)
            (.deliver ⟨V0r, [q0]⟩) (by
              refine ⟨fun h => absurd h (by decide), fun v h hp => ?_⟩
              cases h; exact absurd hp (by decide)))
          (.send S0) trivial)
        (.deliver ⟨S0, [q0]⟩) (by
          refine ⟨fun h => absurd h (by decide), fun v h => ?_⟩
          cases h))
      (.chain (.challenge Vr [⟨V0r, [p0, q0]⟩] V0r))
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
    (.wait 2) trivial

example : ∃ (r : Route Nat) (alice bob P P1 : Participant) (L0 : FixedPart) (o : Allocation Nat)
    (bal a b : Coins) (net : NetworkState Nat P),
    Assumptions apps2 P (canon P) ∧ r.WellFormed apps2 ∧ apps2 r.V.appDef = satpVirtualRules ∧
    r.peers.head? = some alice ∧ r.peers.getLast? = some bob ∧ P = alice ∧ r.peers[1]? = some P1 ∧
    r.ledgers[0]? = some L0 ∧
    (2 * (canon P).ε ≤ L0.challengeDuration ∧ 2 * (canon P).ε ≤ r.V.challengeDuration) ∧
    r.LedgerAfterRound2 o P P1 P bal r.a0 ∧
    (Nitro.participant apps2 (canon P)).Reachable net ∧
    HoldsLatestLedger net L0 o ∧
    HoldsVirtualSetup net r alice bob true ∧ a + b = r.a0 + r.b0 ∧
    net.chain.finalOutcome r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]) ∧
    net.DeadlineAfter L0 (canon P).ε ∧ net.chain.finalizedWith L0.address = none := by
  refine ⟨r2, p0, q0, p0, q0, Lr, o0, 1, 1, 0, netE, canon_ok _ _, r2_wf, rfl, rfl, rfl, rfl, rfl,
    rfl, ⟨by decide, by decide⟩, by unfold Route.LedgerAfterRound2; decide, netE_reach,
    ⟨⟨S0, [p0, q0]⟩, ?_, by decide, rfl, rfl, rfl, ?_, ?_⟩, ⟨?_, ?_⟩, rfl, by decide, ?_, by decide⟩
  · refine ⟨fun q hq => ?_, fun v hv => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact .inl ⟨rfl, ⟨S0, [p0]⟩, List.mem_cons_self, rfl⟩
      · exact .inr ⟨⟨S0, [q0]⟩, List.mem_cons_self, rfl, List.mem_cons_self⟩
    · simp [S0, State.voucher?] at hv
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

example : ∃ (s : Adjudicator Nat) (r : Route Nat) (alice bob P Pprev Pnext : Participant)
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

end ArmadaLean.Nitro.NonVacuity
