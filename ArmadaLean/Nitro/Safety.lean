/-
  Nitro protocol theorems: on-chain adjudicator safety, conservation and the
  correctness of the data operations. Every proof is `sorry`. The statements
  are the deliverable. Each doc comment cites the source lines and the
  property ids of `docs/nitro-theorems.md`.
-/
import ArmadaLean.Nitro.SATP

namespace ArmadaLean.Nitro

open Classical

/-- S1-D02, S2-02, S2-03, S3-05, S4-0010-02, S1-F01. S1:610-611: "The
    resulting channelId is designed to uniquely identify the channel";
    S2:158-160: impossible "to construct a channel whose address is A".
    Two fixed parts with one address are one channel. -/
theorem channel_address_inj (c c' : FixedPart) (h : c.address = c'.address) : c = c' := by
  sorry

/-- S1-D02, S2-02. A channel address is never a participant address, so a
    channel's funds cannot be read as a participant's. -/
theorem channel_address_ne_participant (c : FixedPart) (p : Participant) :
    c.address ≠ .participant p := by
  sorry

/-- S2-01. S2:162-163: "If an address does not appear in the table we take
    the balance to be zero." -/
theorem balances_absent_zero (b : Balances) (a : Address) (h : ∀ e ∈ b, e.1 ≠ a) :
    b.get a = 0 := by
  sorry

/-- S2-08, S2-05, S1-F04, S4-C-01. S2:230-231: "The total coins held by the
    smart contract should always equal the sum of the balances." -/
theorem held_eq_total_balances (apps : Apps) (s : Adjudicator) (h : Reachable apps s) :
    s.held = s.balances.total := by
  sorry

/-- S2-04, S2-05, S1-C01, S4-0060-03, S4-0060-04, S4-0060-05. S2:165-168:
    the deposit `D_A(x)` raises `A`'s balance by `x` and brings `x` coins into
    the adjudicator. It touches nothing else. A second deposit adds to the
    first. -/
theorem deposit_effects (s : Adjudicator) (a : Address) (x : Coins) :
    (s.deposit a x).balances.get a = s.balances.get a + x ∧
    (s.deposit a x).held = s.held + x ∧
    (∀ b, b ≠ a → (s.deposit a x).balances.get b = s.balances.get b) ∧
    (s.deposit a x).status = s.status ∧ (s.deposit a x).now = s.now := by
  sorry

/-- S2-04. S2:166-167: "There are no restrictions on who can deposit coins
    for an address". The deposit succeeds for every caller and every address
    kind. -/
theorem deposit_can_happen (apps : Apps) (caller : Participant) (s : Adjudicator) (a : Address)
    (x : Coins) : s.apply apps caller (.deposit a x) = some (s.deposit a x) := by
  sorry

/-- S2-06, S2-07, S3-16. S2:227-229: "funds can only be withdrawn from
    participant addresses - and only by a party who knows the private key."
    A successful withdrawal is by the owner and within the balance. -/
theorem withdraw_requires_key (s : Adjudicator) (caller a : Participant) (x : Coins)
    (s' : Adjudicator) (h : s.withdraw caller a x = some s') :
    caller = a ∧ x ≤ s.balances.get (.participant a) := by
  sorry

/-- S2-06. S2:169-170: the withdrawal lowers `A`'s balance by `x` and takes
    `x` coins out of the adjudicator. Every other balance is unchanged. -/
theorem withdraw_effects (s : Adjudicator) (caller a : Participant) (x : Coins)
    (s' : Adjudicator) (h : s.withdraw caller a x = some s') :
    s'.balances.get (.participant a) = s.balances.get (.participant a) - x ∧
    s'.held = s.held - x ∧
    (∀ b, b ≠ .participant a → s'.balances.get b = s.balances.get b) ∧
    s'.status = s.status := by
  sorry

/-- S2-07. S2:227-229: no withdrawal moves a channel's balance. The only
    operation that takes a channel's coins is a redistribution. -/
theorem withdraw_leaves_channels (s : Adjudicator) (caller a : Participant) (x : Coins)
    (s' : Adjudicator) (h : s.withdraw caller a x = some s') (c : FixedPart) :
    s'.balances.get c.address = s.balances.get c.address := by
  sorry

/-- S1-A16, S1-B07, S2-26, S3-12, S4-0080-03. S1:1837-1853: participant `k`
    receives `min(owed_k, balance − pending)` where `pending` is the total
    owed to the entries before `k`. S2:747-749: "the addresses at the
    beginning of the allocation will receive funds first." -/
theorem payout_priority_formula (held : Coins) (o : Allocation) (k : Nat) (e : Entry)
    (h : o[k]? = some e) :
    (o.payout held)[k]? = some (e.dest, min e.amount (held - Allocation.total (o.take k))) := by
  sorry

/-- S1-B07, S2-26. S1:1812-1821: "paying out Alice first, allowing her to
    recover her funds even if Bob does not deposit." If a later entry
    receives anything, every earlier entry received its full amount. -/
theorem payout_earlier_paid_in_full (held : Coins) (o : Allocation) (i j : Nat)
    (ei ej : Entry) (pi pj : Coins) (hi : o[i]? = some ei) (hj : o[j]? = some ej) (hij : i < j)
    (hpi : (o.payout held)[i]? = some (ei.dest, pi))
    (hpj : (o.payout held)[j]? = some (ej.dest, pj)) (hpos : 0 < pj) :
    pi = ei.amount := by
  sorry

/-- S2-26, S2-28. The payout never exceeds the coins held, and never pays an
    entry more than its amount. -/
theorem payout_bounded (held : Coins) (o : Allocation) :
    ((o.payout held).map (·.2)).sum ≤ held ∧
    ∀ (i : Nat) (e : Entry) (x : Coins), o[i]? = some e → (o.payout held)[i]? = some (e.dest, x) →
      x ≤ e.amount := by
  sorry

/-- S2-25. S2:744-746: "ignoring any additional entries for a given address
    after the first." A destination receives at most the amount of its first
    entry. -/
theorem paidTo_first_entry_only (held : Coins) (o : Allocation) (d : Address) :
    o.paidTo held d ≤ o.owed d := by
  sorry

/-- S2-27, S2-16. S2:749-751: a channel that holds the whole total of its
    allocation affords every entry in full. -/
theorem affords_when_fully_funded (held : Coins) (o : Allocation) (d : Address)
    (h : o.total ≤ held) : o.Affords held d (o.owed d) := by
  sorry

/-- S2-28, S2-10, S1-A15, S4-0080-03, S4-0080-04. S2:765-770: when `A` can
    afford `x` for `B`, `T(A, B, x)` lowers `A`'s funds by `x`, raises `B`'s
    funds by `x`, and lowers the amount owed to `B` in `A`'s outcome by `x`.
    No coin leaves the adjudicator. -/
theorem transfer_effects (s : Adjudicator) (a : FixedPart) (b : Address) (x : Coins)
    (s' : Adjudicator) (h : s.transfer a b x = some s') :
    ∃ o, s.finalOutcome a.address = some (.allocation o) ∧
      o.Affords (s.balances.get a.address) b x ∧
      s'.balances.get a.address + x = s.balances.get a.address + (if b = a.address then x else 0) ∧
      (b ≠ a.address → s'.balances.get b = s.balances.get b + x) ∧
      (∀ d, d ≠ a.address → d ≠ b → s'.balances.get d = s.balances.get d) ∧
      s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) ∧
      s'.held = s.held ∧ s'.now = s.now := by
  sorry

/-- S2-28, S2-43. The reduction of an owed amount is exact. -/
theorem reduceOwed_owed (o : Allocation) (d : Address) (x : Coins) :
    (o.reduceOwed d x).owed d = o.owed d - x ∧
    ∀ d', d' ≠ d → (o.reduceOwed d x).owed d' = o.owed d' := by
  sorry

/-- S2-28, S2-15. S2:765-767: the transfer succeeds whenever `A` is
    finalized with an allocation that affords `x` for `B`. The exact result
    is stated. -/
theorem transfer_can_happen (s : Adjudicator) (a : FixedPart) (b : Address) (x : Coins)
    (o : Allocation) (hf : s.finalOutcome a.address = some (.allocation o))
    (ha : o.Affords (s.balances.get a.address) b x) :
    s.transfer a b x = some
      { (s.setStatus a ((s.statusOf a).withOutcome (.allocation (o.reduceOwed b x)))) with
        balances := (s.balances.sub a.address x).add b x } := by
  sorry

/-- S2-29, S1-A20. S2:771-772: "If A cannot afford x for B, then T(A, B, x)
    fails, leaving the on-chain state unchanged." -/
theorem transfer_fails_when_unaffordable (s : Adjudicator) (a : FixedPart) (b : Address)
    (x : Coins) (h : ∀ o, s.finalOutcome a.address = some (.allocation o) →
      ¬ o.Affords (s.balances.get a.address) b x) :
    s.transfer a b x = none := by
  sorry

/-- S2-10, S1-A15, S3-16, S4-0080-01. S2:261-266: redistribution reads a
    finalized outcome. S1:1725-1728: `withdraw` requires
    `isTerminated(channelId)`. A transfer succeeds only on a finalized
    channel. -/
theorem transfer_requires_finalized (s : Adjudicator) (a : FixedPart) (b : Address) (x : Coins)
    (s' : Adjudicator) (h : s.transfer a b x = some s') : s.mode a = .finalized := by
  sorry

/-- S2-15. S2:312-313: "There is no restriction on who can trigger the
    operations." A redistribution gives the same result for every caller. -/
theorem redistribution_ignores_caller (apps : Apps) (s : Adjudicator) (op : Op)
    (c1 c2 : Participant) (h : op.isRedistribution = true) :
    s.apply apps c1 op = s.apply apps c2 op := by
  sorry

/-- S2-08. A redistribution moves coins between balances. It changes neither
    the sum of the balances nor the coins held. -/
theorem redistribution_conserves_total (apps : Apps) (s s' : Adjudicator) (caller : Participant)
    (op : Op) (hop : op.isRedistribution = true) (h : s.apply apps caller op = some s') :
    s'.balances.total = s.balances.total ∧ s'.held = s.held := by
  sorry

/-- The outcomes a finalized outcome can become through redistribution:
    S2:770 (transfer), S2:1144 (claim on the target), S3:358-361
    (reclaim on the ledger). -/
inductive Redistributed : Outcome → Outcome → Prop
  | refl (Ω : Outcome) : Redistributed Ω Ω
  | reduce {o : Allocation} (d : Address) (x : Coins) (Ω : Outcome) :
      Redistributed Ω (.allocation o) → Redistributed Ω (.allocation (o.reduceOwed d x))
  | reclaim {o : Allocation} (left right v : Address) (x y : Coins) (Ω : Outcome) :
      Redistributed Ω (.allocation o) →
      Redistributed Ω (.allocation (((o.addTo left x).addTo right y).remove v))

/-- S2-11, S1-B03, S3-16, S4-0070-04, S1-A14. S2:288-290: "There are two
    ways for an outcome to become finalized: (i) through a challenge that
    times out before anyone responds, and (ii) through the registration of a
    conclusion proof." A finalized outcome traces to one such step, and has
    only been redistributed since. -/
theorem finalized_two_ways (apps : Apps) (s : Adjudicator) (c : FixedPart) (Ω : Outcome)
    (hr : Reachable apps s) (hf : s.finalOutcome c.address = some Ω) :
    ∃ s0 s1 caller proof candidate, Reachable apps s0 ∧
      Redistributed candidate.outcome Ω ∧
      ((s0.apply apps caller (.conclude c proof candidate) = some s1 ∧ candidate.isFinal = true) ∨
       (s0.apply apps caller (.challenge c proof candidate) = some s1 ∧
          s0.now + c.challengeDuration ≤ s.now)) := by
  sorry

/-- S2-14, S1-A14, S1-D12. S2:301-302: "the rules of operation only allow
    one outcome to be finalized for each channel." Once finalized, a channel
    stays finalized. -/
theorem finalized_permanent (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (h : Step apps s s') (hf : s.mode c = .finalized) : s'.mode c = .finalized := by
  sorry

/-- S2-14. A finalized outcome is never replaced by a second finalization.
    Every later outcome of the channel is a redistribution of the first. -/
theorem finalized_outcome_only_redistributed (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (Ω : Outcome) (h : Step apps s s') (hf : s.finalOutcome c.address = some Ω) :
    ∃ Ω', s'.finalOutcome c.address = some Ω' ∧ Redistributed Ω Ω' := by
  sorry

/-- S1-A10, S1-A21, S3-14, S4-0070-02, S4-0070-03. S1:1340-1354 `forceMove`
    requires no challenge in progress, a non-terminated channel and a valid
    run; S3:303-305 requires an open channel and
    `version >= adjudicatorStatus.version`; S1:1545-1548 requires the
    challenger to be a participant. -/
theorem challenge_requires (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (s' : Adjudicator)
    (h : s.challenge apps challenger c proof candidate = some s') :
    challenger ∈ c.participants ∧ s.mode c = .open ∧
    (apps c.appDef).supports c proof candidate ∧ candidate.channel = c ∧
    (s.statusOf c).turnNumRecord ≤ candidate.turnNum := by
  sorry

/-- S1-A10, S1-C02, S1-F03, S2-12, S3-14, S4-0070-08. S1:1353
    `setChallenge(c, now() + defaultExpirationTime)`; S3:308-310
    `now + consts.challengeDuration`. The exact result. -/
theorem challenge_can_happen (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State)
    (hp : challenger ∈ c.participants) (hm : s.mode c = .open)
    (hs : (apps c.appDef).supports c proof candidate) (hc : candidate.channel = c)
    (ht : (s.statusOf c).turnNumRecord ≤ candidate.turnNum) :
    s.challenge apps challenger c proof candidate = some
      (s.setStatus c (.challenged candidate.turnNum ⟨candidate, s.now + c.challengeDuration⟩)) := by
  sorry

/-- S1-D12, S1-B04, S3-14. A fresh challenge with a positive duration puts
    the channel in challenge mode. Balances, coins held and the clock do not
    move. -/
theorem challenge_effects (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (s' : Adjudicator)
    (h : s.challenge apps challenger c proof candidate = some s') (hd : 0 < c.challengeDuration) :
    s'.mode c = .challenge ∧ s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now ∧
    ∀ c', c' ≠ c → s'.statusOf c' = s.statusOf c' := by
  sorry

/-- S1-A11, S1-A12, S1-A13, S1-B02, S1-A21. S1:1431-1440: a response needs a
    challenge in progress (or an open channel) and a supported state;
    S1:1377-1381: "each of these responses lead to an increase in the
    turnNum from the challenge state stored in the adjudicator." -/
theorem respond_requires (apps : Apps) (s : Adjudicator) (c : FixedPart) (proof : SupportProof)
    (candidate : State) (s' : Adjudicator) (h : s.respond apps c proof candidate = some s') :
    s.mode c ≠ .finalized ∧ (apps c.appDef).supports c proof candidate ∧
    candidate.channel = c ∧ (s.statusOf c).turnNumRecord < candidate.turnNum := by
  sorry

/-- S1-A18, S1-B04, S1-A21, S4-0070-10. S1:1266-1269: "If a valid response
    is received, the game returns to the Collaborative mode"; S1:1765-1770
    `cancelChallenge`; S1:1543-1545: the response's turn is stored. -/
theorem respond_can_happen (apps : Apps) (s : Adjudicator) (c : FixedPart) (proof : SupportProof)
    (candidate : State) (hm : s.mode c ≠ .finalized)
    (hs : (apps c.appDef).supports c proof candidate) (hc : candidate.channel = c)
    (ht : (s.statusOf c).turnNumRecord < candidate.turnNum) :
    s.respond apps c proof candidate = some (s.setStatus c (.open candidate.turnNum)) ∧
    (s.setStatus c (.open candidate.turnNum)).mode c = .open := by
  sorry

/-- S1-B02, S1-A21, S4-0070-03, S4-0040-03. S1:1543-1545: "Only allow new
    force-moves if their response will increase this stored turnNum."
    No step lowers the stored turn number of a channel. -/
theorem turnNumRecord_monotone (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (h : Step apps s s') : (s.statusOf c).turnNumRecord ≤ (s'.statusOf c).turnNumRecord := by
  sorry

/-- S1-A14, S2-13, S3-16, S4-0070-01, S4-0010-05. S1:1495-1500: a conclude
    needs a non-terminated channel and a valid conclusion proof. S3:288-289:
    "supporting a state with isFinal = true". -/
theorem conclude_requires (apps : Apps) (s : Adjudicator) (c : FixedPart) (proof : SupportProof)
    (candidate : State) (s' : Adjudicator) (h : s.conclude apps c proof candidate = some s') :
    s.mode c ≠ .finalized ∧ (apps c.appDef).supports c proof candidate ∧
    candidate.channel = c ∧ candidate.isFinal = true := by
  sorry

/-- S1-A14, S2-13, S3-16, S4-0070-09. S1:1507 `setChallenge(endState,
    now())`: the channel is finalized at once with the candidate's outcome;
    S2:299-300: "the participants avoid having to wait for the challenge
    period." The exact result. -/
theorem conclude_can_happen (apps : Apps) (s : Adjudicator) (c : FixedPart) (proof : SupportProof)
    (candidate : State) (hm : s.mode c ≠ .finalized)
    (hs : (apps c.appDef).supports c proof candidate) (hc : candidate.channel = c)
    (hf : candidate.isFinal = true) :
    s.conclude apps c proof candidate =
      some (s.setStatus c (.finalized candidate.turnNum candidate.outcome)) ∧
    (s.setStatus c (.finalized candidate.turnNum candidate.outcome)).finalOutcome c.address =
      some candidate.outcome ∧
    (s.setStatus c (.finalized candidate.turnNum candidate.outcome)).mode c = .finalized := by
  sorry

/-- S1-A04, S1-A05, S4-0070-07. S1:976-980, S1:1017-1022: the conclude
    transition keeps the resolution; a conclude moves no coins. -/
theorem conclude_moves_no_value (apps : Apps) (s : Adjudicator) (c : FixedPart)
    (proof : SupportProof) (candidate : State) (s' : Adjudicator)
    (h : s.conclude apps c proof candidate = some s') :
    s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now := by
  sorry

/-- S1-A09, S2-13, S3-08, S3-16, S4-0070-01, S4-0020-01. S2:297-298: "all
    the participants sign a special conclude state, called a conclusion
    proof". Under the consensus app a conclude carries one state signed by
    every participant. -/
theorem conclude_consensus_needs_all (apps : Apps) (s : Adjudicator) (c : FixedPart)
    (proof : SupportProof) (candidate : State) (s' : Adjudicator)
    (hc : apps c.appDef = consensusRules) (h : s.conclude apps c proof candidate = some s') :
    ∃ ss, proof = [ss] ∧ ss.state = candidate ∧ ConclusionProof c ss := by
  sorry

/-- S1-B03, S1-D12, S2-12, S4-0040-05, S4-0040-06. S1:1260-1265: "If no
    response is received within the timeout period, the game transitions into
    the Terminated mode... the players can reclaim their funds according to
    the outcome of the game." S1:449-453: "the resolution stored on the
    challenge state s will decide how the funds should be split." -/
theorem timeout_finalizes (s : Adjudicator) (c : FixedPart) (t : Nat) (ch : Challenge)
    (hs : s.statusOf c = .challenged t ch) (hd : ch.deadline ≤ s.now) :
    s.mode c = .finalized ∧ s.finalOutcome c.address = some ch.state.outcome := by
  sorry

/-- S1-D12. S1:1295 `inProgress: c ↦ c.endTime > now()`. -/
theorem challenge_in_progress_before_deadline (s : Adjudicator) (c : FixedPart) (t : Nat)
    (ch : Challenge) (hs : s.statusOf c = .challenged t ch) (hd : s.now < ch.deadline) :
    s.mode c = .challenge ∧ s.finalOutcome c.address = none := by
  sorry

/-- S1-F03, S4-0040-05. S4: "a passive transition which happens when a block
    is produced with a sufficiently large timestamp." The clock changes no
    balance and no status. -/
theorem tick_moves_only_time (s : Adjudicator) (dt : Time) :
    (s.tick dt).balances = s.balances ∧ (s.tick dt).held = s.held ∧
    (s.tick dt).status = s.status ∧ (s.tick dt).now = s.now + dt := by
  sorry

/-- S1-A20. S1:685-686: "making an invalid move is equivalent to not making
    any move at all." A failed operation leaves the chain unchanged. -/
theorem failed_op_no_effect (apps : Apps) (caller : Participant) (op : Op) (s : Adjudicator)
    (h : s.apply apps caller op = none) :
    Adjudicator.applyAll apps [(caller, op)] s = s := by
  sorry

/-- S1-F05. S1:1609-1628: "Funding happens externally to the channel and
    there is no way of telling from the properties of the channel how (or
    even whether) the game is funded." The dispute operations read no
    balance: their success and their status result do not depend on the
    balances. -/
theorem funding_decoupled_from_rules (apps : Apps) (caller : Participant) (s : Adjudicator)
    (b : Balances) (op : Op) (hop : op.isRedistribution = false ∧
      (∀ a x, op ≠ .deposit a x) ∧ (∀ a x, op ≠ .withdraw a x)) :
    ((s.apply apps caller op).map Adjudicator.status) =
      (({ s with balances := b }.apply apps caller op).map Adjudicator.status) := by
  sorry

/-- S1-A01, S1-A02, S1-A03, S1-D05, S1-D06, S1-D04. S1:744-751 `validMove`:
    a valid transition whose signer is the mover; S1:761-778: the channel is
    fixed and the turn number increments by one. Under the ForceMove rules a
    supported candidate ends a run of `n` such moves. -/
theorem forceMove_supports_valid_run (vt : State → State → Prop) (c : FixedPart)
    (proof : SupportProof) (candidate : State)
    (h : (forceMoveRules vt).supports c proof candidate) :
    proof.length = c.n ∧
    (∀ (i : Nat) m1 m2, proof[i]? = some m1 → proof[i + 1]? = some m2 →
      m2.state.channel = m1.state.channel ∧ m2.state.turnNum = m1.state.turnNum + 1 ∧
      m2.ByMover ∧ (m2.state.isFinal = false → vt m1.state m2.state)) ∧
    (∃ m, proof.getLast? = some m ∧ m.state = candidate) := by
  sorry

/-- S1-A04, S1-A05, S1-A08. S1:976-980: "GAME→CONCLUDE needs the resolution
    unchanged"; S1:1017-1022: from CONCLUDE only CONCLUDE with the same
    resolution; S1:1203-1208: backing out keeps the resolution. -/
theorem forceMove_conclude_keeps_outcome (vt : State → State → Prop) (c : FixedPart)
    (proof : SupportProof) (candidate : State)
    (h : (forceMoveRules vt).supports c proof candidate) (i : Nat) (m1 m2 : SignedState)
    (h1 : proof[i]? = some m1) (h2 : proof[i + 1]? = some m2) :
    (m2.state.isFinal = true → m2.state.outcome = m1.state.outcome) ∧
    (m1.state.isFinal = true → m2.state.isFinal = true) := by
  sorry

/-- S1-D05, S1-D06. S1:724-727: "the mover is fully determined by the turn
    number". -/
theorem mover_determined_by_turn (s t : State) (hc : s.channel = t.channel)
    (ht : s.turnNum = t.turnNum) : s.mover = t.mover := by
  sorry

/-- S1-D06. S1:725-727: "players must take turns in a cyclical order." The
    mover of turn `k + n` is the mover of turn `k`. -/
theorem mover_cyclic (s : State) (k : Nat) :
    { s with turnNum := k + s.channel.n }.mover = { s with turnNum := k }.mover := by
  sorry

/-- S2-40, S2-42, S2-43. S2:1139-1141: a claim needs `G` finalized as a
    guarantee for `L`, `L` finalized with an allocation, and `G` able to
    afford `x` for `A` under its prioritization. S2:1072-1074: "The funds
    held in a guarantee channel can only be paid out once the outcome of the
    target channel is finalized." -/
theorem claim_requires (s : Adjudicator) (g : FixedPart) (a : Address) (x : Coins)
    (s' : Adjudicator) (h : s.claim g a x = some s') :
    ∃ l priority target, s.finalOutcome g.address = some (.guarantee (.channel l) priority) ∧
      s.finalOutcome (.channel l) = some (.allocation target) ∧
      s.mode g = .finalized ∧ s.mode l = .finalized ∧
      GuaranteeAffords (s.balances.get g.address) priority target a x := by
  sorry

/-- S2-43. S2:1141-1144: the claim lowers `G`'s funds by `x`, raises `A`'s
    funds by `x`, and lowers the amount owed to `A` in `L`'s outcome by `x`.
    No coin leaves the adjudicator. -/
theorem claim_effects (s : Adjudicator) (g : FixedPart) (a : Address) (x : Coins)
    (s' : Adjudicator) (h : s.claim g a x = some s') :
    ∃ l priority target, s.finalOutcome g.address = some (.guarantee (.channel l) priority) ∧
      s.finalOutcome (.channel l) = some (.allocation target) ∧
      s'.balances.get g.address + x = s.balances.get g.address + (if a = g.address then x else 0) ∧
      (a ≠ g.address → s'.balances.get a = s.balances.get a + x) ∧
      s'.finalOutcome (.channel l) = some (.allocation (target.reduceOwed a x)) ∧
      s'.finalOutcome g.address = s.finalOutcome g.address ∧
      s'.held = s.held := by
  sorry

/-- S2-43, S2-40. S2:1145: "Otherwise, the claim operation has no effect."
    A claim whose target is not finalized, or that is not affordable, fails. -/
theorem claim_fails_otherwise (s : Adjudicator) (g : FixedPart) (a : Address) (x : Coins)
    (h : ∀ l priority target, s.finalOutcome g.address = some (.guarantee (.channel l) priority) →
      s.finalOutcome (.channel l) = some (.allocation target) →
      ¬ GuaranteeAffords (s.balances.get g.address) priority target a x) :
    s.claim g a x = none := by
  sorry

/-- S2-41. S2:1099-1101: "if we have the guarantee (L|A, B, C) and the
    outcome of L is (C : 1, D : 2, A : 4), then the guarantee will pay out as
    though the outcome was (A : 4, C : 1, D : 2)." -/
theorem reprioritize_example (A B C D : Address) (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    Allocation.reprioritize [A, B, C] [alloc C 1, alloc D 2, alloc A 4] =
      [alloc A 4, alloc C 1, alloc D 2] := by
  sorry

/-- S2-39, S2-41. S2:1098-1099: the listed addresses "will be moved to the
    top of the priority order if they appear in the outcome." The
    reprioritized allocation owes each destination the same amount, and the
    listed destinations that appear come first, in list order. -/
theorem reprioritize_keeps_amounts (priority : List Address) (o : Allocation) (d : Address) :
    (o.reprioritize priority).owed d = o.owed d ∧
    (∀ e ∈ o.reprioritize priority, e ∈ o) ∧
    (∀ (i j : Nat) a b, (o.reprioritize priority)[i]? = some a →
      (o.reprioritize priority)[j]? = some b → a.dest ∈ priority → b.dest ∉ priority → i < j) := by
  sorry

/-- S3-15. S3:348-352: a reclaim needs both channels finalized and a
    guarantee entry for the target in the ledger's outcome. -/
theorem reclaim_requires (s : Adjudicator) (l v : FixedPart) (s' : Adjudicator)
    (h : s.reclaim l v = some s') :
    s.mode l = .finalized ∧ s.mode v = .finalized ∧
    ∃ oL oV x left right, s.finalOutcome l.address = some (.allocation oL) ∧
      s.finalOutcome v.address = some (.allocation oV) ∧
      oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ := by
  sorry

/-- S3-15, S4-0080-05. S3:358-363: `o_ledger[left] += o_target[0]`,
    `o_ledger[right] += o_target[1]`, `delete o_ledger[targetChannelId]`.
    The balances do not move. The coins in the ledger outcome rise by the
    target's first two amounts and fall by the guarantee amount. -/
theorem reclaim_effects (s : Adjudicator) (l v : FixedPart) (s' : Adjudicator)
    (oL oV : Allocation) (x : Coins) (left right : Address)
    (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalOutcome v.address = some (.allocation oV))
    (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩)
    (hlr : left ≠ right) (hlv : left ≠ v.address) (hrv : right ≠ v.address)
    (h : s.reclaim l v = some s') :
    ∃ oL', s'.finalOutcome l.address = some (.allocation oL') ∧
      oL'.owed left = oL.owed left + oV.amountAt 0 ∧
      oL'.owed right = oL.owed right + oV.amountAt 1 ∧
      oL'.find v.address = none ∧
      oL'.total + x = oL.total + oV.amountAt 0 + oV.amountAt 1 ∧
      s'.balances = s.balances ∧ s'.held = s.held ∧
      s'.finalOutcome v.address = s.finalOutcome v.address := by
  sorry

/-- S3-15, S4-0080-05. The reclaim succeeds whenever its preconditions hold.
    The exact result is stated. -/
theorem reclaim_can_happen (s : Adjudicator) (l v : FixedPart) (oL oV : Allocation) (x : Coins)
    (left right : Address) (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalOutcome v.address = some (.allocation oV))
    (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩) :
    s.reclaim l v = some (s.setStatus l ((s.statusOf l).withOutcome
      (.allocation ((((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1))).remove
        v.address)))) := by
  sorry

/-- S3-13, S4-0040-02. S3:294-298 `isOpen`: "the channel has no active
    challenge or the channel has not yet finalized". -/
theorem isOpen_iff (st : ChannelStatus) (now : Time) :
    st.IsOpen now ↔ (st.mode now = .open ∨ st.mode now = .challenge) := by
  sorry

/-- S1-D11, S2-11. Every channel is in exactly one mode. A channel with no
    record is open. -/
theorem mode_of_absent (s : Adjudicator) (c : FixedPart) (h : ∀ e ∈ s.status, e.1 ≠ c) :
    s.mode c = .open ∧ (s.statusOf c).turnNumRecord = 0 := by
  sorry

/-- S2-08, S2-05. Only a deposit raises the coins held and only a withdrawal
    lowers them. -/
theorem held_changes_only_by_deposit_withdraw (apps : Apps) (s s' : Adjudicator)
    (caller : Participant) (op : Op) (h : s.apply apps caller op = some s')
    (hne : s'.held ≠ s.held) :
    (∃ a x, op = .deposit a x) ∨ (∃ a x, op = .withdraw a x) := by
  sorry

end ArmadaLean.Nitro
