/-
  Nitro protocol theorems: on-chain adjudicator safety, conservation and the
  correctness of the data operations. Every proof is `sorry`. The statements
  are the deliverable. Each doc comment cites the latest source first (SATP,
  then Nitro, then ForceMove), then go-nitro, and names the property ids of
  `docs/nitro-theorems.md`.
-/
import ArmadaLean.Nitro.SATP

namespace ArmadaLean.Nitro

/-- ForceMove-D02, Nitro-02, Nitro-03, SATP-05, docs-0010-02, ForceMove-F01.
    SATP:213-215: the id is computed from the constants and the nonce makes
    channels distinct; Nitro:158-160: impossible "to construct a channel
    whose address is A"; go-nitro NitroUtils.sol:122-133. Two fixed parts
    with one address are one channel. -/
theorem channel_address_inj (c c' : FixedPart) (h : c.address = c'.address) : c = c' := by
  sorry

/-- ForceMove-D02, Nitro-02. go-nitro `_isExternalDestination`: a channel
    id is never an external address, so a channel's funds cannot be read as
    a participant's. -/
theorem channel_address_ne_participant (c : FixedPart) (p : Participant) :
    c.address ≠ .participant p := by
  sorry

/-- Nitro-01. Nitro:162-163: "If an address does not appear in the table we
    take the balance to be zero." go-nitro: an unset `holdings` entry reads
    as 0. -/
theorem balances_absent_zero (b : Balances) (a : Address) (h : ∀ e ∈ b, e.1 ≠ a) :
    b.get a = 0 := by
  sorry

/-- Nitro-08, Nitro-05, ForceMove-F04, docs-C-01. Nitro:230-231: "The total
    coins held by the smart contract should always equal the sum of the
    balances." go-nitro: `holdings` is per channel, and a payout to an
    external destination leaves the contract (MultiAssetHolder.sol:401-402),
    so the coins held equal the sum of the channel balances. -/
theorem held_eq_channel_balances (apps : Apps) (s : Adjudicator) (h : Reachable apps s) :
    s.held = s.balances.channelTotal := by
  sorry

/-- Nitro-08. Every coin that entered the adjudicator is held for a channel
    or was paid out to a participant. -/
theorem balances_total_split (b : Balances) :
    b.total = b.channelTotal + b.paidOutTotal := by
  sorry

/-- Nitro-04, Nitro-05, ForceMove-C01, docs-0060-03, docs-0060-04,
    docs-0060-05. go-nitro MultiAssetHolder.sol:57-60: `held += amount`;
    Nitro:165-168: the deposit raises the balance by `x` and brings `x` coins
    into the adjudicator. It touches nothing else. A second deposit adds to
    the first. -/
theorem deposit_effects (s : Adjudicator) (c : FixedPart) (x : Coins) (s' : Adjudicator)
    (h : s.deposit c.address x = some s') :
    s'.balances.get c.address = s.balances.get c.address + x ∧
    s'.held = s.held + x ∧
    (∀ b, b ≠ c.address → s'.balances.get b = s.balances.get b) ∧
    s'.status = s.status ∧ s'.now = s.now := by
  sorry

/-- Nitro-04, docs-0060-01. Nitro:166-167: "There are no restrictions on who
    can deposit coins for an address". go-nitro MultiAssetHolder.sol:43: a
    deposit to an external destination reverts, so the address must be a
    channel; the code is followed. The deposit succeeds for every caller
    and every channel. -/
theorem deposit_can_happen (apps : Apps) (caller : Participant) (s : Adjudicator) (c : FixedPart)
    (x : Coins) :
    s.apply apps caller (.deposit c.address x) =
      some { s with balances := s.balances.add c.address x, held := s.held + x } := by
  sorry

/-- docs-0060-01, Nitro-04. go-nitro MultiAssetHolder.sol:43 "Deposit to
    external destination": a deposit to a participant address fails. -/
theorem deposit_to_participant_fails (s : Adjudicator) (p : Participant) (x : Coins) :
    s.deposit (.participant p) x = none := by
  sorry

/-- Nitro-06, Nitro-07, SATP-16. go-nitro MultiAssetHolder.sol:396-408: coins
    leave the contract only through `_executeSingleAssetExit`, which only
    `transfer` (and the batch helpers) call on a finalized outcome. Nitro
    :227-229: "funds can only be withdrawn from participant addresses - and
    only by a party who knows the private key"; go-nitro has no withdrawal
    operation: the payout goes to the participant's address itself. A fall
    of the coins held comes from a redistribution of a finalized channel. -/
theorem held_falls_only_by_payout (apps : Apps) (s s' : Adjudicator) (caller : Participant)
    (op : Op) (h : s.apply apps caller op = some s') (hlt : s'.held < s.held) :
    op.isRedistribution = true ∧
    ∃ p, s'.balances.get (.participant p) = s.balances.get (.participant p) + (s.held - s'.held) ∧
      ∀ q, q ≠ p → s'.balances.get (.participant q) = s.balances.get (.participant q) := by
  sorry

/-- Nitro-07. Nitro:227-229: no operation takes a channel's coins except a
    redistribution. go-nitro: only `holdings[asset][channelId] -=
    totalPayouts` (MultiAssetHolder.sol:203) lowers a holding. -/
theorem channel_balance_falls_only_by_redistribution (apps : Apps) (s s' : Adjudicator)
    (caller : Participant) (op : Op) (h : s.apply apps caller op = some s') (c : FixedPart)
    (hlt : s'.balances.get c.address < s.balances.get c.address) :
    op.isRedistribution = true := by
  sorry

/-- Nitro-06. A participant's paid-out balance never falls: go-nitro has no
    operation that takes coins back from an external destination. -/
theorem paid_out_monotone (apps : Apps) (s s' : Adjudicator) (h : Step apps s s')
    (p : Participant) :
    s.balances.get (.participant p) ≤ s'.balances.get (.participant p) := by
  sorry

/-- ForceMove-A16, ForceMove-B07, Nitro-26, SATP-12, docs-0080-03. go-nitro
    MultiAssetHolder.sol:162-191: entry `k` is paid `min(amount, surplus)`
    where `surplus` is the coins held minus what the earlier entries took.
    ForceMove:1837-1853: `min(owed_k, balance − pending)`; Nitro:747-749:
    "the addresses at the beginning of the allocation will receive funds
    first." -/
theorem payout_priority_formula (held : Coins) (o : Allocation) (k : Nat) (e : Entry)
    (h : o[k]? = some e) :
    (o.payout held)[k]? = some (e.dest, min e.amount (held - Allocation.total (o.take k))) := by
  sorry

/-- ForceMove-B07, Nitro-26, docs-0060-06. ForceMove:1812-1821: "paying out
    Alice first, allowing her to recover her funds even if Bob does not
    deposit." If a later entry receives anything, every earlier entry
    received its full amount. -/
theorem payout_earlier_paid_in_full (held : Coins) (o : Allocation) (i j : Nat)
    (ei ej : Entry) (pi pj : Coins) (hi : o[i]? = some ei) (hj : o[j]? = some ej) (hij : i < j)
    (hpi : (o.payout held)[i]? = some (ei.dest, pi))
    (hpj : (o.payout held)[j]? = some (ej.dest, pj)) (hpos : 0 < pj) :
    pi = ei.amount := by
  sorry

/-- Nitro-26, Nitro-28, docs-0080-03. The payout never exceeds the coins
    held, and never pays an entry more than its amount. -/
theorem payout_bounded (held : Coins) (o : Allocation) :
    ((o.payout held).map (·.2)).sum ≤ held ∧
    ∀ (i : Nat) (e : Entry) (x : Coins), o[i]? = some e → (o.payout held)[i]? = some (e.dest, x) →
      x ≤ e.amount := by
  sorry

/-- Nitro-25. Nitro:744-746: "ignoring any additional entries for a given
    address after the first." A destination receives at most the amount of
    its first entry. -/
theorem paidTo_first_entry_only (held : Coins) (o : Allocation) (d : Address) :
    o.paidTo held d ≤ o.owed d := by
  sorry

/-- Nitro-27, Nitro-16. Nitro:749-751: a channel that holds the whole total
    of its allocation affords every entry in full. -/
theorem affords_when_fully_funded (held : Coins) (o : Allocation) (d : Address)
    (h : o.total ≤ held) : o.Affords held d (o.owed d) := by
  sorry

/-- Nitro-28, Nitro-10, ForceMove-A15, docs-0080-03, docs-0080-04,
    docs-0030-03. go-nitro MultiAssetHolder.sol:72-100, 162-191, 203: the
    transfer pays the selected destination the affordable amount `x`, lowers
    the channel's holding by `x`, and lowers the entry by `x`. Nitro:765-770:
    the three effects of `T(A, B, x)`. A channel destination's balance
    rises by `x`; a participant destination receives `x` out of the
    contract. -/
theorem transfer_effects (s : Adjudicator) (a : FixedPart) (b : Address) (s' : Adjudicator)
    (h : s.transfer a b = some s') :
    ∃ o x, s.finalOutcome a.address = some (.allocation o) ∧
      x = o.paidTo (s.balances.get a.address) b ∧
      s'.balances.get a.address + x = s.balances.get a.address + (if b = a.address then x else 0) ∧
      (b ≠ a.address → s'.balances.get b = s.balances.get b + x) ∧
      (∀ d, d ≠ a.address → d ≠ b → s'.balances.get d = s.balances.get d) ∧
      s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) ∧
      s'.held + (if b.isParticipant then x else 0) = s.held ∧ s'.now = s.now := by
  sorry

/-- Nitro-28. The reduction of an owed amount is exact. -/
theorem reduceOwed_owed (o : Allocation) (d : Address) (x : Coins) :
    (o.reduceOwed d x).owed d = o.owed d - x ∧
    ∀ d', d' ≠ d → (o.reduceOwed d x).owed d' = o.owed d' := by
  sorry

/-- Nitro-28, Nitro-15, ForceMove-C03, docs-0080-06. go-nitro: a transfer on
    a finalized channel with an allocation entry for `b` succeeds, and pays
    the whole affordable amount (MultiAssetHolder.sol:66). The exact result
    is stated. -/
theorem transfer_can_happen (s : Adjudicator) (a : FixedPart) (b : Address) (o : Allocation)
    (amt : Coins) (hf : s.finalOutcome a.address = some (.allocation o))
    (hb : o.find b = some ⟨b, .alloc amt⟩) :
    ∃ s', s.transfer a b = some s' ∧
      s'.balances.get b = s.balances.get b +
        (if b = a.address then 0 else o.paidTo (s.balances.get a.address) b) := by
  sorry

/-- Nitro-29, ForceMove-A20, docs-0030-04. Nitro:771-772: "If A cannot afford
    x for B, then T(A, B, x) fails, leaving the on-chain state unchanged."
    go-nitro: the transfer pays what is affordable; it reverts when the
    channel is not finalized, when `b` has no entry, or when the entry is a
    guarantee ("cannot transfer a guarantee", MultiAssetHolder.sol:172). -/
theorem transfer_fails_otherwise (s : Adjudicator) (a : FixedPart) (b : Address)
    (h : ∀ o, s.finalOutcome a.address = some (.allocation o) →
      ∀ amt, o.find b ≠ some ⟨b, .alloc amt⟩) :
    s.transfer a b = none := by
  sorry

/-- Nitro-29. When `a` affords nothing for `b`, the transfer moves no coins. -/
theorem transfer_zero_moves_nothing (s : Adjudicator) (a : FixedPart) (b : Address)
    (s' : Adjudicator) (h : s.transfer a b = some s')
    (h0 : ∀ o, s.finalOutcome a.address = some (.allocation o) →
      o.paidTo (s.balances.get a.address) b = 0) :
    s'.balances = s.balances ∧ s'.held = s.held := by
  sorry

/-- Nitro-10, ForceMove-A15, SATP-16, docs-0080-01. go-nitro
    `_requireChannelFinalized` (MultiAssetHolder.sol:127); Nitro:261-266:
    redistribution reads a finalized outcome; ForceMove:1725-1728. A transfer
    succeeds only on a finalized channel. -/
theorem transfer_requires_finalized (s : Adjudicator) (a : FixedPart) (b : Address)
    (s' : Adjudicator) (h : s.transfer a b = some s') : s.mode a = .finalized := by
  sorry

/-- Nitro-15. Nitro:312-313: "There is no restriction on who can trigger the
    operations." go-nitro `transfer` and `reclaim` read no caller. A
    redistribution gives the same result for every caller. -/
theorem redistribution_ignores_caller (apps : Apps) (s : Adjudicator) (op : Op)
    (c1 c2 : Participant) (h : op.isRedistribution = true) :
    s.apply apps c1 op = s.apply apps c2 op := by
  sorry

/-- Nitro-08. A redistribution moves coins between balances. The sum of all
    balances (held plus paid out) is unchanged. -/
theorem redistribution_conserves_total (apps : Apps) (s s' : Adjudicator) (caller : Participant)
    (op : Op) (hop : op.isRedistribution = true) (h : s.apply apps caller op = some s') :
    s'.balances.total = s.balances.total ∧
    s'.held + s'.balances.paidOutTotal = s.held + s.balances.paidOutTotal := by
  sorry

/-- The outcomes a finalized outcome can become through redistribution:
    Nitro:770 (transfer), SATP:358-361 and go-nitro
    `compute_reclaim_effects` (reclaim on the ledger). -/
inductive Redistributed : Outcome → Outcome → Prop
  | refl (Ω : Outcome) : Redistributed Ω Ω
  | reduce {o : Allocation} (d : Address) (x : Coins) (Ω : Outcome) :
      Redistributed Ω (.allocation o) → Redistributed Ω (.allocation (o.reduceOwed d x))
  | reclaim {o : Allocation} (left right v : Address) (x y : Coins) (Ω : Outcome) :
      Redistributed Ω (.allocation o) →
      Redistributed Ω (.allocation (((o.addTo left x).addTo right y).remove v))

/-- Nitro-11, ForceMove-B03, SATP-16, docs-0070-04, ForceMove-A14.
    SATP:284-292: assets are released on explicit consent (conclude) or
    after a challenge timeout; Nitro:288-290: "There are two ways for an
    outcome to become finalized: (i) through a challenge that times out
    before anyone responds, and (ii) through the registration of a conclusion
    proof." go-nitro: only `challenge` and `_conclude` write a nonzero
    finalization time. A finalized outcome traces to one such step, and has only
    been redistributed since. -/
theorem finalized_two_ways (apps : Apps) (s : Adjudicator) (c : FixedPart) (Ω : Outcome)
    (hr : Reachable apps s) (hf : s.finalOutcome c.address = some Ω) :
    ∃ s0 s1 caller, Reachable apps s0 ∧
      ((∃ ss, s0.apply apps caller (.conclude c ss) = some s1 ∧ ConclusionProof c ss ∧
          Redistributed ss.state.outcome Ω) ∨
       (∃ proof candidate, s0.apply apps caller (.challenge c proof candidate) = some s1 ∧
          s0.now + c.challengeDuration ≤ s.now ∧ Redistributed candidate.outcome Ω)) := by
  sorry

/-- Nitro-14, ForceMove-A14, ForceMove-D12. Nitro:301-302: "the rules of
    operation only allow one outcome to be finalized for each channel."
    go-nitro: every status write in `challenge`, `checkpoint` and
    `_conclude` is guarded by a not-finalized check. Once finalized, a
    channel stays finalized. -/
theorem finalized_permanent (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (h : Step apps s s') (hf : s.mode c = .finalized) : s'.mode c = .finalized := by
  sorry

/-- Nitro-14. A finalized outcome is never replaced by a second
    finalization. Every later outcome of the channel is a redistribution of
    the first. -/
theorem finalized_outcome_only_redistributed (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (Ω : Outcome) (h : Step apps s s') (hf : s.finalOutcome c.address = some Ω) :
    ∃ Ω', s'.finalOutcome c.address = some Ω' ∧ Redistributed Ω Ω' := by
  sorry

/-- ForceMove-A10, ForceMove-A21, SATP-14, docs-0070-02, docs-0070-03.
    go-nitro ForceMove.sol:46-60: in Open mode the turn must not decrease,
    in Challenge mode it must increase, in Finalized mode the call reverts;
    the app must support the candidate; the challenger must be a
    participant. SATP:303-305 (`isOpen`, `version >=`) is corrected by the
    strict check in Challenge mode. ForceMove:1340-1354 forbids a challenge
    while one runs; the code allows one at a higher turn. -/
theorem challenge_requires (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (s' : Adjudicator)
    (h : s.challenge apps challenger c proof candidate = some s') :
    challenger ∈ c.participants ∧
    (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
    ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
     (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum)) := by
  sorry

/-- SATP-14. go-nitro ForceMove.sol:52-54 and SATP:303: a challenge on a
    finalized channel fails. -/
theorem challenge_fails_when_finalized (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (hf : s.mode c = .finalized) :
    s.challenge apps challenger c proof candidate = none := by
  sorry

/-- SATP-14. go-nitro ForceMove.sol:48-50 `_requireIncreasedTurnNumber`: a
    re-challenge at an equal turn during a running challenge fails. SATP
    Listing 1 would accept it and reset the deadline; the code is followed. -/
theorem rechallenge_equal_turn_fails (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (hm : s.mode c = .challenge)
    (ht : candidate.turnNum ≤ (s.statusOf c).turnNumRecord) :
    s.challenge apps challenger c proof candidate = none := by
  sorry

/-- ForceMove-A10, ForceMove-C02, ForceMove-F03, Nitro-12, SATP-14,
    docs-0070-08. go-nitro ForceMove.sol:70-76: the status becomes the
    candidate's turn with deadline `block.timestamp + challengeDuration`;
    SATP:308-310; ForceMove:1353. The exact result. -/
theorem challenge_can_happen (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State)
    (hp : challenger ∈ c.participants)
    (hs : (apps c.appDef).supports c proof candidate = true) (hc : candidate.channel = c)
    (ht : (s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
      (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum)) :
    s.challenge apps challenger c proof candidate = some
      (s.setStatus c (.challenged candidate.turnNum ⟨candidate, s.now + c.challengeDuration⟩)) := by
  sorry

/-- ForceMove-D12, ForceMove-B04, SATP-14. A fresh challenge with a positive
    duration puts the channel in challenge mode. Balances, coins held and
    the clock do not move. -/
theorem challenge_effects (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (s' : Adjudicator)
    (h : s.challenge apps challenger c proof candidate = some s') (hd : 0 < c.challengeDuration) :
    s'.mode c = .challenge ∧ s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now ∧
    ∀ c', c' ≠ c → s'.statusOf c' = s.statusOf c' := by
  sorry

/-- ForceMove-A11, ForceMove-A12, ForceMove-A13, ForceMove-B02, ForceMove-A21,
    docs-0070-10. go-nitro ForceMove.sol:91-100 `checkpoint`: the channel is
    not finalized, the turn is strictly higher than the record, the app
    supports the candidate. ForceMove:1431-1440 `respondWithMove` and
    ForceMove:1377-1381 ("each of these responses lead to an increase in the
    turnNum") are superseded by it; SATP has no such operation. -/
theorem checkpoint_requires (apps : Apps) (s : Adjudicator) (c : FixedPart) (proof : SupportProof)
    (candidate : State) (s' : Adjudicator) (h : s.checkpoint apps c proof candidate = some s') :
    s.mode c ≠ .finalized ∧ (apps c.appDef).supports c proof candidate = true ∧
    candidate.channel = c ∧ (s.statusOf c).turnNumRecord < candidate.turnNum := by
  sorry

/-- ForceMove-A18, ForceMove-B04, ForceMove-A21, docs-0070-10. go-nitro
    ForceMove.sol:104-113: the status becomes Open at the candidate's turn
    and a running challenge is cleared (`ChallengeCleared`).
    ForceMove:1266-1269: "If a valid response is received, the game returns
    to the Collaborative mode"; ForceMove:1765-1770 `cancelChallenge`. -/
theorem checkpoint_can_happen (apps : Apps) (s : Adjudicator) (c : FixedPart)
    (proof : SupportProof) (candidate : State) (hm : s.mode c ≠ .finalized)
    (hs : (apps c.appDef).supports c proof candidate = true) (hc : candidate.channel = c)
    (ht : (s.statusOf c).turnNumRecord < candidate.turnNum) :
    s.checkpoint apps c proof candidate = some (s.setStatus c (.open candidate.turnNum)) ∧
    (s.setStatus c (.open candidate.turnNum)).mode c = .open := by
  sorry

/-- ForceMove-B02, ForceMove-A21, docs-0070-03, docs-0040-03. go-nitro
    `_requireNonDecreasedTurnNumber` and `_requireIncreasedTurnNumber`
    (ForceMove.sol); ForceMove:1543-1545: "Only allow new force-moves if
    their response will increase this stored turnNum." No step lowers the
    stored turn number of a channel. (go-nitro's reset to 0 on conclude is
    not modelled; see `Adjudicator.conclude`.) -/
theorem turnNumRecord_monotone (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (h : Step apps s s') : (s.statusOf c).turnNumRecord ≤ (s'.statusOf c).turnNumRecord := by
  sorry

/-- ForceMove-A14, Nitro-13, SATP-16, docs-0070-01, docs-0010-05. go-nitro
    ForceMove.sol:142-152: a conclude needs a non-finalized channel, a final
    candidate and unanimous signatures; the application is not consulted.
    SATP:288-289: "supporting a state with isFinal = true";
    ForceMove:1495-1500. -/
theorem conclude_requires (s : Adjudicator) (c : FixedPart) (ss : SignedState) (s' : Adjudicator)
    (h : s.conclude c ss = some s') :
    s.mode c ≠ .finalized ∧ ss.state.channel = c ∧ ss.state.isFinal = true ∧ ss.ByAll := by
  sorry

/-- ForceMove-A09, Nitro-13, SATP-08, SATP-16, docs-0070-01, docs-0020-01.
    go-nitro ForceMove.sol:147-152 `'!unanimous'`; Nitro:297-298: "all the
    participants sign a special conclude state, called a conclusion proof".
    A conclude carries one state signed by every participant, for every
    application. -/
theorem conclude_needs_all (s : Adjudicator) (c : FixedPart) (ss : SignedState) (s' : Adjudicator)
    (h : s.conclude c ss = some s') (p : Participant) (hp : p ∈ c.participants) :
    p ∈ ss.signers := by
  sorry

/-- ForceMove-A14, Nitro-13, SATP-16, docs-0070-09. go-nitro
    ForceMove.sol:155-163: the channel finalizes at `block.timestamp` with
    the candidate's outcome; Nitro:299-300: "the participants avoid having
    to wait for the challenge period"; ForceMove:1507. The exact result. -/
theorem conclude_can_happen (s : Adjudicator) (c : FixedPart) (ss : SignedState)
    (hm : s.mode c ≠ .finalized) (hproof : ConclusionProof c ss) :
    s.conclude c ss = some (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome)) ∧
    (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome)).finalOutcome c.address =
      some ss.state.outcome ∧
    (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome)).mode c = .finalized := by
  sorry

/-- ForceMove-A04, ForceMove-A05, docs-0070-07. go-nitro `_conclude` writes
    only `statusOf`; ForceMove:976-980, 1017-1022: the conclude transition
    keeps the resolution. A conclude moves no coins. -/
theorem conclude_moves_no_value (s : Adjudicator) (c : FixedPart) (ss : SignedState)
    (s' : Adjudicator) (h : s.conclude c ss = some s') :
    s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now := by
  sorry

/-- ForceMove-B03, ForceMove-D12, Nitro-12, docs-0040-05, docs-0040-06.
    go-nitro StatusManager.sol:10-11: a finalization time at or before
    `block.timestamp` is Finalized; ForceMove:1260-1265: "If no response is received within the
    timeout period, the game transitions into the Terminated mode";
    ForceMove:449-453: "the resolution stored on the challenge state s will
    decide how the funds should be split." -/
theorem timeout_finalizes (s : Adjudicator) (c : FixedPart) (t : Nat) (ch : Challenge)
    (hs : s.statusOf c = .challenged t ch) (hd : ch.deadline ≤ s.now) :
    s.mode c = .finalized ∧ s.finalOutcome c.address = some ch.state.outcome := by
  sorry

/-- ForceMove-D12. go-nitro StatusManager.sol:12-13: a future finalization
    time is Challenge mode; ForceMove:1295 `inProgress: c ↦ c.endTime > now()`. -/
theorem challenge_in_progress_before_deadline (s : Adjudicator) (c : FixedPart) (t : Nat)
    (ch : Challenge) (hs : s.statusOf c = .challenged t ch) (hd : s.now < ch.deadline) :
    s.mode c = .challenge ∧ s.finalOutcome c.address = none := by
  sorry

/-- ForceMove-F03, docs-0040-05. docs: "a passive transition which happens
    when a block is produced with a sufficiently large timestamp." The clock
    changes no balance and no status. -/
theorem tick_moves_only_time (s : Adjudicator) (dt : Time) :
    (s.tick dt).balances = s.balances ∧ (s.tick dt).held = s.held ∧
    (s.tick dt).status = s.status ∧ (s.tick dt).now = s.now + dt := by
  sorry

/-- ForceMove-A20. go-nitro: a failed `require` reverts the transaction;
    ForceMove:685-686: "making an invalid move is equivalent to not making
    any move at all." A failed operation leaves the chain unchanged. -/
theorem failed_op_no_effect (apps : Apps) (caller : Participant) (op : Op) (s : Adjudicator)
    (h : s.apply apps caller op = none) :
    Adjudicator.applyAll apps [(caller, op)] s = s := by
  sorry

/-- ForceMove-F05. go-nitro ForceMove.sol reads no `holdings`;
    ForceMove:1609-1628: "there is no way of telling from the properties of
    the channel how (or even whether) the game is funded." The dispute
    operations read no balance: their success and their status result do
    not depend on the balances. -/
theorem funding_decoupled_from_rules (apps : Apps) (caller : Participant) (s : Adjudicator)
    (b : Balances) (op : Op) (hop : op.isRedistribution = false ∧ ∀ a x, op ≠ .deposit a x) :
    ((s.apply apps caller op).map Adjudicator.status) =
      (({ s with balances := b }.apply apps caller op).map Adjudicator.status) := by
  sorry

/-- ForceMove-A01, ForceMove-A02, ForceMove-A03, ForceMove-D05, ForceMove-D06,
    ForceMove-D04 (ForceMove only; go-nitro StrictTurnTaking.sol is the same
    rule as a library). ForceMove:744-751 `validMove`: a valid transition
    whose signer is the mover; ForceMove:761-778: the channel is fixed and
    the turn number increments by one. Under the ForceMove rules a supported
    candidate ends a run of `n` such moves. -/
theorem forceMove_supports_valid_run (vt : State → State → Bool) (c : FixedPart)
    (proof : SupportProof) (candidate : State)
    (h : (forceMoveRules vt).supports c proof candidate = true) :
    proof.length = c.n ∧
    (∀ (i : Nat) m1 m2, proof[i]? = some m1 → proof[i + 1]? = some m2 →
      m2.state.channel = m1.state.channel ∧ m2.state.turnNum = m1.state.turnNum + 1 ∧
      m2.ByMover ∧ (m2.state.isFinal = false → vt m1.state m2.state = true)) ∧
    (∃ m, proof.getLast? = some m ∧ m.state = candidate) := by
  sorry

/-- ForceMove-A04, ForceMove-A05, ForceMove-A08 (ForceMove only).
    ForceMove:976-980: GAME→CONCLUDE needs the resolution unchanged;
    ForceMove:1017-1022: from CONCLUDE only CONCLUDE with the same
    resolution; ForceMove:1203-1208: backing out keeps the resolution. -/
theorem forceMove_conclude_keeps_outcome (vt : State → State → Bool) (c : FixedPart)
    (proof : SupportProof) (candidate : State)
    (h : (forceMoveRules vt).supports c proof candidate = true) (i : Nat) (m1 m2 : SignedState)
    (h1 : proof[i]? = some m1) (h2 : proof[i + 1]? = some m2) :
    (m2.state.isFinal = true → m2.state.outcome = m1.state.outcome) ∧
    (m1.state.isFinal = true → m2.state.isFinal = true) := by
  sorry

/-- ForceMove-D05, ForceMove-D06 (ForceMove only). ForceMove:724-727: "the
    mover is fully determined by the turn number". -/
theorem mover_determined_by_turn (s t : State) (hc : s.channel = t.channel)
    (ht : s.turnNum = t.turnNum) : s.mover = t.mover := by
  sorry

/-- ForceMove-D06 (ForceMove only). ForceMove:725-727: "players must take
    turns in a cyclical order." The mover of turn `k + n` is the mover of
    turn `k`. -/
theorem mover_cyclic (s : State) (k : Nat) :
    { s with turnNum := k + s.channel.n }.mover = { s with turnNum := k }.mover := by
  sorry

/-- SATP-15, docs-0030-04. SATP:348-352 and go-nitro
    MultiAssetHolder.sol:262-300: a reclaim needs both channels finalized
    and a guarantee entry for the target in the ledger's outcome. go-nitro
    adds: `left` and `right` have entries in the ledger (lines 363-364) and
    the target's first two amounts sum to the guarantee amount (line 365). -/
theorem reclaim_requires (s : Adjudicator) (l v : FixedPart) (s' : Adjudicator)
    (h : s.reclaim l v = some s') :
    s.mode l = .finalized ∧ s.mode v = .finalized ∧
    ∃ oL oV x left right, s.finalOutcome l.address = some (.allocation oL) ∧
      s.finalOutcome v.address = some (.allocation oV) ∧
      oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧
      (oL.remove v.address).find left ≠ none ∧ (oL.remove v.address).find right ≠ none ∧
      oV.amountAt 0 + oV.amountAt 1 = x := by
  sorry

/-- SATP-15, docs-0080-05. SATP:358-363 and go-nitro
    `compute_reclaim_effects`: `o_ledger[left] += o_target[0]`,
    `o_ledger[right] += o_target[1]`, the guarantee entry is deleted. The
    balances do not move. The total of the ledger outcome is unchanged
    (go-nitro line 365: `totalReclaimed == guarantee.amount`). -/
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
      oL'.total = oL.total ∧
      s'.balances = s.balances ∧ s'.held = s.held ∧
      s'.finalOutcome v.address = s.finalOutcome v.address := by
  sorry

/-- SATP-15, docs-0080-05. The reclaim succeeds whenever its preconditions
    hold. The exact result is stated. -/
theorem reclaim_can_happen (s : Adjudicator) (l v : FixedPart) (oL oV : Allocation) (x : Coins)
    (left right : Address) (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalOutcome v.address = some (.allocation oV))
    (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩)
    (hl : (oL.remove v.address).find left ≠ none) (hr : (oL.remove v.address).find right ≠ none)
    (hx : oV.amountAt 0 + oV.amountAt 1 = x) :
    s.reclaim l v = some (s.setStatus l ((s.statusOf l).withOutcome
      (.allocation ((((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1))).remove
        v.address)))) := by
  sorry

/-- SATP-15. go-nitro MultiAssetHolder.sol:363-365: a reclaim whose `left`
    or `right` has no ledger entry, or whose target amounts do not sum to
    the guarantee amount, fails. SATP Listing 2 has no such checks; the code
    is followed. -/
theorem reclaim_fails_without_entries (s : Adjudicator) (l v : FixedPart) (oL oV : Allocation)
    (x : Coins) (left right : Address) (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalOutcome v.address = some (.allocation oV))
    (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩)
    (hbad : (oL.remove v.address).find left = none ∨ (oL.remove v.address).find right = none ∨
      oV.amountAt 0 + oV.amountAt 1 ≠ x) :
    s.reclaim l v = none := by
  sorry

/-- SATP-13, docs-0040-02. SATP:294-298 `isOpen`: "the channel has no active
    challenge or the channel has not yet finalized"; go-nitro
    StatusManager.sol:5-14. -/
theorem isOpen_iff (st : ChannelStatus) (now : Time) :
    st.IsOpen now ↔ (st.mode now = .open ∨ st.mode now = .challenge) := by
  sorry

/-- ForceMove-D11, Nitro-11. Every channel is in exactly one mode. A channel
    with no record is open (go-nitro: an empty status unpacks to a zero
    finalization time). -/
theorem mode_of_absent (s : Adjudicator) (c : FixedPart) (h : ∀ e ∈ s.status, e.1 ≠ c) :
    s.mode c = .open ∧ (s.statusOf c).turnNumRecord = 0 := by
  sorry

/-- Nitro-08, Nitro-05. Only a deposit raises the coins held and only a
    payout to a participant lowers them. -/
theorem held_changes_only_by_deposit_payout (apps : Apps) (s s' : Adjudicator)
    (caller : Participant) (op : Op) (h : s.apply apps caller op = some s')
    (hne : s'.held ≠ s.held) :
    (∃ a x, op = .deposit a x) ∨ op.isRedistribution = true := by
  sorry

end ArmadaLean.Nitro
