/-
  Nitro protocol theorems: on-chain adjudicator safety, conservation and the
  correctness of the data operations. The proofs use the `@[simp]` API and
  the invariant `Adjudicator.HeldInv` of `Lemmas.lean`. The statements
  are the deliverable. Each doc comment cites the latest source first (SATP,
  then Nitro, then ForceMove), then go-nitro, and names the property ids of
  `docs/nitro-theorems.md`.
-/
import ArmadaLean.Nitro.SATP
import ArmadaLean.Nitro.Lemmas

namespace ArmadaLean.Nitro

/-- ForceMove-D02, Nitro-02, Nitro-03, SATP-05, docs-0010-02, ForceMove-F01.
    SATP:213-215: the id is computed from the constants and the nonce makes
    channels distinct; Nitro:158-160: impossible "to construct a channel
    whose address is A"; go-nitro NitroUtils.sol:122-133. Two fixed parts
    with one address are one channel. -/
theorem channel_address_inj (c c' : FixedPart) (h : c.address = c'.address) : c = c' := by
  simpa using h

/-- ForceMove-D02, Nitro-02. go-nitro `_isExternalDestination`: a channel
    id is never an external address, so a channel's funds cannot be read as
    a participant's. -/
theorem channel_address_ne_participant (c : FixedPart) (p : Participant) :
    c.address ≠ .participant p := by
  simp

/-- Nitro-01. Nitro:162-163: "If an address does not appear in the table we
    take the balance to be zero." go-nitro: an unset `holdings` entry reads
    as 0. -/
theorem balances_absent_zero (b : Balances) (a : Address) (h : ∀ e ∈ b, e.1 ≠ a) :
    b.get a = 0 := by
  exact Balances.get_of_forall_ne h

/-- Nitro-08, Nitro-05, ForceMove-F04, docs-C-01. Nitro:230-231: "The total
    coins held by the smart contract should always equal the sum of the
    balances." go-nitro: `holdings` is per channel, and a payout to an
    external destination leaves the contract (MultiAssetHolder.sol:401-402),
    so the coins held equal the sum of the channel balances. -/
theorem held_eq_channel_balances (apps : Apps) (s : Adjudicator) (h : Reachable apps s) :
    s.held = s.balances.channelTotal := by
  exact (Adjudicator.heldInv_reachable h).2

/-- Nitro-08. Every coin that entered the adjudicator is held for a channel
    or was paid out to a participant. -/
theorem balances_total_split (b : Balances) :
    b.total = b.channelTotal + b.paidOutTotal := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k, w⟩ := e
    rw [Balances.total_eq_sumIf, Balances.channelTotal_eq_sumIf,
      Balances.paidOutTotal_eq_sumIf] at ih ⊢
    simp only [Balances.sumIf_cons]
    cases k <;> simp <;> grind

/-- Nitro-04, Nitro-05, ForceMove-C01, docs-0060-02, docs-0060-03,
    docs-0060-04, docs-0060-05. go-nitro MultiAssetHolder.sol:51, 57-60:
    `held == expectedHeld`, then `held += amount`; Nitro:165-168: the
    deposit raises the balance by `x` and brings `x` coins into the
    adjudicator. It touches nothing else. A second deposit adds to the
    first. -/
theorem deposit_effects (s : Adjudicator) (c : FixedPart) (e x : Coins) (s' : Adjudicator)
    (h : s.deposit c.address e x = some s') :
    s.balances.get c.address = e ∧
    s'.balances.get c.address = e + x ∧
    s'.held = s.held + x ∧
    (∀ b, b ≠ c.address → s'.balances.get b = s.balances.get b) ∧
    s'.status = s.status ∧ s'.now = s.now := by
  obtain ⟨-, he, hb, hh, hs, hn⟩ := Adjudicator.deposit_some h
  refine ⟨he, ?_, hh, fun b hb' => ?_, hs, hn⟩
  · rw [hb]; simp at he ⊢; rw [he]
  · rw [hb]; simp at hb' ⊢; simp [hb']

/-- Nitro-04, docs-0060-01. Nitro:166-167: "There are no restrictions on who
    can deposit coins for an address". go-nitro MultiAssetHolder.sol:43: a
    deposit to an external destination reverts, so the address must be a
    channel; the code is followed. The deposit succeeds for every caller
    and every channel. -/
theorem deposit_can_happen (apps : Apps) (caller : Participant) (s : Adjudicator) (c : FixedPart)
    (x : Coins) :
    s.apply apps caller (.deposit c.address (s.balances.get c.address) x) =
      some { s with balances := s.balances.add c.address x, held := s.held + x } := by
  simp [Adjudicator.deposit]

/-- docs-0060-02. go-nitro MultiAssetHolder.sol:51 `require(held ==
    expectedHeld, 'held != expectedHeld')`: a deposit whose observation is
    stale fails. A history in which an earlier deposit was dropped or
    reordered is one such history. -/
theorem deposit_requires_expectedHeld (s : Adjudicator) (c : FixedPart) (e x : Coins)
    (h : s.balances.get c.address ≠ e) : s.deposit c.address e x = none := by
  simp at h
  simp [Adjudicator.deposit, h]

/-- The sum of the allocations ahead of entry `k`: the holding a funder in
    position `k` must see before it deposits (ForceMove:1197-1208,
    ForceMove:1797-1808; docs 0060: "participants should not deposit until
    those with higher priority have had their deposits confirmed"). -/
def Allocation.aheadOf (o : Allocation) (k : Nat) : Coins :=
  Allocation.total (o.take k)

/-- docs-0060-02, ForceMove-B07, docs-0060-06. The funding-order theorem,
    over every history. If the funder of entry `k` of the pre-funding
    outcome `o` deposits with `expectedHeld = o.aheadOf k` and the deposit
    succeeds, then the channel held exactly the allocations ahead of `k`
    before, and holds them plus `x` after; so the priority payout
    (Nitro:747-749) pays every entry ahead of `k` in full from the coins
    already there, pays the funder's own entry from the funder's coins, and
    the deposit is paid to no entry ahead of it. A reorganization that
    dropped an earlier deposit makes the guard fail
    (`deposit_requires_expectedHeld`); it is not a separate case. -/
theorem deposit_respects_funding_order (apps : Apps) (s s' : Adjudicator) (hr : Reachable apps s)
    (caller : Participant) (c : FixedPart) (o : Allocation) (hdedup : o.dedup = o) (k : Nat)
    (e : Entry) (he : o[k]? = some e)
    (h : s.apply apps caller (.deposit c.address (o.aheadOf k) e.amount) = some s') :
    s.balances.get c.address = o.aheadOf k ∧
    s'.balances.get c.address = o.aheadOf k + e.amount ∧
    (∀ j f, j < k → o[j]? = some f →
      o.paidTo (s.balances.get c.address) f.dest = f.amount ∧
      o.paidTo (s'.balances.get c.address) f.dest = f.amount) ∧
    o.paidTo (s'.balances.get c.address) e.dest = e.amount ∧
    (∀ j f, k < j → o[j]? = some f → o.paidTo (s'.balances.get c.address) f.dest = 0) := by
  simp only [Adjudicator.apply_deposit] at h
  obtain ⟨-, he0, hb, -, -, -⟩ := Adjudicator.deposit_some h
  have hs' : s'.balances.get c.address = o.aheadOf k + e.amount := by
    rw [hb]; simp at he0 ⊢; rw [he0]
  have hk := Allocation.total_take_succ he
  unfold Allocation.aheadOf at he0 hs' ⊢
  refine ⟨he0, hs', fun j f hj hf => ?_, ?_, fun j f hj hf => ?_⟩
  · have h1 := Allocation.total_take_succ hf
    have h2 := Allocation.total_take_mono o (show j + 1 ≤ k by omega)
    rw [he0, hs', Allocation.paidTo_of_getElem? hdedup hf, Allocation.paidTo_of_getElem? hdedup hf]
    grind
  · rw [hs', Allocation.paidTo_of_getElem? hdedup he]
    grind
  · have h2 := Allocation.total_take_mono o (show k + 1 ≤ j by omega)
    rw [hs', Allocation.paidTo_of_getElem? hdedup hf]
    grind

/-- ForceMove-C01, docs-0060-02. Deposits made in the order of the
    pre-funding outcome, each with `expectedHeld` equal to the allocations
    ahead of it, all succeed from a channel that holds nothing, and leave
    the channel fully funded (ForceMove:1797-1808). -/
theorem deposits_in_order_succeed (apps : Apps) (s : Adjudicator) (c : FixedPart) (o : Allocation)
    (callers : List Participant) (h0 : s.balances.get c.address = 0) :
    let op := fun k => ((callers[k]?).getD ⟨0⟩, Op.deposit c.address (o.aheadOf k) (o.amountAt k))
    let ops := (List.range o.length).map op
    (∀ k, k < o.length →
      (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k ∧
      (Adjudicator.applyAll apps (ops.take k) s).apply apps (op k).1 (op k).2 =
        some (Adjudicator.applyAll apps (ops.take (k + 1)) s)) ∧
    (Adjudicator.applyAll apps ops s).balances.get c.address = o.total := by
  intro op ops
  have hlen : ops.length = o.length := by simp [ops]
  have hops : ∀ k, k < o.length → ops[k]? = some (op k) := by
    intro k hk; simp [ops, hk]
  have hone : ∀ k, k < o.length →
      (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k →
      (Adjudicator.applyAll apps (ops.take k) s).apply apps (op k).1 (op k).2 =
          some (Adjudicator.applyAll apps (ops.take (k + 1)) s) ∧
        (Adjudicator.applyAll apps (ops.take (k + 1)) s).balances.get c.address =
          o.aheadOf (k + 1) := by
    intro k hk hb
    obtain ⟨e, he⟩ : ∃ e, o[k]? = some e := ⟨o[k], List.getElem?_eq_getElem hk⟩
    have hdep := deposit_can_happen apps (op k).1 (Adjudicator.applyAll apps (ops.take k) s) c
      (o.amountAt k)
    rw [hb] at hdep
    have happ : (Adjudicator.applyAll apps (ops.take k) s).apply apps (op k).1 (op k).2 =
        some { Adjudicator.applyAll apps (ops.take k) s with
          balances := (Adjudicator.applyAll apps (ops.take k) s).balances.add c.address (o.amountAt k),
          held := (Adjudicator.applyAll apps (ops.take k) s).held + o.amountAt k } := hdep
    rw [List.take_add_one, hops k hk, Option.toList_some, Adjudicator.applyAll_append,
      Adjudicator.applyAll_singleton_of_some happ]
    refine ⟨happ, ?_⟩
    simp only [Balances.get_add, if_true, hb, Allocation.aheadOf, Allocation.total_take_succ he,
      Allocation.amountAt, he, Option.map_some, Option.getD_some]
  have hall : ∀ k, k ≤ o.length →
      (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k := by
    intro k
    induction k with
    | zero => intro _; simpa [Allocation.aheadOf, Adjudicator.applyAll] using h0
    | succ k ih => intro hk; exact (hone k (by omega) (ih (by omega))).2
  refine ⟨fun k hk => ⟨hall k hk.le, (hone k hk (hall k hk.le)).1⟩, ?_⟩
  have := hall o.length le_rfl
  rw [List.take_of_length_le hlen.le] at this
  rw [this, Allocation.aheadOf, List.take_length]

/-- docs-0060-01, Nitro-04. go-nitro MultiAssetHolder.sol:43 "Deposit to
    external destination": a deposit to a participant address fails. -/
theorem deposit_to_participant_fails (s : Adjudicator) (p : Participant) (e x : Coins) :
    s.deposit (.participant p) e x = none := by
  rfl

/-- Nitro-06, Nitro-07, SATP-16. go-nitro MultiAssetHolder.sol:396-408: coins
    leave the contract only through `_executeSingleAssetExit`, which only
    `transfer` (and the batch helpers) call on a finalized outcome. Nitro
    :227-229: "funds can only be withdrawn from participant addresses - and
    only by a party who knows the private key"; go-nitro has no withdrawal
    operation: the payout goes to the participant's address itself. A fall
    of the coins held comes from a redistribution of a finalized channel.
    The hypothesis `hr` is from the operator ruling 2026-10-27 (counterexample
    in Counter.lean): on an unreachable state the coins held can be fewer
    than the payout. -/
theorem held_falls_only_by_payout (apps : Apps) (s s' : Adjudicator) (hr : Reachable apps s)
    (caller : Participant)
    (op : Op) (h : s.apply apps caller op = some s') (hlt : s'.held < s.held) :
    op.isRedistribution = true ∧
    ∃ p, s'.balances.get (.participant p) = s.balances.get (.participant p) + (s.held - s'.held) ∧
      ∀ q, q ≠ p → s'.balances.get (.participant q) = s.balances.get (.participant q) := by
  obtain ⟨-, hheld⟩ := Adjudicator.heldInv_reachable hr
  cases op with
  | transfer a b =>
    obtain ⟨o, _, x, -, -, hx, hb, hh, -, -⟩ := Adjudicator.transfer_some h
    have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
    have hle := Balances.get_le_sumIf (fun a => decide (a.isParticipant = false)) s.balances
      (a := a.address) (by simp)
    rw [← Balances.channelTotal_eq_sumIf, ← hheld] at hle
    cases b with
    | channel d => simp [hh] at hlt
    | participant p =>
      refine ⟨rfl, p, ?_, fun q hq => ?_⟩
      · rw [hb, hh]; simp; grind
      · rw [hb]; simp [hq]
  | deposit a e x => obtain ⟨-, -, -, hh, -, -⟩ := Adjudicator.deposit_some h; grind
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := Adjudicator.reclaim_some h; simp at hlt
  | challenge c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.challenge_some h; simp at hlt
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.checkpoint_some h; simp at hlt
  | conclude c ss => obtain ⟨_, rfl⟩ := Adjudicator.conclude_some h; simp at hlt
  | tick dt => simp at h; subst h; simp at hlt

/-- Nitro-07. Nitro:227-229: no operation takes a channel's coins except a
    redistribution. go-nitro: only `holdings[asset][channelId] -=
    totalPayouts` (MultiAssetHolder.sol:203) lowers a holding. -/
theorem channel_balance_falls_only_by_redistribution (apps : Apps) (s s' : Adjudicator)
    (caller : Participant) (op : Op) (h : s.apply apps caller op = some s') (c : FixedPart)
    (hlt : s'.balances.get c.address < s.balances.get c.address) :
    op.isRedistribution = true := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, hb, -, -, -⟩ := Adjudicator.deposit_some h
    rw [hb] at hlt; simp at hlt; split at hlt <;> grind
  | transfer a b => rfl
  | reclaim l v => rfl
  | challenge c' proof cand => obtain ⟨_, rfl⟩ := Adjudicator.challenge_some h; simp at hlt
  | checkpoint c' proof cand => obtain ⟨_, rfl⟩ := Adjudicator.checkpoint_some h; simp at hlt
  | conclude c' ss => obtain ⟨_, rfl⟩ := Adjudicator.conclude_some h; simp at hlt
  | tick dt => simp at h; subst h; simp at hlt

/-- Nitro-06. A participant's paid-out balance never falls: go-nitro has no
    operation that takes coins back from an external destination. -/
theorem paid_out_monotone (apps : Apps) (s s' : Adjudicator) (h : Step apps s s')
    (p : Participant) :
    s.balances.get (.participant p) ≤ s'.balances.get (.participant p) := by
  cases h with
  | mk caller op _ _ h =>
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c, rfl⟩, -, hb, -, -, -⟩ := Adjudicator.deposit_some h
    rw [hb]; simp
  | transfer a b =>
    obtain ⟨_, _, x, -, -, -, hb, -, -, -⟩ := Adjudicator.transfer_some h
    rw [hb]; simp; split <;> grind
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := Adjudicator.reclaim_some h; simp
  | challenge c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.challenge_some h; simp
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.checkpoint_some h; simp
  | conclude c ss => obtain ⟨_, rfl⟩ := Adjudicator.conclude_some h; simp
  | tick dt => simp at h; subst h; simp

/-- ForceMove-A16, ForceMove-B07, Nitro-26, SATP-12, docs-0080-03. go-nitro
    MultiAssetHolder.sol:162-191: entry `k` is paid `min(amount, surplus)`
    where `surplus` is the coins held minus what the earlier entries took.
    ForceMove:1837-1853: `min(owed_k, balance − pending)`; Nitro:747-749:
    "the addresses at the beginning of the allocation will receive funds
    first." -/
theorem payout_priority_formula (held : Coins) (o : Allocation) (k : Nat) (e : Entry)
    (h : o[k]? = some e) :
    (o.payout held)[k]? = some (e.dest, min e.amount (held - Allocation.total (o.take k))) := by
  exact Allocation.payout_getElem? h

/-- ForceMove-B07, Nitro-26, docs-0060-06. ForceMove:1812-1821: "paying out
    Alice first, allowing her to recover her funds even if Bob does not
    deposit." If a later entry receives anything, every earlier entry
    received its full amount. -/
theorem payout_earlier_paid_in_full (held : Coins) (o : Allocation) (i j : Nat)
    (ei ej : Entry) (pi pj : Coins) (hi : o[i]? = some ei) (hj : o[j]? = some ej) (hij : i < j)
    (hpi : (o.payout held)[i]? = some (ei.dest, pi))
    (hpj : (o.payout held)[j]? = some (ej.dest, pj)) (hpos : 0 < pj) :
    pi = ei.amount := by
  rw [Allocation.payout_getElem? hi] at hpi
  rw [Allocation.payout_getElem? hj] at hpj
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hpi hpj
  have h1 := Allocation.total_take_succ hi
  have h2 := Allocation.total_take_mono o (show i + 1 ≤ j by omega)
  grind

/-- Nitro-26, Nitro-28, docs-0080-03. The payout never exceeds the coins
    held, and never pays an entry more than its amount. -/
theorem payout_bounded (held : Coins) (o : Allocation) :
    ((o.payout held).map (·.2)).sum ≤ held ∧
    ∀ (i : Nat) (e : Entry) (x : Coins), o[i]? = some e → (o.payout held)[i]? = some (e.dest, x) →
      x ≤ e.amount := by
  refine ⟨Allocation.payout_sum_le held o, fun i e x hi hx => ?_⟩
  rw [Allocation.payout_getElem? hi] at hx
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hx
  grind

/-- Nitro-25. Nitro:744-746: "ignoring any additional entries for a given
    address after the first." A destination receives at most the amount of
    its first entry. -/
theorem paidTo_first_entry_only (held : Coins) (o : Allocation) (d : Address) :
    o.paidTo held d ≤ o.owed d := by
  rw [Allocation.paidTo_eq_get, ← Allocation.owed_dedup]
  exact Allocation.payout_get_le_owed _ _ _

/-- Nitro-27, Nitro-16. Nitro:749-751: a channel that holds the whole total
    of its allocation affords every entry in full. -/
theorem affords_when_fully_funded (held : Coins) (o : Allocation) (d : Address)
    (h : o.total ≤ held) : o.Affords held d (o.owed d) := by
  unfold Allocation.Affords
  rw [Allocation.paidTo_eq_get, ← Allocation.owed_dedup]
  exact Allocation.owed_le_payout_get
    ((Allocation.total_le_of_sublist (Allocation.dedup_sublist o)).trans h) d

/-- Nitro-28, Nitro-10, ForceMove-A15, docs-0080-03, docs-0080-04,
    docs-0030-03. go-nitro MultiAssetHolder.sol:72-100, 162-191, 203: the
    transfer pays the selected destination the affordable amount `x`, lowers
    the channel's holding by `x`, and lowers the entry by `x`. Nitro:765-770:
    the three effects of `T(A, B, x)`. A channel destination's balance
    rises by `x`; a participant destination receives `x` out of the
    contract. The hypothesis `hr` is from the operator ruling 2026-10-27
    (counterexample in Counter.lean): on an unreachable state the coins held
    can be fewer than the payout. -/
theorem transfer_effects (apps : Apps) (s : Adjudicator) (hr : Reachable apps s) (a : FixedPart)
    (b : Address) (s' : Adjudicator)
    (h : s.transfer a b = some s') :
    ∃ o x, s.finalOutcome a.address = some (.allocation o) ∧
      x = o.paidTo (s.balances.get a.address) b ∧
      s'.balances.get a.address + x = s.balances.get a.address + (if b = a.address then x else 0) ∧
      (b ≠ a.address → s'.balances.get b = s.balances.get b + x) ∧
      (∀ d, d ≠ a.address → d ≠ b → s'.balances.get d = s.balances.get d) ∧
      s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) ∧
      s'.held + (if b.isParticipant then x else 0) = s.held ∧ s'.now = s.now := by
  obtain ⟨hnd, hheld⟩ := Adjudicator.heldInv_reachable hr
  obtain ⟨o, _, x, hf, -, hx, hb, hh, hs, hn⟩ := Adjudicator.transfer_some h
  have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
  have hle := Balances.get_le_sumIf (fun a => decide (a.isParticipant = false)) s.balances
    (a := a.address) (by simp)
  rw [← Balances.channelTotal_eq_sumIf, ← hheld] at hle
  refine ⟨o, x, hf, hx, ?_, fun hba => ?_, fun d hda hdb => ?_, ?_, ?_, hn⟩
  · rw [hb]; simp at hxa ⊢; split <;> grind
  · rw [hb]; simp at hba ⊢; simp [hba]
  · rw [hb]; simp at hda ⊢; simp [hda, hdb]
  · simp [Adjudicator.statusOf_of_status hs, hn]
  · rw [hh]
    split
    · simp_all; grind
    · simp_all

/-- Nitro-28. The reduction of an owed amount is exact. -/
theorem reduceOwed_owed (o : Allocation) (d : Address) (x : Coins) :
    (o.reduceOwed d x).owed d = o.owed d - x ∧
    ∀ d', d' ≠ d → (o.reduceOwed d x).owed d' = o.owed d' := by
  refine ⟨by simp [Allocation.owed_reduceOwed], fun d' h => ?_⟩
  simp [Allocation.owed_reduceOwed, h]

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
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
  have ht : s.transfer a b = some ((((s.setStatus a ((s.statusOf a).withOutcome (.allocation
      (o.reduceOwed b (o.paidTo (s.balances.get a.address) b))))).payTo b
        (o.paidTo (s.balances.get a.address) b))) |> fun s' =>
        { s' with balances := s'.balances.sub a.address (o.paidTo (s.balances.get a.address) b) }) := by
    simp only [Adjudicator.transfer, FixedPart.address_eq, Adjudicator.finalOutcome_channel, hf, hb]
  refine ⟨_, ht, ?_⟩
  simp only [Balances.get_sub, Adjudicator.payTo_balances, Adjudicator.setStatus_balances,
    Balances.get_add, FixedPart.address_eq]
  by_cases hba : b = .channel a
  · subst hba; simp
  · simp [hba]

/-- Nitro-29, ForceMove-A20, docs-0030-04. Nitro:771-772: "If A cannot afford
    x for B, then T(A, B, x) fails, leaving the on-chain state unchanged."
    go-nitro: the transfer pays what is affordable; it reverts when the
    channel is not finalized, when `b` has no entry, or when the entry is a
    guarantee ("cannot transfer a guarantee", MultiAssetHolder.sol:172). -/
theorem transfer_fails_otherwise (s : Adjudicator) (a : FixedPart) (b : Address)
    (h : ∀ o, s.finalOutcome a.address = some (.allocation o) →
      ∀ amt, o.find b ≠ some ⟨b, .alloc amt⟩) :
    s.transfer a b = none := by
  cases ht : s.transfer a b with
  | none => rfl
  | some s' =>
    obtain ⟨o, amt, _, hf, hfind, -⟩ := Adjudicator.transfer_some ht
    exact absurd hfind (h o hf amt)

/-- Nitro-29. When `a` affords nothing for `b`, the transfer moves no coins.
    Every balance reads the same; the list itself can change (`add b 0`
    writes an entry). Operator ruling 2026-10-27 (counterexample in
    Counter.lean). -/
theorem transfer_zero_moves_nothing (s : Adjudicator) (a : FixedPart) (b : Address)
    (s' : Adjudicator) (h : s.transfer a b = some s')
    (h0 : ∀ o, s.finalOutcome a.address = some (.allocation o) →
      o.paidTo (s.balances.get a.address) b = 0) :
    (∀ d, s'.balances.get d = s.balances.get d) ∧ s'.held = s.held := by
  obtain ⟨o, _, x, hf, -, hx, hb, hh, -, -⟩ := Adjudicator.transfer_some h
  have hx0 : x = 0 := hx ▸ h0 o hf
  subst hx0
  refine ⟨fun d => ?_, by rw [hh]; simp⟩
  rw [hb]
  simp only [Balances.get_sub, Balances.get_add, Nat.sub_zero, Nat.add_zero]
  by_cases hd : d = a.address
  · subst hd; simp only [if_true]; split <;> simp_all
  · simp only [hd, if_false]; split <;> simp_all

/-- Nitro-10, ForceMove-A15, SATP-16, docs-0080-01. go-nitro
    `_requireChannelFinalized` (MultiAssetHolder.sol:127); Nitro:261-266:
    redistribution reads a finalized outcome; ForceMove:1725-1728. A transfer
    succeeds only on a finalized channel. -/
theorem transfer_requires_finalized (s : Adjudicator) (a : FixedPart) (b : Address)
    (s' : Adjudicator) (h : s.transfer a b = some s') : s.mode a = .finalized := by
  obtain ⟨o, -, -, hf, -⟩ := Adjudicator.transfer_some h
  rw [Adjudicator.mode_eq, ChannelStatus.mode_eq_finalized_iff]
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
  simp [hf]

/-- Nitro-15. Nitro:312-313: "There is no restriction on who can trigger the
    operations." go-nitro `transfer` and `reclaim` read no caller. A
    redistribution gives the same result for every caller. -/
theorem redistribution_ignores_caller (apps : Apps) (s : Adjudicator) (op : Op)
    (c1 c2 : Participant) (h : op.isRedistribution = true) :
    s.apply apps c1 op = s.apply apps c2 op := by
  cases op <;> first | rfl | simp [Op.isRedistribution] at h

/-- Nitro-08. A redistribution moves coins between balances. The sum of all
    balances (held plus paid out) is unchanged. The hypothesis `hr` is from
    the operator ruling 2026-10-27 (counterexample in Counter.lean): on an
    unreachable state an address can have two entries, or the coins held
    can be fewer than the payout. -/
theorem redistribution_conserves_total (apps : Apps) (s s' : Adjudicator) (hr : Reachable apps s)
    (caller : Participant)
    (op : Op) (hop : op.isRedistribution = true) (h : s.apply apps caller op = some s') :
    s'.balances.total = s.balances.total ∧
    s'.held + s'.balances.paidOutTotal = s.held + s.balances.paidOutTotal := by
  obtain ⟨hnd, hheld⟩ := Adjudicator.heldInv_reachable hr
  cases op with
  | transfer a b =>
    obtain ⟨o, _, x, -, -, hx, hb, hh, -, -⟩ := Adjudicator.transfer_some h
    have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
    have hle := Balances.get_le_sumIf (fun a => decide (a.isParticipant = false)) s.balances
      (a := a.address) (by simp)
    rw [← Balances.channelTotal_eq_sumIf, ← hheld] at hle
    have h1 := Balances.sumIf_add_sub (fun _ => true) hnd a.address b hxa
    have h2 := Balances.sumIf_add_sub (fun a => decide (a.isParticipant = true)) hnd a.address b hxa
    rw [Balances.total_eq_sumIf, Balances.total_eq_sumIf, Balances.paidOutTotal_eq_sumIf,
      Balances.paidOutTotal_eq_sumIf, hb, hh]
    cases b <;> simp at h1 h2 ⊢ <;> grind
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := Adjudicator.reclaim_some h; simp
  | _ => simp [Op.isRedistribution] at hop

/-- One redistribution of a finalized outcome: Nitro:770 (transfer),
    SATP:358-361 and go-nitro `compute_reclaim_effects` (reclaim on the
    ledger). -/
inductive RedistributeStep : Outcome → Outcome → Prop
  | reduce (o : Allocation) (d : Address) (x : Coins) :
      RedistributeStep (.allocation o) (.allocation (o.reduceOwed d x))
  | reclaim (o : Allocation) (left right v : Address) (x y : Coins) :
      RedistributeStep (.allocation o) (.allocation (((o.addTo left x).addTo right y).remove v))

/-- Zero or more redistributions (Mathlib `Relation.ReflTransGen`). -/
def Redistributed : Outcome → Outcome → Prop :=
  Relation.ReflTransGen RedistributeStep

/-- The conclusion of `finalized_two_ways` for a channel `c` and an outcome
    `Ω` at the state `s`: a conclude, or a challenge whose deadline is at or
    before `s.now`, followed by redistributions. -/
def FinalizedTwoWays (apps : Apps) (s : Adjudicator) (c : FixedPart) (Ω : Outcome) : Prop :=
  ∃ s0 s1 caller, Reachable apps s0 ∧
    ((∃ ss, s0.apply apps caller (.conclude c ss) = some s1 ∧ ConclusionProof c ss ∧
        Redistributed ss.state.outcome Ω) ∨
     (∃ proof candidate, s0.apply apps caller (.challenge c proof candidate) = some s1 ∧
        s0.now + c.challengeDuration ≤ s.now ∧ Redistributed candidate.outcome Ω))

theorem FinalizedTwoWays.mono {apps : Apps} {s s' : Adjudicator} {c : FixedPart} {Ω Ω' : Outcome}
    (h : FinalizedTwoWays apps s c Ω) (hn : s.now ≤ s'.now) (hR : Redistributed Ω Ω') :
    FinalizedTwoWays apps s' c Ω' := by
  obtain ⟨s0, s1, caller, hr0, ⟨ss, h1, h2, h3⟩ | ⟨proof, cand, h1, h2, h3⟩⟩ := h
  · exact ⟨s0, s1, caller, hr0, Or.inl ⟨ss, h1, h2, h3.trans hR⟩⟩
  · exact ⟨s0, s1, caller, hr0, Or.inr ⟨proof, cand, h1, by grind, h3.trans hR⟩⟩

/-- Nitro:288-290: the origin of a channel status. A running challenge came
    from a challenge step whose deadline it keeps; a finalized status
    satisfies `FinalizedTwoWays`. -/
def StatusOrigin (apps : Apps) (s : Adjudicator) (c : FixedPart) : Prop :=
  match s.statusOf c with
  | .open _ => True
  | .challenged _ ch => ∃ s0 s1 caller proof, Reachable apps s0 ∧
      s0.apply apps caller (.challenge c proof ch.state) = some s1 ∧
      s0.now + c.challengeDuration = ch.deadline
  | .finalized _ Ω => FinalizedTwoWays apps s c Ω

theorem statusOrigin_of_eq {apps : Apps} {s s' : Adjudicator} {c : FixedPart}
    (ho : StatusOrigin apps s c) (hs : s'.statusOf c = s.statusOf c) (hn : s.now ≤ s'.now) :
    StatusOrigin apps s' c := by
  unfold StatusOrigin at ho ⊢
  rw [hs]
  split at ho
  · trivial
  · exact ho
  · exact ho.mono hn Relation.ReflTransGen.refl

/-- A redistribution of a finalized outcome keeps its origin. -/
theorem statusOrigin_redistribute {apps : Apps} {s s' : Adjudicator} {c : FixedPart} {Ω Ω' : Outcome}
    {t : Nat} (ho : StatusOrigin apps s c) (hf : (s.statusOf c).finalOutcome s.now = some Ω)
    (hR : Redistributed Ω Ω') (hn : s.now ≤ s'.now) (hs : s'.statusOf c = .finalized t Ω') :
    StatusOrigin apps s' c := by
  unfold StatusOrigin at ho ⊢
  rw [hs]
  split at ho
  · rename_i hst; rw [hst] at hf; simp at hf
  · rename_i ch hst
    rw [hst] at hf
    simp only [ChannelStatus.finalOutcome_challenged] at hf
    split at hf
    · rename_i hd
      cases hf
      obtain ⟨s0, s1, caller, proof, hr0, h1, h2⟩ := ho
      exact ⟨s0, s1, caller, hr0, Or.inr ⟨proof, ch.state, h1, by grind, hR⟩⟩
    · cases hf
  · rename_i hst
    rw [hst] at hf
    cases hf
    exact ho.mono hn hR

theorem statusOrigin_step {apps : Apps} {s s' : Adjudicator} {caller : Participant} {op : Op}
    (hr : Reachable apps s) (ho : ∀ c, StatusOrigin apps s c)
    (h : s.apply apps caller op = some s') (c : FixedPart) : StatusOrigin apps s' c := by
  have hn := Adjudicator.apply_now_le h
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
    exact statusOrigin_of_eq (ho c) (Adjudicator.statusOf_of_status hs c) hn
  | tick dt => simp at h; subst h; exact statusOrigin_of_eq (ho c) rfl hn
  | transfer a b =>
    obtain ⟨o, _, x, hf, -, -, -, -, hs, -⟩ := Adjudicator.transfer_some h
    have hsc := Adjudicator.statusOf_of_status hs c
    simp only [Adjudicator.statusOf_setStatus, ChannelStatus.withOutcome_eq] at hsc
    by_cases hca : c = a
    · subst hca
      simp only [if_true] at hsc
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
      exact statusOrigin_redistribute (ho c) hf
        (Relation.ReflTransGen.single (RedistributeStep.reduce o b x)) hn hsc
    · simp only [hca, if_false] at hsc
      exact statusOrigin_of_eq (ho c) hsc hn
  | reclaim l v =>
    obtain ⟨oL, oV, x, left, right, hL, -, -, -, -, -, rfl⟩ := Adjudicator.reclaim_some h
    by_cases hcl : c = l
    · subst hcl
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hL
      exact statusOrigin_redistribute (ho c) hL
        (Relation.ReflTransGen.single
          (RedistributeStep.reclaim oL left right v.address (oV.amountAt 0) (oV.amountAt 1))) hn
        (by simp only [Adjudicator.statusOf_setStatus, if_true, ChannelStatus.withOutcome_eq]; rfl)
    · exact statusOrigin_of_eq (ho c) (by simp [hcl]) hn
  | challenge c' proof cand =>
    have h' := h
    obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
    by_cases hcc : c = c'
    · subst hcc
      unfold StatusOrigin
      simp only [Adjudicator.statusOf_setStatus, if_true]
      exact ⟨s, _, caller, proof, hr, h', rfl⟩
    · exact statusOrigin_of_eq (ho c) (by simp [hcc]) hn
  | checkpoint c' proof cand =>
    obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
    by_cases hcc : c = c'
    · subst hcc; unfold StatusOrigin; simp
    · exact statusOrigin_of_eq (ho c) (by simp [hcc]) hn
  | conclude c' ss =>
    have h' := h
    obtain ⟨⟨-, hp⟩, rfl⟩ := Adjudicator.conclude_some h
    by_cases hcc : c = c'
    · subst hcc
      unfold StatusOrigin
      simp only [Adjudicator.statusOf_setStatus, if_true]
      exact ⟨s, _, caller, hr, Or.inl ⟨ss, h', hp, Relation.ReflTransGen.refl⟩⟩
    · exact statusOrigin_of_eq (ho c) (by simp [hcc]) hn

theorem statusOrigin_reachable {apps : Apps} {s : Adjudicator} (hr : Reachable apps s)
    (c : FixedPart) : StatusOrigin apps s c := by
  induction hr generalizing c with
  | refl => unfold StatusOrigin; exact trivial
  | tail hr' hstep ih =>
    cases hstep with
    | mk caller op _ _ h => exact statusOrigin_step hr' ih h c

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
  have ho := statusOrigin_reachable hr c
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
  unfold StatusOrigin at ho
  revert ho hf
  cases s.statusOf c with
  | «open» t => simp
  | challenged t ch =>
    intro hf ho
    simp only [ChannelStatus.finalOutcome_challenged] at hf
    split at hf
    · cases hf
      obtain ⟨s0, s1, caller, proof, hr0, h1, h2⟩ := ho
      exact ⟨s0, s1, caller, hr0, Or.inr ⟨proof, ch.state, h1, by grind, Relation.ReflTransGen.refl⟩⟩
    · cases hf
  | finalized t Ω0 =>
    intro hf ho
    cases hf
    exact ho

/-- Nitro-14, ForceMove-A14, ForceMove-D12. Nitro:301-302: "the rules of
    operation only allow one outcome to be finalized for each channel."
    go-nitro: every status write in `challenge`, `checkpoint` and
    `_conclude` is guarded by a not-finalized check. Once finalized, a
    channel stays finalized. -/
theorem finalized_permanent (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (h : Step apps s s') (hf : s.mode c = .finalized) : s'.mode c = .finalized := by
  cases h with
  | mk caller op _ _ h =>
  rw [Adjudicator.mode_eq] at hf ⊢
  have hn := Adjudicator.apply_now_le h
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
    rw [Adjudicator.statusOf_of_status hs]; exact ChannelStatus.mode_finalized_mono hf hn
  | tick dt =>
    simp at h; subst h; exact ChannelStatus.mode_finalized_mono hf hn
  | transfer a b =>
    obtain ⟨_, _, _, -, -, -, -, -, hs, -⟩ := Adjudicator.transfer_some h
    rw [Adjudicator.statusOf_of_status hs]
    simp only [Adjudicator.statusOf_setStatus, ChannelStatus.withOutcome_eq]
    split
    · rfl
    · exact ChannelStatus.mode_finalized_mono hf hn
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := Adjudicator.reclaim_some h
    simp only [Adjudicator.statusOf_setStatus, ChannelStatus.withOutcome_eq]
    split
    · rfl
    · exact hf
  | challenge c' proof cand =>
    obtain ⟨⟨-, -, -, hm⟩, rfl⟩ := Adjudicator.challenge_some h
    simp only [Adjudicator.statusOf_setStatus]
    split
    · rename_i hcc; subst hcc; rw [Adjudicator.mode_eq] at hm
      rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hf <;> cases hf
    · exact hf
  | checkpoint c' proof cand =>
    obtain ⟨⟨ho, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
    simp only [Adjudicator.statusOf_setStatus]
    split
    · rename_i hcc; subst hcc; exact absurd hf ho
    · exact hf
  | conclude c' ss =>
    obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
    simp only [Adjudicator.statusOf_setStatus]
    split
    · rfl
    · exact hf

/-- Nitro-14. A finalized outcome is never replaced by a second
    finalization. Every later outcome of the channel is a redistribution of
    the first. -/
theorem finalized_outcome_only_redistributed (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (Ω : Outcome) (h : Step apps s s') (hf : s.finalOutcome c.address = some Ω) :
    ∃ Ω', s'.finalOutcome c.address = some Ω' ∧ Redistributed Ω Ω' := by
  cases h with
  | mk caller op _ _ h =>
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf ⊢
  have hn := Adjudicator.apply_now_le h
  have hsame : ∀ {t : Adjudicator}, t.statusOf c = s.statusOf c → s.now ≤ t.now →
      ∃ Ω', (t.statusOf c).finalOutcome t.now = some Ω' ∧ Redistributed Ω Ω' :=
    fun hs hn => ⟨Ω, by rw [hs]; exact ChannelStatus.finalOutcome_mono hf hn,
      Relation.ReflTransGen.refl⟩
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
    exact hsame (Adjudicator.statusOf_of_status hs c) hn
  | tick dt => simp at h; subst h; exact hsame rfl hn
  | transfer a b =>
    obtain ⟨o, _, x, hfo, -, -, -, -, hs, hn'⟩ := Adjudicator.transfer_some h
    rw [Adjudicator.statusOf_of_status hs, hn']
    simp only [Adjudicator.statusOf_setStatus, ChannelStatus.withOutcome_eq]
    split
    · rename_i hca; subst hca
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hf] at hfo
      cases hfo
      exact ⟨_, rfl, Relation.ReflTransGen.single (RedistributeStep.reduce o b x)⟩
    · exact ⟨Ω, hf, Relation.ReflTransGen.refl⟩
  | reclaim l v =>
    obtain ⟨oL, _, _, left, right, hL, _, _, _, _, _, rfl⟩ := Adjudicator.reclaim_some h
    simp only [Adjudicator.statusOf_setStatus, ChannelStatus.withOutcome_eq,
      Adjudicator.setStatus_now]
    split
    · rename_i hcl; subst hcl
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hf] at hL
      cases hL
      exact ⟨_, rfl, Relation.ReflTransGen.single (RedistributeStep.reclaim oL left right _ _ _)⟩
    · exact ⟨Ω, hf, Relation.ReflTransGen.refl⟩
  | challenge c' proof cand =>
    obtain ⟨⟨-, -, -, hm⟩, rfl⟩ := Adjudicator.challenge_some h
    by_cases hcc : c = c'
    · subst hcc; rw [Adjudicator.mode_eq] at hm
      rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hfin <;> cases hfin
    · exact hsame (by simp [hcc]) hn
  | checkpoint c' proof cand =>
    obtain ⟨⟨ho, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
    by_cases hcc : c = c'
    · subst hcc; exact absurd hfin ho
    · exact hsame (by simp [hcc]) hn
  | conclude c' ss =>
    obtain ⟨⟨ho, -⟩, rfl⟩ := Adjudicator.conclude_some h
    by_cases hcc : c = c'
    · subst hcc; exact absurd hfin ho
    · exact hsame (by simp [hcc]) hn

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
  exact (Adjudicator.challenge_some h).1

/-- SATP-14. go-nitro ForceMove.sol:52-54 and SATP:303: a challenge on a
    finalized channel fails. -/
theorem challenge_fails_when_finalized (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (hf : s.mode c = .finalized) :
    s.challenge apps challenger c proof candidate = none := by
  cases hc : s.challenge apps challenger c proof candidate with
  | none => rfl
  | some s' =>
    obtain ⟨⟨-, -, -, hm⟩, -⟩ := Adjudicator.challenge_some hc
    rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hf <;> cases hf

/-- SATP-14. go-nitro ForceMove.sol:48-50 `_requireIncreasedTurnNumber`: a
    re-challenge at an equal turn during a running challenge fails. SATP
    Listing 1 would accept it and reset the deadline; the code is followed. -/
theorem rechallenge_equal_turn_fails (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (hm : s.mode c = .challenge)
    (ht : candidate.turnNum ≤ (s.statusOf c).turnNumRecord) :
    s.challenge apps challenger c proof candidate = none := by
  cases hc : s.challenge apps challenger c proof candidate with
  | none => rfl
  | some s' =>
    obtain ⟨⟨-, -, -, hm'⟩, -⟩ := Adjudicator.challenge_some hc
    rcases hm' with ⟨hm', -⟩ | ⟨-, hlt⟩
    · rw [hm] at hm'; cases hm'
    · omega

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
  simp only [Adjudicator.challenge, if_pos (And.intro hp (And.intro hs (And.intro hc ht)))]

/-- ForceMove-D12, ForceMove-B04, SATP-14. A fresh challenge with a positive
    duration puts the channel in challenge mode. Balances, coins held and
    the clock do not move. -/
theorem challenge_effects (apps : Apps) (s : Adjudicator) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof) (candidate : State) (s' : Adjudicator)
    (h : s.challenge apps challenger c proof candidate = some s') (hd : 0 < c.challengeDuration) :
    s'.mode c = .challenge ∧ s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now ∧
    ∀ c', c' ≠ c → s'.statusOf c' = s.statusOf c' := by
  obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
  refine ⟨?_, rfl, rfl, rfl, fun c' hc' => by simp [hc']⟩
  rw [Adjudicator.mode_eq]
  simp
  grind

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
  obtain ⟨⟨ho, hs, hc, ht⟩, -⟩ := Adjudicator.checkpoint_some h
  exact ⟨ho, hs, hc, ht⟩

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
  refine ⟨?_, by rw [Adjudicator.mode_eq]; simp⟩
  simp only [Adjudicator.checkpoint]
  rw [if_pos ⟨hm, hs, hc, ht⟩]

/-- ForceMove-B02, ForceMove-A21, docs-0070-03, docs-0040-03. go-nitro
    `_requireNonDecreasedTurnNumber` and `_requireIncreasedTurnNumber`
    (ForceMove.sol); ForceMove:1543-1545: "Only allow new force-moves if
    their response will increase this stored turnNum." No step lowers the
    stored turn number of a channel, except a conclude of that channel,
    which finalizes it in the same step: `Adjudicator.conclude` has no turn
    check and stores the candidate's turn (go-nitro stores 0). Operator
    ruling 2026-10-27 (counterexample in Counter.lean). -/
theorem turnNumRecord_monotone (apps : Apps) (s s' : Adjudicator) (c : FixedPart)
    (h : Step apps s s') :
    (s.statusOf c).turnNumRecord ≤ (s'.statusOf c).turnNumRecord ∨
    ∃ caller ss, s.apply apps caller (.conclude c ss) = some s' ∧ s'.mode c = .finalized := by
  cases h with
  | mk caller op _ _ h =>
  cases op with
  | conclude c' ss =>
    by_cases hcc : c = c'
    · subst hcc
      refine Or.inr ⟨caller, ss, h, ?_⟩
      obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
      rw [Adjudicator.mode_eq]; simp
    · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
      left; simp [hcc]
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
    left; rw [Adjudicator.statusOf_of_status hs]
  | tick dt => simp at h; subst h; left; simp
  | transfer a b =>
    obtain ⟨_, _, _, -, -, -, -, -, hs, -⟩ := Adjudicator.transfer_some h
    left; rw [Adjudicator.statusOf_of_status hs]
    simp only [Adjudicator.statusOf_setStatus, ChannelStatus.withOutcome_eq]
    split
    · rename_i hca; subst hca; simp
    · exact le_rfl
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := Adjudicator.reclaim_some h
    left; simp only [Adjudicator.statusOf_setStatus, ChannelStatus.withOutcome_eq]
    split
    · rename_i hcl; subst hcl; simp
    · exact le_rfl
  | challenge c' proof cand =>
    obtain ⟨⟨-, -, -, hm⟩, rfl⟩ := Adjudicator.challenge_some h
    left; simp only [Adjudicator.statusOf_setStatus]
    split
    · rename_i hcc; subst hcc; simp; omega
    · exact le_rfl
  | checkpoint c' proof cand =>
    obtain ⟨⟨-, -, -, ht⟩, rfl⟩ := Adjudicator.checkpoint_some h
    left; simp only [Adjudicator.statusOf_setStatus]
    split
    · rename_i hcc; subst hcc; simp; omega
    · exact le_rfl

/-- ForceMove-A14, Nitro-13, SATP-16, docs-0070-01, docs-0010-05. go-nitro
    ForceMove.sol:142-152: a conclude needs a non-finalized channel, a final
    candidate and unanimous signatures; the application is not consulted.
    SATP:288-289: "supporting a state with isFinal = true";
    ForceMove:1495-1500. -/
theorem conclude_requires (s : Adjudicator) (c : FixedPart) (ss : SignedState) (s' : Adjudicator)
    (h : s.conclude c ss = some s') :
    s.mode c ≠ .finalized ∧ ss.state.channel = c ∧ ss.state.isFinal = true ∧ ss.ByAll := by
  obtain ⟨⟨ho, hc, hf, hall⟩, -⟩ := Adjudicator.conclude_some h
  exact ⟨ho, hc, hf, hall⟩

/-- ForceMove-A09, Nitro-13, SATP-08, SATP-16, docs-0070-01, docs-0020-01.
    go-nitro ForceMove.sol:147-152 `'!unanimous'`; Nitro:297-298: "all the
    participants sign a special conclude state, called a conclusion proof".
    A conclude carries one state signed by every participant, for every
    application. -/
theorem conclude_needs_all (s : Adjudicator) (c : FixedPart) (ss : SignedState) (s' : Adjudicator)
    (h : s.conclude c ss = some s') (p : Participant) (hp : p ∈ c.participants) :
    p ∈ ss.signers := by
  obtain ⟨⟨-, hc, -, hall⟩, -⟩ := Adjudicator.conclude_some h
  exact hall p (hc ▸ hp)

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
  refine ⟨?_, by simp, by rw [Adjudicator.mode_eq]; simp⟩
  simp only [Adjudicator.conclude]
  rw [if_pos ⟨hm, hproof⟩]

/-- ForceMove-A04, ForceMove-A05, docs-0070-07. go-nitro `_conclude` writes
    only `statusOf`; ForceMove:976-980, 1017-1022: the conclude transition
    keeps the resolution. A conclude moves no coins. -/
theorem conclude_moves_no_value (s : Adjudicator) (c : FixedPart) (ss : SignedState)
    (s' : Adjudicator) (h : s.conclude c ss = some s') :
    s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now := by
  obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
  exact ⟨rfl, rfl, rfl⟩

/-- ForceMove-B03, ForceMove-D12, Nitro-12, docs-0040-05, docs-0040-06.
    go-nitro StatusManager.sol:10-11: a finalization time at or before
    `block.timestamp` is Finalized; ForceMove:1260-1265: "If no response is received within the
    timeout period, the game transitions into the Terminated mode";
    ForceMove:449-453: "the resolution stored on the challenge state s will
    decide how the funds should be split." -/
theorem timeout_finalizes (s : Adjudicator) (c : FixedPart) (t : Nat) (ch : Challenge)
    (hs : s.statusOf c = .challenged t ch) (hd : ch.deadline ≤ s.now) :
    s.mode c = .finalized ∧ s.finalOutcome c.address = some ch.state.outcome := by
  simp [Adjudicator.mode_eq, hs, hd]

/-- ForceMove-D12. go-nitro StatusManager.sol:12-13: a future finalization
    time is Challenge mode; ForceMove:1295 `inProgress: c ↦ c.endTime > now()`. -/
theorem challenge_in_progress_before_deadline (s : Adjudicator) (c : FixedPart) (t : Nat)
    (ch : Challenge) (hs : s.statusOf c = .challenged t ch) (hd : s.now < ch.deadline) :
    s.mode c = .challenge ∧ s.finalOutcome c.address = none := by
  simp [Adjudicator.mode_eq, hs, Nat.not_le.2 hd]

/-- ForceMove-F03, docs-0040-05. docs: "a passive transition which happens
    when a block is produced with a sufficiently large timestamp." The clock
    changes no balance and no status. -/
theorem tick_moves_only_time (s : Adjudicator) (dt : Time) :
    (s.tick dt).balances = s.balances ∧ (s.tick dt).held = s.held ∧
    (s.tick dt).status = s.status ∧ (s.tick dt).now = s.now + dt := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- ForceMove-A20. go-nitro: a failed `require` reverts the transaction;
    ForceMove:685-686: "making an invalid move is equivalent to not making
    any move at all." A failed operation leaves the chain unchanged. -/
theorem failed_op_no_effect (apps : Apps) (caller : Participant) (op : Op) (s : Adjudicator)
    (h : s.apply apps caller op = none) :
    Adjudicator.applyAll apps [(caller, op)] s = s := by
  simp [Adjudicator.applyAll, h]

/-- ForceMove-F05. go-nitro ForceMove.sol reads no `holdings`;
    ForceMove:1609-1628: "there is no way of telling from the properties of
    the channel how (or even whether) the game is funded." The dispute
    operations read no balance: their success and their status result do
    not depend on the balances. -/
theorem funding_decoupled_from_rules (apps : Apps) (caller : Participant) (s : Adjudicator)
    (b : Balances) (op : Op) (hop : op.isRedistribution = false ∧ ∀ a e x, op ≠ .deposit a e x) :
    ((s.apply apps caller op).map Adjudicator.status) =
      (({ s with balances := b }.apply apps caller op).map Adjudicator.status) := by
  obtain ⟨h1, h2⟩ := hop
  cases op with
  | deposit a e x => exact absurd rfl (h2 a e x)
  | transfer a b => simp [Op.isRedistribution] at h1
  | reclaim l v => simp [Op.isRedistribution] at h1
  | challenge c proof cand =>
    simp [Adjudicator.challenge, Adjudicator.mode, Adjudicator.statusOf, Adjudicator.setStatus]
  | checkpoint c proof cand =>
    simp [Adjudicator.checkpoint, Adjudicator.statusOf, Adjudicator.setStatus]
  | conclude c ss =>
    simp [Adjudicator.conclude, Adjudicator.statusOf, Adjudicator.setStatus]
  | tick dt => rfl

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
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hrun⟩, -⟩, hlast⟩ := h
  refine ⟨hlen, fun i m1 m2 h1 h2 => ?_, ?_⟩
  · have hm := validRun_getElem? hrun h1 h2
    simp only [validMove, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at hm
    obtain ⟨⟨⟨⟨⟨hc, ht⟩, -⟩, -⟩, hvt⟩, hmv⟩ := hm
    refine ⟨hc, ht, (SignedState.byMover_iff _).1 hmv, fun hf => ?_⟩
    rcases hvt with hvt | hvt
    · rw [hf] at hvt; cases hvt
    · exact hvt
  · cases hp : proof.getLast? with
    | none => rw [hp] at hlast; cases hlast
    | some m =>
      rw [hp] at hlast
      simp only [Option.map_some, Option.some.injEq] at hlast
      exact ⟨m, rfl, hlast⟩

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
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq] at h
  have hm := validRun_getElem? h.1.1.2 h1 h2
  simp only [validMove, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hm
  obtain ⟨⟨⟨⟨⟨-, -⟩, hout⟩, hfin⟩, -⟩, -⟩ := hm
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rcases hout with hout | hout
    · rw [hf] at hout; cases hout
    · exact hout
  · rcases hfin with hfin | hfin
    · rw [hf] at hfin; cases hfin
    · exact hfin

/-- ForceMove-D05, ForceMove-D06 (ForceMove only). ForceMove:724-727: "the
    mover is fully determined by the turn number". -/
theorem mover_determined_by_turn (s t : State) (hc : s.channel = t.channel)
    (ht : s.turnNum = t.turnNum) : s.mover = t.mover := by
  unfold State.mover
  rw [hc, ht]

/-- ForceMove-D06 (ForceMove only). ForceMove:725-727: "players must take
    turns in a cyclical order." The mover of turn `k + n` is the mover of
    turn `k`. -/
theorem mover_cyclic (s : State) (k : Nat) :
    { s with turnNum := k + s.channel.n }.mover = { s with turnNum := k }.mover := by
  simp [State.mover, Nat.add_mod_right]

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
  obtain ⟨oL, oV, x, left, right, hL, hV, hg, hl, hr, hx, -⟩ := Adjudicator.reclaim_some h
  refine ⟨?_, ?_, oL, oV, x, left, right, hL, hV, hg, hl, hr, hx⟩
  · simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hL
    rw [Adjudicator.mode_eq, ChannelStatus.mode_eq_finalized_iff, hL]; rfl
  · simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hV
    rw [Adjudicator.mode_eq, ChannelStatus.mode_eq_finalized_iff, hV]; rfl

/-- SATP-15, docs-0080-05. SATP:358-363 and go-nitro
    `compute_reclaim_effects`: `o_ledger[left] += o_target[0]`,
    `o_ledger[right] += o_target[1]`, the guarantee entry is deleted. The
    balances do not move. The total of the ledger outcome is unchanged
    (go-nitro line 365: `totalReclaimed == guarantee.amount`). The
    hypotheses `hne` and `hdedup` are from the operator ruling 2026-10-27
    (counterexample in Counter.lean): a ledger that guarantees itself, or a
    ledger with a second entry for `v` (Nitro-25: each address appears
    once), breaks the statement. -/
theorem reclaim_effects (s : Adjudicator) (l v : FixedPart) (s' : Adjudicator)
    (oL oV : Allocation) (x : Coins) (left right : Address)
    (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalOutcome v.address = some (.allocation oV))
    (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩)
    (hlr : left ≠ right) (hlv : left ≠ v.address) (hrv : right ≠ v.address)
    (hne : l ≠ v) (hdedup : oL.dedup = oL)
    (h : s.reclaim l v = some s') :
    ∃ oL', s'.finalOutcome l.address = some (.allocation oL') ∧
      oL'.owed left = oL.owed left + oV.amountAt 0 ∧
      oL'.owed right = oL.owed right + oV.amountAt 1 ∧
      oL'.find v.address = none ∧
      oL'.total = oL.total ∧
      s'.balances = s.balances ∧ s'.held = s.held ∧
      s'.finalOutcome v.address = s.finalOutcome v.address := by
  obtain ⟨oL0, oV0, x0, left0, right0, hL0, hV0, hg0, hl, hr, hx, rfl⟩ := Adjudicator.reclaim_some h
  rw [hL] at hL0; rw [hV] at hV0
  simp only [Option.some.injEq, Outcome.allocation.injEq] at hL0 hV0
  subst hL0 hV0
  rw [hg] at hg0
  simp only [Option.some.injEq, Entry.mk.injEq, Item.guarantee.injEq, List.cons.injEq, true_and,
    and_true] at hg0
  obtain ⟨rfl, rfl, rfl⟩ := hg0
  rw [Allocation.find_remove, if_neg hlv] at hl
  rw [Allocation.find_remove, if_neg hrv] at hr
  have hrl : right ≠ left := Ne.symm hlr
  have hr1 : (oL.addTo left (oV.amountAt 0)).find right ≠ none := by
    rwa [Allocation.find_addTo_of_ne _ _ hrl]
  have hnd : (oL.map Entry.dest).Nodup := hdedup ▸ Allocation.dedup_nodup oL
  have hnd2 : ((((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1))).map
      Entry.dest).Nodup := by
    rwa [Allocation.addTo_map_dest, Allocation.addTo_map_dest]
  have hown : oL.owed v.address = x := by rw [Allocation.owed, hg]; rfl
  have htot := Allocation.total_remove hnd2 v.address
  rw [Allocation.owed_addTo_of_ne _ _ (Ne.symm hrv), Allocation.owed_addTo_of_ne _ _ (Ne.symm hlv),
    hown, Allocation.total_addTo _ hr1, Allocation.total_addTo _ hl] at htot
  refine ⟨((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address,
    by simp, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · rw [Allocation.owed_remove_of_ne _ hlv, Allocation.owed_addTo_of_ne _ _ hlr,
      Allocation.owed_addTo_self _ hl]
  · rw [Allocation.owed_remove_of_ne _ hrv, Allocation.owed_addTo_self _ hr1,
      Allocation.owed_addTo_of_ne _ _ hrl]
  · rw [Allocation.find_remove, if_pos rfl]
  · grind
  · simp [Ne.symm hne]

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
  simp only [Adjudicator.reclaim, hL, hV, hg]
  rw [if_pos ⟨hl, hr, hx⟩]

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
  cases hc : s.reclaim l v with
  | none => rfl
  | some s' =>
    obtain ⟨oL0, oV0, x0, left0, right0, hL0, hV0, hg0, hl, hr, hx, -⟩ := Adjudicator.reclaim_some hc
    rw [hL] at hL0; rw [hV] at hV0
    simp only [Option.some.injEq, Outcome.allocation.injEq] at hL0 hV0
    subst hL0 hV0
    rw [hg] at hg0
    simp only [Option.some.injEq, Entry.mk.injEq, Item.guarantee.injEq, List.cons.injEq, true_and,
      and_true] at hg0
    obtain ⟨rfl, rfl, rfl⟩ := hg0
    rcases hbad with h | h | h
    · exact absurd h hl
    · exact absurd h hr
    · exact absurd hx h

/-- SATP-13, docs-0040-02. SATP:294-298 `isOpen`: "the channel has no active
    challenge or the channel has not yet finalized"; go-nitro
    StatusManager.sol:5-14. -/
theorem isOpen_iff (st : ChannelStatus) (now : Time) :
    st.IsOpen now ↔ (st.mode now = .open ∨ st.mode now = .challenge) := by
  unfold ChannelStatus.IsOpen
  cases st.mode now <;> simp

/-- ForceMove-D11, Nitro-11. Every channel is in exactly one mode. A channel
    with no record is open (go-nitro: an empty status unpacks to a zero
    finalization time). -/
theorem mode_of_absent (s : Adjudicator) (c : FixedPart) (h : ∀ e ∈ s.status, e.1 ≠ c) :
    s.mode c = .open ∧ (s.statusOf c).turnNumRecord = 0 := by
  have hl : s.status.lookup c = none := by
    simp only [List.lookup_eq_none_iff, bne_iff_ne, ne_eq]
    exact fun p hp hpc => h p hp hpc.symm
  have hs : s.statusOf c = .open 0 := by simp [Adjudicator.statusOf, hl]
  simp [Adjudicator.mode_eq, hs]

/-- Nitro-08, Nitro-05. Only a deposit raises the coins held and only a
    payout to a participant lowers them. -/
theorem held_changes_only_by_deposit_payout (apps : Apps) (s s' : Adjudicator)
    (caller : Participant) (op : Op) (h : s.apply apps caller op = some s')
    (hne : s'.held ≠ s.held) :
    (∃ a e x, op = .deposit a e x) ∨ op.isRedistribution = true := by
  cases op with
  | deposit a e x => exact Or.inl ⟨a, e, x, rfl⟩
  | transfer a b => exact Or.inr rfl
  | reclaim l v => exact Or.inr rfl
  | challenge c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.challenge_some h; simp at hne
  | checkpoint c proof cand => obtain ⟨_, rfl⟩ := Adjudicator.checkpoint_some h; simp at hne
  | conclude c ss => obtain ⟨_, rfl⟩ := Adjudicator.conclude_some h; simp at hne
  | tick dt => simp at h; subst h; simp at hne

end ArmadaLean.Nitro
