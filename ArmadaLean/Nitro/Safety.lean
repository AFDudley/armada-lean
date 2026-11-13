/-
  Nitro protocol theorems: on-chain adjudicator safety, conservation and the
  correctness of the data operations. The proofs use the `@[simp]` API and
  the invariant `Adjudicator.Inv` of `Invariant.lean`. The statements
  are the deliverable. Each doc comment cites the latest source first (SATP,
  then Nitro, then ForceMove), then go-nitro, and names the property ids of
  `docs/nitro-theorems.md`.
-/
import ArmadaLean.Nitro.SATP
import ArmadaLean.Nitro.Lemmas
import ArmadaLean.Nitro.Invariant
import ArmadaLean.Nitro.OpEquations
import ArmadaLean.Types.Reachable
import ArmadaLean.SpecTools
import ArmadaLean.Nitro.Reachable
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

omit [DecidableEq E] in
/-- ForceMove-D02, Nitro-02, Nitro-03, SATP-05, docs-0010-02, ForceMove-F01.
    SATP:213-215: the id is computed from the constants and the nonce makes
    channels distinct; Nitro:158-160: impossible "to construct a channel
    whose address is A"; go-nitro NitroUtils.sol:122-133. Two fixed parts
    with one address are one channel. -/
theorem channel_address_inj (c c' : FixedPart) (h : (c.address : Address E) = c'.address) :
    c = c' := by
  (simpa? using h says simpa only [FixedPart.address_eq, Address.channel.injEq] using h)

omit [DecidableEq E] in
/-- ForceMove-D02, Nitro-02. go-nitro `_isExternalDestination`
    (MultiAssetHolder.sol:436): a channel id is never an external
    destination, so a channel's funds cannot be read as an external
    destination's. -/
theorem channel_address_ne_external (c : FixedPart) (e : E) :
    c.address ≠ Address.external e := by
  (simp? says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])

/-- Nitro-01. Nitro:162-163: "If an address does not appear in the table we
    take the balance to be zero." go-nitro: an unset `holdings` entry reads
    as 0. -/
theorem balances_absent_zero (b : Balances E) (a : Address E) (h : ∀ e ∈ b, e.1 ≠ a) :
    b.get a = 0 := by
  exact Balances.get_of_forall_ne h

/-- Nitro-08, Nitro-05, ForceMove-F04, docs-C-01. Nitro:230-231: "The total
    coins held by the smart contract should always equal the sum of the
    balances." go-nitro: `holdings` is per channel, and a payout to an
    external destination leaves the contract (MultiAssetHolder.sol:401-402),
    so the coins held equal the sum of the channel balances. -/
theorem held_eq_channel_balances (apps : Apps E) (s : ReachableState (Nitro.chain apps)) :
    s.state.held = s.state.balances.channelTotal := by
  obtain_reach ⟨s, h : Reachable apps s⟩ := s
  exact (Adjudicator.inv_reachable h).held

omit [DecidableEq E] in
/-- Nitro-08. Every coin that entered the adjudicator is held for a channel
    or was paid out to a participant. -/
theorem balances_total_split (b : Balances E) :
    b.total = b.channelTotal + b.paidOutTotal :=
  Balances.total_eq_channelTotal_add_paidOutTotal b

/-- Nitro-04, Nitro-05, ForceMove-C01, docs-0060-02, docs-0060-03,
    docs-0060-04, docs-0060-05. go-nitro MultiAssetHolder.sol:51, 57-60:
    `held == expectedHeld`, then `held += amount`; Nitro:165-168: the
    deposit raises the balance by `x` and brings `x` coins into the
    adjudicator. It touches nothing else. A second deposit adds to the
    first. -/
theorem deposit_effects (s : Adjudicator E) (c : FixedPart) (e x : Coins) (s' : Adjudicator E)
    (h : s.deposit c.address e x = some s') :
    s.balances.get c.address = e ∧
    s'.balances.get c.address = e + x ∧
    s'.held = s.held + x ∧
    (∀ b, b ≠ c.address → s'.balances.get b = s.balances.get b) ∧
    s'.status = s.status ∧ s'.now = s.now := by
  obtain ⟨-, he, hb, hh, hs, hn⟩ := Adjudicator.deposit_some h
  refine ⟨he, ?_, hh, fun b hb' => ?_, hs, hn⟩
  · rw [hb]; (simp? at he ⊢ says simp only [FixedPart.address_eq, Balances.get_add, ↓reduceIte, Nat.add_right_cancel_iff] at he ⊢); rw [he]
  · rw [hb]; (simp? at hb' ⊢ says simp only [FixedPart.address_eq, ne_eq, Balances.get_add, ite_eq_right_iff] at hb' ⊢); (simp? [hb'] says simp only [hb', IsEmpty.forall_iff])

/-- Nitro-04, docs-0060-01. Nitro:166-167: "There are no restrictions on who
    can deposit coins for an address". go-nitro MultiAssetHolder.sol:43: a
    deposit to an external destination reverts, so the address must be a
    channel; the code is followed. The deposit succeeds for every caller
    and every ledger channel (`ChannelKind`: a
    virtual channel never accepts one). -/
theorem deposit_can_happen (apps : Apps E) (caller : Participant) (s : Adjudicator E) (c : FixedPart)
    (hk : c.kind = .ledger) (x : Coins) :
    s.apply apps caller (.deposit c.address (s.balances.get c.address) x) =
      some { s with balances := s.balances.add c.address x, held := s.held + x } := by
  have hpre : s.DepositPre c.address (s.balances.get c.address) :=
    ⟨rfl, by (simp? [Address.fundable, hk] says simp only [Address.fundable, FixedPart.address_eq, hk, decide_true]), rfl⟩
  rw [Adjudicator.apply_deposit_equation, dif_pos hpre]
  rfl

/-- docs-0060-02. go-nitro MultiAssetHolder.sol:51 `require(held ==
    expectedHeld, 'held != expectedHeld')`: a deposit whose observation is
    stale fails. A history in which an earlier deposit was dropped or
    reordered is one such history. -/
theorem deposit_requires_expectedHeld (s : Adjudicator E) (c : FixedPart) (e x : Coins)
    (h : s.balances.get c.address ≠ e) : s.deposit c.address e x = none := by
  (simp? at h says simp only [FixedPart.address_eq, ne_eq] at h)
  (simp? [Adjudicator.deposit, h] says simp only [Adjudicator.deposit, FixedPart.address_eq, h, and_false, ↓reduceIte])

/-- The sum of the allocations ahead of entry `k`: the holding a funder in
    position `k` must see before it deposits (ForceMove:1197-1208,
    ForceMove:1797-1808; docs 0060: "participants should not deposit until
    those with higher priority have had their deposits confirmed"). -/
def Allocation.aheadOf (o : Allocation E) (k : Nat) : Coins :=
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
theorem deposit_respects_funding_order (apps : Apps E) (s : ReachableState (Nitro.chain apps)) (s' : Adjudicator E)
    (caller : Participant) (c : FixedPart) (o : Allocation E) (hdedup : o.dedup = o) (k : Nat)
    (e : Entry E) (he : o[k]? = some e)
    (h : s.state.apply apps caller (.deposit c.address (o.aheadOf k) e.amount) = some s') :
    s.state.balances.get c.address = o.aheadOf k ∧
    s'.balances.get c.address = o.aheadOf k + e.amount ∧
    (∀ j f, j < k → o[j]? = some f →
      o.paidTo (s.state.balances.get c.address) f.dest = f.amount ∧
      o.paidTo (s'.balances.get c.address) f.dest = f.amount) ∧
    o.paidTo (s'.balances.get c.address) e.dest = e.amount ∧
    (∀ j f, k < j → o[j]? = some f → o.paidTo (s'.balances.get c.address) f.dest = 0) := by
  obtain_reach ⟨s, hr : Reachable apps s⟩ := s
  rw [Adjudicator.apply_deposit] at h
  obtain ⟨-, he0, hb, -⟩ := Adjudicator.deposit_some h
  have hs' : s'.balances.get c.address = o.aheadOf k + e.amount := by
    rw [hb]; (simp? at he0 ⊢ says simp only [FixedPart.address_eq, Balances.get_add, ↓reduceIte, Nat.add_right_cancel_iff] at he0 ⊢); rw [he0]
  have hk := Allocation.total_take_succ he
  unfold Allocation.aheadOf at he0 hs' ⊢
  refine ⟨he0, hs', fun j f hj hf => ?_, ?_, fun j f hj hf => ?_⟩
  · have h1 := Allocation.total_take_succ hf
    have h2 := Allocation.total_take_mono o (show j + 1 ≤ k by omega)
    rw [he0, hs', Allocation.paidTo_of_getElem? hdedup hf, Allocation.paidTo_of_getElem? hdedup hf]
    (grind? says grind only [= min_def, #1b03, #946b, #360f, #6f2e, #8a6f])
  · rw [hs', Allocation.paidTo_of_getElem? hdedup he]
    (grind? says grind only [= min_def, #e527])
  · have h2 := Allocation.total_take_mono o (show k + 1 ≤ j by omega)
    rw [hs', Allocation.paidTo_of_getElem? hdedup hf]
    (grind? says grind only [= min_def, #946b, #8a6f])

/-- ForceMove-C01, docs-0060-02. Deposits made in the order of the
    pre-funding outcome, each with `expectedHeld` equal to the allocations
    ahead of it, all succeed from a channel that holds nothing, and leave
    the channel fully funded (ForceMove:1797-1808). -/
theorem deposits_in_order_succeed (apps : Apps E) (s : Adjudicator E) (c : FixedPart) (o : Allocation E)
    (callers : List Participant) (hck : c.kind = .ledger) (h0 : s.balances.get c.address = 0) :
    let op := fun k => ((callers[k]?).getD ⟨0⟩, Op.deposit c.address (o.aheadOf k) (o.amountAt k))
    let ops := (List.range o.length).map op
    (∀ k, k < o.length →
      (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k ∧
      (Adjudicator.applyAll apps (ops.take k) s).apply apps (op k).1 (op k).2 =
        some (Adjudicator.applyAll apps (ops.take (k + 1)) s)) ∧
    (Adjudicator.applyAll apps ops s).balances.get c.address = o.total := by
  intro op ops
  have hlen : ops.length = o.length := by (simp? [ops] says simp only [List.length_map, List.length_range, ops])
  have hops : ∀ k, k < o.length → ops[k]? = some (op k) := by
    intro k hk; (simp? [ops, hk] says simp only [List.length_map, List.length_range, hk, getElem?_pos, List.getElem_map, List.getElem_range, ops])
  have hpreK : ∀ k, (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k →
      (Adjudicator.applyAll apps (ops.take k) s).DepositPre c.address (o.aheadOf k) :=
    fun k hb => ⟨rfl, by (simp? [Address.fundable, hck] says simp only [Address.fundable, FixedPart.address_eq, hck, decide_true]), hb⟩
  have hstep : ∀ k, k < o.length →
      (hb : (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k) →
      Adjudicator.applyAll apps (ops.take (k + 1)) s =
        (Adjudicator.applyAll apps (ops.take k) s).depositEffect (o.aheadOf k)
          ⟨c.address, hpreK k hb⟩ (o.amountAt k) := by
    intro k hk hb
    rw [List.take_add_one, hops k hk, Option.toList_some, Adjudicator.applyAll_append,
      Adjudicator.applyAll_singleton_of_some
        (show (Adjudicator.applyAll apps (ops.take k) s).apply apps (op k).1 (op k).2 =
            some ((Adjudicator.applyAll apps (ops.take k) s).depositEffect (o.aheadOf k)
              ⟨c.address, hpreK k hb⟩ (o.amountAt k)) by
          rw [Adjudicator.apply_deposit_equation, dif_pos (hpreK k hb)])]
  have hone : ∀ k, k < o.length →
      (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k →
      (Adjudicator.applyAll apps (ops.take (k + 1)) s).balances.get c.address = o.aheadOf (k + 1) := by
    intro k hk hb
    obtain ⟨e, he⟩ : ∃ e, o[k]? = some e := ⟨o[k], List.getElem?_eq_getElem hk⟩
    rw [hstep k hk hb]
    simp only [Adjudicator.depositEffect, Balances.get_add, if_true, hb, Allocation.aheadOf,
      Allocation.total_take_succ he, Allocation.amountAt, he, Option.map_some, Option.getD_some]
  have hall : ∀ k, k ≤ o.length →
      (Adjudicator.applyAll apps (ops.take k) s).balances.get c.address = o.aheadOf k := by
    intro k
    induction k with
    | zero => intro _; (simpa? [Allocation.aheadOf, Adjudicator.applyAll] using h0 says simpa only [List.take_zero, Adjudicator.applyAll, FixedPart.address_eq, Allocation.aheadOf, Allocation.total_nil] using h0)
    | succ k ih => intro hk; exact hone k (by omega) (ih (by omega))
  refine ⟨fun k hk => ⟨hall k hk.le, ?_⟩, ?_⟩
  · rw [hstep k hk (hall k hk.le), Adjudicator.apply_deposit_equation,
      dif_pos (hpreK k (hall k hk.le))]
  · have := hall o.length le_rfl
    rw [List.take_of_length_le hlen.le] at this
    rw [this, Allocation.aheadOf, List.take_length]

/-- docs-0060-01, Nitro-04. go-nitro MultiAssetHolder.sol:43 "Deposit to
    external destination": a deposit to an external destination fails. -/
theorem deposit_to_external_fails (s : Adjudicator E) (d : E) (e x : Coins) :
    s.deposit (.external d) e x = none := by
  rfl

/-- Nitro-06, Nitro-07, SATP-16. go-nitro MultiAssetHolder.sol:396-408: coins
    leave the contract only through `_executeSingleAssetExit`, which only
    `transfer` (and the batch helpers) call on a finalized outcome. Nitro
    :227-229: "funds can only be withdrawn from participant addresses - and
    only by a party who knows the private key"; go-nitro has no withdrawal
    operation: the payout goes to the participant's address itself. A fall
    of the coins held comes from a redistribution of a finalized channel.
    The hypothesis `hr` guards against the case (counterexample
    in Counter.lean): on an unreachable state the coins held can be fewer
    than the payout. -/
theorem held_falls_only_by_payout (apps : Apps E) (s : ReachableState (Nitro.chain apps)) (s' : Adjudicator E)
    (caller : Participant)
    (op : Op E) (h : s.state.apply apps caller op = some s') (hlt : s'.held < s.state.held) :
    op.isRedistribution = true ∧
    ∃ d : E, s'.balances.get (.external d) = s.state.balances.get (.external d) + (s.state.held - s'.held) ∧
      ∀ d', d' ≠ d → s'.balances.get (.external d') = s.state.balances.get (.external d') := by
  obtain_reach ⟨s, hr : Reachable apps s⟩ := s
  exact (Adjudicator.inv_reachable hr).heldFalls h hlt

/-- Nitro-07. Nitro:227-229: no operation takes a channel's coins except a
    redistribution. go-nitro: only `holdings[asset][channelId] -=
    totalPayouts` (MultiAssetHolder.sol:203) lowers a holding. -/
theorem channel_balance_falls_only_by_redistribution (apps : Apps E) (s s' : Adjudicator E)
    (caller : Participant) (op : Op E) (h : s.apply apps caller op = some s') (c : FixedPart)
    (hlt : s'.balances.get c.address < s.balances.get c.address) :
    op.isRedistribution = true := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, hb, -, -, -⟩ := Adjudicator.deposit_some h
    rw [hb] at hlt; (simp? at hlt says simp only [FixedPart.address_eq, Balances.get_add] at hlt); split at hlt <;> (grind? says grind only)
  | transfer a b => rfl
  | reclaim l v => rfl
  | _ => exact absurd (congrArg (·.get c.address) (Adjudicator.apply_balances_frame rfl h)) (ne_of_lt hlt)

/-- Nitro-06. An external destination's paid-out balance never falls:
    go-nitro has no operation that takes coins back from an external
    destination. -/
theorem paid_out_monotone (apps : Apps E) (s s' : Adjudicator E) (h : Step apps s s')
    (d : E) :
    s.balances.get (.external d) ≤ s'.balances.get (.external d) := by
  cases h with
  | mk caller op _ _ h =>
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c, rfl, -⟩, -, hb, -, -, -⟩ := Adjudicator.deposit_some h
    rw [hb]; (simp? says simp only [Balances.get_add, reduceCtorEq, ↓reduceIte, Std.le_refl])
  | transfer a b =>
    obtain ⟨_, _, x, -, -, -, hb, -, -, -⟩ := Adjudicator.transfer_some h
    rw [hb]; (simp? says simp only [FixedPart.address_eq, Balances.get_sub, reduceCtorEq, ↓reduceIte, Balances.get_add]); split <;> (grind? says grind only)
  | _ => exact (congrArg (·.get (.external d)) (Adjudicator.apply_balances_frame rfl h)).symm.le

omit [DecidableEq E] in
/-- ForceMove-A16, ForceMove-B07, Nitro-26, SATP-12, docs-0080-03. go-nitro
    MultiAssetHolder.sol:162-191: entry `k` is paid `min(amount, surplus)`
    where `surplus` is the coins held minus what the earlier entries took.
    ForceMove:1837-1853: `min(owed_k, balance − pending)`; Nitro:747-749:
    "the addresses at the beginning of the allocation will receive funds
    first." -/
theorem payout_priority_formula (held : Coins) (o : Allocation E) (k : Nat) (e : Entry E)
    (h : o[k]? = some e) :
    (o.payout held)[k]? = some (e.dest, min e.amount (held - Allocation.total (o.take k))) := by
  exact Allocation.payout_getElem? h

omit [DecidableEq E] in
/-- ForceMove-B07, Nitro-26, docs-0060-06. ForceMove:1812-1821: "paying out
    Alice first, allowing her to recover her funds even if Bob does not
    deposit." If a later entry receives anything, every earlier entry
    received its full amount. -/
theorem payout_earlier_paid_in_full (held : Coins) (o : Allocation E) (i j : Nat)
    (ei ej : Entry E) (pi pj : Coins) (hi : o[i]? = some ei) (hj : o[j]? = some ej) (hij : i < j)
    (hpi : (o.payout held)[i]? = some (ei.dest, pi))
    (hpj : (o.payout held)[j]? = some (ej.dest, pj)) (hpos : 0 < pj) :
    pi = ei.amount := by
  rw [Allocation.payout_getElem? hi] at hpi
  rw [Allocation.payout_getElem? hj] at hpj
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hpi hpj
  have h1 := Allocation.total_take_succ hi
  have h2 := Allocation.total_take_mono o (show i + 1 ≤ j by omega)
  (grind? says grind only [= min_def, #b75d, #d8a2, #b748, #0a27])

omit [DecidableEq E] in
/-- Nitro-26, Nitro-28, docs-0080-03. The payout never exceeds the coins
    held, and never pays an entry more than its amount. -/
theorem payout_bounded (held : Coins) (o : Allocation E) :
    ((o.payout held).map (·.2)).sum ≤ held ∧
    ∀ (i : Nat) (e : Entry E) (x : Coins), o[i]? = some e → (o.payout held)[i]? = some (e.dest, x) →
      x ≤ e.amount := by
  refine ⟨Allocation.payout_sum_le held o, fun i e x hi hx => ?_⟩
  rw [Allocation.payout_getElem? hi] at hx
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hx
  (grind? says grind only [= min_def, #b4a6])

/-- Nitro-25. Nitro:744-746: "ignoring any additional entries for a given
    address after the first." A destination receives at most the amount of
    its first entry. -/
theorem paidTo_first_entry_only (held : Coins) (o : Allocation E) (d : Address E) :
    o.paidTo held d ≤ o.owed d := by
  rw [Allocation.paidTo_eq_get, ← Allocation.owed_dedup]
  exact Allocation.payout_get_le_owed _ _ _

/-- Nitro-27, Nitro-16. Nitro:749-751: a channel that holds the whole total
    of its allocation affords every entry in full. -/
theorem affords_when_fully_funded (held : Coins) (o : Allocation E) (d : Address E)
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
    The hypothesis `hr` guards against the case
    (counterexample in Counter.lean): on an unreachable state the coins held
    can be fewer than the payout. -/
theorem transfer_effects (apps : Apps E) (s : ReachableState (Nitro.chain apps)) (a : FixedPart)
    (b : Address E) (s' : Adjudicator E)
    (h : s.state.transfer a b = some s') :
    ∃ o x, s.state.finalOutcome a.address = some (.allocation o) ∧
      x = o.paidTo (s.state.balances.get a.address) b ∧
      s'.balances.get a.address + x = s.state.balances.get a.address + (if b = a.address then x else 0) ∧
      (b ≠ a.address → s'.balances.get b = s.state.balances.get b + x) ∧
      (∀ d, d ≠ a.address → d ≠ b → s'.balances.get d = s.state.balances.get d) ∧
      s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) ∧
      s'.held + (if b.isExternal then x else 0) = s.state.held ∧ s'.now = s.state.now := by
  obtain_reach ⟨s, hr : Reachable apps s⟩ := s
  have hheld := (Adjudicator.inv_reachable hr).held
  obtain ⟨o, -, x, hf, -, hx, hb, hh, hs, hn, -, -⟩ := Adjudicator.transfer_some h
  have hxa : x ≤ s.balances.get a.address := hx ▸ Allocation.paidTo_le_held _ _ _
  have hle := Balances.get_le_sumIf (fun a => decide (a.isExternal = false)) s.balances
    (a := a.address) (by (simp? says simp only [FixedPart.address_eq, Address.isExternal_channel, decide_true]))
  rw [← Balances.channelTotal_eq_sumIf, ← hheld] at hle
  refine ⟨o, x, hf, hx, ?_, fun hba => ?_, fun d hda hdb => ?_, ?_, ?_, hn⟩
  · rw [hb]; (simp? at hxa ⊢ says simp only [FixedPart.address_eq, Balances.get_sub, ↓reduceIte, Balances.get_add] at hxa ⊢); split <;> grind
  · rw [hb]; (simp? at hba ⊢ says simp only [FixedPart.address_eq, ne_eq, Balances.get_sub, Balances.get_add, ↓reduceIte, ite_eq_right_iff] at hba ⊢); (simp? [hba] says simp only [hba, IsEmpty.forall_iff])
  · rw [hb]; (simp? at hda ⊢ says simp only [FixedPart.address_eq, ne_eq, Balances.get_sub, Balances.get_add] at hda ⊢); (simp? [hda, hdb] says simp only [hda, ↓reduceIte, hdb])
  · (simp? [Adjudicator.statusOf_of_status hs, hn] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus, ↓reduceIte, hn, ChannelStatus.finalOutcome_withOutcome])
  · rw [hh]
    split
    · (simp_all? says simp_all only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ↓reduceIte]); (grind? says grind only)
    · (simp_all? says simp_all only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true, add_zero])

/-- Nitro-28. The reduction of an owed amount is exact. -/
theorem reduceOwed_owed (o : Allocation E) (d : Address E) (x : Coins) :
    (o.reduceOwed d x).owed d = o.owed d - x ∧
    ∀ d', d' ≠ d → (o.reduceOwed d x).owed d' = o.owed d' := by
  refine ⟨by (simp? [Allocation.owed_reduceOwed] says simp only [Allocation.owed_reduceOwed, ↓reduceIte]), fun d' h => ?_⟩
  (simp? [Allocation.owed_reduceOwed, h] says simp only [Allocation.owed_reduceOwed, h, ↓reduceIte])

/-- Nitro-28, Nitro-15, ForceMove-C03, docs-0080-06. go-nitro: a transfer on
    a finalized channel with an allocation entry for `b` succeeds, and pays
    the whole affordable amount (MultiAssetHolder.sol:66). The exact result
    is stated. Channel types (`ChannelKind`):
    `a` must be a ledger channel and `b`, if a channel, must be too. -/
theorem transfer_can_happen (s : Adjudicator E) (a : FixedPart) (b : Address E) (o : Allocation E)
    (amt : Coins) (ha : a.kind = .ledger) (hbf : b.fundable = true)
    (hf : s.finalOutcome a.address = some (.allocation o))
    (hb : o.find b = some ⟨b, .alloc amt⟩) :
    ∃ s', s.transfer a b = some s' ∧
      s'.balances.get b = s.balances.get b +
        (if b = a.address then 0 else o.paidTo (s.balances.get a.address) b) := by
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
  have ht : s.transfer a b = some ((((s.setStatus a ((s.statusOf a).withOutcome (.allocation
      (o.reduceOwed b (o.paidTo (s.balances.get a.address) b))))).payTo b
        (o.paidTo (s.balances.get a.address) b))) |> fun s' =>
        { s' with balances := s'.balances.sub a.address (o.paidTo (s.balances.get a.address) b) }) := by
    unfold Adjudicator.transfer
    rw [if_pos (⟨ha, hbf⟩ : a.kind = .ledger ∧ b.fundable = true)]
    simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hf, hb]
  refine ⟨_, ht, ?_⟩
  simp only [Balances.get_sub, Adjudicator.payTo_balances, Adjudicator.setStatus_balances,
    Balances.get_add, FixedPart.address_eq]
  by_cases hba : b = .channel a
  · subst hba; (simp? says simp only [↓reduceIte, add_tsub_cancel_right, add_zero])
  · (simp? [hba] says simp only [hba, ↓reduceIte, Nat.add_left_cancel_iff])

/-- Nitro-29, ForceMove-A20, docs-0030-04. Nitro:771-772: "If A cannot afford
    x for B, then T(A, B, x) fails, leaving the on-chain state unchanged."
    go-nitro: the transfer pays what is affordable; it reverts when the
    channel is not finalized, when `b` has no entry, or when the entry is a
    guarantee ("cannot transfer a guarantee", MultiAssetHolder.sol:172). -/
theorem transfer_fails_otherwise (s : Adjudicator E) (a : FixedPart) (b : Address E)
    (h : ∀ o, s.finalOutcome a.address = some (.allocation o) →
      ∀ amt, o.find b ≠ some ⟨b, .alloc amt⟩) :
    s.transfer a b = none := by
  cases ht : s.transfer a b with
  | none => rfl
  | some s' =>
    obtain ⟨o, amt, -, hf, hfind, -⟩ := Adjudicator.transfer_some ht
    exact absurd hfind (h o hf amt)

/-- Nitro-29. When `a` affords nothing for `b`, the transfer moves no coins.
    Every balance reads the same; the list itself can change (`add b 0`
    writes an entry). This is checked (counterexample in
    Counter.lean). -/
theorem transfer_zero_moves_nothing (s : Adjudicator E) (a : FixedPart) (b : Address E)
    (s' : Adjudicator E) (h : s.transfer a b = some s')
    (h0 : ∀ o, s.finalOutcome a.address = some (.allocation o) →
      o.paidTo (s.balances.get a.address) b = 0) :
    (∀ d, s'.balances.get d = s.balances.get d) ∧ s'.held = s.held := by
  obtain ⟨o, _, x, hf, -, hx, hb, hh, -, -⟩ := Adjudicator.transfer_some h
  have hx0 : x = 0 := hx ▸ h0 o hf
  subst hx0
  refine ⟨fun d => ?_, by rw [hh]; (simp? says simp only [tsub_zero, ite_self])⟩
  rw [hb]
  simp only [Balances.get_sub, Balances.get_add, Nat.sub_zero, Nat.add_zero]
  by_cases hd : d = a.address
  · subst hd; simp only [if_true]; split <;> (simp_all? says simp_all only [FixedPart.address_eq, Adjudicator.finalOutcome_channel])
  · simp only [hd, if_false]; split <;> (simp_all? says simp_all only [FixedPart.address_eq, Adjudicator.finalOutcome_channel])

/-- Nitro-10, ForceMove-A15, SATP-16, docs-0080-01. go-nitro
    `_requireChannelFinalized` (MultiAssetHolder.sol:127); Nitro:261-266:
    redistribution reads a finalized outcome; ForceMove:1725-1728. A transfer
    succeeds only on a finalized channel. -/
theorem transfer_requires_finalized (s : Adjudicator E) (a : FixedPart) (b : Address E)
    (s' : Adjudicator E) (h : s.transfer a b = some s') : s.mode a = .finalized := by
  obtain ⟨o, -, -, hf, -⟩ := Adjudicator.transfer_some h
  rw [Adjudicator.mode_eq, ChannelStatus.mode_eq_finalized_iff]
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
  (simp? [hf] says simp only [hf, Option.isSome_some])

/-- Nitro-15. Nitro:312-313: "There is no restriction on who can trigger the
    operations." go-nitro `transfer` and `reclaim` read no caller. A
    redistribution gives the same result for every caller. -/
theorem redistribution_ignores_caller (apps : Apps E) (s : Adjudicator E) (op : Op E)
    (c1 c2 : Participant) (h : op.isRedistribution = true) :
    s.apply apps c1 op = s.apply apps c2 op := by
  cases op <;> first | rfl | (simp? [Op.isRedistribution] at h says simp only [Op.isRedistribution, Bool.false_eq_true] at h)

/-- Nitro-08. A redistribution moves coins between balances. The sum of all
    balances (held plus paid out) is unchanged. The hypothesis `hr` guards against the case (counterexample in Counter.lean): on an
    unreachable state an address can have two entries, or the coins held
    can be fewer than the payout. -/
theorem redistribution_conserves_total (apps : Apps E) (s : ReachableState (Nitro.chain apps)) (s' : Adjudicator E)
    (caller : Participant)
    (op : Op E) (hop : op.isRedistribution = true) (h : s.state.apply apps caller op = some s') :
    s'.balances.total = s.state.balances.total ∧
    s'.held + s'.balances.paidOutTotal = s.state.held + s.state.balances.paidOutTotal := by
  obtain_reach ⟨s, hr : Reachable apps s⟩ := s
  exact (Adjudicator.inv_reachable hr).conserves hop h

/-- Nitro-11, ForceMove-B03, SATP-16, docs-0070-04, ForceMove-A14.
    SATP:284-292: assets are released on explicit consent (conclude) or
    after a challenge timeout; Nitro:288-290: "There are two ways for an
    outcome to become finalized: (i) through a challenge that times out
    before anyone responds, and (ii) through the registration of a conclusion
    proof." go-nitro: only `challenge` and `_conclude` write a nonzero
    finalization time. A finalized outcome traces to one such step, and has only
    been redistributed since. -/
theorem finalized_two_ways (apps : Apps E) (s : ReachableState (Nitro.chain apps)) (c : FixedPart) (Ω : Outcome E)
    (hf : s.state.finalOutcome c.address = some Ω) :
    ∃ s0 s1 caller, Reachable apps s0 ∧
      ((∃ ss, s0.apply apps caller (.conclude c ss) = some s1 ∧ ConclusionProof c ss ∧
          Redistributed ss.state.outcome Ω) ∨
       (∃ proof candidate, s0.apply apps caller (.challenge c proof candidate) = some s1 ∧
          s0.now + c.challengeDuration ≤ s.state.now ∧ Redistributed candidate.outcome Ω)) := by
  obtain_reach ⟨s, hr : Reachable apps s⟩ := s
  exact (Adjudicator.inv_reachable hr).twoWays c Ω hf

/-- Nitro-14, ForceMove-A14, ForceMove-D12. Nitro:301-302: "the rules of
    operation only allow one outcome to be finalized for each channel."
    go-nitro: every status write in `challenge`, `checkpoint` and
    `_conclude` is guarded by a not-finalized check. Once finalized, a
    channel stays finalized. -/
theorem finalized_permanent (apps : Apps E) (s s' : Adjudicator E) (c : FixedPart)
    (h : Step apps s s') (hf : s.mode c = .finalized) : s'.mode c = .finalized := by
  cases h with
  | mk caller op _ _ h =>
  rw [Adjudicator.mode_eq] at hf ⊢
  have hn := Adjudicator.apply_now_le h
  rcases Adjudicator.statusOf_step h c with
    heq | ⟨_, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, heq⟩ |
    ⟨proof, cand, hch, heq⟩ | ⟨proof, cand, hcp, heq⟩ | ⟨ss, hcl, heq⟩
  · rw [heq]; exact ChannelStatus.mode_finalized_mono hf hn
  · rw [heq]; exact ChannelStatus.mode_withOutcome _ _ _
  · rw [heq]; exact ChannelStatus.mode_withOutcome _ _ _
  · obtain ⟨⟨-, -, -, hm⟩, -⟩ := Adjudicator.challenge_some hch
    rw [Adjudicator.mode_eq] at hm
    rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hf <;> cases hf
  · obtain ⟨⟨ho, -⟩, -⟩ := Adjudicator.checkpoint_some hcp
    exact absurd hf ho
  · rw [heq]; rfl

/-- Nitro-14. A finalized outcome is never replaced by a second
    finalization. Every later outcome of the channel is a redistribution of
    the first. -/
theorem finalized_outcome_only_redistributed (apps : Apps E) (s s' : Adjudicator E) (c : FixedPart)
    (Ω : Outcome E) (h : Step apps s s') (hf : s.finalOutcome c.address = some Ω) :
    ∃ Ω', s'.finalOutcome c.address = some Ω' ∧ Redistributed Ω Ω' := by
  cases h with
  | mk caller op _ _ h =>
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf ⊢
  have hn := Adjudicator.apply_now_le h
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf]; rfl
  rcases Adjudicator.statusOf_step h c with
    heq | ⟨o, b, x, hf', heq⟩ | ⟨oL, left, x1, right, x2, rm, hL, heq⟩ |
    ⟨proof, cand, hch, heq⟩ | ⟨proof, cand, hcp, heq⟩ | ⟨ss, hcl, heq⟩
  · exact ⟨Ω, by rw [heq]; exact ChannelStatus.finalOutcome_mono hf hn, Relation.ReflTransGen.refl⟩
  · rw [hf] at hf'
    cases hf'
    exact ⟨_, by rw [heq]; exact ChannelStatus.finalOutcome_withOutcome _ _ _,
      Relation.ReflTransGen.single (RedistributeStep.reduce o b x)⟩
  · rw [hf] at hL
    cases hL
    exact ⟨_, by rw [heq]; exact ChannelStatus.finalOutcome_withOutcome _ _ _,
      Relation.ReflTransGen.single (RedistributeStep.reclaim oL left right rm x1 x2)⟩
  · obtain ⟨⟨-, -, -, hm⟩, -⟩ := Adjudicator.challenge_some hch
    rw [Adjudicator.mode_eq] at hm
    rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hfin <;> cases hfin
  · obtain ⟨⟨ho, -⟩, -⟩ := Adjudicator.checkpoint_some hcp
    exact absurd hfin ho
  · obtain ⟨⟨ho, -⟩, -⟩ := Adjudicator.conclude_some hcl
    exact absurd hfin ho

omit [DecidableEq E] in
/-- ForceMove-A10, ForceMove-A21, SATP-14, docs-0070-02, docs-0070-03.
    go-nitro ForceMove.sol:46-60: in Open mode the turn must not decrease,
    in (Challenge E) mode it must increase, in Finalized mode the call reverts;
    the app must support the candidate; the challenger must be a
    participant. SATP:303-305 (`isOpen`, `version >=`) is corrected by the
    strict check in (Challenge E) mode. ForceMove:1340-1354 forbids a challenge
    while one runs; the code allows one at a higher turn. -/
theorem challenge_requires (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) (s' : Adjudicator E)
    (h : s.challenge apps challenger c proof candidate = some s') :
    challenger ∈ c.participants ∧
    (apps c.appDef).supports c proof candidate = true ∧ candidate.channel = c ∧
    ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
     (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum)) := by
  exact (Adjudicator.challenge_some h).1

omit [DecidableEq E] in
/-- SATP-14. go-nitro ForceMove.sol:52-54 and SATP:303: a challenge on a
    finalized channel fails. -/
theorem challenge_fails_when_finalized (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) (hf : s.mode c = .finalized) :
    s.challenge apps challenger c proof candidate = none := by
  cases hc : s.challenge apps challenger c proof candidate with
  | none => rfl
  | some s' =>
    obtain ⟨⟨-, -, -, hm⟩, -⟩ := Adjudicator.challenge_some hc
    rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hf <;> cases hf

omit [DecidableEq E] in
/-- SATP-14. go-nitro ForceMove.sol:48-50 `_requireIncreasedTurnNumber`: a
    re-challenge at an equal turn during a running challenge fails. SATP
    Listing 1 would accept it and reset the deadline; the code is followed. -/
theorem rechallenge_equal_turn_fails (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) (hm : s.mode c = .challenge)
    (ht : candidate.turnNum ≤ (s.statusOf c).turnNumRecord) :
    s.challenge apps challenger c proof candidate = none := by
  cases hc : s.challenge apps challenger c proof candidate with
  | none => rfl
  | some s' =>
    obtain ⟨⟨-, -, -, hm'⟩, -⟩ := Adjudicator.challenge_some hc
    rcases hm' with ⟨hm', -⟩ | ⟨-, hlt⟩
    · rw [hm] at hm'; cases hm'
    · omega

omit [DecidableEq E] in
/-- ForceMove-A10, ForceMove-C02, ForceMove-F03, Nitro-12, SATP-14,
    docs-0070-08. go-nitro ForceMove.sol:70-76: the status becomes the
    candidate's turn with deadline `block.timestamp + challengeDuration`;
    SATP:308-310; ForceMove:1353. The exact result. -/
theorem challenge_can_happen (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E)
    (hp : challenger ∈ c.participants)
    (hs : (apps c.appDef).supports c proof candidate = true) (hc : candidate.channel = c)
    (ht : (s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ candidate.turnNum) ∨
      (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < candidate.turnNum)) :
    s.challenge apps challenger c proof candidate = some
      (s.setStatus c (.challenged candidate.turnNum ⟨candidate, s.now + c.challengeDuration⟩)) := by
  have hpre : s.ChallengePre apps challenger c proof candidate := ⟨hp, hs, hc, ht⟩
  classical
  have heq : s.challenge apps challenger c proof candidate =
      (if h : s.ChallengePre apps challenger c proof candidate then
        some (s.challengeEffect apps challenger c proof ⟨candidate, h⟩) else none) :=
    Adjudicator.apply_challenge_equation apps challenger c proof candidate s
  rw [heq, dif_pos hpre]
  rfl

omit [DecidableEq E] in
/-- ForceMove-D12, ForceMove-B04, SATP-14. A fresh challenge with a positive
    duration puts the channel in challenge mode. (Balances E), coins held and
    the clock do not move. -/
theorem challenge_effects (apps : Apps E) (s : Adjudicator E) (challenger : Participant)
    (c : FixedPart) (proof : SupportProof E) (candidate : State E) (s' : Adjudicator E)
    (h : s.challenge apps challenger c proof candidate = some s') (hd : 0 < c.challengeDuration) :
    s'.mode c = .challenge ∧ s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now ∧
    ∀ c', c' ≠ c → s'.statusOf c' = s.statusOf c' := by
  obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
  refine ⟨?_, rfl, rfl, rfl, fun c' hc' => by (simp? [hc'] says simp only [Adjudicator.statusOf_setStatus, hc', ↓reduceIte])⟩
  rw [Adjudicator.mode_eq]
  (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.mode_challenged, add_le_iff_nonpos_right, nonpos_iff_eq_zero, ite_eq_right_iff, reduceCtorEq, imp_false])
  (grind? says grind only)

omit [DecidableEq E] in
/-- ForceMove-A11, ForceMove-A12, ForceMove-A13, ForceMove-B02, ForceMove-A21,
    docs-0070-10. go-nitro ForceMove.sol:91-100 `checkpoint`: the channel is
    not finalized, the turn is strictly higher than the record, the app
    supports the candidate. ForceMove:1431-1440 `respondWithMove` and
    ForceMove:1377-1381 ("each of these responses lead to an increase in the
    turnNum") are superseded by it; SATP has no such operation. -/
theorem checkpoint_requires (apps : Apps E) (s : Adjudicator E) (c : FixedPart) (proof : SupportProof E)
    (candidate : State E) (s' : Adjudicator E) (h : s.checkpoint apps c proof candidate = some s') :
    s.mode c ≠ .finalized ∧ (apps c.appDef).supports c proof candidate = true ∧
    candidate.channel = c ∧ (s.statusOf c).turnNumRecord < candidate.turnNum := by
  exact (Adjudicator.checkpoint_some h).1

omit [DecidableEq E] in
/-- ForceMove-A18, ForceMove-B04, ForceMove-A21, docs-0070-10. go-nitro
    ForceMove.sol:104-113: the status becomes Open at the candidate's turn
    and a running challenge is cleared (`ChallengeCleared`).
    ForceMove:1266-1269: "If a valid response is received, the game returns
    to the Collaborative mode"; ForceMove:1765-1770 `cancelChallenge`. -/
theorem checkpoint_can_happen (apps : Apps E) (s : Adjudicator E) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E) (hm : s.mode c ≠ .finalized)
    (hs : (apps c.appDef).supports c proof candidate = true) (hc : candidate.channel = c)
    (ht : (s.statusOf c).turnNumRecord < candidate.turnNum) :
    s.checkpoint apps c proof candidate = some (s.setStatus c (.open candidate.turnNum)) ∧
    (s.setStatus c (.open candidate.turnNum)).mode c = .open := by
  have hpre : s.CheckpointPre apps c proof candidate := ⟨hm, hs, hc, ht⟩
  classical
  have heq : s.checkpoint apps c proof candidate =
      (if hp : s.CheckpointPre apps c proof candidate then
        some (s.checkpointEffect apps c proof ⟨candidate, hp⟩) else none) :=
    Adjudicator.apply_checkpoint_equation apps ⟨0⟩ c proof candidate s
  refine ⟨?_, by rw [Adjudicator.mode_eq]; (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.mode_open])⟩
  rw [heq, dif_pos hpre]; rfl

/-- ForceMove-B02, ForceMove-A21, docs-0070-03, docs-0040-03. go-nitro
    `_requireNonDecreasedTurnNumber` and `_requireIncreasedTurnNumber`
    (ForceMove.sol); ForceMove:1543-1545: "Only allow new force-moves if
    their response will increase this stored turnNum." No step lowers the
    stored turn number of a channel, except a conclude of that channel,
    which finalizes it in the same step: `Adjudicator.conclude` has no turn
    check and stores the candidate's turn (go-nitro stores 0). This is checked
    (counterexample in Counter.lean). -/
theorem turnNumRecord_monotone (apps : Apps E) (s s' : Adjudicator E) (c : FixedPart)
    (h : Step apps s s') :
    (s.statusOf c).turnNumRecord ≤ (s'.statusOf c).turnNumRecord ∨
    ∃ caller ss, s.apply apps caller (.conclude c ss) = some s' ∧ s'.mode c = .finalized := by
  cases h with
  | mk caller op _ _ h =>
  rcases Adjudicator.statusOf_step h c with
    heq | ⟨o, b, x, _, heq⟩ | ⟨oL, left, x1, right, x2, rm, _, heq⟩ |
    ⟨proof, cand, hch, heq⟩ | ⟨proof, cand, hcp, heq⟩ | ⟨ss, hcl, heq⟩
  · exact Or.inl (congrArg ChannelStatus.turnNumRecord heq).ge
  · refine Or.inl ?_
    rw [heq]
    exact (ChannelStatus.turnNumRecord_withOutcome _ _).ge
  · refine Or.inl ?_
    rw [heq]
    exact (ChannelStatus.turnNumRecord_withOutcome _ _).ge
  · refine Or.inl ?_
    rw [heq]
    simp only [ChannelStatus.turnNumRecord_challenged]
    obtain ⟨-, -, -, hm⟩ := (Adjudicator.challenge_some hch).1
    rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩ <;> omega
  · refine Or.inl ?_
    rw [heq]
    simp only [ChannelStatus.turnNumRecord_open]
    obtain ⟨-, -, -, ht⟩ := (Adjudicator.checkpoint_some hcp).1
    omega
  · exact Or.inr ⟨caller, ss, hcl, by rw [Adjudicator.mode_eq, heq]; rfl⟩

omit [DecidableEq E] in
/-- ForceMove-A14, Nitro-13, SATP-16, docs-0070-01, docs-0010-05. go-nitro
    ForceMove.sol:142-152: a conclude needs a non-finalized channel, a final
    candidate and unanimous signatures; the application is not consulted.
    SATP:288-289: "supporting a state with isFinal = true";
    ForceMove:1495-1500. -/
theorem conclude_requires (s : Adjudicator E) (c : FixedPart) (ss : SignedState E) (s' : Adjudicator E)
    (h : s.conclude c ss = some s') :
    s.mode c ≠ .finalized ∧ ss.state.channel = c ∧ ss.state.isFinal = true ∧ ss.ByAll := by
  exact (Adjudicator.conclude_some h).1

omit [DecidableEq E] in
/-- ForceMove-A09, Nitro-13, SATP-08, SATP-16, docs-0070-01, docs-0020-01.
    go-nitro ForceMove.sol:147-152 `'!unanimous'`; Nitro:297-298: "all the
    participants sign a special conclude state, called a conclusion proof".
    A conclude carries one state signed by every participant, for every
    application. -/
theorem conclude_needs_all (s : Adjudicator E) (c : FixedPart) (ss : SignedState E) (s' : Adjudicator E)
    (h : s.conclude c ss = some s') (p : Participant) (hp : p ∈ c.participants) :
    p ∈ ss.signers := by
  obtain ⟨⟨-, hc, -, hall⟩, -⟩ := Adjudicator.conclude_some h
  exact hall p (hc ▸ hp)

omit [DecidableEq E] in
/-- ForceMove-A14, Nitro-13, SATP-16, docs-0070-09. go-nitro
    ForceMove.sol:155-163: the channel finalizes at `block.timestamp` with
    the candidate's outcome; Nitro:299-300: "the participants avoid having
    to wait for the challenge period"; ForceMove:1507. The exact result. -/
theorem conclude_can_happen (s : Adjudicator E) (c : FixedPart) (ss : SignedState E)
    (hm : s.mode c ≠ .finalized) (hproof : ConclusionProof c ss) :
    s.conclude c ss =
      some (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)) ∧
    (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)).finalOutcome
      c.address = some ss.state.outcome ∧
    (s.setStatus c (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)).mode c =
      .finalized := by
  have hpre : s.ConcludePre c ss := ⟨hm, hproof⟩
  classical
  have heq : s.conclude c ss =
      (if h : s.ConcludePre c ss then some (s.concludeEffect c ⟨ss, h⟩) else none) :=
    Adjudicator.apply_conclude_equation (fun _ => ⟨fun _ _ _ => false⟩) ⟨0⟩ c ss s
  refine ⟨?_, by (simp? says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_finalized]), by rw [Adjudicator.mode_eq]; (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.mode_finalized])⟩
  rw [heq, dif_pos hpre]
  rfl

omit [DecidableEq E] in
/-- ForceMove-A04, ForceMove-A05, docs-0070-07. go-nitro `_conclude` writes
    only `statusOf`; ForceMove:976-980, 1017-1022: the conclude transition
    keeps the resolution. A conclude moves no coins. -/
theorem conclude_moves_no_value (s : Adjudicator E) (c : FixedPart) (ss : SignedState E)
    (s' : Adjudicator E) (h : s.conclude c ss = some s') :
    s'.balances = s.balances ∧ s'.held = s.held ∧ s'.now = s.now := by
  obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
  exact ⟨rfl, rfl, rfl⟩

omit [DecidableEq E] in
/-- ForceMove-B03, ForceMove-D12, Nitro-12, docs-0040-05, docs-0040-06.
    go-nitro StatusManager.sol:10-11: a finalization time at or before
    `block.timestamp` is Finalized; ForceMove:1260-1265: "If no response is received within the
    timeout period, the game transitions into the Terminated mode";
    ForceMove:449-453: "the resolution stored on the challenge state s will
    decide how the funds should be split." -/
theorem timeout_finalizes (s : Adjudicator E) (c : FixedPart) (t : Nat) (ch : Challenge E)
    (hs : s.statusOf c = .challenged t ch) (hd : ch.deadline ≤ s.now) :
    s.mode c = .finalized ∧ s.finalOutcome c.address = some ch.state.outcome := by
  (simp? [Adjudicator.mode_eq, hs, hd] says simp only [Adjudicator.mode_eq, hs, ChannelStatus.mode_challenged, hd, ↓reduceIte, FixedPart.address_eq, Adjudicator.finalOutcome_channel, ChannelStatus.finalOutcome_challenged, and_self])

omit [DecidableEq E] in
/-- ForceMove-D12. go-nitro StatusManager.sol:12-13: a future finalization
    time is (Challenge E) mode; ForceMove:1295 `inProgress: c ↦ c.endTime > now()`. -/
theorem challenge_in_progress_before_deadline (s : Adjudicator E) (c : FixedPart) (t : Nat)
    (ch : Challenge E) (hs : s.statusOf c = .challenged t ch) (hd : s.now < ch.deadline) :
    s.mode c = .challenge ∧ s.finalOutcome c.address = none := by
  (simp? [Adjudicator.mode_eq, hs, Nat.not_le.2 hd] says simp only [Adjudicator.mode_eq, hs, ChannelStatus.mode_challenged, Nat.not_le.2 hd, ↓reduceIte, FixedPart.address_eq, Adjudicator.finalOutcome_channel, ChannelStatus.finalOutcome_challenged, and_self])

omit [DecidableEq E] in
/-- ForceMove-F03, docs-0040-05. docs: "a passive transition which happens
    when a block is produced with a sufficiently large timestamp." The clock
    changes no balance and no status. -/
theorem tick_moves_only_time (s : Adjudicator E) (dt : Time) :
    (s.tick dt).balances = s.balances ∧ (s.tick dt).held = s.held ∧
    (s.tick dt).status = s.status ∧ (s.tick dt).now = s.now + dt := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- ForceMove-A20. go-nitro: a failed `require` reverts the transaction;
    ForceMove:685-686: "making an invalid move is equivalent to not making
    any move at all." A failed operation leaves the chain unchanged. -/
theorem failed_op_no_effect (apps : Apps E) (caller : Participant) (op : Op E) (s : Adjudicator E)
    (h : s.apply apps caller op = none) :
    Adjudicator.applyAll apps [(caller, op)] s = s := by
  (simp? [Adjudicator.applyAll, h] says simp only [Adjudicator.applyAll, h, Option.getD_none])

/-- ForceMove-F05. go-nitro ForceMove.sol reads no `holdings`;
    ForceMove:1609-1628: "there is no way of telling from the properties of
    the channel how (or even whether) the game is funded." The dispute
    operations read no balance: their success and their status result do
    not depend on the balances. -/
theorem funding_decoupled_from_rules (apps : Apps E) (caller : Participant) (s : Adjudicator E)
    (b : Balances E) (op : Op E) (hop : op.isRedistribution = false ∧ ∀ a e x, op ≠ .deposit a e x) :
    ((s.apply apps caller op).map Adjudicator.status) =
      (({ s with balances := b }.apply apps caller op).map Adjudicator.status) := by
  obtain ⟨h1, h2⟩ := hop
  cases op with
  | deposit a e x => exact absurd rfl (h2 a e x)
  | transfer a b => simp only [Op.isRedistribution] at h1; cases h1
  | reclaim l v => simp only [Op.isRedistribution] at h1; cases h1
  | _ =>
    simp only [Adjudicator.apply_challenge, Adjudicator.challenge, Adjudicator.apply_checkpoint,
      Adjudicator.checkpoint, Adjudicator.apply_conclude, Adjudicator.conclude, Adjudicator.mode,
      Adjudicator.statusOf, Adjudicator.setStatus, ne_eq, decide_not, Option.map_if,
      Adjudicator.apply_tick, Option.map_some, Adjudicator.tick_status]

/-- ForceMove-A01, ForceMove-A02, ForceMove-A03, ForceMove-D05, ForceMove-D06,
    ForceMove-D04 (ForceMove only; go-nitro StrictTurnTaking.sol is the same
    rule as a library). ForceMove:744-751 `validMove`: a valid transition
    whose signer is the mover; ForceMove:761-778: the channel is fixed and
    the turn number increments by one. Under the ForceMove rules a supported
    candidate ends a run of `n` such moves. -/
theorem forceMove_supports_valid_run (vt : State E → State E → Bool) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E)
    (h : (forceMoveRules vt).supports c proof candidate = true) :
    proof.length = c.n ∧
    (∀ (i : Nat) m1 m2, proof[i]? = some m1 → proof[i + 1]? = some m2 →
      m2.state.channel = m1.state.channel ∧ m2.state.turnNum = m1.state.turnNum + 1 ∧
      m2.ByMover ∧ (m2.state.isFinal = false → vt m1.state m2.state = true)) ∧
    (∃ m, proof.getLast? = some m ∧ m.state = candidate) := by
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlen, -⟩, hrun⟩, -⟩, hlast⟩ := h
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
theorem forceMove_conclude_keeps_outcome (vt : State E → State E → Bool) (c : FixedPart)
    (proof : SupportProof E) (candidate : State E)
    (h : (forceMoveRules vt).supports c proof candidate = true) (i : Nat) (m1 m2 : SignedState E)
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

/-- Every state of a `forceMoveRules` support proof is a state of `c`: the
    conjunct `proof.all (channel = c)` of `forceMoveRules.supports`. -/
theorem forceMove_supports_all_channel {vt : State E → State E → Bool} {c : FixedPart}
    {proof : SupportProof E} {candidate : State E}
    (h : (forceMoveRules vt).supports c proof candidate = true) :
    ∀ m ∈ proof, m.state.channel = c := by
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, -⟩ := h
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp hall m hm)

/-- The first state of a `forceMoveRules` support proof is signed by its
    mover: the conjunct `proof.head?.all byMover` of `forceMoveRules.supports`. -/
theorem forceMove_supports_head_byMover {vt : State E → State E → Bool} {c : FixedPart}
    {proof : SupportProof E} {candidate : State E}
    (h : (forceMoveRules vt).supports c proof candidate = true)
    {m0 : SignedState E} (h0 : proof[0]? = some m0) : m0.ByMover := by
  simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, hhead⟩, -⟩, -⟩, -⟩ := h
  have hm0 : proof.head? = some m0 := by
    cases proof with
    | nil => (simp? at h0 says simp only [List.length_nil, lt_self_iff_false, not_false_eq_true, getElem?_neg, reduceCtorEq] at h0)
    | cons a t => (simpa? using h0 says simpa only [List.head?_cons, Option.some.injEq, List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, List.getElem_cons_zero] using h0)
  rw [hm0] at hhead
  exact (SignedState.byMover_iff m0).1 hhead

/-- The turn number along a `forceMoveRules` support proof: the state `k`
    positions after position `i0` has the turn of position `i0` plus `k`
    (`UniversalTransition`). -/
theorem forceMove_fwd_turnNum {vt : State E → State E → Bool} {c : FixedPart}
    {proof : SupportProof E} {candidate : State E}
    (h : (forceMoveRules vt).supports c proof candidate = true)
    {i0 : Nat} {m0 : SignedState E} (h0 : proof[i0]? = some m0) :
    ∀ k, i0 + k < proof.length → ∃ mk : SignedState E, proof[i0 + k]? = some mk ∧
      mk.state.turnNum = m0.state.turnNum + k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨m0, by (simpa? using h0 says simpa only [add_zero] using h0), by (simp? says simp only [add_zero])⟩
  | succ k ih =>
    intro hlt
    obtain ⟨mk, hmk, hturn⟩ := ih (by omega)
    obtain ⟨mk1, hmk1⟩ : ∃ mk1, proof[(i0 + k) + 1]? = some mk1 :=
      ⟨proof[(i0 + k) + 1], List.getElem?_eq_getElem hlt⟩
    have hstep := (forceMove_supports_valid_run vt c proof candidate h).2.1 (i0 + k) mk mk1 hmk hmk1
    exact ⟨mk1, hmk1, by rw [hstep.2.1, hturn]; rfl⟩

omit [DecidableEq E] in
/-- A state signed by its mover carries the signature of its mover. -/
theorem SignedState.ByMover.signer_of_mover {ss : SignedState E} (hbm : ss.ByMover)
    {p : Participant} (hmv : ss.state.mover = some p) : p ∈ ss.signers := by
  obtain ⟨m, hm, hms⟩ := hbm
  rw [hmv] at hm
  cases hm
  exact hms

/-- A `forceMoveRules` support proof carries, at some position, a state of
    `c` whose mover is `p` and which `p` signed: its `c.n` consecutive turns
    cover every participant once (`turn_mod_exists`). -/
theorem forceMove_mover_pos {vt : State E → State E → Bool} {c : FixedPart}
    {proof : SupportProof E} {candidate : State E}
    (h : (forceMoveRules vt).supports c proof candidate = true)
    {p : Participant} (hp : p ∈ c.participants) :
    ∃ i, i < proof.length ∧ ∃ mi : SignedState E, proof[i]? = some mi ∧
      mi.state.channel = c ∧ mi.state.mover = some p ∧ p ∈ mi.signers := by
  have hn : 0 < c.n := List.length_pos_of_mem hp
  have hlen : proof.length = c.n := (forceMove_supports_valid_run vt c proof candidate h).1
  obtain ⟨m0, h0⟩ : ∃ m0, proof[0]? = some m0 :=
    ⟨proof[0], List.getElem?_eq_getElem (by rw [hlen]; exact hn)⟩
  obtain ⟨k, hk_get⟩ := List.mem_iff_getElem?.mp hp
  have hk_lt : k < c.n := (List.getElem?_eq_some_iff.mp hk_get).1
  obtain ⟨i0, hi0lt, hmodeq⟩ := turn_mod_exists c.n m0.state.turnNum k hn hk_lt
  obtain ⟨mi, hmi, hturn⟩ := forceMove_fwd_turnNum h h0 i0 (by rw [hlen, Nat.zero_add]; exact hi0lt)
  rw [Nat.zero_add] at hmi
  have hchan : mi.state.channel = c :=
    forceMove_supports_all_channel h mi (List.mem_of_getElem? hmi)
  have hmv : mi.state.mover = some p := by
    unfold State.mover
    rw [hchan, hturn, hmodeq]
    exact hk_get
  refine ⟨i0, by rw [hlen]; exact hi0lt, mi, hmi, hchan, hmv, ?_⟩
  cases i0 with
  | zero =>
    have heq : mi = m0 := Option.some.inj (hmi.symm.trans h0)
    subst heq
    exact (forceMove_supports_head_byMover h h0).signer_of_mover hmv
  | succ j =>
    obtain ⟨mprev, hmprev, -⟩ :=
      forceMove_fwd_turnNum h h0 j (by rw [hlen, Nat.zero_add]; exact Nat.lt_of_succ_lt hi0lt)
    rw [Nat.zero_add] at hmprev
    exact ((forceMove_supports_valid_run vt c proof candidate h).2.1 j mprev mi hmprev hmi).2.2.1.signer_of_mover hmv

omit [DecidableEq E] in
/-- ForceMove-D05, ForceMove-D06 (ForceMove only). ForceMove:724-727: "the
    mover is fully determined by the turn number". -/
theorem mover_determined_by_turn (s t : State E) (hc : s.channel = t.channel)
    (ht : s.turnNum = t.turnNum) : s.mover = t.mover := by
  unfold State.mover
  rw [hc, ht]

omit [DecidableEq E] in
/-- ForceMove-D06 (ForceMove only). ForceMove:725-727: "players must take
    turns in a cyclical order." The mover of turn `k + n` is the mover of
    turn `k`. -/
theorem mover_cyclic (s : State E) (k : Nat) :
    { s with turnNum := k + s.channel.n }.mover = { s with turnNum := k }.mover := by
  (simp? [State.mover, Nat.add_mod_right] says simp only [State.mover, Nat.add_mod_right])

/-- SATP-15, docs-0030-04. SATP:348-352 and go-nitro
    MultiAssetHolder.sol:262-300: a reclaim needs both channels finalized
    and a guarantee entry for the target in the ledger's outcome. go-nitro
    adds: `left` and `right` have entries in the ledger (lines 363-364) and
    the target's first two amounts sum to the guarantee amount (line 365).
    Channel types (`ChannelKind`): `l` is a
    ledger channel and `v` is virtual. `v`'s outcome is read as the outcome
    it finalized with (SATP §2.4 SATP:335-338). -/
theorem reclaim_requires (s : Adjudicator E) (l v : FixedPart) (s' : Adjudicator E)
    (h : s.reclaim l v = some s') :
    s.mode l = .finalized ∧ s.mode v = .finalized ∧ l.kind = .ledger ∧ v.kind = .virtual ∧
    ∃ oL oV x left right, s.finalOutcome l.address = some (.allocation oL) ∧
      s.finalizedWith v.address = some (.allocation oV) ∧
      oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩ ∧
      (oL.remove v.address).find left ≠ none ∧ (oL.remove v.address).find right ≠ none ∧
      oV.amountAt 0 + oV.amountAt 1 = x := by
  obtain ⟨oL, oV, x, left, right, hL, hV, hg, hl, hr, hx, -, hkl, hkv⟩ := Adjudicator.reclaim_some h
  refine ⟨?_, ?_, hkl, hkv, oL, oV, x, left, right, hL, hV, hg, hl, hr, hx⟩
  · simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hL
    rw [Adjudicator.mode_eq, ChannelStatus.mode_eq_finalized_iff, hL]; rfl
  · have hVsome : ((s.statusOf v).finalizedWith s.now).isSome := by
      simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hV
      rw [hV]; rfl
    rw [Adjudicator.mode_eq, ChannelStatus.mode_eq_finalized_iff,
      ← ChannelStatus.finalizedWith_isSome_iff]
    exact hVsome

/-- SATP-15, docs-0080-05. SATP:358-363 and go-nitro
    `compute_reclaim_effects`: `o_ledger[left] += o_target[0]`,
    `o_ledger[right] += o_target[1]`, the guarantee entry is deleted. The
    balances do not move. The total of the ledger outcome is unchanged
    (go-nitro line 365: `totalReclaimed == guarantee.amount`). The
    hypotheses `hne` and `hdedup` guard against the case (counterexample in Counter.lean): a ledger that guarantees itself, or a
    ledger with a second entry for `v` (Nitro-25: each address appears
    once), breaks the statement. `v`'s outcome is read as the outcome it
    finalized with (SATP §2.4). -/
theorem reclaim_effects (s : Adjudicator E) (l v : FixedPart) (s' : Adjudicator E)
    (oL oV : Allocation E) (x : Coins) (left right : Address E)
    (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalizedWith v.address = some (.allocation oV))
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
  obtain ⟨oL0, oV0, x0, left0, right0, hL0, hV0, hg0, hl, hr, hx, rfl, -, -⟩ := Adjudicator.reclaim_some h
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
    by (simp? says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_withOutcome]), ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · rw [Allocation.owed_remove_of_ne _ hlv, Allocation.owed_addTo_of_ne _ _ hlr,
      Allocation.owed_addTo_self _ hl]
  · rw [Allocation.owed_remove_of_ne _ hrv, Allocation.owed_addTo_self _ hr1,
      Allocation.owed_addTo_of_ne _ _ hrl]
  · rw [Allocation.find_remove, if_pos rfl]
  · (grind? says grind only)
  · (simp? [Ne.symm hne] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, Ne.symm hne, ↓reduceIte, Adjudicator.setStatus_now])

/-- SATP-15, docs-0080-05. The reclaim succeeds whenever its preconditions
    hold. The exact result is stated. -/
theorem reclaim_can_happen (s : Adjudicator E) (l v : FixedPart) (oL oV : Allocation E) (x : Coins)
    (left right : Address E) (hkl : l.kind = .ledger) (hkv : v.kind = .virtual)
    (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalizedWith v.address = some (.allocation oV))
    (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩)
    (hl : (oL.remove v.address).find left ≠ none) (hr : (oL.remove v.address).find right ≠ none)
    (hx : oV.amountAt 0 + oV.amountAt 1 = x) :
    s.reclaim l v = some (s.setStatus l ((s.statusOf l).withOutcome
      (.allocation ((((oL.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1))).remove
        v.address)))) := by
  classical
  have hsrc : s.reclaimSource? l v = some ⟨oL, oV, left, right⟩ := by
    simp only [Adjudicator.reclaimSource?, hL, hV, hg, hl, hr, hx, ne_eq, not_false_eq_true,
      and_self, ↓reduceIte]
  have hpre : s.ReclaimPre l v := ⟨hkl, hkv, by (simp? [hsrc] says simp only [hsrc, Option.isSome_some])⟩
  have hget : (s.reclaimSource? l v).get hpre.2.2 = ⟨oL, oV, left, right⟩ := by
    (simp? [hsrc] says simp only [hsrc, Option.get_some])
  have heq : s.reclaim l v =
      (if hp : s.ReclaimPre l v then some (s.reclaimEffect v ⟨l, hp⟩) else none) :=
    Adjudicator.apply_reclaim_equation (fun _ => ⟨fun _ _ _ => false⟩) ⟨0⟩ l v s
  rw [heq, dif_pos hpre]
  congr 1
  unfold Adjudicator.reclaimEffect
  rw [hget]

/-- SATP-15. go-nitro MultiAssetHolder.sol:363-365: a reclaim whose `left`
    or `right` has no ledger entry, or whose target amounts do not sum to
    the guarantee amount, fails. SATP Listing 2 has no such checks; the code
    is followed. -/
theorem reclaim_fails_without_entries (s : Adjudicator E) (l v : FixedPart) (oL oV : Allocation E)
    (x : Coins) (left right : Address E) (hL : s.finalOutcome l.address = some (.allocation oL))
    (hV : s.finalizedWith v.address = some (.allocation oV))
    (hg : oL.find v.address = some ⟨v.address, .guarantee x [left, right]⟩)
    (hbad : (oL.remove v.address).find left = none ∨ (oL.remove v.address).find right = none ∨
      oV.amountAt 0 + oV.amountAt 1 ≠ x) :
    s.reclaim l v = none := by
  cases hc : s.reclaim l v with
  | none => rfl
  | some s' =>
    obtain ⟨oL0, oV0, x0, left0, right0, hL0, hV0, hg0, hl, hr, hx, -, -, -⟩ :=
      Adjudicator.reclaim_some hc
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

omit [DecidableEq E] in
/-- SATP-13, docs-0040-02. SATP:294-298 `isOpen`: "the channel has no active
    challenge or the channel has not yet finalized"; go-nitro
    StatusManager.sol:5-14. -/
theorem isOpen_iff (st : ChannelStatus E) (now : Time) :
    st.IsOpen now ↔ (st.mode now = .open ∨ st.mode now = .challenge) := by
  unfold ChannelStatus.IsOpen
  cases st.mode now <;> simp

omit [DecidableEq E] in
/-- ForceMove-D11, Nitro-11. Every channel is in exactly one mode. A channel
    with no record is open (go-nitro: an empty status unpacks to a zero
    finalization time). -/
theorem mode_of_absent (s : Adjudicator E) (c : FixedPart) (h : ∀ e ∈ s.status, e.1 ≠ c) :
    s.mode c = .open ∧ (s.statusOf c).turnNumRecord = 0 := by
  have hl : s.status.lookup c = none := by
    simp only [List.lookup_eq_none_iff, bne_iff_ne, ne_eq]
    exact fun p hp hpc => h p hp hpc.symm
  have hs : s.statusOf c = .open 0 := by (simp? [Adjudicator.statusOf, hl] says simp only [Adjudicator.statusOf, hl, Option.getD_none])
  (simp? [Adjudicator.mode_eq, hs] says simp only [Adjudicator.mode_eq, hs, ChannelStatus.mode_open, ChannelStatus.turnNumRecord_open, and_self])

/-- Nitro-08, Nitro-05. Only a deposit raises the coins held and only a
    payout to a participant lowers them. -/
theorem held_changes_only_by_deposit_payout (apps : Apps E) (s s' : Adjudicator E)
    (caller : Participant) (op : Op E) (h : s.apply apps caller op = some s')
    (hne : s'.held ≠ s.held) :
    (∃ a e x, op = .deposit a e x) ∨ op.isRedistribution = true := by
  cases op with
  | deposit a e x => exact Or.inl ⟨a, e, x, rfl⟩
  | transfer a b => exact Or.inr rfl
  | reclaim l v => exact Or.inr rfl
  | _ => exact absurd (Adjudicator.apply_held_frame rfl h) hne

end ArmadaLean.Nitro
