/-
  Nitro protocol theorems: unbeatable strategies, finalizability, value
  algorithms, ledger and virtual channel constructions, and the SATP
  protocol guarantees. Not every proof is `sorry`; `docs/nitro-repair-2026-10-27.md`
  §3 and the README give each theorem's current proof status. Each doc comment cites
  the source lines and the property ids of `docs/nitro-theorems.md`. The repair of
  2026-10-27 (every changed type, with its reason) is `docs/nitro-repair-2026-10-27.md`.
-/
import ArmadaLean.Nitro.Safety
import ArmadaLean.Nitro.Reachable
import ArmadaLean.Types.Channel
import ArmadaLean.Types.Outcome
import ArmadaLean.Types.Reachable
import ArmadaLean.SpecTools
import ArmadaLean.Types.Satp
import ArmadaLean.Types.App
import Mathlib.Tactic.Says

namespace ArmadaLean.Nitro

variable {E : Type} [DecidableEq E]

/-- An honest move that signs no state: a reaction with no sends, or a wait. A strategy of
    such moves keeps `p`'s `sent` list, so it keeps every fact about what `p` signed
    (`HoldsVirtualSetup`). -/
def HonestMove.NoSend : HonestMove E → Prop
  | .react r => r.sends = []
  | .wait _ => True

/-- An honest move that does not let time pass. -/
def HonestMove.NoWait : HonestMove E → Prop
  | .wait _ => False
  | _ => True

/-- `Unbeatable` with no `wait` move: the goal is reached "instantly", with
    no challenge period (Nitro:1046-1047: "A was able to withdraw their funds
    instantly, without having to wait for the channel timeout"). -/
def UnbeatableNoWait (apps : Apps E) {p : Participant} (T : Threat E p)
    (G : NetworkState E p → Prop) (net : NetworkState E p) : Prop :=
  UnbeatableIn apps T HonestMove.NoWait G net

/-- ForceMove-A06, ForceMove-A07. ForceMove:1092-1125 and ForceMove:1150-1184: through the
    PreFundSetup and PostFundSetup phases (the first `2n` states) every
    transition keeps the resolution. -/
def SetupPhaseKeepsOutcome (vt : State E → State E → Bool) (c : FixedPart) : Prop :=
  ∀ s1 s2, vt s1 s2 = true → s1.channel = c → s1.turnNum + 1 < 2 * c.n → s2.outcome = s1.outcome

/-- ForceMove:1092-1125: the game library accepts every setup transition of
    `c` (one step up in turn, below the funding point, same outcome, not
    final). -/
def SetupPhaseAccepted (vt : State E → State E → Bool) (c : FixedPart) : Prop :=
  ∀ s1 s2, s1.channel = c → s2.channel = c → s2.turnNum = s1.turnNum + 1 → s2.turnNum < c.n →
    s2.outcome = s1.outcome → s2.isFinal = false → vt s1 s2 = true

/-- One on-chain step never lowers `c`'s fully-funded slack at an external
    destination `d`. If `c` is finalized with an allocation `o` whose total
    is covered by `c`'s balance (`ht`), and `o`'s own first entry for `d` is
    the `.alloc amt` item `hd` names, then after any one successful
    `Adjudicator.apply`, `c` is still finalized with some allocation `o'`
    whose total is still covered, `o'`'s own first entry for `d` is STILL an
    `.alloc` item (never removed — only `c`'s own channel entry is ever
    dropped, by a `reclaim`'s `remove`, and `d` is external, never a channel
    address — and never turned into a guarantee — a `reduceOwed` or `addTo`
    that touches it always rewrites it back to `.alloc`,
    `Allocation.find_reduceOwed`/`Allocation.find_addTo_self`), and "what
    `d` already holds, plus what that entry still owes" has not fallen. The
    only op that can move it is a `transfer` on `c` itself: paying `b`
    drops `c`'s stored amount owed to `b` by exactly what it adds to `b`'s
    balance, so the sum is unchanged whether `b = d` or not; a reclaim onto
    `c` only ever raises `d`'s entry (`addTo`, when `d ∈ {left, right}`),
    while conserving (never raising) `c`'s total
    (`Allocation.total_addTo_le` / `Allocation.total_remove_le`); every
    other op (a deposit, an unrelated transfer, or a reclaim elsewhere)
    does not touch `c`'s allocation or `d`'s balance at all; a challenge,
    checkpoint or conclude cannot even target an already-finalized `c`.
    Used by `directly_funded_pays` (`ArmadaLean/Nitro/Liveness.lean`). -/
theorem directly_funded_step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c : FixedPart} {o : Allocation E} {d : E} {amt : Coins}
    (hf : s.finalOutcome c.address = some (.allocation o))
    (ht : o.total ≤ s.balances.get c.address)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩)
    (h : s.apply apps caller op = some s') :
    ∃ o' amt', s'.finalOutcome c.address = some (.allocation o') ∧
      o'.total ≤ s'.balances.get c.address ∧
      o'.find (.external d) = some ⟨.external d, .alloc amt'⟩ ∧
      s.balances.get (.external d) + amt ≤ s'.balances.get (.external d) + amt' := by
  have hf0 : (s.statusOf c).finalOutcome s.now = some (.allocation o) := by
    (simpa? [FixedPart.address_eq] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hf)
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf0]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c', hac', -⟩, -, hb, -, hs, hn⟩ := Adjudicator.deposit_some h
    have had : a ≠ (Address.external d : Address E) := by rw [hac']; intro hh; cases hh
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · (simpa? [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_of_status hs, hn] using hf)
    · rw [hb, Balances.get_add]
      by_cases hca : c.address = a
      · rw [if_pos hca]; (grind? says grind only)
      · rw [if_neg hca]; exact ht
    · rw [hb, Balances.get_add, if_neg (Ne.symm had)]
  | transfer a b =>
    by_cases hac : a = c
    · subst hac
      obtain ⟨o'', amt'', x, hf'', hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
        Adjudicator.transfer_some h
      rw [hf] at hf''
      simp only [Option.some.injEq, Outcome.allocation.injEq] at hf''
      subst hf''
      have hfo' : s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) := by
        have hstatc : s'.statusOf a = (s.statusOf a).withOutcome (.allocation (o.reduceOwed b x)) :=
          by rw [Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_pos rfl]
        (simp? [FixedPart.address_eq, hstatc] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, ChannelStatus.finalOutcome_withOutcome])
      have hxb : x ≤ o.owed b := hxeq ▸ paidTo_first_entry_only _ _ _
      have htot := Allocation.total_reduceOwed o b hxb
      have hxh : x ≤ s.balances.get a.address := hxeq ▸ Allocation.paidTo_le_held _ _ _
      have hcd : (Address.external d : Address E) ≠ a.address := by
        rw [FixedPart.address_eq]; intro hh; cases hh
      have hfind' := Allocation.find_reduceOwed o b (Address.external d) x
      by_cases hbd : (Address.external d : Address E) = b
      · subst hbd
        rw [if_pos rfl, hd] at hfind'
        simp only [Option.map_some] at hfind'
        have hxamt : x ≤ amt := by
          have heq : o.owed (Address.external d) = amt := by (simp? [Allocation.owed, hd] says simp only [Allocation.owed, hd, Option.map_some, Entry.amount_mk, Item.amount_alloc, Option.getD_some])
          rw [heq] at hxb; exact hxb
        refine ⟨o.reduceOwed (Address.external d) x, amt - x, hfo', ?_, hfind', ?_⟩
        · rw [hbal, Balances.get_sub, if_pos rfl]
          by_cases hba : (Address.external d : Address E) = a.address
          · rw [hba, Balances.get_add, if_pos rfl]; (grind? says grind only)
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; (grind? says grind only)
        · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_pos rfl]
          (grind? says grind only)
      · rw [if_neg hbd] at hfind'
        refine ⟨o.reduceOwed b x, amt, hfo', ?_, by rw [hfind']; exact hd, ?_⟩
        · rw [hbal, Balances.get_sub, if_pos rfl]
          by_cases hba : b = a.address
          · rw [hba, Balances.get_add, if_pos rfl]; (grind? says grind only [#5d85])
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; (grind? says grind only)
        · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_neg hbd]
    · obtain ⟨o'', amt'', x, hf'', hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
        Adjudicator.transfer_some h
      have haddr : (c.address : Address E) ≠ a.address := by
        intro hh; injection hh with hh'; exact hac hh'.symm
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac)]
      have hcd : (Address.external d : Address E) ≠ a.address := by
        rw [FixedPart.address_eq]; intro hh; cases hh
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal, Balances.get_sub, if_neg haddr, Balances.get_add]
        by_cases hbc : c.address = b
        · rw [if_pos hbc]; (grind? says grind only)
        · rw [if_neg hbc]; exact ht
      · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add]
        by_cases hbd : (Address.external d : Address E) = b
        · rw [if_pos hbd]; (grind? says grind only)
        · rw [if_neg hbd]
  | reclaim l v =>
    by_cases hcl : l = c
    · subst hcl
      obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      rw [hf] at hL
      simp only [Option.some.injEq, Outcome.allocation.injEq] at hL
      subst hL
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      have hfo' : s'.finalOutcome l.address = some (.allocation
          (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address)) := by
        have hstatl : s'.statusOf l = (s.statusOf l).withOutcome (.allocation
            (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address)) := by
          rw [hsucc, Adjudicator.statusOf_setStatus, if_pos rfl]
        (simp? [FixedPart.address_eq, hstatl] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatl, ChannelStatus.finalOutcome_withOutcome])
      have h1 : (o.addTo left (oV.amountAt 0)).total ≤ o.total + oV.amountAt 0 :=
        Allocation.total_addTo_le _ _ _
      have h2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).total ≤
          (o.addTo left (oV.amountAt 0)).total + oV.amountAt 1 :=
        Allocation.total_addTo_le _ _ _
      have h3 : o.owed v.address ≤ (o.addTo left (oV.amountAt 0)).owed v.address :=
        Allocation.owed_addTo_ge _ _ _ _
      have h4 : (o.addTo left (oV.amountAt 0)).owed v.address ≤
          ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).owed v.address :=
        Allocation.owed_addTo_ge _ _ _ _
      have h5 := Allocation.total_remove_le
        ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)) v.address
      have hvo : o.owed v.address = x := by
        simp only [Allocation.owed, hfind, Option.map_some, Option.getD_some, Entry.amount_mk,
          Item.amount_guarantee]
      have had : (Address.external d : Address E) ≠ v.address := by intro hh; cases hh
      have hfind1 : (o.addTo left (oV.amountAt 0)).find (Address.external d) =
          some ⟨Address.external d, .alloc (if (Address.external d : Address E) = left
            then amt + oV.amountAt 0 else amt)⟩ := by
        by_cases hld : (Address.external d : Address E) = left
        · rw [if_pos hld, ← hld, Allocation.find_addTo_self, hd]; (simp? says simp only [Option.map_some, Entry.amount_mk, Item.amount_alloc])
        · rw [if_neg hld, Allocation.find_addTo_of_ne _ _ hld, hd]
      have hfind2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).find
          (Address.external d) = some ⟨Address.external d, .alloc
            ((if (Address.external d : Address E) = left then amt + oV.amountAt 0 else amt) +
              (if (Address.external d : Address E) = right then oV.amountAt 1 else 0))⟩ := by
        by_cases hrd : (Address.external d : Address E) = right
        · rw [if_pos hrd, ← hrd, Allocation.find_addTo_self, hfind1]; (simp? says simp only [Option.map_some, Entry.amount_mk, Item.amount_alloc])
        · rw [if_neg hrd, Allocation.find_addTo_of_ne _ _ hrd, hfind1]; (simp? says simp only [add_zero])
      have hfind3 : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
          v.address).find (Address.external d) = some ⟨Address.external d, .alloc
            ((if (Address.external d : Address E) = left then amt + oV.amountAt 0 else amt) +
              (if (Address.external d : Address E) = right then oV.amountAt 1 else 0))⟩ := by
        rw [Allocation.find_remove, if_neg had, hfind2]
      refine ⟨_, _, hfo', ?_, hfind3, ?_⟩
      · rw [hbal']; (grind? says grind only)
      · rw [hbal']
        split <;> split <;> (grind? says grind only)
    · obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcl)]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | challenge c' proof candidate =>
    obtain ⟨⟨-, -, -, hm⟩, hsucc⟩ := Adjudicator.challenge_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      rw [Adjudicator.mode_eq] at hm
      rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hfin <;> cases hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | checkpoint c' proof candidate =>
    obtain ⟨⟨ho, -, -, -⟩, hsucc⟩ := Adjudicator.checkpoint_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      exact ho hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | conclude c' ss =>
    obtain ⟨⟨ho, -⟩, hsucc⟩ := Adjudicator.conclude_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      exact ho hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | tick dt =>
    have hs' : s.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
    subst hs'
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · (simpa? [FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt) says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.tick_statusOf, Adjudicator.tick_now] using ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt))
    · (simpa? using ht says simpa only [Adjudicator.tick_balances, FixedPart.address_eq] using ht)
    · (simp? says simp only [Adjudicator.tick_balances, Std.le_refl])

/-- `UnbeatableIn` is monotone in its allowed-move set: a strategy built from
    a more restrictive `allowed1` is still a strategy under any looser
    `allowed2` that contains it. Used to widen `UnbeatableNoWait` (moves
    excluding `.wait`) into `Unbeatable` (every move). -/
theorem UnbeatableIn.mono {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed1 allowed2 : HonestMove E → Prop} (hsub : ∀ m, allowed1 m → allowed2 m)
    {G : NetworkState E p → Prop} {net : NetworkState E p}
    (hU : UnbeatableIn apps T allowed1 G net) : UnbeatableIn apps T allowed2 G net := by
  induction hU with
  | done hG => exact .done hG
  | move m hm hfeas _ ih => exact .move m (hsub m hm) hfeas ih
/-- An adversary move changes only the chain and what `p` has received; the
    states `p` has itself sent are untouched (`NetworkState.applyAdv`). -/
@[simp] theorem NetworkState.applyAdv_sent (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (m : AdvMove E) : (net.applyAdv apps m).sent = net.sent := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases net.chain.apply apps caller op <;> rfl
  | deliver ss => rfl
  | tick dt => rfl
  | land op =>
    simp only [NetworkState.applyAdv]
    cases net.chain.apply apps p op <;> rfl


/-- Over a round's adversary play, `p`'s own sent list never changes: only
    `p`'s own honest moves touch it (`NetworkState.applyAdv_sent`, by
    induction). Used by `latest_state_finalizable` to carry `hlatest`/
    `hfinal` from the original network state to the state reached after `p`'s
    own challenge move. -/
theorem Threat.RoundSeq.sent_eq {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (h : T.RoundSeq apps t pending net net') : net'.sent = net.sent := by
  induction h with
  | nil => rfl
  | land _ _ ih => rw [ih, NetworkState.applyAdv_sent]
  | tick _ _ _ ih => rw [ih, NetworkState.applyAdv_sent]
  | other _ _ _ _ ih => rw [ih, NetworkState.applyAdv_sent]

/-- **An external destination's paid-out balance only grows over a whole
    round.** Every step of `Threat.RoundSeq` (`land`, `tick`, `other`) is one
    `NetworkState.applyAdv`, which never touches the chain except through
    one `Adjudicator.apply` (a `Step`, or a no-op on failure); `Step`-level
    monotonicity is `paid_out_monotone`. Used by `directly_funded_round` to
    carry a balance fact from the moment `p`'s own transfer lands to the
    round's end `net'`. -/
theorem Threat.RoundSeq.balances_external_mono {apps : Apps E} {p : Participant} {T : Threat E p}
    {t : Time} {pending : List (Op E)} {net net' : NetworkState E p}
    (h : T.RoundSeq apps t pending net net') (d : E) :
    net.chain.balances.get (.external d) ≤ net'.chain.balances.get (.external d) := by
  induction h with
  | nil => exact le_refl _
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    refine le_trans ?_ ih
    simp only [NetworkState.applyAdv]
    cases hop : net1.chain.apply apps p op with
    | none => exact le_refl _
    | some s' => exact paid_out_monotone apps net1.chain s' (Step.mk p op net1.chain s' hop) d
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    refine le_trans ?_ ih
    simpa [NetworkState.applyAdv] using
      paid_out_monotone apps net1.chain (net1.chain.tick dt)
        (Step.mk p (Op.tick dt) net1.chain (net1.chain.tick dt) rfl) d
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    refine le_trans ?_ ih
    cases m with
    | chain caller op =>
      simp only [NetworkState.applyAdv]
      cases hop : net1.chain.apply apps caller op with
      | none => exact le_refl _
      | some s' => exact paid_out_monotone apps net1.chain s' (Step.mk caller op net1.chain s' hop) d
    | deliver ss => (simp? [NetworkState.applyAdv] says simp only [NetworkState.applyAdv, Std.le_refl])
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)

/-- Once channel `c` is finalized with `Ω`, it stays so for the rest of a
    round's adversary play (`Adjudicator.finalizedWith_apply`): `land`,
    `tick`, and `other` are each one `NetworkState.applyAdv`, which never
    un-finalizes a channel. Used by `round_keeps_status` to carry the fact
    that `p`'s own `conclude` call finalized `c`, from the moment it lands
    to the round's end. -/
theorem Threat.RoundSeq.finalizedWith_mono {apps : Apps E} {p : Participant} {T : Threat E p}
    {t : Time} {pending : List (Op E)} {c : FixedPart} {Ω : Outcome E}
    {net net' : NetworkState E p} (h : Threat.RoundSeq apps T t pending net net') :
    net.chain.finalizedWith c.address = some Ω → net'.chain.finalizedWith c.address = some Ω := by
  induction h with
  | nil => exact id
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro hfz
    apply ih
    simp only [NetworkState.applyAdv]
    cases hop : net1.chain.apply apps p op with
    | none => exact hfz
    | some s' => exact Adjudicator.finalizedWith_apply hop hfz
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hfz
    apply ih
    simpa [NetworkState.applyAdv, FixedPart.address_eq] using
      ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hfz)
        (Nat.le_add_right _ dt)
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hfz
    apply ih
    cases m with
    | deliver _ => exact hfz
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | chain caller op =>
      simp only [NetworkState.applyAdv]
      cases hop : net1.chain.apply apps caller op with
      | none => exact hfz
      | some s' => exact Adjudicator.finalizedWith_apply hop hfz

/-- Over a round that lands `p`'s one pending call, the transfer to `d`
    (`Threat.RoundSeq`, `pending = [Op.transfer c d]`): `c`'s fully-funded
    slack at `d` (`directly_funded_step`) only grows up to the moment the
    transfer lands — `other` (an adversary `.chain`/`.deliver`) follows
    `directly_funded_step`, or leaves everything unchanged on failure;
    `tick` only advances the clock (`ChannelStatus.finalOutcome_mono`).
    `land` is forced, exactly once (`pending` is a singleton): at that
    point the slack invariant, carried this far, is exactly
    `transfer_can_happen`'s own hypothesis, so the transfer itself
    succeeds and pays `d` at least `amt`; after that, `d`'s raw balance
    (not the slack) only grows for the rest of the round
    (`Threat.RoundSeq.balances_external_mono`). Used by
    `directly_funded_pays`. -/
theorem directly_funded_round {apps : Apps E} {p : Participant} {T : Threat E p} (c : FixedPart)
    (d : E) (hk : c.kind = .ledger) (net net' : NetworkState E p) (t : Time)
    (ht : t = net.chain.now)
    (hseq : Threat.RoundSeq apps T t [Op.transfer c (.external d)] net net') :
    ∀ {o : Allocation E} {amt : Coins},
      net.chain.finalOutcome c.address = some (.allocation o) →
      o.total ≤ net.chain.balances.get c.address →
      o.find (.external d) = some ⟨.external d, .alloc amt⟩ →
      net.chain.balances.get (.external d) + amt ≤ net'.chain.balances.get (.external d) := by
  clear ht
  generalize hp : ([Op.transfer c (.external d)] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro o amt hf ht hd; cases hp
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro o amt hf ht hd
    cases hp
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · cases hsplit
        have hbf : (Address.external d : Address E).fundable = true := rfl
        obtain ⟨s', hs', hbal⟩ := transfer_can_happen net1.chain c (.external d) o amt hk hbf hf hd
        have happly : net1.chain.apply apps p (.transfer c (.external d)) = some s' := by
          rw [Adjudicator.apply_transfer]; exact hs'
        have hchain : (net1.applyAdv apps (.land (Op.transfer c (.external d)))).chain = s' := by
          (simp? [NetworkState.applyAdv, happly] says simp only [NetworkState.applyAdv, happly])
        have hmono := hrest.balances_external_mono d
        rw [hchain] at hmono
        have hcne : (Address.external d : Address E) ≠ c.address := by
          rw [FixedPart.address_eq]; intro hh; cases hh
        rw [hbal, if_neg hcne] at hmono
        have hpaid : amt ≤ o.paidTo (net1.chain.balances.get c.address) (Address.external d) := by
          have hsub : o.dedup.total ≤ o.total :=
            Allocation.total_le_of_sublist (Allocation.dedupFrom_sublist [] o)
          have hdedup_le : o.dedup.total ≤ net1.chain.balances.get c.address := le_trans hsub ht
          have howed1 : o.owed (Address.external d) = amt := by (simp? [Allocation.owed, hd] says simp only [Allocation.owed, hd, Option.map_some, Entry.amount_mk, Item.amount_alloc, Option.getD_some])
          have hdedup_owed : o.dedup.owed (Address.external d) = amt := by
            rw [Allocation.owed_dedup]; exact howed1
          have hle := Allocation.owed_le_payout_get hdedup_le (Address.external d)
          rw [hdedup_owed] at hle
          rwa [Allocation.paidTo_eq_get]
        (grind? says grind only)
      · (simp? at hsplit says simp only [List.nil_append, List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at hsplit)
    · (simp? at hsplit says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro o amt hf ht hd
    refine ih hp ?_ ?_ hd
    · simpa [NetworkState.applyAdv, FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono
          (show (net1.chain.statusOf c).finalOutcome net1.chain.now = some (.allocation o) by
            simpa [FixedPart.address_eq] using hf)
          (Nat.le_add_right net1.chain.now dt)
    · (simpa? [NetworkState.applyAdv] using ht says simpa only [NetworkState.applyAdv, Adjudicator.tick_balances, FixedPart.address_eq] using ht)
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro o amt hf ht hd
    cases m with
    | chain caller op =>
      cases hm : net1.chain.apply apps caller op with
      | none =>
        have := ih hp (by simp only [NetworkState.applyAdv, hm]; exact hf)
          (by simp only [NetworkState.applyAdv, hm]; exact ht) hd
        (simpa? [NetworkState.applyAdv, hm] using this says simpa only [ge_iff_le, NetworkState.applyAdv, hm] using this)
      | some s' =>
        obtain ⟨o1, amt1, hf1, ht1, hd1, hle1⟩ := directly_funded_step hf ht hd hm
        have := ih hp (by simp only [NetworkState.applyAdv, hm]; exact hf1)
          (by simp only [NetworkState.applyAdv, hm]; exact ht1) hd1
        have heq : (NetworkState.applyAdv apps (AdvMove.chain caller op) net1).chain.balances.get
            (Address.external d) = s'.balances.get (Address.external d) := by
          (simp? [NetworkState.applyAdv, hm] says simp only [NetworkState.applyAdv, hm])
        rw [heq] at this
        exact le_trans hle1 this
    | deliver ss =>
      have := ih hp (by simp only [NetworkState.applyAdv]; exact hf)
        (by simp only [NetworkState.applyAdv]; exact ht) hd
      (simpa? [NetworkState.applyAdv] using this says simpa only [ge_iff_le, NetworkState.applyAdv] using this)
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)

/-- Nitro-16, Nitro-21, ForceMove-B01, ForceMove-C03, docs-0070-05, docs-0080-06. Nitro:395-398: "where
    the channel L itself has enough coins in the adjudicator to cover the
    entire allocation ... A will receive all x coins allocated to them in ω."
    The strategy is one transfer. The entry of `d` is an allocation item:
    go-nitro refuses to transfer a guarantee (MultiAssetHolder.sol:169-170).

    Design decision 2026-10-29: `net` is a reachable network state
    (`Nitro.participant_chain_reachable`); a reachable chain never pays a
    virtual-kind channel's own balance out through `d` (the unreachable
    counterexample put coins in a virtual-kind channel,
    `Reachable.balances_virtual_zero`). -/
theorem directly_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.state.chain.finalOutcome c.address = some (.allocation o))
    (hfund : net.state.chain.DirectlyFunded c) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    UnbeatableNoWait apps T
      (fun net' => net.state.chain.balances.get (.external d) + o.owed (.external d) ≤
        net'.chain.balances.get (.external d)) net.state := by
  obtain_reach ⟨net, hr⟩ := net
  have hrc : Reachable apps net.chain := Nitro.participant_chain_reachable hr
  obtain ⟨o', hfo', htot'⟩ := hfund
  rw [hf] at hfo'
  simp only [Option.some.injEq, Outcome.allocation.injEq] at hfo'
  subst hfo'
  have howed : o.owed (Address.external d) = amt := by (simp? [Allocation.owed, hd] says simp only [Allocation.owed, hd, Option.map_some, Entry.amount_mk, Item.amount_alloc, Option.getD_some])
  rw [howed]
  cases hk : c.kind with
  | virtual =>
    have hzero : net.chain.balances.get (Address.channel c) = 0 :=
      Reachable.balances_virtual_zero ⟨_, (Nitro.chain_reachable_iff.mpr hrc)⟩ c hk
    have htot0 : o.total = 0 := by
      have := htot'
      rw [FixedPart.address_eq, hzero] at this
      exact Nat.le_zero.mp this
    have hamt0 : amt = 0 := by
      have hle := Allocation.owed_le_total o (Address.external d)
      rw [howed, htot0] at hle
      exact Nat.le_zero.mp hle
    exact UnbeatableIn.done (by rw [hamt0]; exact Nat.le_refl _)
  | ledger =>
    refine UnbeatableIn.move (.chain (.transfer c (.external d))) trivial
      (by (simp? [Op.HonestFeasible, Op.proofStates] says simp only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.not_mem_nil, IsEmpty.forall_iff, implies_true])) ?_
    intro net' hround
    obtain ⟨hseq, -⟩ := hround
    simp only [HonestMove.calls_chain] at hseq
    have hle := directly_funded_round c d hk net net' _ rfl hseq hf htot' hd
    apply UnbeatableIn.done
    (simpa? using hle says simpa only [NetworkState.applyHonest_chain] using hle)

/-- Within one round, `p`'s own `conclude c ss` call lands exactly once
    (the round's `pending` is the singleton `[Op.conclude c ss]`); it needs
    no `hbounds.unforgeable` detour, because `op` is known exactly — `p`'s
    own call, not a forgery. Before it lands, channel `c` is either already
    finalized with `Ω` (nothing left to do) or open; if open, `conclude`'s
    own success condition (`(statusOf c).IsOpen now ∧ ConclusionProof c
    ss`) is met, so the call succeeds and finalizes `c` with
    `ss.state.outcome` (`Adjudicator.conclude`'s own success semantics).
    Either way `c` ends up finalized with `Ω` once `p`'s call has landed,
    and stays so for the rest of the round (`Threat.RoundSeq.finalizedWith_mono`).
    A fresh or renewed challenge on `c`, before the landing, cannot expire
    before the round ends: its deadline is set at least
    `c.challengeDuration ≥ 2 * T.ε` past the current clock (`hdur`), and the
    round itself ends strictly before `T.ε` has passed from that clock
    (`hεbound`, per step). An adversary `conclude` on `c` before the
    landing still needs `p`'s genuine signature (`hbounds.unforgeable`,
    `hp`), which `p` only ever put on a final state of `c` that already
    carries `Ω` (`hsent`); so it cannot finalize `c` with anything but `Ω`.
    Used by `conclusion_proof_finalizable`. -/
theorem round_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω : Outcome E}
    (hp : p ∈ c.participants) (hdur : 2 * T.ε ≤ c.challengeDuration)
    (hproof : ConclusionProof c ss) (hΩeq : ss.state.outcome = Ω) (net net' : NetworkState E p)
    (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.TimedRun apps T t [Op.conclude c ss] net net') :
    (∀ t0 ∈ net.sent, t0.state.channel = c → t0.state.isFinal = true → t0.state.outcome = Ω) →
    (net.chain.finalizedWith c.address = some Ω ∨ (net.chain.statusOf c).IsOpen net'.chain.now) →
    net'.chain.finalizedWith c.address = some Ω := by
  obtain ⟨hseq, hεb⟩ := hseq; revert hεb
  clear ht
  generalize heq : ([Op.conclude c ss] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => cases heq
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro hεbound hsent hbase
    cases heq
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨hopeq, -⟩ := hsplit
        subst hopeq
        have hle12 : net1.chain.now ≤ net2.chain.now :=
          le_trans (NetworkState.applyAdv_now_le apps net1 (.land (Op.conclude c ss))) hrest.now_le
        have hland : (net1.applyAdv apps (AdvMove.land (Op.conclude c ss))).chain.finalizedWith
            c.address = some Ω := by
          rcases hbase with hfz | hopen
          · have hfz1 : (net1.chain.statusOf c).finalizedWith net1.chain.now = some Ω := by
              (simpa? [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hfz says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hfz)
            have hmode1 : (net1.chain.statusOf c).mode net1.chain.now = .finalized := by
              rw [ChannelStatus.mode_eq_finalized_iff, ← ChannelStatus.finalizedWith_isSome_iff,
                hfz1]
              rfl
            have hnopen : ¬ (net1.chain.statusOf c).IsOpen net1.chain.now := by
              rw [ChannelStatus.isOpen_iff_ne, not_not]; exact hmode1
            cases hop : net1.chain.apply apps p (Op.conclude c ss) with
            | none => (simpa? [NetworkState.applyAdv, hop] using hfz says simpa only [NetworkState.applyAdv, hop, FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hfz)
            | some s' =>
              exfalso
              have hop' : net1.chain.conclude c ss = some s' := by
                rw [← Adjudicator.apply_conclude]; exact hop
              obtain ⟨⟨hopn, -⟩, -⟩ := Adjudicator.conclude_some hop'
              exact hnopen hopn
          · have hopen1 : (net1.chain.statusOf c).IsOpen net1.chain.now := by
              by_contra hc'
              rw [ChannelStatus.isOpen_iff_ne, not_not] at hc'
              exact absurd (ChannelStatus.mode_finalized_mono hc' hle12)
                ((ChannelStatus.isOpen_iff_ne _ _).mp hopen)
            have hsucc : net1.chain.conclude c ss =
                some (net1.chain.setStatus c
                  (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)) := by
              unfold Adjudicator.conclude
              rw [if_pos (And.intro hopen1 hproof)]
            have hop : net1.chain.apply apps p (Op.conclude c ss) =
                some (net1.chain.setStatus c
                  (.finalized ss.state.turnNum ss.state.outcome ss.state.outcome)) := by
              rw [Adjudicator.apply_conclude]; exact hsucc
            simp only [NetworkState.applyAdv, hop]
            (simpa? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
              Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_finalized] using hΩeq says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized, Option.some.injEq] using hΩeq)
        exact hrest.finalizedWith_mono hland
      · (simp? at hsplit says simp only [List.nil_append, List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at hsplit)
    · (simp? at hsplit says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hsent hbase
    have step : net1.chain.finalizedWith c.address = some Ω ∨
        (net1.chain.statusOf c).IsOpen net2.chain.now →
        (net1.applyAdv apps (AdvMove.tick dt)).chain.finalizedWith c.address = some Ω ∨
        ((net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c).IsOpen net2.chain.now := by
      intro hbase1
      rcases hbase1 with h | h
      · exact Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono
              (by simpa [FixedPart.address_eq] using h) (Nat.le_add_right _ dt))
      · exact Or.inr (by (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using h says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using h))
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps (AdvMove.tick dt)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = Ω := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih heq hεbound' hsent' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hsent hbase
    have step : net1.chain.finalizedWith c.address = some Ω ∨
        (net1.chain.statusOf c).IsOpen net2.chain.now →
        (net1.applyAdv apps m).chain.finalizedWith c.address = some Ω ∨
        ((net1.applyAdv apps m).chain.statusOf c).IsOpen net2.chain.now := by
      intro hbase1
      cases m with
      | deliver ss' => exact hbase1
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | chain caller op =>
        simp only [NetworkState.applyAdv]
        cases h : net1.chain.apply apps caller op with
        | none => (simpa? using hbase1 says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hbase1)
        | some s' =>
          rcases hbase1 with hfz | hop
          · exact Or.inl (Adjudicator.finalizedWith_apply h hfz)
          · have hle : net1.chain.now ≤ net2.chain.now :=
              le_trans (NetworkState.applyAdv_now_le apps net1 (.chain caller op)) hrest.now_le
            have hopen1 : (net1.chain.statusOf c).IsOpen net1.chain.now := by
              by_contra hc'
              rw [ChannelStatus.isOpen_iff_ne, not_not] at hc'
              exact hop (ChannelStatus.mode_finalized_mono hc' hle)
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel]
              have hns : ¬ ((net1.chain.statusOf c).finalOutcome net1.chain.now).isSome := by
                rw [← ChannelStatus.mode_eq_finalized_iff]; exact hopen1
              exact Option.not_isSome_iff_eq_none.mp hns
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              exact Or.inr (by rw [Adjudicator.statusOf_of_status hs]; exact hop)
            | tick dt' =>
              have hs' : net1.chain.tick dt' = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
              subst hs'
              exact Or.inr (by rw [Adjudicator.tick_statusOf]; exact hop)
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]
                  exact hop)
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                exact Or.inr (by
                  rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]; exact hop)
            | challenge c' proof candidate =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                refine Or.inr ?_
                rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                have hself : T.ε ≤ 2 * T.ε := by
                  rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                have hge : T.ε ≤ c'.challengeDuration := le_trans hself hdur
                have hdlt : net2.chain.now < net1.chain.now + c'.challengeDuration :=
                  lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
                (simp? [ChannelStatus.IsOpen, ChannelStatus.mode, not_le.mpr hdlt] says simp only [ChannelStatus.IsOpen, ChannelStatus.mode, not_le.mpr hdlt, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true])
              · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hop)
            | checkpoint c' proof candidate =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                refine Or.inr ?_
                rw [Adjudicator.statusOf_setStatus, if_pos rfl]
                (simp? [ChannelStatus.IsOpen, ChannelStatus.mode] says simp only [ChannelStatus.IsOpen, ChannelStatus.mode, ne_eq, reduceCtorEq, not_false_eq_true])
              · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hop)
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                refine Or.inl ?_
                have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
                have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by (simp? [Op.proofStates] says simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false])
                have := (hbounds.unforgeable net1 caller (.conclude c' ss') hfeas ss' hmem).1 hp'
                obtain ⟨t', htmem, hteq⟩ := this
                have hΩ' := hsent t' htmem (hteq ▸ hproof'.1) (hteq ▸ hproof'.2.1)
                (simp? [Adjudicator.finalizedWith_channel, hteq ▸ hΩ'] says simp only [hteq ▸ hΩ', FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized])
              · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                exact Or.inr (by
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hop)
    have hbase' := step hbase
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = Ω := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih heq hεbound' hsent' hbase'

/-- The round that lands `p`'s own `conclude c ss`, from a state where `c`
    is not finalized and no running challenge of `c` ends within `T.ε`,
    ends with `c` finalized with `Ω` (`round_keeps_status`). A running
    challenge cannot end in the round, because the round ends before `T.ε`
    passes. Used by `conclusion_proof_finalizable` and
    `conclude_transfer_pays`. -/
theorem conclude_round_finalized {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω : Outcome E}
    (hp : p ∈ c.participants) (hdur : 2 * T.ε ≤ c.challengeDuration)
    (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = Ω) {net net' : NetworkState E p}
    (hseq : Threat.TimedRun apps T net.chain.now [Op.conclude c ss] net net')
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true → t.state.outcome = Ω)
    (hopen : net.chain.finalizedWith c.address = none) (hpend : net.DeadlineAfter c T.ε) :
    net'.chain.finalizedWith c.address = some Ω := by
  obtain ⟨hseq, hεbound⟩ := hseq
  have hbase : net.chain.finalizedWith c.address = some Ω ∨
      (net.chain.statusOf c).IsOpen net'.chain.now := by
    right
    rcases hstat : net.chain.statusOf c with t | ⟨t, ch⟩ | ⟨t, f, o⟩
    · (simp? [ChannelStatus.IsOpen, ChannelStatus.mode] says simp only [ChannelStatus.IsOpen, ChannelStatus.mode, ne_eq, reduceCtorEq, not_false_eq_true])
    · have hdl := hpend t ch hstat
      have hnf : ¬ (ch.deadline ≤ net'.chain.now) := by
        intro hle
        exact absurd (le_trans hdl hle) (not_le.mpr hεbound)
      (simp? [ChannelStatus.IsOpen, ChannelStatus.mode, hnf] says simp only [ChannelStatus.IsOpen, ChannelStatus.mode, hnf, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true])
    · exfalso
      have hfw : net.chain.finalizedWith c.address = some f := by
        simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstat,
          ChannelStatus.finalizedWith_finalized]
      rw [hopen] at hfw
      exact absurd hfw (by simp)
  exact round_keeps_status hbounds hp hdur hproof hΩ net net' net.chain.now rfl ⟨hseq, hεbound⟩
    hsent hbase

/-- Nitro-13, Nitro-21, Nitro-23, docs-0070-05, ForceMove-A14. SATP:286-289: a
    final state supported by all finalizes "without delay"; Nitro:296-299: a
    participant who holds a conclusion proof can register it; go-nitro
    `_conclude` accepts it from any caller. Under the consensus app no other
    participant can finalize a different outcome without `p`'s signature
    before `p`'s conclude lands, because a challenge lasts at least `2 * ε`
    and no running challenge ends within `ε` (Nitro:537-539). -/
theorem conclusion_proof_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε) (ss : SignedState E)
    (Ω : Outcome E) (hc : apps (c : FixedPart).appDef = consensusRules)
    (hp : p ∈ (c : FixedPart).participants)
    (hh : net.state.Holds ss) (hproof : ConclusionProof (c : FixedPart) ss) (hΩ : ss.state.outcome = Ω)
    (hsent : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) → t.state.isFinal = true →
      t.state.outcome = Ω)
    (hchain : net.state.chain.finalizedWith (c : FixedPart).address = none ∨
      net.state.Finalized (c : FixedPart) Ω)
    (hpend : net.state.DeadlineAfter (c : FixedPart) T.ε) :
    UnbeatableNoWait apps T (fun net' => net'.Finalized (c : FixedPart) Ω) net.state := by
  obtain_reach ⟨net, _hr⟩ := net
  obtain ⟨c, hdur⟩ := c
  rcases hchain with h1 | h2
  · refine UnbeatableIn.move (.chain (.conclude c ss)) trivial
      (by (simpa? [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh says simpa only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hh)) ?_
    intro net' hround
    obtain ⟨hseq, hεbound⟩ := hround
    simp only [HonestMove.calls_chain] at hseq
    have hfinal := conclude_round_finalized A.toBounds hp hdur hproof hΩ ⟨hseq, hεbound⟩ hsent h1
      hpend
    apply UnbeatableIn.done
    show (net'.applyHonest (.chain (.conclude c ss))).Finalized c Ω
    simpa [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel]
      using hfinal
  · exact UnbeatableIn.done h2

/-- The channel an operation can change the status of — a local copy of
    `NonVacuity.lean`'s `opOn` (that file imports this one, not the other
    way around). Used by `channel_stays_open_round`. -/
def Op.targets : Op E → FixedPart → Prop
  | .conclude c' _, c2 => c' = c2
  | .challenge c' _ _, c2 => c' = c2
  | .checkpoint c' _ _, c2 => c' = c2
  | .transfer c' _, c2 => c' = c2
  | .reclaim c' _, c2 => c' = c2
  | _, _ => False

/-- An operation that doesn't target `c2` leaves its status alone. -/
theorem statusOf_apply_of_not_targets {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') {c2 : FixedPart}
    (hc2 : ¬ Op.targets op c2) : s'.statusOf c2 = s.statusOf c2 := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
    exact Adjudicator.statusOf_of_status hs c2
  | tick dt => (simp? at h says simp only [Adjudicator.apply_tick, Option.some.injEq] at h); subst h; rfl
  | transfer a b =>
    obtain ⟨_, _, _, -, -, -, -, -, hs, -⟩ := Adjudicator.transfer_some h
    rw [Adjudicator.statusOf_of_status hs]
    simp only [Adjudicator.statusOf_setStatus, Op.targets] at hc2 ⊢
    rw [if_neg (Ne.symm hc2)]
  | reclaim l v' =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := Adjudicator.reclaim_some h
    simp only [Adjudicator.statusOf_setStatus, Op.targets] at hc2 ⊢
    rw [if_neg (Ne.symm hc2)]
  | challenge c' proof cand =>
    obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
    simp only [Adjudicator.statusOf_setStatus, Op.targets] at hc2 ⊢
    rw [if_neg (Ne.symm hc2)]
  | checkpoint c' proof cand =>
    obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
    simp only [Adjudicator.statusOf_setStatus, Op.targets] at hc2 ⊢
    rw [if_neg (Ne.symm hc2)]
  | conclude c' ss =>
    obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
    simp only [Adjudicator.statusOf_setStatus, Op.targets] at hc2 ⊢
    rw [if_neg (Ne.symm hc2)]

/-- The exact effect of a successful call `op` that targets channel `c`
    (`Op.targets`), when `c` is not yet finalized (`hlive`). A `transfer`
    or `reclaim` targeting `c` cannot succeed here: both need `c` already
    finalized (`Adjudicator.transfer_some`/`reclaim_some`'s own
    precondition), contradicting `hlive`. A `challenge`/`checkpoint`/
    `conclude` gives its own success lemma's exact new record. Pairs with
    `statusOf_apply_of_not_targets` for the non-targeting half: that
    lemma covers "`op` does not touch `c`"; this one covers "`op` touches
    `c` and `c` is still live". Together they replace the
    `have step := by cases op with …` block duplicated in
    `latest_round_keeps_status_nil`, `_nil_prelanding`, `_nil_D`, and
    `late_round_keeps_status_nil`. -/
theorem Op.latest_record_step {apps : Apps E} {c : FixedPart} {caller : Participant}
    {op : Op E} {s s' : Adjudicator E} (h : s.apply apps caller op = some s')
    (ht : Op.targets op c) (hlive : s.finalOutcome c.address = none) :
    (∃ proof cand, op = Op.challenge c proof cand ∧
      (apps c.appDef).supports c proof cand = true ∧ cand.channel = c ∧
      ((s.mode c = .open ∧ (s.statusOf c).turnNumRecord ≤ cand.turnNum) ∨
       (s.mode c = .challenge ∧ (s.statusOf c).turnNumRecord < cand.turnNum)) ∧
      s'.statusOf c = .challenged cand.turnNum ⟨cand, s.now + c.challengeDuration⟩) ∨
    (∃ proof cand, op = Op.checkpoint c proof cand ∧
      (apps c.appDef).supports c proof cand = true ∧ cand.channel = c ∧
      (s.statusOf c).turnNumRecord < cand.turnNum ∧
      s'.statusOf c = .open cand.turnNum) ∨
    (∃ ss' : SignedState E, op = Op.conclude c ss' ∧ ConclusionProof c ss' ∧
      s'.statusOf c = .finalized ss'.state.turnNum ss'.state.outcome ss'.state.outcome) := by
  cases op with
  | deposit a e x => exact ht.elim
  | tick dt => exact ht.elim
  | transfer a b =>
    simp only [Op.targets] at ht
    subst ht
    obtain ⟨o, -, -, hfo, -⟩ := Adjudicator.transfer_some h
    rw [hlive] at hfo
    exact absurd hfo (by simp only [reduceCtorEq, not_false_eq_true])
  | reclaim l v =>
    simp only [Op.targets] at ht
    subst ht
    obtain ⟨oL, -, -, -, -, hfo, -⟩ := Adjudicator.reclaim_some h
    rw [hlive] at hfo
    exact absurd hfo (by simp only [reduceCtorEq, not_false_eq_true])
  | challenge c' proof cand =>
    simp only [Op.targets] at ht
    subst ht
    obtain ⟨⟨hp', hs, hch, hmode⟩, rfl⟩ := Adjudicator.challenge_some h
    exact Or.inl ⟨proof, cand, rfl, hs, hch, hmode, by
      rw [Adjudicator.statusOf_setStatus, if_pos rfl]⟩
  | checkpoint c' proof cand =>
    simp only [Op.targets] at ht
    subst ht
    obtain ⟨⟨-, hs, hch, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
    exact Or.inr (Or.inl ⟨proof, cand, rfl, hs, hch, hlt, by
      rw [Adjudicator.statusOf_setStatus, if_pos rfl]⟩)
  | conclude c' ss' =>
    simp only [Op.targets] at ht
    subst ht
    obtain ⟨⟨-, hcp⟩, rfl⟩ := Adjudicator.conclude_some h
    exact Or.inr (Or.inr ⟨ss', rfl, hcp, by
      rw [Adjudicator.statusOf_setStatus, if_pos rfl]⟩)


/-- Over a round's play with nothing of `p`'s own still pending, "finalized
    with `ss.state.outcome`, or challenged at a turn at or above
    `ss.state.turnNum`, matching `ss.state`, with a deadline still ahead" is
    preserved: the turn-bound argument (`hbounds.unforgeable`, `hlatest`)
    bounds any OTHER candidate's turn at or below `ss.state.turnNum`, so no
    fresh `challenge` or `checkpoint` can push the record past where it
    already sits. A `conclude` needs `p`'s own signature on a final state,
    which `hfinal` ties to `ss.state.outcome`. Restated against the
    explicit-time game (design decision 2026-10-29): the invariant drops
    the old "open" branch entirely, because `latest_round_keeps_status`'s
    own `land` step (its one caller) never leaves that branch standing.
    Used by `latest_round_keeps_status` for the adversary play before and
    after `p`'s own `challenge` call lands. -/
theorem latest_round_keeps_status_nil {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants)
    (hdur : 2 * T.ε ≤ c.challengeDuration) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      net'.chain.now < net.chain.now + T.ε →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) →
      (∀ t0 ∈ net.sent, t0.state.channel = c → t0.state.isFinal = true →
        t0.state.outcome = ss.state.outcome) →
      (net.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ net'.chain.now < ch.deadline) →
      net'.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net'.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ net'.chain.now < ch.deadline := by
  intro net net' t hseq hεbound hlatest hfinal hbase
  have hres := Threat.RoundSeq.nil_invariant
    (Inv := fun n => (net'.chain.now < n.chain.now + T.ε) ∧
      (∀ t0 ∈ n.sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧
      (∀ t0 ∈ n.sent, t0.state.channel = c → t0.state.isFinal = true →
        t0.state.outcome = ss.state.outcome) ∧
      (n.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, n.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ net'.chain.now < ch.deadline))
    hseq ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩ ⟨hεbound, hlatest, hfinal, hbase⟩
  · exact hres.2.2.2
  · intro n ss' hnow _ ⟨hεb, hlat, hfin, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.deliver ss')) T.ε), by rw [NetworkState.applyAdv_sent]; exact hlat,
      by rw [NetworkState.applyAdv_sent]; exact hfin, hb⟩
  · intro n dt hnow _ ⟨hεb, hlat, hfin, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.tick dt)) T.ε), by rw [NetworkState.applyAdv_sent]; exact hlat,
      by rw [NetworkState.applyAdv_sent]; exact hfin, ?_⟩
    rcases hb with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
    · exact Or.inl (by
        simpa [NetworkState.applyAdv, FixedPart.address_eq] using
          ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
            (Nat.le_add_right _ dt))
    · exact Or.inr ⟨T0, ch, by (simpa? [NetworkState.applyAdv] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst), hT0, hchs, hdd⟩
  · intro n caller op hnow hfeas ⟨hεb, hlat, hfin, hb⟩
    have hεb' : net'.chain.now < (n.applyAdv apps (.chain caller op)).chain.now + T.ε :=
      lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
        (.chain caller op)) T.ε)
    have hlat' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlat
    have hfin' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfin
    refine ⟨hεb', hlat', hfin', ?_⟩
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      obtain ⟨x, hx, hxs, hch⟩ := ConsensusMember.sent_cand ⟨hc, hp⟩ hU hs
      have hb2 := hlat x hx (by rw [hxs]; exact hch)
      rw [hxs] at hb2
      exact hb2
    rcases hb with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
    · refine Or.inl ?_
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => (simpa? using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
      | some s' => exact Adjudicator.finalizedWith_apply h hf
    · have hltdl : n.chain.now < ch.deadline := lt_of_le_of_lt hnow hdd
      have hm1 : n.chain.mode c = .challenge := by
        rw [Adjudicator.mode_eq, hst, ChannelStatus.mode_challenged, if_neg (not_le.mpr hltdl)]
      have hfo1 : n.chain.finalOutcome c.address = none := by
        simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
          ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inr ⟨T0, ch, hst, hT0, hchs, hdd⟩
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, hmode, _⟩ |
              ⟨proof, cand, hop, hs, -, hlt2, _⟩ |
              ⟨ss', hop, hcp, hnew⟩
          · subst hop
            exfalso
            rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt2⟩
            · rw [hm1] at hmo; exact absurd hmo (by decide)
            · rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
              rcases hsupp proof cand hU hs with hlt3 | heqc3
              · omega
              · rw [heqc3] at hlt2; omega
          · subst hop
            exfalso
            rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
            rcases hsupp proof cand hU hs with hlt3 | heqc3
            · omega
            · rw [heqc3] at hlt2; omega
          · subst hop
            refine Or.inl ?_
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hp)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hΩ' := hfin x hxmem (hxeq ▸ hcp.1) (hxeq ▸ hcp.2.1)
            simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hnew,
              ChannelStatus.finalizedWith, hxeq ▸ hΩ']
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inr ⟨T0, ch, hst, hT0, hchs, hdd⟩

/-- Over a round's play with nothing of `p`'s own still pending, the
    PRE-land three-way invariant ("finalized with `ss.state.outcome`, or
    open at a turn at or below `ss.state.turnNum`, or challenged at a turn
    at or below `ss.state.turnNum` (or matching `ss.state`) with a deadline
    still ahead") is preserved: the same turn-bound argument
    (`hbounds.unforgeable`, `hlatest`) as `latest_round_keeps_status`'s own
    `tick`/`other` cases, extracted standalone because those two cases
    never consult `pending`'s contents — only `land` (excluded here,
    `pending = []`) does. Used by `latest_round_keeps_status_two` for
    channel `c`'s own invariant while the OTHER channel's call is still
    pending or already landed elsewhere in a two-call reaction
    (`satp_intermediary_before_round2`'s argument). -/
theorem latest_round_keeps_status_nil_prelanding {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {D : Time}
    (hC : TimedConsensusMember apps p T.ε c) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      net'.chain.now ≤ D →
      D < net.chain.now + T.ε →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) →
      (∀ t0 ∈ net.sent, t0.state.channel = c → t0.state.isFinal = true →
        t0.state.outcome = ss.state.outcome) →
      (net.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, net.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)) →
      net'.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, net'.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net'.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline) := by
  intro net net' t hseq hDbound hεbound hlatest hfinal hbase
  have hres := Threat.RoundSeq.nil_invariant
    (Inv := fun n => (D < n.chain.now + T.ε) ∧
      (∀ t0 ∈ n.sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧
      (∀ t0 ∈ n.sent, t0.state.channel = c → t0.state.isFinal = true →
        t0.state.outcome = ss.state.outcome) ∧
      (n.chain.finalizedWith c.address = some ss.state.outcome ∨
        (∃ t0, n.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, n.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)))
    hseq ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩ ⟨hεbound, hlatest, hfinal, hbase⟩
  · exact hres.2.2.2
  · intro n ss' hnow _ ⟨hεb, hlat, hfin, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.deliver ss')) T.ε), by rw [NetworkState.applyAdv_sent]; exact hlat,
      by rw [NetworkState.applyAdv_sent]; exact hfin, hb⟩
  · intro n dt hnow _ ⟨hεb, hlat, hfin, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.tick dt)) T.ε), by rw [NetworkState.applyAdv_sent]; exact hlat,
      by rw [NetworkState.applyAdv_sent]; exact hfin, ?_⟩
    rcases hb with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
    · exact Or.inl (by
        simpa [NetworkState.applyAdv, FixedPart.address_eq] using
          ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
            (Nat.le_add_right _ dt))
    · exact Or.inr (Or.inl ⟨t0, by (simpa? [NetworkState.applyAdv] using ho says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using ho), hle⟩)
    · exact Or.inr (Or.inr ⟨t0, ch, by (simpa? [NetworkState.applyAdv] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst), hdis, hdd⟩)
  · intro n caller op hnow hfeas ⟨hεb, hlat, hfin, hb⟩
    have hεb' : D < (n.applyAdv apps (.chain caller op)).chain.now + T.ε :=
      lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
        (.chain caller op)) T.ε)
    have hlat' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlat
    have hfin' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfin
    refine ⟨hεb', hlat', hfin', ?_⟩
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      obtain ⟨x, hx, hxs, hch⟩ := hC.sent_cand hU hs
      have hb2 := hlat x hx (by rw [hxs]; exact hch)
      rw [hxs] at hb2
      exact hb2
    rcases hb with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
    · refine Or.inl ?_
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => (simpa? using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
      | some s' => exact Adjudicator.finalizedWith_apply h hf
    · simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inr (Or.inl ⟨t0, ho, hle⟩)
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          have hfo1 : n.chain.finalOutcome c.address = none := by
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
              ChannelStatus.finalOutcome_open]
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨ss', hop, hcp, hnew⟩
          · subst hop
            rcases hsupp proof cand hU hs with hlt | heqc
            · refine Or.inr (Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inl hlt, ?_⟩)
              have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
              have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
              exact lt_of_lt_of_le hεb (Nat.add_le_add_left hge n.chain.now)
            · refine Or.inr (Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inr heqc, ?_⟩)
              have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
              have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
              exact lt_of_lt_of_le hεb (Nat.add_le_add_left hge n.chain.now)
          · subst hop
            refine Or.inr (Or.inl ⟨cand.turnNum, hnew, ?_⟩)
            rcases hsupp proof cand hU hs with hlt | heqc
            · exact le_of_lt hlt
            · exact le_of_eq (by rw [heqc])
          · subst hop
            refine Or.inl ?_
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hC.mem)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hΩ' := hfin x hxmem (hxeq ▸ hcp.1) (hxeq ▸ hcp.2.1)
            simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hnew,
              ChannelStatus.finalizedWith, hxeq ▸ hΩ']
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inr (Or.inl ⟨t0, ho, hle⟩)
    · have hltdl : n.chain.now < ch.deadline :=
        lt_of_le_of_lt (le_trans hnow hDbound) hdd
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inr (Or.inr ⟨t0, ch, hst, hdis, hdd⟩)
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          have hfo1 : n.chain.finalOutcome c.address = none := by
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
              ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨ss', hop, hcp, hnew⟩
          · subst hop
            rcases hsupp proof cand hU hs with hlt | heqc
            · refine Or.inr (Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inl hlt, ?_⟩)
              have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
              have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
              exact lt_of_lt_of_le hεb (Nat.add_le_add_left hge n.chain.now)
            · refine Or.inr (Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inr heqc, ?_⟩)
              have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
              have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
              exact lt_of_lt_of_le hεb (Nat.add_le_add_left hge n.chain.now)
          · subst hop
            refine Or.inr (Or.inl ⟨cand.turnNum, hnew, ?_⟩)
            rcases hsupp proof cand hU hs with hlt | heqc
            · exact le_of_lt hlt
            · exact le_of_eq (by rw [heqc])
          · subst hop
            refine Or.inl ?_
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hC.mem)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hΩ' := hfin x hxmem (hxeq ▸ hcp.1) (hxeq ▸ hcp.2.1)
            simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hnew,
              ChannelStatus.finalizedWith, hxeq ▸ hΩ']
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inr (Or.inr ⟨t0, ch, hst, hdis, hdd⟩)


/-- `latest_round_keeps_status_nil`, decoupled from its own `RoundSeq`
    endpoint: the deadline bound is checked against an independently-fixed
    `D` (with `net'.chain.now ≤ D` supplied once) instead of the segment's
    own endpoint, so it composes across a multi-segment round where this
    segment ends before the round itself does. Used by
    `latest_round_keeps_status_two` for a channel whose own call has
    ALREADY landed, while the OTHER channel's call is still pending or
    landing later in the same two-call reaction
    (`satp_intermediary_before_round2`'s argument). -/
theorem latest_round_keeps_status_nil_D {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {D : Time}
    (hC : ConsensusMember apps p c) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      net'.chain.now ≤ D →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) →
      (∀ t0 ∈ net.sent, t0.state.channel = c → t0.state.isFinal = true →
        t0.state.outcome = ss.state.outcome) →
      (net.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ D < ch.deadline) →
      net'.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, net'.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ D < ch.deadline := by
  intro net net' t hseq hDbound hlatest hfinal hbase
  have hres := Threat.RoundSeq.nil_invariant
    (Inv := fun n => (∀ t0 ∈ n.sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧
      (∀ t0 ∈ n.sent, t0.state.channel = c → t0.state.isFinal = true →
        t0.state.outcome = ss.state.outcome) ∧
      (n.chain.finalizedWith c.address = some ss.state.outcome ∨
        ∃ T0 ch, n.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          ch.state = ss.state ∧ D < ch.deadline))
    hseq ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩ ⟨hlatest, hfinal, hbase⟩
  · exact hres.2.2
  · intro n ss' _ _ ⟨hlat, hfin, hb⟩
    exact ⟨by rw [NetworkState.applyAdv_sent]; exact hlat,
      by rw [NetworkState.applyAdv_sent]; exact hfin, hb⟩
  · intro n dt _ _ ⟨hlat, hfin, hb⟩
    refine ⟨by rw [NetworkState.applyAdv_sent]; exact hlat,
      by rw [NetworkState.applyAdv_sent]; exact hfin, ?_⟩
    rcases hb with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
    · exact Or.inl (by
        simpa [NetworkState.applyAdv, FixedPart.address_eq] using
          ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
            (Nat.le_add_right _ dt))
    · exact Or.inr ⟨T0, ch, by (simpa? [NetworkState.applyAdv] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst), hT0, hchs, hdd⟩
  · intro n caller op hnow hfeas ⟨hlat, hfin, hb⟩
    have hlat' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlat
    have hfin' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfin
    refine ⟨hlat', hfin', ?_⟩
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      obtain ⟨x, hx, hxs, hch⟩ := hC.sent_cand hU hs
      have hb2 := hlat x hx (by rw [hxs]; exact hch)
      rw [hxs] at hb2
      exact hb2
    rcases hb with hf | ⟨T0, ch, hst, hT0, hchs, hdd⟩
    · refine Or.inl ?_
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => (simpa? using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
      | some s' => exact Adjudicator.finalizedWith_apply h hf
    · have hltdl : n.chain.now < ch.deadline := lt_of_le_of_lt (le_trans hnow hDbound) hdd
      have hm1 : n.chain.mode c = .challenge := by
        rw [Adjudicator.mode_eq, hst, ChannelStatus.mode_challenged, if_neg (not_le.mpr hltdl)]
      have hfo1 : n.chain.finalOutcome c.address = none := by
        simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
          ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inr ⟨T0, ch, hst, hT0, hchs, hdd⟩
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, hmode, _⟩ |
              ⟨proof, cand, hop, hs, -, hlt2, _⟩ |
              ⟨ss', hop, hcp, hnew⟩
          · subst hop
            exfalso
            rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt2⟩
            · rw [hm1] at hmo; exact absurd hmo (by decide)
            · rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
              rcases hsupp proof cand hU hs with hlt3 | heqc3
              · omega
              · rw [heqc3] at hlt2; omega
          · subst hop
            exfalso
            rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2
            rcases hsupp proof cand hU hs with hlt3 | heqc3
            · omega
            · rw [heqc3] at hlt2; omega
          · subst hop
            refine Or.inl ?_
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hC.mem)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hΩ' := hfin x hxmem (hxeq ▸ hcp.1) (hxeq ▸ hcp.2.1)
            simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hnew,
              ChannelStatus.finalizedWith, hxeq ▸ hΩ']
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inr ⟨T0, ch, hst, hT0, hchs, hdd⟩

/-- Landing `p`'s own `challenge c' proof cand` call touches only channel
    `c'`'s own status: for any OTHER channel `c ≠ c'`, its status and
    `finalizedWith` entry are untouched (`Adjudicator.statusOf_setStatus`'s
    `if_neg`, whether the challenge call succeeds or fails). Used by
    `latest_round_keeps_status_two` to carry one channel's invariant
    through the OTHER channel's own call landing, in a two-call reaction. -/
theorem land_challenge_other_statusOf {apps : Apps E} {p : Participant}
    {c c' : FixedPart} (hne : c' ≠ c) (proof : SupportProof E) (cand : State E)
    (net : NetworkState E p) :
    (net.applyAdv apps (AdvMove.land (Op.challenge c' proof cand))).chain.statusOf c =
      net.chain.statusOf c ∧
    (net.applyAdv apps (AdvMove.land (Op.challenge c' proof cand))).chain.finalizedWith
        c.address = net.chain.finalizedWith c.address := by
  simp only [NetworkState.applyAdv]
  cases h : net.chain.apply apps p (Op.challenge c' proof cand) with
  | none => (simp? says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, and_self])
  | some s' =>
    obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
    exact ⟨by (simp? [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)] says simp only [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)]),
      by (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
        Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne), Adjudicator.setStatus_now])⟩

/-- Landing `p`'s own `challenge c [ss] ss.state` call transitions the
    PRE-land three-way invariant into the POST-land two-way invariant
    ("finalized with `ss.state.outcome`, or challenged at a turn at or
    above `ss.state.turnNum`, matching `ss.state`, with a deadline still
    ahead"): the challenge either finds `c` already finalized (unchanged,
    `hf` branch), open at or below `ss.state.turnNum` (the challenge
    succeeds, landing exactly `ss.state.turnNum`), or already challenged —
    behind `ss.state.turnNum` (the challenge still succeeds, same
    landing) or already matching it (the challenge fails on a stale
    precondition, but the existing record already satisfies the goal).
    Extracted from `latest_round_keeps_status`'s own `land` case (its one
    caller there) so `latest_round_keeps_status_two` can invoke it once
    per channel, against the round's own fixed endpoint `net'` rather than
    a freshly-destructed `RoundSeq` remainder. -/
theorem land_own_challenge_transitions_status {apps : Apps E} {p : Participant} {T : Threat E p}
    {c : FixedPart} {ss : SignedState E} (hC : TimedConsensusMember apps p T.ε c) (hall : ss.ByAll)
    (hchan : ss.state.channel = c) {net1 net' : NetworkState E p}
    (hεbound : net'.chain.now < net1.chain.now + T.ε) (hmono0 : net1.chain.now ≤ net'.chain.now)
    (hbase : net1.chain.finalizedWith c.address = some ss.state.outcome ∨
      (∃ t0, net1.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
      (∃ t0 ch, net1.chain.statusOf c = .challenged t0 ch ∧
        (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline)) :
    (net1.applyAdv apps (AdvMove.land (Op.challenge c [ss] ss.state))).chain.finalizedWith
        c.address = some ss.state.outcome ∨
    ∃ T0 ch, (net1.applyAdv apps (AdvMove.land (Op.challenge c [ss] ss.state))).chain.statusOf c =
        .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧ ch.state = ss.state ∧
      net'.chain.now < ch.deadline := by
  rcases hbase with hf | ⟨t0, ho, hle⟩ | ⟨t0, ch0, hst0, hdis0, hdd0⟩
  · have hfz1 : (net1.chain.statusOf c).finalizedWith net1.chain.now =
        some ss.state.outcome := by
      (simpa? [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
    have hm1 : net1.chain.mode c = .finalized := by
      rw [Adjudicator.mode_eq, ChannelStatus.mode_eq_finalized_iff,
        ← ChannelStatus.finalizedWith_isSome_iff, hfz1]
      rfl
    have hcondneg : ¬ (p ∈ c.participants ∧
        (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
        ((net1.chain.mode c = .open ∧
            (net1.chain.statusOf c).turnNumRecord ≤ ss.state.turnNum) ∨
         (net1.chain.mode c = .challenge ∧
            (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum))) := by
      rintro ⟨-, -, -, hmode⟩
      rcases hmode with ⟨hmo, -⟩ | ⟨hmo, -⟩ <;> rw [hm1] at hmo <;>
        exact absurd hmo (by decide)
    have hop : net1.chain.apply apps p (Op.challenge c [ss] ss.state) = none := by
      rw [Adjudicator.apply_challenge]; unfold Adjudicator.challenge
      rw [if_neg hcondneg]
    simp only [NetworkState.applyAdv, hop]
    exact Or.inl hf
  · have hcond : p ∈ c.participants ∧
        (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
        ((net1.chain.mode c = .open ∧
            (net1.chain.statusOf c).turnNumRecord ≤ ss.state.turnNum) ∨
         (net1.chain.mode c = .challenge ∧
            (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum)) := by
      refine ⟨hC.mem, by rw [hC.app]; (simp? [consensusRules, hchan, hall] says simp only [consensusRules, decide_true, hchan, Bool.and_self, hall]), hchan, Or.inl ⟨?_, ?_⟩⟩
      · rw [Adjudicator.mode_eq, ho]; rfl
      · rw [ho, ChannelStatus.turnNumRecord_open]; exact hle
    have hop : net1.chain.apply apps p (Op.challenge c [ss] ss.state) =
        some (net1.chain.setStatus c
          (.challenged ss.state.turnNum ⟨ss.state, net1.chain.now + c.challengeDuration⟩)) := by
      rw [Adjudicator.apply_challenge]; unfold Adjudicator.challenge; rw [if_pos hcond]
    simp only [NetworkState.applyAdv, hop]
    refine Or.inr ⟨ss.state.turnNum, ⟨ss.state, net1.chain.now + c.challengeDuration⟩,
      ?_, le_refl _, rfl, ?_⟩
    · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
    · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
      have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
      exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
  · have hltdl0 : net1.chain.now < ch0.deadline := lt_of_le_of_lt hmono0 hdd0
    have hm1 : net1.chain.mode c = .challenge := by
      rw [Adjudicator.mode_eq, hst0, ChannelStatus.mode_challenged,
        if_neg (not_le.mpr hltdl0)]
    by_cases hlt0 : t0 < ss.state.turnNum
    · have hcond : p ∈ c.participants ∧
          (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
          ((net1.chain.mode c = .open ∧
              (net1.chain.statusOf c).turnNumRecord ≤ ss.state.turnNum) ∨
           (net1.chain.mode c = .challenge ∧
              (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum)) := by
        refine ⟨hC.mem, by rw [hC.app]; (simp? [consensusRules, hchan, hall] says simp only [consensusRules, decide_true, hchan, Bool.and_self, hall]), hchan,
          Or.inr ⟨hm1, ?_⟩⟩
        rw [hst0, ChannelStatus.turnNumRecord_challenged]; exact hlt0
      have hop : net1.chain.apply apps p (Op.challenge c [ss] ss.state) =
          some (net1.chain.setStatus c
            (.challenged ss.state.turnNum
              ⟨ss.state, net1.chain.now + c.challengeDuration⟩)) := by
        rw [Adjudicator.apply_challenge]; unfold Adjudicator.challenge; rw [if_pos hcond]
      simp only [NetworkState.applyAdv, hop]
      refine Or.inr ⟨ss.state.turnNum, ⟨ss.state, net1.chain.now + c.challengeDuration⟩,
        ?_, le_refl _, rfl, ?_⟩
      · rw [Adjudicator.statusOf_setStatus, if_pos rfl]
      · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
        have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
        exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
    · have hchs0 : ch0.state = ss.state := hdis0.resolve_left hlt0
      have hcondneg : ¬ (p ∈ c.participants ∧
          (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
          ((net1.chain.mode c = .open ∧
              (net1.chain.statusOf c).turnNumRecord ≤ ss.state.turnNum) ∨
           (net1.chain.mode c = .challenge ∧
              (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum))) := by
        rintro ⟨-, -, -, hmode⟩
        rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt2⟩
        · rw [hm1] at hmo; exact absurd hmo (by decide)
        · rw [hst0, ChannelStatus.turnNumRecord_challenged] at hlt2; exact hlt0 hlt2
      have hop : net1.chain.apply apps p (Op.challenge c [ss] ss.state) = none := by
        rw [Adjudicator.apply_challenge]; unfold Adjudicator.challenge
        rw [if_neg hcondneg]
      simp only [NetworkState.applyAdv, hop]
      exact Or.inr ⟨t0, ch0, hst0, not_lt.mp hlt0, hchs0, hdd0⟩

/-- `latest_round_keeps_status_two`, fixed to the order "`c1`'s call lands
    first" (`hpre`, `hmid`): `hpre` carries BOTH channels' pre-land
    invariants, unaffected, up to the moment `c1` lands (`n1`);
    `land_own_challenge_transitions_status` lands `c1`;
    `land_challenge_other_statusOf` carries `c2`'s pre-land invariant,
    unaffected, THROUGH that same land (`c1 ≠ c2`); `Threat.RoundSeq.peel_one`
    on `hmid` splits the rest into another no-land phase, `c2`'s own land,
    and a final no-land phase, with `c1`'s now-landed invariant carried
    across `c2`'s land the same way, symmetrically. Every deadline
    comparison is pinned to the ROUND's own fixed endpoint `net'` throughout
    (the `_prelanding`/`_D` lemmas' own `D` parameter), never a segment's
    local one — the fix this design decision's own argument turns on
    (`Strategy.lean`'s header, "Time bounds per pending action"). -/
theorem latest_round_keeps_status_two_ordered {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c1 c2 : FixedPart} {ss1 ss2 : SignedState E} (hne : c1 ≠ c2)
    (hC1 : TimedConsensusMember apps p T.ε c1) (hC2 : TimedConsensusMember apps p T.ε c2)
    (hall1 : ss1.ByAll) (hchan1 : ss1.state.channel = c1)
    (hall2 : ss2.ByAll) (hchan2 : ss2.state.channel = c2)
    {net n1 net' : NetworkState E p} {t : Time} (hpre : Threat.RoundSeq apps T t [] net n1)
    (hmid : Threat.RoundSeq apps T t [Op.challenge c2 [ss2] ss2.state]
      (n1.applyAdv apps (.land (Op.challenge c1 [ss1] ss1.state))) net')
    (hεbound : net'.chain.now < net.chain.now + T.ε)
    (hlatest1 : ∀ t0 ∈ net.sent, t0.state.channel = c1 →
      t0.state.turnNum < ss1.state.turnNum ∨ t0.state = ss1.state)
    (hlatest2 : ∀ t0 ∈ net.sent, t0.state.channel = c2 →
      t0.state.turnNum < ss2.state.turnNum ∨ t0.state = ss2.state)
    (hfinal1 : ∀ t0 ∈ net.sent, t0.state.channel = c1 → t0.state.isFinal = true →
      t0.state.outcome = ss1.state.outcome)
    (hfinal2 : ∀ t0 ∈ net.sent, t0.state.channel = c2 → t0.state.isFinal = true →
      t0.state.outcome = ss2.state.outcome)
    (hbase1 : net.chain.finalizedWith c1.address = some ss1.state.outcome ∨
      (∃ t0, net.chain.statusOf c1 = .open t0 ∧ t0 ≤ ss1.state.turnNum) ∨
      (∃ t0 ch, net.chain.statusOf c1 = .challenged t0 ch ∧
        (t0 < ss1.state.turnNum ∨ ch.state = ss1.state) ∧ net'.chain.now < ch.deadline))
    (hbase2 : net.chain.finalizedWith c2.address = some ss2.state.outcome ∨
      (∃ t0, net.chain.statusOf c2 = .open t0 ∧ t0 ≤ ss2.state.turnNum) ∨
      (∃ t0 ch, net.chain.statusOf c2 = .challenged t0 ch ∧
        (t0 < ss2.state.turnNum ∨ ch.state = ss2.state) ∧ net'.chain.now < ch.deadline)) :
    (net'.chain.finalizedWith c1.address = some ss1.state.outcome ∨
      ∃ T0 ch, net'.chain.statusOf c1 = .challenged T0 ch ∧ ss1.state.turnNum ≤ T0 ∧
        ch.state = ss1.state ∧ net'.chain.now < ch.deadline) ∧
    (net'.chain.finalizedWith c2.address = some ss2.state.outcome ∨
      ∃ T0 ch, net'.chain.statusOf c2 = .challenged T0 ch ∧ ss2.state.turnNum ≤ T0 ∧
        ch.state = ss2.state ∧ net'.chain.now < ch.deadline) := by
  have hmono_n1 : n1.chain.now ≤ net'.chain.now :=
    le_trans (NetworkState.applyAdv_now_le apps n1 (.land (Op.challenge c1 [ss1] ss1.state)))
      hmid.now_le
  have hεbound_n1 : net'.chain.now < n1.chain.now + T.ε :=
    lt_of_lt_of_le hεbound (Nat.add_le_add_right hpre.now_le T.ε)
  -- `c2`'s pre-land invariant, carried unaffected to `n1`.
  have hbase2_n1 := latest_round_keeps_status_nil_prelanding hbounds hC2
    (D := net'.chain.now) hpre hmono_n1 hεbound hlatest2 hfinal2 hbase2
  -- `c1`'s pre-land invariant, carried unaffected to `n1`.
  have hbase1_n1 := latest_round_keeps_status_nil_prelanding hbounds hC1
    (D := net'.chain.now) hpre hmono_n1 hεbound hlatest1 hfinal1 hbase1
  -- `c1` lands at `n1`.
  have hc1_landed := land_own_challenge_transitions_status hC1 hall1 hchan1
    (net1 := n1) (net' := net') hεbound_n1 hmono_n1 hbase1_n1
  -- `c2`'s invariant survives `c1`'s own land (different channels).
  have hframe1 := land_challenge_other_statusOf (apps := apps) (c := c2) (c' := c1) hne
    [ss1] ss1.state n1
  set net1' := n1.applyAdv apps (.land (Op.challenge c1 [ss1] ss1.state)) with hnet1'def
  have hbase2_landed : net1'.chain.finalizedWith c2.address = some ss2.state.outcome ∨
      (∃ t0, net1'.chain.statusOf c2 = .open t0 ∧ t0 ≤ ss2.state.turnNum) ∨
      (∃ t0 ch, net1'.chain.statusOf c2 = .challenged t0 ch ∧
        (t0 < ss2.state.turnNum ∨ ch.state = ss2.state) ∧
        net'.chain.now < ch.deadline) := by
    rw [hnet1'def, hframe1.1, hframe1.2]; exact hbase2_n1
  obtain ⟨n2, hmid_pre, hmid_post⟩ :=
    Threat.RoundSeq.peel_one (Op.challenge c2 [ss2] ss2.state) _ _ hmid
  have hmono_n2 : n2.chain.now ≤ net'.chain.now :=
    le_trans (NetworkState.applyAdv_now_le apps n2 (.land (Op.challenge c2 [ss2] ss2.state)))
      hmid_post.now_le
  have hn1_le_n2 : n1.chain.now ≤ n2.chain.now :=
    le_trans (NetworkState.applyAdv_now_le apps n1 (.land (Op.challenge c1 [ss1] ss1.state)))
      hmid_pre.now_le
  have hεbound_n2 : net'.chain.now < n2.chain.now + T.ε :=
    lt_of_lt_of_le hεbound_n1 (Nat.add_le_add_right hn1_le_n2 T.ε)
  have hnet1'_sent : net1'.sent = net.sent := by
    rw [hnet1'def, NetworkState.applyAdv_sent]; exact hpre.sent_eq
  have hn2_sent : n2.sent = net.sent := by rw [hmid_pre.sent_eq, hnet1'_sent]
  have hnet1'_now : net1'.chain.now = n1.chain.now := by
    rw [hnet1'def]
    simp only [NetworkState.applyAdv]
    cases h : n1.chain.apply apps p (Op.challenge c1 [ss1] ss1.state) with
    | none => rfl
    | some s' => obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h; rfl
  have hεbound_n1' : net'.chain.now < net1'.chain.now + T.ε := hnet1'_now ▸ hεbound_n1
  -- `c1`'s now-landed invariant, carried unaffected through the no-land phase to `n2`.
  have hc1_n2 := latest_round_keeps_status_nil_D hbounds hC1.toConsensusMember
    (D := net'.chain.now) hmid_pre hmono_n2 (by rw [hnet1'_sent]; exact hlatest1)
    (by rw [hnet1'_sent]; exact hfinal1) hc1_landed
  -- `c2`'s pre-land invariant, carried unaffected through the same phase.
  have hbase2_n2 := latest_round_keeps_status_nil_prelanding hbounds hC2
    (D := net'.chain.now) hmid_pre hmono_n2 hεbound_n1' (by rw [hnet1'_sent]; exact hlatest2)
    (by rw [hnet1'_sent]; exact hfinal2) hbase2_landed
  -- `c2` lands at `n2`.
  have hc2_landed := land_own_challenge_transitions_status hC2 hall2 hchan2
    (net1 := n2) (net' := net') hεbound_n2 hmono_n2 hbase2_n2
  -- `c1`'s invariant survives `c2`'s own land (different channels).
  have hframe2 := land_challenge_other_statusOf (apps := apps) (c := c1) (c' := c2) hne.symm
    [ss2] ss2.state n2
  set net2' := n2.applyAdv apps (.land (Op.challenge c2 [ss2] ss2.state)) with hnet2'def
  have hc1_landed2 : net2'.chain.finalizedWith c1.address = some ss1.state.outcome ∨
      ∃ T0 ch, net2'.chain.statusOf c1 = .challenged T0 ch ∧ ss1.state.turnNum ≤ T0 ∧
        ch.state = ss1.state ∧ net'.chain.now < ch.deadline := by
    rw [hnet2'def, hframe2.1, hframe2.2]; exact hc1_n2
  have hn2'_sent : net2'.sent = net.sent := by
    rw [hnet2'def, NetworkState.applyAdv_sent]; exact hn2_sent
  -- the final no-land phase to `net'`, for both channels.
  have hc1_final := latest_round_keeps_status_nil_D hbounds hC1.toConsensusMember
    (D := net'.chain.now) hmid_post (le_refl _)
    (by rw [hn2'_sent]; exact hlatest1) (by rw [hn2'_sent]; exact hfinal1) hc1_landed2
  have hc2_final := latest_round_keeps_status_nil_D hbounds hC2.toConsensusMember
    (D := net'.chain.now) hmid_post (le_refl _)
    (by rw [hn2'_sent]; exact hlatest2) (by rw [hn2'_sent]; exact hfinal2) hc2_landed
  exact ⟨hc1_final, hc2_final⟩

/-- One round of a two-call reaction `[Op.challenge c1 ..., Op.challenge c2
    ...]` (`satp_intermediary_before_round2`'s argument): whichever of the
    two the adversary front-runs and lands first
    (`Threat.RoundSeq.peel_two`), `latest_round_keeps_status_two_ordered`
    applies — directly, or with `c1`/`c2` swapped, since the adversary's
    choice of order is exactly that lemma's own case split. Each channel's
    own `T.ε` deadline margin (`hbase1`/`hbase2`, each against the ROUND's
    own end `net'`, never `2 * T.ε`) suffices for BOTH calls, because they
    share the one round's single `T.ε` bound, not two sequential rounds'
    worth. -/
theorem latest_round_keeps_status_two {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c1 c2 : FixedPart} {ss1 ss2 : SignedState E} (hne : c1 ≠ c2)
    (hC1 : TimedConsensusMember apps p T.ε c1) (hC2 : TimedConsensusMember apps p T.ε c2)
    (hall1 : ss1.ByAll) (hchan1 : ss1.state.channel = c1)
    (hall2 : ss2.ByAll) (hchan2 : ss2.state.channel = c2)
    {net net' : NetworkState E p} (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.TimedRun apps T t
      [Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state] net net') :
    (∀ t0 ∈ net.sent, t0.state.channel = c1 →
      t0.state.turnNum < ss1.state.turnNum ∨ t0.state = ss1.state) →
    (∀ t0 ∈ net.sent, t0.state.channel = c2 →
      t0.state.turnNum < ss2.state.turnNum ∨ t0.state = ss2.state) →
    (∀ t0 ∈ net.sent, t0.state.channel = c1 → t0.state.isFinal = true →
      t0.state.outcome = ss1.state.outcome) →
    (∀ t0 ∈ net.sent, t0.state.channel = c2 → t0.state.isFinal = true →
      t0.state.outcome = ss2.state.outcome) →
    (net.chain.finalizedWith c1.address = some ss1.state.outcome ∨
      (∃ t0, net.chain.statusOf c1 = .open t0 ∧ t0 ≤ ss1.state.turnNum) ∨
      (∃ t0 ch, net.chain.statusOf c1 = .challenged t0 ch ∧
        (t0 < ss1.state.turnNum ∨ ch.state = ss1.state) ∧ net'.chain.now < ch.deadline)) →
    (net.chain.finalizedWith c2.address = some ss2.state.outcome ∨
      (∃ t0, net.chain.statusOf c2 = .open t0 ∧ t0 ≤ ss2.state.turnNum) ∨
      (∃ t0 ch, net.chain.statusOf c2 = .challenged t0 ch ∧
        (t0 < ss2.state.turnNum ∨ ch.state = ss2.state) ∧ net'.chain.now < ch.deadline)) →
    (net'.chain.finalizedWith c1.address = some ss1.state.outcome ∨
      ∃ T0 ch, net'.chain.statusOf c1 = .challenged T0 ch ∧ ss1.state.turnNum ≤ T0 ∧
        ch.state = ss1.state ∧ net'.chain.now < ch.deadline) ∧
    (net'.chain.finalizedWith c2.address = some ss2.state.outcome ∨
      ∃ T0 ch, net'.chain.statusOf c2 = .challenged T0 ch ∧ ss2.state.turnNum ≤ T0 ∧
        ch.state = ss2.state ∧ net'.chain.now < ch.deadline) := by
  obtain ⟨hseq, hεb⟩ := hseq; revert hεb
  clear ht
  intro hεbound hlatest1 hlatest2 hfinal1 hfinal2 hbase1 hbase2
  rcases hseq.peel_two with ⟨n1, hpre, hmid⟩ | ⟨n1, hpre, hmid⟩
  · exact latest_round_keeps_status_two_ordered hbounds hne hC1 hC2 hall1 hchan1 hall2
      hchan2 hpre hmid hεbound hlatest1 hlatest2 hfinal1 hfinal2 hbase1 hbase2
  · have hswap := latest_round_keeps_status_two_ordered hbounds hne.symm hC2 hC1 hall2
      hchan2 hall1 hchan1 hpre hmid hεbound hlatest2 hlatest1 hfinal2 hfinal1 hbase2
      hbase1
    exact ⟨hswap.2, hswap.1⟩

/-- One round of adversary play on `p`'s own `challenge c [ss] ss.state`
    call, under the explicit-time game: `p`'s call lands exactly once
    (`pending` is the singleton `[Op.challenge c [ss] ss.state]`), always
    moving the record to "challenged, at least `ss.state.turnNum`" — either
    it succeeds (the `open`/`challenge`-mode precondition always holds once
    the turn record is at or below `ss.state.turnNum`, Nitro:540-542's
    front-running: whatever the adversary did first, `p`'s own candidate is
    never behind), landing `.challenged ss.state.turnNum ⟨ss.state, now +
    challengeDuration⟩` exactly; or it fails, which (given `hall`, `hchan`,
    so every OTHER precondition of `challenge` holds) only happens when the
    record is already finalized, or already at or above `ss.state.turnNum`
    — in the finalized case `hbase`'s own disjunct carries unchanged, in the
    latter case `hbase`'s "challenged" disjunct's own turn bound forces it
    to be the same `ss.state`-matching record already. Either way the
    result feeds `latest_round_keeps_status_nil`, whose own turn-bound
    argument (`hbounds.unforgeable`) shows no later adversary play in the
    same round pushes the record past `ss.state.turnNum`. Used by
    `latest_state_finalizable`; closes the old two gaps (`hopen`/`hlt`
    branches) by proving them unreachable in a single round, not by a
    second one. -/
theorem latest_round_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E}
    (hc : apps c.appDef = consensusRules) (hp : p ∈ c.participants) (hall : ss.ByAll)
    (hchan : ss.state.channel = c) (hdur : 2 * T.ε ≤ c.challengeDuration)
    {net net' : NetworkState E p} (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.RoundSeq apps T t [Op.challenge c [ss] ss.state] net net') :
    net'.chain.now < net.chain.now + T.ε →
    (∀ t0 ∈ net.sent, t0.state.channel = c →
      t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) →
    (∀ t0 ∈ net.sent, t0.state.channel = c → t0.state.isFinal = true →
      t0.state.outcome = ss.state.outcome) →
    (net.chain.finalizedWith c.address = some ss.state.outcome ∨
      (∃ t0, net.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
      (∃ t0 ch, net.chain.statusOf c = .challenged t0 ch ∧
        (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline)) →
    net'.chain.finalizedWith c.address = some ss.state.outcome ∨
      ∃ T0 ch, net'.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
        ch.state = ss.state ∧ net'.chain.now < ch.deadline := by
  clear ht
  intro hεbound hlatest hfinal hbase
  obtain ⟨n1, hpre, hpost⟩ := hseq.peel_one
  have hmono0 : n1.chain.now ≤ net'.chain.now :=
    le_trans (NetworkState.applyAdv_now_le apps n1 (.land (Op.challenge c [ss] ss.state)))
      hpost.now_le
  have hεbound1 : net'.chain.now < n1.chain.now + T.ε :=
    lt_of_lt_of_le hεbound (Nat.add_le_add_right hpre.now_le T.ε)
  have hbase1 := latest_round_keeps_status_nil_prelanding hbounds ⟨⟨hc, hp⟩, hdur⟩
    (D := net'.chain.now) hpre hmono0 hεbound hlatest hfinal hbase
  have hland := land_own_challenge_transitions_status ⟨⟨hc, hp⟩, hdur⟩ hall hchan hεbound1 hmono0 hbase1
  have hεbound' : net'.chain.now <
      (n1.applyAdv apps (.land (Op.challenge c [ss] ss.state))).chain.now + T.ε :=
    lt_of_lt_of_le hεbound1
      (Nat.add_le_add_right
        (NetworkState.applyAdv_now_le apps n1 (.land (Op.challenge c [ss] ss.state))) T.ε)
  have hlatest_land : ∀ t0 ∈
      (n1.applyAdv apps (.land (Op.challenge c [ss] ss.state))).sent,
      t0.state.channel = c → t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
    rw [NetworkState.applyAdv_sent, hpre.sent_eq]; exact hlatest
  have hfinal_land : ∀ t0 ∈
      (n1.applyAdv apps (.land (Op.challenge c [ss] ss.state))).sent,
      t0.state.channel = c → t0.state.isFinal = true →
      t0.state.outcome = ss.state.outcome := by
    rw [NetworkState.applyAdv_sent, hpre.sent_eq]; exact hfinal
  exact latest_round_keeps_status_nil hbounds hc hp hdur hpost hεbound' hlatest_land
    hfinal_land hland

/-- One round of adversary play keeps "finalized with `ss.state.outcome`, or
    still challenged with the fixed `ch`" (`ch.state = ss.state`): the same
    turn-bound argument as `latest_round_keeps_status`, specialized to a
    status already at `ss.state.turnNum`, so no legal `challenge` or
    `checkpoint` can move it (a candidate's turn is at most
    `ss.state.turnNum`, by `hlatest`, but both operations need a turn
    strictly above the current record). `p`'s own move during this phase
    is always `.wait`, which carries no pending call, so the round never
    hits `Threat.RoundSeq.land`. Used by `latest_state_finalizable` for the
    wait phase, after `p`'s own challenge lands. -/
theorem latest_wait_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {T0 : Nat} {ch : Challenge E}
    (hC : ConsensusMember apps p c) (hchs : ch.state = ss.state)
    (hT0 : ss.state.turnNum ≤ T0) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) →
      (∀ t0 ∈ net.sent, t0.state.channel = c → t0.state.isFinal = true →
        t0.state.outcome = ss.state.outcome) →
      (net.chain.finalizedWith c.address = some ss.state.outcome ∨
        net.chain.statusOf c = .challenged T0 ch) →
      net'.chain.finalizedWith c.address = some ss.state.outcome ∨
        net'.chain.statusOf c = .challenged T0 ch := by
  intro net net' t hseq
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; (simp? at hsplit says simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hlatest hfinal hbase
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        net1.chain.statusOf c = .challenged T0 ch) →
        ((net1.applyAdv apps (AdvMove.tick dt)).chain.finalizedWith c.address =
          some ss.state.outcome ∨
        (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .challenged T0 ch) := by
      intro hbase1
      rcases hbase1 with hf | hst
      · refine Or.inl ?_
        simpa [NetworkState.applyAdv, FixedPart.address_eq] using
          ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
            (Nat.le_add_right _ dt)
      · by_cases hexp : ch.deadline ≤ net1.chain.now
        · have hf : net1.chain.finalizedWith c.address = some ss.state.outcome := by
            simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
              ChannelStatus.finalizedWith_challenged, if_pos hexp, hchs]
          refine Or.inl ?_
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
              (Nat.le_add_right _ dt)
        · exact Or.inr (by (simpa? [NetworkState.applyAdv] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst))
    have hbase' := step hbase
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hpnil hlatest' hfinal' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hlatest hfinal hbase
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ net1.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum ≤ ss.state.turnNum := by
      intro proof cand hU hs
      obtain ⟨x, hx, hxs, hch⟩ := hC.sent_cand hU hs
      have hb := hlatest x hx (by rw [hxs]; exact hch)
      rw [hxs] at hb
      rcases hb with hlt | heqc
      · exact le_of_lt hlt
      · exact le_of_eq (by rw [heqc])
    have step : (net1.chain.finalizedWith c.address = some ss.state.outcome ∨
        net1.chain.statusOf c = .challenged T0 ch) →
        ((net1.applyAdv apps m).chain.finalizedWith c.address = some ss.state.outcome ∨
        (net1.applyAdv apps m).chain.statusOf c = .challenged T0 ch) := by
      intro hbase1
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver ss' =>
        rcases hbase1 with hf | hst
        · exact Or.inl hf
        · exact Or.inr hst
      | chain caller op =>
        rcases hbase1 with hf | hst
        · refine Or.inl ?_
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => (simpa? using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
          | some s' => exact Adjudicator.finalizedWith_apply h hf
        · by_cases hexp : ch.deadline ≤ net1.chain.now
          · have hf : net1.chain.finalizedWith c.address = some ss.state.outcome := by
              simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, if_pos hexp, hchs]
            refine Or.inl ?_
            simp only [NetworkState.applyAdv]
            cases h : net1.chain.apply apps caller op with
            | none => (simpa? using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
            | some s' => exact Adjudicator.finalizedWith_apply h hf
          · simp only [NetworkState.applyAdv]
            cases h : net1.chain.apply apps caller op with
            | none => exact Or.inr hst
            | some s' =>
              have hfo1 : net1.chain.finalOutcome c.address = none := by
                simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
                  ChannelStatus.finalOutcome_challenged, if_neg hexp]
              have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
                  ∃ x ∈ net1.sent, x.state = ss'.state :=
                fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
              cases op with
              | deposit a e x =>
                obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
                refine Or.inr ?_
                rw [Adjudicator.statusOf_of_status hs]; exact hst
              | tick dt =>
                have hs' : net1.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
                subst hs'
                refine Or.inr ?_
                rw [Adjudicator.tick_statusOf]; exact hst
              | transfer a b =>
                by_cases hac : a = c
                · subst hac
                  obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                  refine Or.inr ?_
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]
                  exact hst
              | reclaim l v =>
                by_cases hlc : l = c
                · subst hlc
                  obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
                  refine Or.inr ?_
                  rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                  exact hst
              | challenge c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  obtain ⟨⟨-, hs, -, hm⟩, rfl⟩ := Adjudicator.challenge_some h
                  have hturn := hsupp proof cand hU hs
                  rw [Adjudicator.mode_eq, hst] at hm
                  simp only [ChannelStatus.mode_challenged, ChannelStatus.turnNumRecord_challenged,
                    if_neg hexp] at hm
                  rcases hm with ⟨hm, -⟩ | ⟨-, hlt⟩
                  · cases hm
                  · omega
                · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
                  refine Or.inr ?_
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                  exact hst
              | checkpoint c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  obtain ⟨⟨-, hs, -, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
                  have hturn := hsupp proof cand hU hs
                  rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt
                  omega
                · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
                  refine Or.inr ?_
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                  exact hst
              | conclude c' ss' =>
                by_cases hcc : c' = c
                · subst hcc
                  obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
                  refine Or.inl ?_
                  have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hC.mem)
                  have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by (simp? [Op.proofStates] says simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false])
                  obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
                  have hΩ' := hfinal x hxmem (hxeq ▸ hproof'.1) (hxeq ▸ hproof'.2.1)
                  (simp? [Adjudicator.finalizedWith_channel, hxeq ▸ hΩ'] says simp only [hxeq ▸ hΩ', FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized])
                · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
                  refine Or.inr ?_
                  rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
                  exact hst
    have hbase' := step hbase
    have hlatest' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state := by
      rw [NetworkState.applyAdv_sent]; exact hlatest
    have hfinal' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
        t0.state.isFinal = true → t0.state.outcome = ss.state.outcome := by
      rw [NetworkState.applyAdv_sent]; exact hfinal
    exact ih hpnil hlatest' hfinal' hbase'

/-- Waiting `w` ticks past a channel's deadline-or-already-finalized state
    finalizes it: either it was already finalized at `net2` and stays so
    (`Threat.RoundSeq.finalizedWith_mono` through the adversary's own
    sub-round, `ChannelStatus.finalizedWith_mono` through the wait's own
    tick), or it is challenged with a recorded deadline `d`, which `w`
    reaches (`hdw`), and `latest_wait_keeps_status` shows no adversary play
    during the sub-round moves the record past `ss.state.turnNum`.
    Parameterized by a FIXED `d`, decoupled from the deadline's own channel,
    so `latest_state_finalizable_two`'s `finish2` can share one `w` (the
    max of two channels' own needs) between two calls of this lemma. -/
theorem wait_resolves_challenge {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E}
    (hC : ConsensusMember apps p c)
    {net2 net3 : NetworkState E p} {d w : Time}
    (hle : net2.chain.now ≤ d) (hdw : d ≤ net2.chain.now + w)
    (hlatest : ∀ t ∈ net2.sent, t.state.channel = c →
      t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state)
    (hfinal : ∀ t ∈ net2.sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = ss.state.outcome)
    (hseq2 : Threat.RoundSeq apps T net2.chain.now [] net2 net3)
    (hb : net2.chain.finalizedWith c.address = some ss.state.outcome ∨
      ∃ T0 ch, net2.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
        ch.state = ss.state ∧ ch.deadline = d) :
    (net3.chain.tick w).finalizedWith c.address = some ss.state.outcome := by
  have hmono2 : net2.chain.now ≤ net3.chain.now := hseq2.now_le
  rcases hb with hf | ⟨T0, ch, hst, hT0, hchs, hd⟩
  · have hf3 : net3.chain.finalizedWith c.address = some ss.state.outcome :=
      hseq2.finalizedWith_mono hf
    simpa [Adjudicator.tick_statusOf, Adjudicator.tick_now, FixedPart.address_eq] using
      ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf3)
        (Nat.le_add_right _ w)
  · have hinv2 := latest_wait_keeps_status hbounds hC hchs hT0 hseq2 hlatest hfinal (Or.inr hst)
    rcases hinv2 with hf3 | hst3
    · simpa [Adjudicator.tick_statusOf, Adjudicator.tick_now, FixedPart.address_eq] using
        ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf3)
          (Nat.le_add_right _ w)
    · have hge : ch.deadline ≤ net3.chain.now + w :=
        hd ▸ le_trans hdw (Nat.add_le_add_right hmono2 w)
      simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
        Adjudicator.tick_statusOf, hst3, Adjudicator.tick_now,
        ChannelStatus.finalizedWith_challenged, if_pos hge, hchs]

/-- Nitro-12, ForceMove-B01, ForceMove-B03, docs-0070-06, ForceMove-C02.
    SATP:290-292: "an adjudicator implements a challenge operation, enabling
    peers to recover funds from the channel after a timeout"; Nitro:292-296:
    "if no other participant responds during the timeout period, then the
    challenge times out and the outcome corresponding to the challenge state
    is finalized." go-nitro: a later challenge or checkpoint needs a strictly
    higher turn (ForceMove.sol:48-50, 95), so the holder of the highest
    supported state wins.
    Under the consensus app, a participant who holds a supported state, has
    signed no other state at that turn or above, and sees no chain record
    above it, can finalize that state's outcome. -/
theorem latest_state_finalizable (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε) (ss : SignedState E)
    (hc : apps (c : FixedPart).appDef = consensusRules) (hp : p ∈ (c : FixedPart).participants)
    (hh : net.state.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = (c : FixedPart))
    (hlatest : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) →
      t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state)
    (hfinal : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) → t.state.isFinal = true →
      t.state.outcome = ss.state.outcome)
    (hst : net.state.Finalized (c : FixedPart) ss.state.outcome ∨
      (∃ t, net.state.chain.statusOf (c : FixedPart) = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.state.chain.statusOf (c : FixedPart) = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.state.chain.now + T.ε ≤ ch.deadline)) :
    Finalizable apps T (c : FixedPart) ss.state.outcome net.state := by
  obtain_reach ⟨net, _hr⟩ := net
  obtain ⟨c, hdur⟩ := c
  rcases hst with hfz | hst'
  · exact UnbeatableIn.done hfz
  have finish : ∀ (net2 : NetworkState E p) (T0 : Nat) (ch2 : Challenge E),
      ch2.state = ss.state → ss.state.turnNum ≤ T0 →
      net2.chain.statusOf c = .challenged T0 ch2 →
      net2.chain.now ≤ ch2.deadline → net2.sent = net.sent →
      UnbeatableIn apps T (fun _ => True) (fun n => n.Finalized c ss.state.outcome) net2 := by
    intro net2 T0 ch2 hch2s hT0 hch2 hle2 hsent2
    refine UnbeatableIn.move (.wait (ch2.deadline - net2.chain.now)) trivial trivial ?_
    intro net3 hround2
    obtain ⟨hseq2, -⟩ := hround2
    have hmono2 : net2.chain.now ≤ net3.chain.now := hseq2.now_le
    have hlatest2 : ∀ t ∈ net2.sent, t.state.channel = c →
        t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state := by rw [hsent2]; exact hlatest
    have hfinal2 : ∀ t ∈ net2.sent, t.state.channel = c → t.state.isFinal = true →
        t.state.outcome = ss.state.outcome := by rw [hsent2]; exact hfinal
    have hinv2 := latest_wait_keeps_status A.toBounds ⟨hc, hp⟩ hch2s hT0 hseq2 hlatest2 hfinal2
      (Or.inr hch2)
    apply UnbeatableIn.done
    show (net3.applyHonest (.wait (ch2.deadline - net2.chain.now))).Finalized c
      ss.state.outcome
    show (net3.chain.tick (ch2.deadline - net2.chain.now)).finalizedWith c.address =
      some ss.state.outcome
    rcases hinv2 with hf3 | hst3
    · simpa [Adjudicator.tick_statusOf, Adjudicator.tick_now, FixedPart.address_eq] using
        ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf3)
          (Nat.le_add_right _ _)
    · have hge : ch2.deadline ≤ net3.chain.now + (ch2.deadline - net2.chain.now) := by
        have h1 : net2.chain.now + (ch2.deadline - net2.chain.now) = ch2.deadline :=
          Nat.add_sub_cancel' hle2
        calc ch2.deadline = net2.chain.now + (ch2.deadline - net2.chain.now) := h1.symm
          _ ≤ net3.chain.now + (ch2.deadline - net2.chain.now) := Nat.add_le_add_right hmono2 _
      simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
        Adjudicator.tick_statusOf, hst3, Adjudicator.tick_now,
        ChannelStatus.finalizedWith_challenged, if_pos hge, hch2s]
  refine UnbeatableIn.move (.chain (.challenge c [ss] ss.state)) trivial
    (by (simpa? [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh says simpa only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hh)) ?_
  intro net1 hround
  obtain ⟨hseq, hεbound⟩ := hround
  simp only [HonestMove.calls_chain] at hseq
  have hbase : net.chain.finalizedWith c.address = some ss.state.outcome ∨
      (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net1.chain.now < ch.deadline) := by
    rcases hst' with ho | ⟨t, ch, hstt, hlt, hdd⟩
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr ⟨t, ch, hstt, hlt, lt_of_lt_of_le hεbound hdd⟩)
  have hinv := latest_round_keeps_status A.toBounds hc hp hall hchan hdur net.chain.now rfl hseq
    hεbound hlatest hfinal hbase
  rcases hinv with hfz' | ⟨T0, ch, hchal, hT0, hchs, hdd⟩
  · apply UnbeatableIn.done
    (simpa? [NetworkState.Finalized, NetworkState.applyHonest_chain] using hfz' says simpa only [NetworkState.Finalized, NetworkState.applyHonest_chain, FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hfz')
  · exact finish net1 T0 ch hchs hT0 hchal (le_of_lt hdd) hseq.sent_eq

/-- Two-channel analogue of `latest_state_finalizable`: `p` holds the latest
    state of BOTH `c1` and `c2`, neither already finalized, each with its
    own `T.ε` deadline margin if currently mid-challenge (never `2 * T.ε`
    on either — `satp_intermediary_before_round2`'s argument, the fix
    `Strategy.lean`'s header describes). `p`'s one reaction issues BOTH
    challenges together (`HonestMove.react`, `Reaction.calls`), so both
    land before the SAME round's `t + T.ε` (`latest_round_keeps_status_two`);
    `finish2` then waits out whichever of the two resulting deadlines is
    later (or not at all, if both already finalized by the round's end),
    via `wait_resolves_challenge` once per channel against the one shared
    wait. The strategy plays only that reaction and one wait, so it is a
    strategy in any `allowed` that admits both (`hreact`, `hwait`). -/
theorem latest_state_finalizable_two (apps : Apps E) {p : Participant} (T : Threat E p)
    {allowed : HonestMove E → Prop} (A : Assumptions apps p T) (net : NetworkState E p)
    (_hr : (Nitro.participant apps T).Reachable net)
    (c1 c2 : FixedPart) (ss1 ss2 : SignedState E) (hne : c1 ≠ c2)
    (hC1 : TimedConsensusMember apps p T.ε c1) (hC2 : TimedConsensusMember apps p T.ε c2)
    (hh1 : net.Holds ss1) (hh2 : net.Holds ss2) (hall1 : ss1.ByAll) (hall2 : ss2.ByAll)
    (hchan1 : ss1.state.channel = c1) (hchan2 : ss2.state.channel = c2)
    (hlatest1 : ∀ t ∈ net.sent, t.state.channel = c1 →
      t.state.turnNum < ss1.state.turnNum ∨ t.state = ss1.state)
    (hlatest2 : ∀ t ∈ net.sent, t.state.channel = c2 →
      t.state.turnNum < ss2.state.turnNum ∨ t.state = ss2.state)
    (hfinal1 : ∀ t ∈ net.sent, t.state.channel = c1 → t.state.isFinal = true →
      t.state.outcome = ss1.state.outcome)
    (hfinal2 : ∀ t ∈ net.sent, t.state.channel = c2 → t.state.isFinal = true →
      t.state.outcome = ss2.state.outcome)
    (hst1 : (∃ t, net.chain.statusOf c1 = .open t ∧ t ≤ ss1.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c1 = .challenged t ch ∧
        (t < ss1.state.turnNum ∨ ch.state = ss1.state) ∧ net.chain.now + T.ε ≤ ch.deadline))
    (hst2 : (∃ t, net.chain.statusOf c2 = .open t ∧ t ≤ ss2.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c2 = .challenged t ch ∧
        (t < ss2.state.turnNum ∨ ch.state = ss2.state) ∧ net.chain.now + T.ε ≤ ch.deadline))
    (hreact : allowed
      (.react ⟨[Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state], []⟩))
    (hwait : ∀ dt, allowed (.wait dt)) :
    UnbeatableIn apps T allowed
      (fun n => n.Finalized c1 ss1.state.outcome ∧ n.Finalized c2 ss2.state.outcome) net := by
  have finish2 : ∀ (net2 : NetworkState E p),
      (net2.chain.finalizedWith c1.address = some ss1.state.outcome ∨
        ∃ T0 ch, net2.chain.statusOf c1 = .challenged T0 ch ∧ ss1.state.turnNum ≤ T0 ∧
          ch.state = ss1.state ∧ net2.chain.now ≤ ch.deadline) →
      (net2.chain.finalizedWith c2.address = some ss2.state.outcome ∨
        ∃ T0 ch, net2.chain.statusOf c2 = .challenged T0 ch ∧ ss2.state.turnNum ≤ T0 ∧
          ch.state = ss2.state ∧ net2.chain.now ≤ ch.deadline) →
      net2.sent = net.sent →
      UnbeatableIn apps T allowed
        (fun n => n.Finalized c1 ss1.state.outcome ∧ n.Finalized c2 ss2.state.outcome) net2 := by
    intro net2 hb1 hb2 hsent2
    obtain ⟨d1, hle1, hb1'⟩ :
        ∃ d1, net2.chain.now ≤ d1 ∧
          (net2.chain.finalizedWith c1.address = some ss1.state.outcome ∨
           ∃ T0 ch, net2.chain.statusOf c1 = .challenged T0 ch ∧ ss1.state.turnNum ≤ T0 ∧
             ch.state = ss1.state ∧ ch.deadline = d1) := by
      rcases hb1 with hf1 | ⟨T0, ch, hst, hT0, hchs, hle⟩
      · exact ⟨net2.chain.now, le_refl _, Or.inl hf1⟩
      · exact ⟨ch.deadline, hle, Or.inr ⟨T0, ch, hst, hT0, hchs, rfl⟩⟩
    obtain ⟨d2, hle2, hb2'⟩ :
        ∃ d2, net2.chain.now ≤ d2 ∧
          (net2.chain.finalizedWith c2.address = some ss2.state.outcome ∨
           ∃ T0 ch, net2.chain.statusOf c2 = .challenged T0 ch ∧ ss2.state.turnNum ≤ T0 ∧
             ch.state = ss2.state ∧ ch.deadline = d2) := by
      rcases hb2 with hf2 | ⟨T0, ch, hst, hT0, hchs, hle⟩
      · exact ⟨net2.chain.now, le_refl _, Or.inl hf2⟩
      · exact ⟨ch.deadline, hle, Or.inr ⟨T0, ch, hst, hT0, hchs, rfl⟩⟩
    refine UnbeatableIn.move (.wait (max d1 d2 - net2.chain.now)) (hwait _) trivial ?_
    intro net3 hround2
    obtain ⟨hseq2, -⟩ := hround2
    have hmax1 : net2.chain.now ≤ max d1 d2 := le_trans hle1 (le_max_left _ _)
    have hwdef : net2.chain.now + (max d1 d2 - net2.chain.now) = max d1 d2 :=
      Nat.add_sub_cancel' hmax1
    have hdw1 : d1 ≤ net2.chain.now + (max d1 d2 - net2.chain.now) := by
      rw [hwdef]; exact le_max_left _ _
    have hdw2 : d2 ≤ net2.chain.now + (max d1 d2 - net2.chain.now) := by
      rw [hwdef]; exact le_max_right _ _
    have hlatest1' : ∀ t ∈ net2.sent, t.state.channel = c1 →
        t.state.turnNum < ss1.state.turnNum ∨ t.state = ss1.state := by
      rw [hsent2]; exact hlatest1
    have hfinal1' : ∀ t ∈ net2.sent, t.state.channel = c1 → t.state.isFinal = true →
        t.state.outcome = ss1.state.outcome := by rw [hsent2]; exact hfinal1
    have hlatest2' : ∀ t ∈ net2.sent, t.state.channel = c2 →
        t.state.turnNum < ss2.state.turnNum ∨ t.state = ss2.state := by
      rw [hsent2]; exact hlatest2
    have hfinal2' : ∀ t ∈ net2.sent, t.state.channel = c2 → t.state.isFinal = true →
        t.state.outcome = ss2.state.outcome := by rw [hsent2]; exact hfinal2
    apply UnbeatableIn.done
    refine ⟨?_, ?_⟩
    · show (net3.applyHonest (.wait (max d1 d2 - net2.chain.now))).Finalized c1 ss1.state.outcome
      show (net3.chain.tick (max d1 d2 - net2.chain.now)).finalizedWith c1.address =
        some ss1.state.outcome
      exact wait_resolves_challenge A.toBounds hC1.toConsensusMember hle1 hdw1 hlatest1' hfinal1'
        hseq2 hb1'
    · show (net3.applyHonest (.wait (max d1 d2 - net2.chain.now))).Finalized c2 ss2.state.outcome
      show (net3.chain.tick (max d1 d2 - net2.chain.now)).finalizedWith c2.address =
        some ss2.state.outcome
      exact wait_resolves_challenge A.toBounds hC2.toConsensusMember hle2 hdw2 hlatest2' hfinal2'
        hseq2 hb2'
  have hfeasR : Reaction.Feasible net
      ⟨[Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state], []⟩ := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · (simpa? [Op.HonestFeasible, Op.proofStates] using hh1 says simpa only [Op.HonestFeasible, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hh1)
    · (simpa? [Op.HonestFeasible, Op.proofStates] using hh2 says simpa only [Op.HonestFeasible, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hh2)
  refine UnbeatableIn.move
    (.react ⟨[Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state], []⟩) hreact
    ⟨hfeasR, fun _ h => absurd h List.not_mem_nil⟩ ?_
  intro net1 hround
  obtain ⟨hseq, hεbound⟩ := hround
  have hbase1 : net.chain.finalizedWith c1.address = some ss1.state.outcome ∨
      (∃ t, net.chain.statusOf c1 = .open t ∧ t ≤ ss1.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c1 = .challenged t ch ∧
        (t < ss1.state.turnNum ∨ ch.state = ss1.state) ∧ net1.chain.now < ch.deadline) := by
    rcases hst1 with ho | ⟨t, ch, hstt, hlt, hdd⟩
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr ⟨t, ch, hstt, hlt, lt_of_lt_of_le hεbound hdd⟩)
  have hbase2 : net.chain.finalizedWith c2.address = some ss2.state.outcome ∨
      (∃ t, net.chain.statusOf c2 = .open t ∧ t ≤ ss2.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c2 = .challenged t ch ∧
        (t < ss2.state.turnNum ∨ ch.state = ss2.state) ∧ net1.chain.now < ch.deadline) := by
    rcases hst2 with ho | ⟨t, ch, hstt, hlt, hdd⟩
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr ⟨t, ch, hstt, hlt, lt_of_lt_of_le hεbound hdd⟩)
  have hinv := latest_round_keeps_status_two A.toBounds hne hC1 hC2 hall1 hchan1 hall2
    hchan2 net.chain.now rfl ⟨hseq, hεbound⟩ hlatest1 hlatest2 hfinal1 hfinal2 hbase1
    hbase2
  obtain ⟨hinv1, hinv2⟩ := hinv
  have hb1 : net1.chain.finalizedWith c1.address = some ss1.state.outcome ∨
      ∃ T0 ch, net1.chain.statusOf c1 = .challenged T0 ch ∧ ss1.state.turnNum ≤ T0 ∧
        ch.state = ss1.state ∧ net1.chain.now ≤ ch.deadline := by
    rcases hinv1 with h | ⟨T0, ch, hst, hT0, hchs, hdd⟩
    · exact Or.inl h
    · exact Or.inr ⟨T0, ch, hst, hT0, hchs, le_of_lt hdd⟩
  have hb2 : net1.chain.finalizedWith c2.address = some ss2.state.outcome ∨
      ∃ T0 ch, net1.chain.statusOf c2 = .challenged T0 ch ∧ ss2.state.turnNum ≤ T0 ∧
        ch.state = ss2.state ∧ net1.chain.now ≤ ch.deadline := by
    rcases hinv2 with h | ⟨T0, ch, hst, hT0, hchs, hdd⟩
    · exact Or.inl h
    · exact Or.inr ⟨T0, ch, hst, hT0, hchs, le_of_lt hdd⟩
  have hnet1 : net1.applyHonest
      (.react ⟨[Op.challenge c1 [ss1] ss1.state, Op.challenge c2 [ss2] ss2.state], []⟩) = net1 := by
    (simp? [NetworkState.applyHonest] says simp only [NetworkState.applyHonest, List.map_nil, List.nil_append])
  rw [hnet1]
  exact finish2 net1 hb1 hb2 hseq.sent_eq
/-- Over a round's play with nothing of `p`'s own still pending, "open at a
    turn at or above `ss.state.turnNum`, or challenged at a turn at or above
    `ss.state.turnNum` with a deadline still ahead" is preserved, when `p`
    has sent nothing of `c` above `ss.state.turnNum` except `ss.state`
    itself, and nothing final at all (`hsent`). The turn-bound argument of
    `latest_round_keeps_status_nil` applies unchanged to `challenge` and
    `checkpoint`: any OTHER candidate's turn is at or below
    `ss.state.turnNum`, so it can push the record no higher than where it
    already sits. A `conclude` on `c` is excluded outright, not merely
    assigned an outcome, because it needs `p`'s own signature on a final
    state of `c` (`ConclusionProof`, `p ∈ c.participants`), which
    `hbounds.unforgeable` ties to a state in `net.sent` — contradicting
    `hsent`'s `isFinal = false`. Used by `late_round_keeps_status`. -/
theorem late_round_keeps_status_nil {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E}
    (hC : TimedConsensusMember apps p T.ε c) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.TimedRun apps T t [] net net' →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false) →
      ((∃ T0, net.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, net.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          net'.chain.now < ch.deadline)) →
      (∃ T0, net'.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, net'.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          net'.chain.now < ch.deadline) := by
  intro net net' t ⟨hseq, hεbound⟩ hsent hbase
  have hres := Threat.RoundSeq.nil_invariant
    (Inv := fun n => (net'.chain.now < n.chain.now + T.ε) ∧
      (∀ t0 ∈ n.sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false) ∧
      ((∃ T0, n.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
        (∃ T0 ch, n.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
          net'.chain.now < ch.deadline)))
    hseq ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩ ⟨hεbound, hsent, hbase⟩
  · exact hres.2.2
  · intro n ss' hnow _ ⟨hεb, hsnt, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.deliver ss')) T.ε), by rw [NetworkState.applyAdv_sent]; exact hsnt, hb⟩
  · intro n dt hnow _ ⟨hεb, hsnt, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.tick dt)) T.ε), by rw [NetworkState.applyAdv_sent]; exact hsnt, ?_⟩
    rcases hb with ⟨T0, ho, hT0⟩ | ⟨T0, ch, hst, hT0, hdd⟩
    · exact Or.inl ⟨T0, by (simpa? [NetworkState.applyAdv] using ho says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using ho), hT0⟩
    · exact Or.inr ⟨T0, ch, by (simpa? [NetworkState.applyAdv] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst), hT0, hdd⟩
  · intro n caller op hnow hfeas ⟨hεb, hsnt, hb⟩
    have hεb' : net'.chain.now < (n.applyAdv apps (.chain caller op)).chain.now + T.ε :=
      lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
        (.chain caller op)) T.ε)
    have hsnt' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false := by
      rw [NetworkState.applyAdv_sent]; exact hsnt
    refine ⟨hεb', hsnt', ?_⟩
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      obtain ⟨x, hx, hxs, hch⟩ := hC.sent_cand hU hs
      have hb2 := (hsnt x hx (by rw [hxs]; exact hch)).1
      rw [hxs] at hb2
      exact hb2
    have hcb : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum ≤ ss.state.turnNum := by
      intro proof cand hU hs
      rcases hsupp proof cand hU hs with h1 | h2
      · exact le_of_lt h1
      · exact le_of_eq (by rw [h2])
    rcases hb with ⟨T0, ho, hT0⟩ | ⟨T0, ch, hst, hT0, hdd⟩
    · simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inl ⟨T0, ho, hT0⟩
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          have hfo1 : n.chain.finalOutcome c.address = none := by
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
              ChannelStatus.finalOutcome_open]
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, hmode, hnew⟩ |
              ⟨proof, cand, hop, hs, -, hlt2, _⟩ |
              ⟨ss', hop, hcp, _⟩
          · subst hop
            have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
            rcases hmode with ⟨-, hle2⟩ | ⟨hmo, -⟩
            · rw [ho, ChannelStatus.turnNumRecord_open] at hle2
              refine Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, by omega, ?_⟩
              have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
              have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
              exact lt_of_lt_of_le hεb (Nat.add_le_add_left hge n.chain.now)
            · exfalso
              rw [Adjudicator.mode_eq, ho] at hmo
              (simp? [ChannelStatus.mode_open] at hmo says simp only [ChannelStatus.mode_open, reduceCtorEq] at hmo)
          · subst hop
            exfalso
            have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
            rw [ho, ChannelStatus.turnNumRecord_open] at hlt2
            omega
          · subst hop
            exfalso
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hC.mem)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hnf := (hsnt x hxmem (by rw [hxeq]; exact hcp.1)).2
            have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hcp.2.1
            (simp? [hnf] at hxfinal says simp only [hnf, Bool.false_eq_true] at hxfinal)
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inl ⟨T0, ho, hT0⟩
    · have hltdl : n.chain.now < ch.deadline := lt_of_le_of_lt hnow hdd
      have hm1 : n.chain.mode c = .challenge := by
        rw [Adjudicator.mode_eq, hst, ChannelStatus.mode_challenged, if_neg (not_le.mpr hltdl)]
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inr ⟨T0, ch, hst, hT0, hdd⟩
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          have hfo1 : n.chain.finalOutcome c.address = none := by
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
              ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, hmode, _⟩ |
              ⟨proof, cand, hop, hs, -, hlt2, _⟩ |
              ⟨ss', hop, hcp, _⟩
          · subst hop
            exfalso
            have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
            rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt2⟩
            · rw [hm1] at hmo; exact absurd hmo (by decide)
            · rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2; omega
          · subst hop
            exfalso
            have hcbd : cand.turnNum ≤ ss.state.turnNum := hcb proof cand hU hs
            rw [hst, ChannelStatus.turnNumRecord_challenged] at hlt2; omega
          · subst hop
            exfalso
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hC.mem)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hnf := (hsnt x hxmem (by rw [hxeq]; exact hcp.1)).2
            have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hcp.2.1
            (simp? [hnf] at hxfinal says simp only [hnf, Bool.false_eq_true] at hxfinal)
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inr ⟨T0, ch, hst, hT0, hdd⟩

/-- Over a round with nothing of `p`'s own pending, the PRE-land invariant ("open at a turn at
    or below `ss.state.turnNum`, or challenged at a turn at or below it (or matching
    `ss.state`), with a deadline still ahead") is preserved, decoupled from its own `RoundSeq`
    endpoint: the deadline bound is checked against an independently-fixed `D` (with
    `net'.chain.now ≤ D` supplied once). The window premise is the weakest one the proof
    uses: `D < net.chain.now + c.challengeDuration`, so a challenge registered anywhere in the
    segment has its deadline after `D`. A caller with the round's own ε-bound and
    `2 * T.ε ≤ c.challengeDuration` derives it in one step. No `hsupp`-derived turn bound is
    needed on the escalating branch here (unlike the POST-land `late_round_keeps_status_nil`):
    any successful challenge/checkpoint's own candidate is already at or below
    `ss.state.turnNum` by `hsupp` alone, which is exactly the BELOW conclusion's own shape.
    Used by `late_round_keeps_status` to carry the PRE-land invariant from `net` to the state
    right before `p`'s own checkpoint call lands, against the ROUND's own fixed end rather
    than that segment's own endpoint. -/
theorem late_round_keeps_status_nil_prelanding {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {D : Time}
    (hC : ConsensusMember apps p c) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      net'.chain.now ≤ D →
      D < net.chain.now + c.challengeDuration →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false) →
      ((∃ t0, net.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)) →
      (∃ t0, net'.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, net'.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline) := by
  intro net net' t hseq hDbound hcdbound hsent hbase
  have hres := Threat.RoundSeq.nil_invariant
    (Inv := fun n => (D < n.chain.now + c.challengeDuration) ∧
      (∀ t0 ∈ n.sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false) ∧
      ((∃ t0, n.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
        (∃ t0 ch, n.chain.statusOf c = .challenged t0 ch ∧
          (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ D < ch.deadline)))
    hseq ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩ ⟨hcdbound, hsent, hbase⟩
  · exact hres.2.2
  · intro n ss' hnow _ ⟨hεb, hsnt, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.deliver ss')) c.challengeDuration), by rw [NetworkState.applyAdv_sent]; exact hsnt, hb⟩
  · intro n dt hnow _ ⟨hεb, hsnt, hb⟩
    refine ⟨lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
      (.tick dt)) c.challengeDuration), by rw [NetworkState.applyAdv_sent]; exact hsnt, ?_⟩
    rcases hb with ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
    · exact Or.inl ⟨t0, by (simpa? [NetworkState.applyAdv] using ho says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using ho), hle⟩
    · exact Or.inr ⟨t0, ch, by (simpa? [NetworkState.applyAdv] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst), hdis, hdd⟩
  · intro n caller op hnow hfeas ⟨hεb, hsnt, hb⟩
    have hεb' : D < (n.applyAdv apps (.chain caller op)).chain.now + c.challengeDuration :=
      lt_of_lt_of_le hεb (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps n
        (.chain caller op)) c.challengeDuration)
    have hsnt' : ∀ t0 ∈ (n.applyAdv apps (.chain caller op)).sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false := by
      rw [NetworkState.applyAdv_sent]; exact hsnt
    refine ⟨hεb', hsnt', ?_⟩
    have hsupp : ∀ (proof : SupportProof E) (cand : State E),
        (∀ ss' ∈ proof, p ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) →
        (apps c.appDef).supports c proof cand = true →
        cand.turnNum < ss.state.turnNum ∨ cand = ss.state := by
      intro proof cand hU hs
      obtain ⟨x, hx, hxs, hch⟩ := hC.sent_cand hU hs
      have hb2 := (hsnt x hx (by rw [hxs]; exact hch)).1
      rw [hxs] at hb2
      exact hb2
    rcases hb with ⟨t0, ho, hle⟩ | ⟨t0, ch, hst, hdis, hdd⟩
    · simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inl ⟨t0, ho, hle⟩
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          have hfo1 : n.chain.finalOutcome c.address = none := by
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
              ChannelStatus.finalOutcome_open]
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨ss', hop, hcp, _⟩
          · subst hop
            rcases hsupp proof cand hU hs with hlt | heqc
            · exact Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inl hlt, hεb⟩
            · exact Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inr heqc, hεb⟩
          · subst hop
            refine Or.inl ⟨cand.turnNum, hnew, ?_⟩
            rcases hsupp proof cand hU hs with hlt | heqc
            · exact le_of_lt hlt
            · exact le_of_eq (by rw [heqc])
          · subst hop
            exfalso
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hC.mem)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hnf := (hsnt x hxmem (by rw [hxeq]; exact hcp.1)).2
            have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hcp.2.1
            (simp? [hnf] at hxfinal says simp only [hnf, Bool.false_eq_true] at hxfinal)
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inl ⟨t0, ho, hle⟩
    · have hltdl : n.chain.now < ch.deadline := lt_of_le_of_lt (le_trans hnow hDbound) hdd
      simp only [NetworkState.applyAdv]
      cases h : n.chain.apply apps caller op with
      | none => exact Or.inr ⟨t0, ch, hst, hdis, hdd⟩
      | some s' =>
        by_cases htarget : Op.targets op c
        · have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ n.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable n caller op hfeas ss' hmem).1 hsig
          have hfo1 : n.chain.finalOutcome c.address = none := by
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
              ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
          rcases Op.latest_record_step h htarget hfo1 with
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨proof, cand, hop, hs, -, -, hnew⟩ |
              ⟨ss', hop, hcp, _⟩
          · subst hop
            rcases hsupp proof cand hU hs with hlt | heqc
            · exact Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inl hlt, hεb⟩
            · exact Or.inr ⟨cand.turnNum,
                Challenge.mk cand (n.chain.now + c.challengeDuration), hnew, Or.inr heqc, hεb⟩
          · subst hop
            refine Or.inl ⟨cand.turnNum, hnew, ?_⟩
            rcases hsupp proof cand hU hs with hlt | heqc
            · exact le_of_lt hlt
            · exact le_of_eq (by rw [heqc])
          · subst hop
            exfalso
            have hp' : p ∈ ss'.signers := hcp.2.2 p (hcp.1 ▸ hC.mem)
            have hmem : ss' ∈ (Op.conclude c ss').proofStates := by
              simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]
            obtain ⟨x, hxmem, hxeq⟩ := hU ss' hmem hp'
            have hnf := (hsnt x hxmem (by rw [hxeq]; exact hcp.1)).2
            have hxfinal : x.state.isFinal = true := by rw [hxeq]; exact hcp.2.1
            (simp? [hnf] at hxfinal says simp only [hnf, Bool.false_eq_true] at hxfinal)
        · rw [statusOf_apply_of_not_targets h htarget]
          exact Or.inr ⟨t0, ch, hst, hdis, hdd⟩

/-- One round of adversary play on `p`'s own `checkpoint c [ss] ss.state`
    call, under the explicit-time game: `p`'s call lands exactly once
    (`pending` is the singleton `[Op.checkpoint c [ss] ss.state]`). From an
    open record `t0 ≤ ss.state.turnNum`: if `t0 < ss.state.turnNum`
    strictly, `p`'s call always succeeds (`checkpoint_can_happen`), landing
    `.open ss.state.turnNum` exactly; if `t0 = ss.state.turnNum` already,
    the call fails on the strict-turn precondition, but the record was
    already there, so the invariant is already met. From a challenged
    record: the same case split, except success clears the challenge to
    `.open ss.state.turnNum` instead of leaving it challenged. Either way
    the result feeds `late_round_keeps_status_nil`, whose own turn-bound
    argument (`hbounds.unforgeable`) shows no later adversary play in the
    same round pushes the record past `ss.state.turnNum`. Used by
    `late_observer_can_checkpoint`; closes the old two gaps (`hopen1`/`hlt1`
    branches) by proving them unreachable in a single round, not by a
    second one. -/
theorem late_round_keeps_status {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E}
    (hC : TimedConsensusMember apps p T.ε c) (hall : ss.ByAll)
    (hchan : ss.state.channel = c) {net net' : NetworkState E p} (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.TimedRun apps T t [Op.checkpoint c [ss] ss.state] net net') :
    (∀ t0 ∈ net.sent, t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧ t0.state.isFinal = false) →
    ((∃ t0, net.chain.statusOf c = .open t0 ∧ t0 ≤ ss.state.turnNum) ∨
      (∃ t0 ch, net.chain.statusOf c = .challenged t0 ch ∧
        (t0 < ss.state.turnNum ∨ ch.state = ss.state) ∧ net'.chain.now < ch.deadline)) →
    (∃ T0, net'.chain.statusOf c = .open T0 ∧ ss.state.turnNum ≤ T0) ∨
      (∃ T0 ch, net'.chain.statusOf c = .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧
        net'.chain.now < ch.deadline) := by
  obtain ⟨hseq, hεb⟩ := hseq; revert hεb
  clear ht
  intro hεbound hsent hbase
  obtain ⟨n1, hpre, hpost⟩ := hseq.peel_one
  have hmono0 : n1.chain.now ≤ net'.chain.now :=
    le_trans (NetworkState.applyAdv_now_le apps n1 (.land (Op.checkpoint c [ss] ss.state)))
      hpost.now_le
  have hεbound1 : net'.chain.now < n1.chain.now + T.ε :=
    lt_of_lt_of_le hεbound (Nat.add_le_add_right hpre.now_le T.ε)
  have hcdbound : net'.chain.now < net.chain.now + c.challengeDuration :=
    lt_of_lt_of_le hεbound (Nat.add_le_add_left
      (le_trans (by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε) hC.timed) net.chain.now)
  have hbase1 := late_round_keeps_status_nil_prelanding hbounds hC.toConsensusMember
    (D := net'.chain.now) hpre hmono0 hcdbound hsent hbase
  have hbase_land :
      (∃ T0, (n1.applyAdv apps (.land (Op.checkpoint c [ss] ss.state))).chain.statusOf c =
        .open T0 ∧ ss.state.turnNum ≤ T0) ∨
      (∃ T0 ch, (n1.applyAdv apps (.land (Op.checkpoint c [ss] ss.state))).chain.statusOf c =
        .challenged T0 ch ∧ ss.state.turnNum ≤ T0 ∧ net'.chain.now < ch.deadline) := by
    rcases hbase1 with ⟨t0, ho, hle⟩ | ⟨t0, ch0, hst0, hdis0, hdd0⟩
    · by_cases hlt0 : t0 < ss.state.turnNum
      · have hcond : (n1.chain.statusOf c).IsOpen n1.chain.now ∧
            (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
            (n1.chain.statusOf c).turnNumRecord < ss.state.turnNum := by
          refine ⟨?_, by rw [hC.app]; (simp? [consensusRules, hchan, hall] says simp only [consensusRules, decide_true, hchan, Bool.and_self, hall]), hchan, ?_⟩
          · rw [ho]; (simp? [ChannelStatus.IsOpen, ChannelStatus.mode_open] says simp only [ChannelStatus.IsOpen, ChannelStatus.mode_open, ne_eq, reduceCtorEq, not_false_eq_true])
          · rw [ho, ChannelStatus.turnNumRecord_open]; exact hlt0
        have hop : n1.chain.apply apps p (Op.checkpoint c [ss] ss.state) =
            some (n1.chain.setStatus c (.open ss.state.turnNum)) := by
          rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
          rw [if_pos hcond]
        simp only [NetworkState.applyAdv, hop]
        exact Or.inl ⟨ss.state.turnNum,
          by rw [Adjudicator.statusOf_setStatus, if_pos rfl], le_refl _⟩
      · have hle2 : ss.state.turnNum ≤ t0 := not_lt.mp hlt0
        have hcondneg : ¬ ((n1.chain.statusOf c).IsOpen n1.chain.now ∧
            (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
            (n1.chain.statusOf c).turnNumRecord < ss.state.turnNum) := by
          rintro ⟨-, -, -, hlt2⟩
          rw [ho, ChannelStatus.turnNumRecord_open] at hlt2
          exact hlt0 hlt2
        have hop : n1.chain.apply apps p (Op.checkpoint c [ss] ss.state) = none := by
          rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
          rw [if_neg hcondneg]
        simp only [NetworkState.applyAdv, hop]
        exact Or.inl ⟨t0, ho, hle2⟩
    · have hltdl0 : n1.chain.now < ch0.deadline := lt_of_le_of_lt hmono0 hdd0
      have hio0 : (n1.chain.statusOf c).IsOpen n1.chain.now := by
        rw [hst0, ChannelStatus.IsOpen, ChannelStatus.mode_challenged,
          if_neg (not_le.mpr hltdl0)]
        decide
      by_cases hlt0 : t0 < ss.state.turnNum
      · have hcond : (n1.chain.statusOf c).IsOpen n1.chain.now ∧
            (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
            (n1.chain.statusOf c).turnNumRecord < ss.state.turnNum := by
          refine ⟨hio0, by rw [hC.app]; (simp? [consensusRules, hchan, hall] says simp only [consensusRules, decide_true, hchan, Bool.and_self, hall]), hchan, ?_⟩
          rw [hst0, ChannelStatus.turnNumRecord_challenged]; exact hlt0
        have hop : n1.chain.apply apps p (Op.checkpoint c [ss] ss.state) =
            some (n1.chain.setStatus c (.open ss.state.turnNum)) := by
          rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
          rw [if_pos hcond]
        simp only [NetworkState.applyAdv, hop]
        exact Or.inl ⟨ss.state.turnNum,
          by rw [Adjudicator.statusOf_setStatus, if_pos rfl], le_refl _⟩
      · have hle2 : ss.state.turnNum ≤ t0 := not_lt.mp hlt0
        have hcondneg : ¬ ((n1.chain.statusOf c).IsOpen n1.chain.now ∧
            (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
            (n1.chain.statusOf c).turnNumRecord < ss.state.turnNum) := by
          rintro ⟨-, -, -, hlt2⟩
          rw [hst0, ChannelStatus.turnNumRecord_challenged] at hlt2
          exact hlt0 hlt2
        have hop : n1.chain.apply apps p (Op.checkpoint c [ss] ss.state) = none := by
          rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
          rw [if_neg hcondneg]
        simp only [NetworkState.applyAdv, hop]
        exact Or.inr ⟨t0, ch0, hst0, hle2, hdd0⟩
  have hεbound' : net'.chain.now <
      (n1.applyAdv apps (.land (Op.checkpoint c [ss] ss.state))).chain.now + T.ε :=
    lt_of_lt_of_le hεbound1
      (Nat.add_le_add_right
        (NetworkState.applyAdv_now_le apps n1 (.land (Op.checkpoint c [ss] ss.state))) T.ε)
  have hsent_land : ∀ t0 ∈
      (n1.applyAdv apps (.land (Op.checkpoint c [ss] ss.state))).sent,
      t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state) ∧
        t0.state.isFinal = false := by
    rw [NetworkState.applyAdv_sent, hpre.sent_eq]; exact hsent
  exact late_round_keeps_status_nil hbounds hC ⟨hpost, hεbound'⟩ hsent_land hbase_land

/-- ForceMove-B05. ForceMove:1511-1529: "as long as Alice notices Bob's challenge within
    the timeout period, she cannot hurt her position by playing on as though
    still in Collaborative mode ... all the moves made in Collaborative still
    stand." A participant who holds a supported state above the challenge
    state, and signed nothing above it, can bring the record to that turn
    before the deadline, with go-nitro `checkpoint`, and the channel is not
    finalized. The adversary can register that same state as a challenge, so
    the goal does not ask for Open mode. -/
theorem late_observer_can_checkpoint (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε) (ss : SignedState E)
    (t : Nat) (ch : Challenge E) (hc : apps (c : FixedPart).appDef = consensusRules)
    (hp : p ∈ (c : FixedPart).participants)
    (hh : net.state.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = (c : FixedPart))
    (hsent : ∀ u ∈ net.state.sent, u.state.channel = (c : FixedPart) →
      (u.state.turnNum < ss.state.turnNum ∨ u.state = ss.state) ∧ u.state.isFinal = false)
    (hst : net.state.chain.statusOf (c : FixedPart) = .challenged t ch) (hgt : t < ss.state.turnNum)
    (hnow : net.state.chain.now + T.ε ≤ ch.deadline) :
    UnbeatableNoWait apps T
      (fun net' => net'.chain.mode (c : FixedPart) ≠ .finalized ∧
        ss.state.turnNum ≤ (net'.chain.statusOf (c : FixedPart)).turnNumRecord) net.state := by
  obtain_reach ⟨net, _hr⟩ := net
  obtain ⟨c, hdur⟩ := c
  refine UnbeatableIn.move (.chain (.checkpoint c [ss] ss.state)) trivial
    (by (simpa? [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh says simpa only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hh)) ?_
  intro net1 hround
  obtain ⟨hseq, hεbound⟩ := hround
  simp only [HonestMove.calls_chain] at hseq
  have hbase : (∃ t, net.chain.statusOf c = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf c = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net1.chain.now < ch.deadline) :=
    Or.inr ⟨t, ch, hst, Or.inl hgt, lt_of_lt_of_le hεbound hnow⟩
  have hinv := late_round_keeps_status A.toBounds ⟨⟨hc, hp⟩, hdur⟩ hall hchan net.chain.now rfl ⟨hseq,
    hεbound⟩ hsent hbase
  rcases hinv with ⟨t1, hopen1, hle1⟩ | ⟨t1, ch1, hchal1, hle1, hdd1⟩
  · apply UnbeatableIn.done
    show net1.chain.mode c ≠ .finalized ∧ ss.state.turnNum ≤ (net1.chain.statusOf c).turnNumRecord
    exact ⟨by rw [Adjudicator.mode_eq, hopen1]; (simp? says simp only [ChannelStatus.mode_open, ne_eq, reduceCtorEq, not_false_eq_true]),
      by rw [hopen1, ChannelStatus.turnNumRecord_open]; exact hle1⟩
  · apply UnbeatableIn.done
    show net1.chain.mode c ≠ .finalized ∧ ss.state.turnNum ≤ (net1.chain.statusOf c).turnNumRecord
    exact ⟨by rw [Adjudicator.mode_eq, hchal1, ChannelStatus.mode_challenged,
        if_neg (not_le.mpr hdd1)]; decide,
      by rw [hchal1, ChannelStatus.turnNumRecord_challenged]; exact hle1⟩

/-! ### The joint play of two participants (`finalizable_unique`)

`finalizable_unique` plays the strategy tree of `p` and the strategy tree of
`q` together, each in its own game. One shared chain is not possible: a
`wait` is atomic, and the adversary moves only at a round's boundary, so a
wait of `p` and a different wait of `q` cannot occur on one clock.

Thus each participant keeps its own view and its own clock. A reaction of one
participant lands its calls in its own round (`Threat.RoundSeq.land`), and
the same calls run in the view of the other participant as adversary
`.chain` moves, inside the round that is open there (`mirror_land`). A
`wait` moves only the clock of the participant that waits.

The two chains then can differ in time, but channel `c` keeps one status on
both, up to the deadline of a running challenge (`ChanAgree`). An operation
on `c` reads the mode and the turn record of `c`, not the clock, and a
challenge sets its deadline `challengeDuration` after the clock of its own
chain (`ChanAgree.apply`). The status of `c` differs only when a wait passes
a deadline on one chain. The schedule chooses which participant waits
first: if the running challenge pays `Ω`, `q` waits first, else `p` waits
first. If the wait of `p` finalizes `c`, the outcome is not `Ω`, and the
tree of `p` cannot win from there. If the wait of `q` finalizes `c`, the
outcome is `Ω`, so `Ω' = Ω`. A conclude finalizes `c` on both chains with
one outcome (`ChanAgreeOrFin`). Each step uses one move of one tree, so the
play ends (`finalizable_joint`).

The calls of one participant are feasible adversary moves in the view of
the other, because every signature of `p` or `q` that a view received is
genuine (`JointGenuine`, from `Nitro.network_received_signers`).
-/

/-- A single adversary move only ever adds to what `p` has received
    (`NetworkState.applyAdv`'s `deliver` and successful `chain` cases
    prepend; `tick` and a failed `chain` call leave it unchanged). -/
theorem NetworkState.applyAdv_received_subset (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (m : AdvMove E) :
    ∀ r ∈ net.received, r ∈ (net.applyAdv apps m).received := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases net.chain.apply apps caller op with
    | none => exact fun r hr => hr
    | some s' => exact fun r hr => List.mem_append_right _ hr
  | deliver ss => exact fun r hr => List.mem_cons_of_mem _ hr
  | tick dt => exact fun r hr => hr
  | land op =>
    simp only [NetworkState.applyAdv]
    cases net.chain.apply apps p op with
    | none => exact fun r hr => hr
    | some s' => exact fun r hr => List.mem_append_right _ hr

/-- Adversary moves inside one open round: no `tick` and no landing, so the
    moves fit into a round for any pending calls (`OtherSteps.roundSeq`).
    In the joint play these are the calls of the other participant. -/
inductive OtherSteps (apps : Apps E) {p : Participant} (T : Threat E p) :
    NetworkState E p → NetworkState E p → Prop
  | refl {net} : OtherSteps apps T net net
  | tail {net mid m} : OtherSteps apps T net mid → T.feasible mid m → (∀ dt, m ≠ .tick dt) →
      (∀ op, m ≠ .land op) → OtherSteps apps T net (mid.applyAdv apps m)

namespace OtherSteps

variable {apps : Apps E} {p : Participant} {T : Threat E p}

theorem trans {a b d : NetworkState E p} (h1 : OtherSteps apps T a b)
    (h2 : OtherSteps apps T b d) : OtherSteps apps T a d := by
  induction h2 with
  | refl => exact h1
  | tail _ hf hnt hnl ih => exact .tail ih hf hnt hnl

/-- The moves come first in a round with any pending calls: each is the
    round's own `Threat.RoundSeq.other` step. -/
theorem roundSeq {t : Time} {pending : List (Op E)} {a b d : NetworkState E p}
    (h1 : OtherSteps apps T a b) (h2 : T.RoundSeq apps t pending b d) :
    T.RoundSeq apps t pending a d := by
  induction h1 generalizing d with
  | refl => exact h2
  | tail _ hf hnt hnl ih => exact ih (.other hf hnt hnl h2)

theorem sent_eq {a b : NetworkState E p} (h : OtherSteps apps T a b) : b.sent = a.sent := by
  induction h with
  | refl => rfl
  | tail _ _ _ _ ih => rw [NetworkState.applyAdv_sent, ih]

theorem received_subset {a b : NetworkState E p} (h : OtherSteps apps T a b) :
    ∀ r ∈ a.received, r ∈ b.received := by
  induction h with
  | refl => exact fun r hr => hr
  | tail _ _ _ _ ih => exact fun r hr => NetworkState.applyAdv_received_subset apps _ _ r (ih r hr)

theorem finalizedWith_mono {a b : NetworkState E p} (h : OtherSteps apps T a b) {c : FixedPart}
    {f : Outcome E} (hf : a.chain.finalizedWith c.address = some f) :
    b.chain.finalizedWith c.address = some f :=
  (h.roundSeq (t := a.chain.now) Threat.RoundSeq.nil).finalizedWith_mono hf

end OtherSteps

omit [DecidableEq E] in
/-- An honest move keeps the outcome of finalization: a reaction does not
    touch the chain, and a wait only moves the clock. -/
theorem NetworkState.applyHonest_finalizedWith {p : Participant} (m : HonestMove E)
    (net : NetworkState E p) {c : FixedPart} {f : Outcome E}
    (hf : net.chain.finalizedWith c.address = some f) :
    (net.applyHonest m).chain.finalizedWith c.address = some f := by
  cases m with
  | react r => exact hf
  | wait dt =>
    simpa [NetworkState.applyHonest, FixedPart.address_eq] using
      ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf)
        (Nat.le_add_right _ dt)

omit [DecidableEq E] in
theorem Op.HonestFeasible.not_tick {p : Participant} {net : NetworkState E p} {op : Op E}
    (h : op.HonestFeasible net) : ∀ dt, op ≠ .tick dt := by
  rintro dt rfl
  exact h

omit [DecidableEq E] in
theorem Op.HonestFeasible.holds {p : Participant} {net : NetworkState E p} {op : Op E}
    (h : op.HonestFeasible net) : ∀ ss ∈ op.proofStates, net.Holds ss := by
  cases op with
  | deposit _ _ _ => exact h.elim
  | tick _ => exact h.elim
  | transfer _ _ | reclaim _ _ | challenge _ _ _ | checkpoint _ _ _ | conclude _ _ => exact h

/-- A strategy for `Finalized c Ω` from a state where `c` already finalized
    with `Ω0` shows `Ω0 = Ω`: any play of the strategy (`Threat.Round.exists`)
    keeps the outcome of finalization and ends at the goal. -/
theorem UnbeatableIn.finalized_eq {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {c : FixedPart} {Ω Ω0 : Outcome E} {net : NetworkState E p}
    (hU : UnbeatableIn apps T allowed (fun n => n.Finalized c Ω) net)
    (hf : net.chain.finalizedWith c.address = some Ω0) : Ω0 = Ω := by
  induction hU with
  | done hG => exact Option.some.inj (hf.symm.trans hG)
  | move m _ hfeas _ ih =>
    obtain ⟨net1, hround⟩ := Threat.Round.exists T hfeas
    exact ih net1 hround (NetworkState.applyHonest_finalizedWith m net1 (hround.1.finalizedWith_mono hf))

/-- `UnbeatableIn.finalized_eq` inside an open round: the strategy's next
    round is these adversary moves, then its own calls, landed with no tick
    (`Threat.RoundSeq.landAll`). -/
theorem UnbeatableIn.finalized_eq_of_steps {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {c : FixedPart} {Ω Ω0 : Outcome E} {np Sp : NetworkState E p}
    (hU : UnbeatableIn apps T allowed (fun n => n.Finalized c Ω) np) (hS : OtherSteps apps T np Sp)
    (hnow : Sp.chain.now = np.chain.now) (hf : Sp.chain.finalizedWith c.address = some Ω0) :
    Ω0 = Ω := by
  cases hU with
  | done hG => exact Option.some.inj (hf.symm.trans (hS.finalizedWith_mono hG))
  | move m _ hfeas hcont =>
    have hnotick : ∀ op ∈ m.calls, ∀ dt, op ≠ Op.tick dt := by
      cases m with
      | react r => exact fun op hop => Op.HonestFeasible.not_tick (hfeas.1 op hop)
      | wait _ => intro op hop; (simp? [HonestMove.calls] at hop says simp only [HonestMove.calls, List.not_mem_nil] at hop)
    obtain ⟨S', hseq, hnow'⟩ := Threat.RoundSeq.landAll apps T np.chain.now m.calls hnotick Sp
    have hround : T.Round apps m np S' :=
      ⟨hS.roundSeq hseq, by rw [hnow', hnow]; exact Nat.lt_add_of_pos_right T.ε_pos⟩
    exact (hcont S' hround).finalized_eq
      (NetworkState.applyHonest_finalizedWith m S' (hseq.finalizedWith_mono hf))

/-- Channel `c` has one status on two chains, up to the deadline of a
    running challenge, and neither chain has finalized it. The clocks of
    the two chains can differ. -/
def ChanAgree (c : FixedPart) (s1 s2 : Adjudicator E) : Prop :=
  (∃ r, s1.statusOf c = .open r ∧ s2.statusOf c = .open r) ∨
  (∃ r ch1 ch2, s1.statusOf c = .challenged r ch1 ∧ s2.statusOf c = .challenged r ch2 ∧
    ch1.state = ch2.state ∧ s1.now < ch1.deadline ∧ s2.now < ch2.deadline)

/-- `ChanAgree`, or both chains finalized `c` with one outcome. -/
def ChanAgreeOrFin (c : FixedPart) (s1 s2 : Adjudicator E) : Prop :=
  ChanAgree c s1 s2 ∨
    ∃ Ω0, s1.finalizedWith c.address = some Ω0 ∧ s2.finalizedWith c.address = some Ω0

omit [DecidableEq E] in
theorem ChanAgree.symm {c : FixedPart} {s1 s2 : Adjudicator E} (h : ChanAgree c s1 s2) :
    ChanAgree c s2 s1 := by
  rcases h with ⟨r, h1, h2⟩ | ⟨r, ch1, ch2, h1, h2, hs, hl1, hl2⟩
  · exact Or.inl ⟨r, h2, h1⟩
  · exact Or.inr ⟨r, ch2, ch1, h2, h1, hs.symm, hl2, hl1⟩

omit [DecidableEq E] in
theorem ChanAgreeOrFin.symm {c : FixedPart} {s1 s2 : Adjudicator E} (h : ChanAgreeOrFin c s1 s2) :
    ChanAgreeOrFin c s2 s1 := by
  rcases h with h | ⟨Ω0, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨Ω0, h2, h1⟩

omit [DecidableEq E] in
/-- One chain agrees with itself: `c` is open, or challenged and not yet
    finalized, or finalized. -/
theorem ChanAgreeOrFin.refl (c : FixedPart) (s : Adjudicator E) : ChanAgreeOrFin c s s := by
  cases hst : s.statusOf c with
  | «open» r => exact Or.inl (Or.inl ⟨r, hst, hst⟩)
  | challenged r ch =>
    by_cases hlt : s.now < ch.deadline
    · exact Or.inl (Or.inr ⟨r, ch, ch, hst, hst, rfl, hlt, hlt⟩)
    · have hf : s.finalizedWith c.address = some ch.state.outcome := by
        (simp? [FixedPart.address_eq, hst, not_lt.mp hlt] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst, ChannelStatus.finalizedWith_challenged, not_lt.mp hlt, ↓reduceIte])
      exact Or.inr ⟨ch.state.outcome, hf, hf⟩
  | finalized r f o =>
    have hf : s.finalizedWith c.address = some f := by (simp? [FixedPart.address_eq, hst] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst, ChannelStatus.finalizedWith_finalized])
    exact Or.inr ⟨f, hf, hf⟩

omit [DecidableEq E] in
theorem ChanAgree.finalOutcome_left {c : FixedPart} {s1 s2 : Adjudicator E}
    (h : ChanAgree c s1 s2) : (s1.statusOf c).finalOutcome s1.now = none := by
  rcases h with ⟨r, h1, -⟩ | ⟨r, ch1, ch2, h1, -, -, hl1, -⟩
  · rw [h1]; rfl
  · rw [h1]; (simp? [not_le.mpr hl1] says simp only [ChannelStatus.finalOutcome_challenged, not_le.mpr hl1, ↓reduceIte])

omit [DecidableEq E] in
theorem ChanAgree.finalizedWith_left {c : FixedPart} {s1 s2 : Adjudicator E}
    (h : ChanAgree c s1 s2) : s1.finalizedWith c.address = none := by
  rcases h with ⟨r, h1, -⟩ | ⟨r, ch1, ch2, h1, -, -, hl1, -⟩
  · (simp? [FixedPart.address_eq, h1] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, h1, ChannelStatus.finalizedWith_open])
  · (simp? [FixedPart.address_eq, h1, not_le.mpr hl1] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, h1, ChannelStatus.finalizedWith_challenged, not_le.mpr hl1, ↓reduceIte])

omit [DecidableEq E] in
theorem ChanAgree.finalizedWith_right {c : FixedPart} {s1 s2 : Adjudicator E}
    (h : ChanAgree c s1 s2) : s2.finalizedWith c.address = none :=
  h.symm.finalizedWith_left

omit [DecidableEq E] in
theorem ChanAgree.congr {c : FixedPart} {s1 s2 s1' s2' : Adjudicator E} (h : ChanAgree c s1 s2)
    (h1 : s1'.statusOf c = s1.statusOf c) (h1n : s1'.now = s1.now)
    (h2 : s2'.statusOf c = s2.statusOf c) (h2n : s2'.now = s2.now) : ChanAgree c s1' s2' := by
  unfold ChanAgree; rw [h1, h2, h1n, h2n]; exact h

theorem Adjudicator.apply_getD_now {apps : Apps E} {s : Adjudicator E} {x : Participant}
    {op : Op E} (hop : ∀ dt, op ≠ .tick dt) : ((s.apply apps x op).getD s).now = s.now := by
  cases h : s.apply apps x op with
  | none => rfl
  | some s' => exact Adjudicator.apply_now_eq_of_not_tick hop h

theorem Adjudicator.apply_getD_finalizedWith {apps : Apps E} {s : Adjudicator E}
    {x : Participant} {op : Op E} {c : FixedPart} {f : Outcome E}
    (hf : s.finalizedWith c.address = some f) :
    ((s.apply apps x op).getD s).finalizedWith c.address = some f := by
  cases h : s.apply apps x op with
  | none => exact hf
  | some s' => exact Adjudicator.finalizedWith_apply h hf

/-- An operation that is not a `challenge`, `checkpoint` or `conclude` of
    `c` keeps the status of `c`, while `c` is not finalized: `transfer` and
    `reclaim` write only the status of a finalized channel. -/
theorem Adjudicator.apply_getD_statusOf_neutral {apps : Apps E} {s : Adjudicator E}
    {x : Participant} {op : Op E} {c : FixedPart}
    (hnf : (s.statusOf c).finalOutcome s.now = none)
    (h1 : ∀ proof cand, op ≠ .challenge c proof cand)
    (h2 : ∀ proof cand, op ≠ .checkpoint c proof cand) (h3 : ∀ ss, op ≠ .conclude c ss) :
    ((s.apply apps x op).getD s).statusOf c = s.statusOf c := by
  cases h : s.apply apps x op with
  | none => rfl
  | some s' =>
    simp only [Option.getD_some]
    cases op with
    | deposit a e v => exact Adjudicator.statusOf_of_status (Adjudicator.deposit_some h).2.2.2.2.1 c
    | transfer a b =>
      obtain ⟨_, _, _, hfa, -, -, -, -, hs, -, -, -⟩ := Adjudicator.transfer_some h
      rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus, if_neg]
      rintro rfl
      (simp? [FixedPart.address_eq, hnf] at hfa says simp only [FixedPart.address_eq, finalOutcome_channel, hnf, reduceCtorEq] at hfa)
    | reclaim l v =>
      obtain ⟨_, _, _, _, _, hfl, -, -, -, -, -, rfl, -, -⟩ := Adjudicator.reclaim_some h
      rw [Adjudicator.statusOf_setStatus, if_neg]
      rintro rfl
      (simp? [FixedPart.address_eq, hnf] at hfl says simp only [FixedPart.address_eq, finalOutcome_channel, hnf, reduceCtorEq] at hfl)
    | challenge c' proof cand =>
      obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
      rw [Adjudicator.statusOf_setStatus, if_neg]
      rintro rfl; exact h1 proof cand rfl
    | checkpoint c' proof cand =>
      obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
      rw [Adjudicator.statusOf_setStatus, if_neg]
      rintro rfl; exact h2 proof cand rfl
    | conclude c' ss =>
      obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
      rw [Adjudicator.statusOf_setStatus, if_neg]
      rintro rfl; exact h3 ss rfl
    | tick dt =>
      (simp? at h says simp only [apply_tick, Option.some.injEq] at h); subst h; rfl

/-- **One operation keeps `ChanAgree`, or finalizes `c` on both chains.**
    An operation on `c` succeeds on one chain exactly when it succeeds on
    the other: it reads the mode and the turn record of `c`, which agree. A
    challenge sets each deadline `challengeDuration` after its own chain's
    clock, so both deadlines are ahead of their clocks, or (with a zero
    duration) both chains finalize with the candidate's outcome. A conclude
    finalizes both chains with one outcome. Any other operation keeps the
    status of `c` (`Adjudicator.apply_getD_statusOf_neutral`). -/
theorem ChanAgree.apply {apps : Apps E} {c : FixedPart} {s1 s2 : Adjudicator E}
    (h : ChanAgree c s1 s2) (x : Participant) {op : Op E} (hop : ∀ dt, op ≠ .tick dt) :
    ChanAgreeOrFin c ((s1.apply apps x op).getD s1) ((s2.apply apps x op).getD s2) := by
  have hnf1 := h.finalOutcome_left
  have hnf2 := h.symm.finalOutcome_left
  have hmode : s1.mode c = s2.mode c := by
    rcases h with ⟨r, h1, h2⟩ | ⟨r, ch1, ch2, h1, h2, -, hl1, hl2⟩
    · (simp? [Adjudicator.mode_eq, h1, h2] says simp only [Adjudicator.mode_eq, h1, ChannelStatus.mode_open, h2])
    · (simp? [Adjudicator.mode_eq, h1, h2, not_le.mpr hl1, not_le.mpr hl2] says simp only [Adjudicator.mode_eq, h1, ChannelStatus.mode_challenged, not_le.mpr hl1, ↓reduceIte, h2, not_le.mpr hl2])
  have hrec : (s1.statusOf c).turnNumRecord = (s2.statusOf c).turnNumRecord := by
    rcases h with ⟨r, h1, h2⟩ | ⟨r, ch1, ch2, h1, h2, -, -, -⟩ <;> simp [h1, h2]
  have hopen1 : (s1.statusOf c).IsOpen s1.now := by
    rw [ChannelStatus.isOpen_iff_ne, ne_eq, ChannelStatus.mode_eq_finalized_iff, hnf1]; (simp? says simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true])
  have hopen2 : (s2.statusOf c).IsOpen s2.now := by
    rw [ChannelStatus.isOpen_iff_ne, ne_eq, ChannelStatus.mode_eq_finalized_iff, hnf2]; (simp? says simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true])
  have hneutral : (∀ proof cand, op ≠ .challenge c proof cand) →
      (∀ proof cand, op ≠ .checkpoint c proof cand) → (∀ ss, op ≠ .conclude c ss) →
      ChanAgreeOrFin c ((s1.apply apps x op).getD s1) ((s2.apply apps x op).getD s2) :=
    fun ha hb hc => Or.inl (h.congr (Adjudicator.apply_getD_statusOf_neutral hnf1 ha hb hc)
      (Adjudicator.apply_getD_now hop) (Adjudicator.apply_getD_statusOf_neutral hnf2 ha hb hc)
      (Adjudicator.apply_getD_now hop))
  cases op with
  | deposit a e v =>
    exact hneutral (by intro _ _ he; cases he) (by intro _ _ he; cases he) (by intro _ he; cases he)
  | transfer a b =>
    exact hneutral (by intro _ _ he; cases he) (by intro _ _ he; cases he) (by intro _ he; cases he)
  | reclaim l v =>
    exact hneutral (by intro _ _ he; cases he) (by intro _ _ he; cases he) (by intro _ he; cases he)
  | tick dt => exact absurd rfl (hop dt)
  | challenge c' proof cand =>
    by_cases hcc : c' = c
    · subst hcc
      simp only [Adjudicator.apply_challenge, Adjudicator.challenge, hmode, hrec]
      split_ifs with hP
      · simp only [Option.getD_some]
        by_cases hD : 0 < c'.challengeDuration
        · refine Or.inl (Or.inr ⟨cand.turnNum, ⟨cand, s1.now + c'.challengeDuration⟩,
            ⟨cand, s2.now + c'.challengeDuration⟩, ?_, ?_, rfl, ?_, ?_⟩)
          · (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])
          · (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])
          · (simp? says simp only [Adjudicator.setStatus_now, lt_add_iff_pos_right]); omega
          · (simp? says simp only [Adjudicator.setStatus_now, lt_add_iff_pos_right]); omega
        · have hD0 : c'.challengeDuration = 0 := Nat.eq_zero_of_not_pos hD
          refine Or.inr ⟨cand.outcome, ?_, ?_⟩ <;> (simp? [FixedPart.address_eq, hD0] says simp only [hD0, add_zero, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_challenged, Std.le_refl])
      · exact Or.inl h
    · exact hneutral (fun _ _ he => hcc (Op.challenge.inj he).1) (by intro _ _ he; cases he)
        (by intro _ he; cases he)
  | checkpoint c' proof cand =>
    by_cases hcc : c' = c
    · subst hcc
      simp only [Adjudicator.apply_checkpoint, Adjudicator.checkpoint, hrec, hopen1, hopen2,
        true_and]
      split_ifs with hP
      · simp only [Option.getD_some]
        exact Or.inl (Or.inl ⟨cand.turnNum, by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte]), by (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])⟩)
      · exact Or.inl h
    · exact hneutral (by intro _ _ he; cases he) (fun _ _ he => hcc (Op.checkpoint.inj he).1)
        (by intro _ he; cases he)
  | conclude c' ss =>
    by_cases hcc : c' = c
    · subst hcc
      simp only [Adjudicator.apply_conclude, Adjudicator.conclude, hopen1, hopen2, true_and]
      split_ifs with hP
      · simp only [Option.getD_some]
        exact Or.inr ⟨ss.state.outcome, by (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized]),
          by (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized])⟩
      · exact Or.inl h
    · exact hneutral (by intro _ _ he; cases he) (by intro _ _ he; cases he)
        (fun _ he => hcc (Op.conclude.inj he).1)

theorem ChanAgreeOrFin.apply {apps : Apps E} {c : FixedPart} {s1 s2 : Adjudicator E}
    (h : ChanAgreeOrFin c s1 s2) (x : Participant) {op : Op E} (hop : ∀ dt, op ≠ .tick dt) :
    ChanAgreeOrFin c ((s1.apply apps x op).getD s1) ((s2.apply apps x op).getD s2) := by
  rcases h with h | ⟨Ω0, h1, h2⟩
  · exact h.apply x hop
  · exact Or.inr ⟨Ω0, Adjudicator.apply_getD_finalizedWith h1,
      Adjudicator.apply_getD_finalizedWith h2⟩

theorem NetworkState.applyAdv_chain_chain (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (x : Participant) (op : Op E) :
    (net.applyAdv apps (.chain x op)).chain = (net.chain.apply apps x op).getD net.chain := by
  simp only [NetworkState.applyAdv]
  cases net.chain.apply apps x op <;> rfl

theorem NetworkState.applyAdv_land_chain (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (op : Op E) :
    (net.applyAdv apps (.land op)).chain = (net.chain.apply apps p op).getD net.chain := by
  simp only [NetworkState.applyAdv]
  cases net.chain.apply apps p op <;> rfl

theorem NetworkState.applyAdv_chain_received (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (x : Participant) (op : Op E) :
    ∀ r ∈ (net.applyAdv apps (.chain x op)).received, r ∈ op.proofStates ∨ r ∈ net.received := by
  simp only [NetworkState.applyAdv]
  cases net.chain.apply apps x op with
  | none => exact fun r hr => Or.inr hr
  | some s' => exact fun r hr => List.mem_append.mp hr

theorem NetworkState.applyAdv_land_received (apps : Apps E) {p : Participant}
    (net : NetworkState E p) (op : Op E) :
    ∀ r ∈ (net.applyAdv apps (.land op)).received, r ∈ op.proofStates ∨ r ∈ net.received := by
  simp only [NetworkState.applyAdv]
  cases net.chain.apply apps p op with
  | none => exact fun r hr => Or.inr hr
  | some s' => exact fun r hr => List.mem_append.mp hr

/-- The signatures of `p` and of `q` that a signed state carries are on
    states each of them sent. -/
def SigOK (p q : Participant) (sp sq : List (SignedState E)) (r : SignedState E) : Prop :=
  (p ∈ r.signers → ∃ s ∈ sp, s.state = r.state) ∧ (q ∈ r.signers → ∃ s ∈ sq, s.state = r.state)

omit [DecidableEq E] in
theorem SigOK.swap {p q : Participant} {sp sq : List (SignedState E)} {r : SignedState E}
    (h : SigOK p q sp sq r) : SigOK q p sq sp r := ⟨h.2, h.1⟩

omit [DecidableEq E] in
theorem SigOK.mono {p q : Participant} {sp sq sp' sq' : List (SignedState E)}
    {r : SignedState E} (h : SigOK p q sp sq r) (hp : ∀ s ∈ sp, s ∈ sp')
    (hq : ∀ s ∈ sq, s ∈ sq') : SigOK p q sp' sq' r := by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · obtain ⟨s, hs, he⟩ := h.1 hm; exact ⟨s, hp s hs, he⟩
  · obtain ⟨s, hs, he⟩ := h.2 hm; exact ⟨s, hq s hs, he⟩

/-- The voucher `p` or `q` signs, on a signed state that carries it, is on
    a state each of them sent carrying the same voucher. The voucher
    analog of `SigOK` (D7 voucher rule repaired; see
    the funding-point alternative-moves analysis). -/
def VoucherOK (p q : Participant) (sp sq : List (SignedState E)) (r : SignedState E) : Prop :=
  ∀ v, r.state.voucher? = some v →
    (p ∈ v.signers → ∃ s ∈ sp, s.state.voucher? = some v) ∧
    (q ∈ v.signers → ∃ s ∈ sq, s.state.voucher? = some v)

omit [DecidableEq E] in
theorem VoucherOK.swap {p q : Participant} {sp sq : List (SignedState E)} {r : SignedState E}
    (h : VoucherOK p q sp sq r) : VoucherOK q p sq sp r := fun v hv => ⟨(h v hv).2, (h v hv).1⟩

omit [DecidableEq E] in
theorem VoucherOK.mono {p q : Participant} {sp sq sp' sq' : List (SignedState E)}
    {r : SignedState E} (h : VoucherOK p q sp sq r) (hp : ∀ s ∈ sp, s ∈ sp')
    (hq : ∀ s ∈ sq, s ∈ sq') : VoucherOK p q sp' sq' r := fun v hv => by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · obtain ⟨s, hs, he⟩ := (h v hv).1 hm; exact ⟨s, hp s hs, he⟩
  · obtain ⟨s, hs, he⟩ := (h v hv).2 hm; exact ⟨s, hq s hs, he⟩

/-- Every signature of `p` or of `q` that either view received is on a
    state its signer sent, in that signer's own view, and likewise for
    every voucher a received state carries. -/
def JointGenuine {p q : Participant} (Sp : NetworkState E p) (Sq : NetworkState E q) : Prop :=
  (∀ r ∈ Sp.received, SigOK p q Sp.sent Sq.sent r) ∧
  (∀ r ∈ Sq.received, SigOK p q Sp.sent Sq.sent r) ∧
  (∀ r ∈ Sp.received, VoucherOK p q Sp.sent Sq.sent r) ∧
  (∀ r ∈ Sq.received, VoucherOK p q Sp.sent Sq.sent r)

omit [DecidableEq E] in
theorem JointGenuine.symm {p q : Participant} {Sp : NetworkState E p} {Sq : NetworkState E q}
    (h : JointGenuine Sp Sq) : JointGenuine Sq Sp :=
  ⟨fun r hr => (h.2.1 r hr).swap, fun r hr => (h.1 r hr).swap,
    fun r hr => (h.2.2.2 r hr).swap, fun r hr => (h.2.2.1 r hr).swap⟩

omit [DecidableEq E] in
/-- A state `x` holds carries genuine signatures of `x` and of `y`, and
    genuine vouchers of `x` and of `y`, so the adversary of `y` may submit
    it (`NetworkState.Unforged`). -/
theorem NetworkState.Holds.sigOK {x y : Participant} (hxy : x ≠ y) {nx Sx : NetworkState E x}
    {Sy : NetworkState E y} (hrecv : ∀ r ∈ nx.received, r ∈ Sx.received)
    (hsent : nx.sent = Sx.sent) (hG : ∀ r ∈ Sx.received, SigOK x y Sx.sent Sy.sent r)
    (hV : ∀ r ∈ Sx.received, VoucherOK x y Sx.sent Sy.sent r)
    {ss : SignedState E} (hh : nx.Holds ss) :
    SigOK x y Sx.sent Sy.sent ss ∧ VoucherOK x y Sx.sent Sy.sent ss ∧ Sy.Unforged ss := by
  obtain ⟨h1, h2⟩ := hh
  have hx : x ∈ ss.signers → ∃ s ∈ Sx.sent, s.state = ss.state := fun hm => by
    rcases h1 x hm with ⟨-, s, hs, hse⟩ | ⟨r, hr, hre, hrx⟩
    · exact ⟨s, hsent ▸ hs, hse⟩
    · obtain ⟨s, hs, hse⟩ := (hG r (hrecv r hr)).1 hrx
      exact ⟨s, hs, hse.trans hre⟩
  have hy : y ∈ ss.signers → ∃ s ∈ Sy.sent, s.state = ss.state := fun hm => by
    rcases h1 y hm with ⟨hyx, -⟩ | ⟨r, hr, hre, hry⟩
    · exact absurd hyx.symm hxy
    · obtain ⟨s, hs, hse⟩ := (hG r (hrecv r hr)).2 hry
      exact ⟨s, hs, hse.trans hre⟩
  have hvv : VoucherOK x y Sx.sent Sy.sent ss := fun v hv => by
    refine ⟨fun hxv => ?_, fun hyv => ?_⟩
    · rcases h2 v hv x hxv with ⟨-, s, hs, hse⟩ | ⟨r, hr, hrv⟩
      · exact ⟨s, hsent ▸ hs, hse⟩
      · exact (hV r (hrecv r hr) v hrv).1 hxv
    · rcases h2 v hv y hyv with ⟨hyx, -⟩ | ⟨r, hr, hrv⟩
      · exact absurd hyx.symm hxy
      · exact (hV r (hrecv r hr) v hrv).2 hyv
  exact ⟨⟨hx, hy⟩, hvv, hy, fun v hv hyv => (hvv v hv).2 hyv⟩

/-- **One reaction's calls, in both views.** Participant `x` lands its
    pending `calls` in its own round (`Threat.RoundSeq.land`, in order, with
    no tick). The same calls run in the view of `y` as the adversary's
    `.chain x` moves (`OtherSteps`): `Capable.capable` allows each one,
    because its proof states carry no forged signature of `y`. Both views
    apply one operation with one caller, so `ChanAgreeOrFin.apply` carries
    the status of `c`, and each new received entry has genuine signatures. -/
theorem mirror_land {apps : Apps E} {x y : Participant} (hxy : x ≠ y) {Tx : Threat E x}
    {Ty : Threat E y} (Cy : Capable apps y Ty) (c : FixedPart) (t : Time)
    (sx sy : List (SignedState E)) :
    ∀ (calls : List (Op E)) (Sx : NetworkState E x) (Sy : NetworkState E y),
      Sx.sent = sx → Sy.sent = sy →
      (∀ op ∈ calls, (∀ dt, op ≠ .tick dt) ∧
        ∀ ss ∈ op.proofStates, SigOK x y sx sy ss ∧ VoucherOK x y sx sy ss ∧ Sy.Unforged ss) →
      ChanAgreeOrFin c Sx.chain Sy.chain →
      (∀ r ∈ Sx.received, SigOK x y sx sy r) → (∀ r ∈ Sy.received, SigOK x y sx sy r) →
      (∀ r ∈ Sx.received, VoucherOK x y sx sy r) → (∀ r ∈ Sy.received, VoucherOK x y sx sy r) →
      ∃ Sx' Sy', Tx.RoundSeq apps t calls Sx Sx' ∧ OtherSteps apps Ty Sy Sy' ∧
        ChanAgreeOrFin c Sx'.chain Sy'.chain ∧
        (∀ r ∈ Sx'.received, SigOK x y sx sy r) ∧ (∀ r ∈ Sy'.received, SigOK x y sx sy r) ∧
        (∀ r ∈ Sx'.received, VoucherOK x y sx sy r) ∧ (∀ r ∈ Sy'.received, VoucherOK x y sx sy r) ∧
        Sx'.chain.now = Sx.chain.now ∧ Sy'.chain.now = Sy.chain.now ∧ Sx'.sent = sx ∧
        Sy'.sent = sy := by
  intro calls
  induction calls with
  | nil =>
    intro Sx Sy hsx hsy _ hag hgx hgy hvx hvy
    exact ⟨Sx, Sy, .nil, .refl, hag, hgx, hgy, hvx, hvy, rfl, rfl, hsx, hsy⟩
  | cons op rest ih =>
    intro Sx Sy hsx hsy hcalls hag hgx hgy hvx hvy
    obtain ⟨hnt, hss⟩ := hcalls op List.mem_cons_self
    have hfeas : Ty.feasible Sy (.chain x op) :=
      Cy.capable Sy x op hxy (fun ss h => (hss ss h).2.2)
    have hag1 : ChanAgreeOrFin c (Sx.applyAdv apps (.land op)).chain
        (Sy.applyAdv apps (.chain x op)).chain := by
      rw [NetworkState.applyAdv_land_chain, NetworkState.applyAdv_chain_chain]
      exact hag.apply x hnt
    have hrest : ∀ op' ∈ rest, (∀ dt, op' ≠ .tick dt) ∧
        ∀ ss ∈ op'.proofStates, SigOK x y sx sy ss ∧ VoucherOK x y sx sy ss ∧
          (Sy.applyAdv apps (.chain x op)).Unforged ss := by
      intro op' hop'
      obtain ⟨hnt', hss'⟩ := hcalls op' (List.mem_cons_of_mem _ hop')
      exact ⟨hnt', fun ss h => ⟨(hss' ss h).1, (hss' ss h).2.1,
        (hss' ss h).2.2.of_sent (NetworkState.applyAdv_sent apps Sy _).symm⟩⟩
    obtain ⟨Sx', Sy', hseq, hSy, hag', hgx', hgy', hvx', hvy', hnx, hny, hsx', hsy'⟩ :=
      ih (Sx.applyAdv apps (.land op)) (Sy.applyAdv apps (.chain x op))
        (by rw [NetworkState.applyAdv_sent, hsx]) (by rw [NetworkState.applyAdv_sent, hsy])
        hrest hag1
        (fun r hr => (NetworkState.applyAdv_land_received apps Sx op r hr).elim
          (fun h => (hss r h).1) (hgx r))
        (fun r hr => (NetworkState.applyAdv_chain_received apps Sy x op r hr).elim
          (fun h => (hss r h).1) (hgy r))
        (fun r hr => (NetworkState.applyAdv_land_received apps Sx op r hr).elim
          (fun h => (hss r h).2.1) (hvx r))
        (fun r hr => (NetworkState.applyAdv_chain_received apps Sy x op r hr).elim
          (fun h => (hss r h).2.1) (hvy r))
    refine ⟨Sx', Sy', .land (l1 := []) (l2 := rest) rfl hseq,
      (OtherSteps.refl.tail hfeas (fun _ h => by cases h) (fun _ h => by cases h)).trans hSy,
      hag', hgx', hgy', hvx', hvy', ?_, ?_, hsx', hsy'⟩
    · rw [hnx, NetworkState.applyAdv_land_chain, Adjudicator.apply_getD_now hnt]
    · rw [hny, NetworkState.applyAdv_chain_chain, Adjudicator.apply_getD_now hnt]

/-- **The joint play.** `p` is at a node of its strategy tree for
    `Finalized c Ω`, with the adversary moves `OtherSteps` already done in
    its open round; `q` likewise for `Finalized c Ω'`. Then `Ω = Ω'`. By
    induction on the tree of `p` and, inside it, on the tree of `q`:
    - a reaction of `p` runs in both views (`mirror_land`), and `p` moves on;
    - while `p` waits, a reaction of `q` runs in both views, and `q` moves on;
    - when both wait, one wait runs, in the view of its own participant only:
      `q`'s wait if the running challenge pays `Ω`, else `p`'s wait. A wait
      that finalizes `c` gives `Ω = Ω'` (`q` waited), or contradicts the
      tree of `p` (`p` waited, and the outcome is not `Ω`).
    When both chains finalize `c` with one outcome `Ω0`, both trees give
    `Ω0` (`UnbeatableIn.finalized_eq_of_steps`). -/
theorem finalizable_joint {apps : Apps E} {p q : Participant} (hpq : p ≠ q)
    {Tp : Threat E p} {Tq : Threat E q} (Cp : Capable apps p Tp) (Cq : Capable apps q Tq)
    {allp allq : HonestMove E → Prop} {c : FixedPart} {Ω Ω' : Outcome E}
    {np : NetworkState E p}
    (hp : UnbeatableIn apps Tp allp (fun net => net.Finalized c Ω) np) :
    ∀ (Sp : NetworkState E p), OtherSteps apps Tp np Sp → Sp.chain.now = np.chain.now →
    ∀ {nq : NetworkState E q}, UnbeatableIn apps Tq allq (fun net => net.Finalized c Ω') nq →
    ∀ (Sq : NetworkState E q), OtherSteps apps Tq nq Sq → Sq.chain.now = nq.chain.now →
    ChanAgreeOrFin c Sp.chain Sq.chain → JointGenuine Sp Sq → Ω = Ω' := by
  induction hp with
  | done hGp =>
    intro Sp hSp _ nq hq Sq hSq hnq hag _
    have hfp := hSp.finalizedWith_mono hGp
    rcases hag with hA | ⟨Ω0, h1, h2⟩
    · rw [hA.finalizedWith_left] at hfp; cases hfp
    · rw [h1] at hfp
      exact (Option.some.inj hfp).symm.trans (hq.finalized_eq_of_steps hSq hnq h2)
  | @move np mp halp hfeasp hcontp ihp =>
    intro Sp hSp hnp nq hq
    have hUp : UnbeatableIn apps Tp allp (fun net => net.Finalized c Ω) np :=
      .move mp halp hfeasp hcontp
    induction hq generalizing Sp with
    | done hGq =>
      intro Sq hSq _ hag _
      have hfq := hSq.finalizedWith_mono hGq
      rcases hag with hA | ⟨Ω0, h1, h2⟩
      · rw [hA.finalizedWith_right] at hfq; cases hfq
      · rw [h2] at hfq
        exact (hUp.finalized_eq_of_steps hSp hnp h1).symm.trans (Option.some.inj hfq)
    | @move nq mq halq hfeasq hcontq ihq =>
      intro Sq hSq hnq hag hgen
      have hUq : UnbeatableIn apps Tq allq (fun net => net.Finalized c Ω') nq :=
        .move mq halq hfeasq hcontq
      rcases hag with hA | ⟨Ω0, h1, h2⟩
      swap
      · exact (hUp.finalized_eq_of_steps hSp hnp h1).symm.trans
          (hUq.finalized_eq_of_steps hSq hnq h2)
      cases mp with
      | react rp =>
        -- `p` issues its reaction; its calls run in `q`'s view as adversary moves.
        have hcalls : ∀ op ∈ rp.calls, (∀ dt, op ≠ .tick dt) ∧
            ∀ ss ∈ op.proofStates, SigOK p q Sp.sent Sq.sent ss ∧ VoucherOK p q Sp.sent Sq.sent ss ∧
              Sq.Unforged ss := by
          intro op hop
          have hf : op.HonestFeasible np := hfeasp.1 op hop
          exact ⟨hf.not_tick, fun ss hss =>
            (hf.holds ss hss).sigOK hpq hSp.received_subset hSp.sent_eq.symm hgen.1 hgen.2.2.1⟩
        obtain ⟨Sp', Sq', hseq, hSq', hag', hgp', hgq', hvp', hvq', hnp', hnq', hsp', hsq'⟩ :=
          mirror_land hpq Cq c np.chain.now Sp.sent Sq.sent rp.calls Sp Sq rfl rfl hcalls
            (Or.inl hA) hgen.1 hgen.2.1 hgen.2.2.1 hgen.2.2.2
        have hround : Tp.Round apps (.react rp) np Sp' :=
          ⟨hSp.roundSeq hseq, by rw [hnp', hnp]; exact Nat.lt_add_of_pos_right Tp.ε_pos⟩
        have hsub : ∀ s ∈ Sp.sent, s ∈ (Sp'.applyHonest (.react rp)).sent := by
          intro s hs
          show s ∈ rp.sends.map _ ++ Sp'.sent
          rw [hsp']
          exact List.mem_append_right _ hs
        refine ihp Sp' hround (Sp'.applyHonest (.react rp)) .refl rfl hUq Sq' (hSq.trans hSq')
          (by rw [hnq', hnq]) hag' ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
        · exact (hgp' r hr).mono hsub (fun s hs => by rw [hsq']; exact hs)
        · exact (hgq' r hr).mono hsub (fun s hs => by rw [hsq']; exact hs)
        · exact (hvp' r hr).mono hsub (fun s hs => by rw [hsq']; exact hs)
        · exact (hvq' r hr).mono hsub (fun s hs => by rw [hsq']; exact hs)
      | wait dp =>
        cases mq with
        | react rq =>
          -- `q` issues its reaction; its calls run in `p`'s open round.
          have hcalls : ∀ op ∈ rq.calls, (∀ dt, op ≠ .tick dt) ∧
              ∀ ss ∈ op.proofStates, SigOK q p Sq.sent Sp.sent ss ∧ VoucherOK q p Sq.sent Sp.sent ss ∧
                Sp.Unforged ss := by
            intro op hop
            have hf : op.HonestFeasible nq := hfeasq.1 op hop
            exact ⟨hf.not_tick, fun ss hss =>
              (hf.holds ss hss).sigOK (Ne.symm hpq) hSq.received_subset hSq.sent_eq.symm
                hgen.symm.1 hgen.symm.2.2.1⟩
          obtain ⟨Sq', Sp', hseq, hSp', hag', hgq', hgp', hvq', hvp', hnq', hnp', hsq', hsp'⟩ :=
            mirror_land (Ne.symm hpq) Cp c nq.chain.now Sq.sent Sp.sent rq.calls Sq Sp rfl rfl
              hcalls (Or.inl hA.symm) hgen.symm.1 hgen.symm.2.1 hgen.symm.2.2.1 hgen.symm.2.2.2
          have hround : Tq.Round apps (.react rq) nq Sq' :=
            ⟨hSq.roundSeq hseq, by rw [hnq', hnq]; exact Nat.lt_add_of_pos_right Tq.ε_pos⟩
          have hsub : ∀ s ∈ Sq.sent, s ∈ (Sq'.applyHonest (.react rq)).sent := by
            intro s hs
            show s ∈ rq.sends.map _ ++ Sq'.sent
            rw [hsq']
            exact List.mem_append_right _ hs
          refine ihq Sq' hround Sp' (hSp.trans hSp') (by rw [hnp', hnp])
            (Sq'.applyHonest (.react rq)) .refl rfl hag'.symm
            ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
          · exact ((hgp' r hr).mono hsub (fun s hs => by rw [hsp']; exact hs)).swap
          · exact ((hgq' r hr).mono hsub (fun s hs => by rw [hsp']; exact hs)).swap
          · exact ((hvp' r hr).mono hsub (fun s hs => by rw [hsp']; exact hs)).swap
          · exact ((hvq' r hr).mono hsub (fun s hs => by rw [hsp']; exact hs)).swap
        | wait dq =>
          have hroundp : Tp.Round apps (.wait dp) np Sp :=
            ⟨hSp.roundSeq .nil, by rw [hnp]; exact Nat.lt_add_of_pos_right Tp.ε_pos⟩
          have hroundq : Tq.Round apps (.wait dq) nq Sq :=
            ⟨hSq.roundSeq .nil, by rw [hnq]; exact Nat.lt_add_of_pos_right Tq.ε_pos⟩
          rcases hA with ⟨r, ho1, ho2⟩ | ⟨r, ch1, ch2, hc1, hc2, hst, hlt1, hlt2⟩
          · -- `c` is open: `p`'s wait cannot finalize it.
            exact ihp Sp hroundp (Sp.applyHonest (.wait dp)) .refl rfl hUq Sq hSq hnq
              (Or.inl (Or.inl ⟨r, by (simpa? [NetworkState.applyHonest] using ho1 says simpa only [NetworkState.applyHonest, Adjudicator.tick_statusOf] using ho1), ho2⟩)) hgen
          · by_cases hout : ch1.state.outcome = Ω
            · -- The running challenge pays `p`'s outcome: `q` waits first.
              by_cases hcross : Sq.chain.now + dq < ch2.deadline
              · exact ihq Sq hroundq Sp hSp hnp (Sq.applyHonest (.wait dq)) .refl rfl
                  (Or.inl (Or.inr ⟨r, ch1, ch2, hc1,
                    by (simpa? [NetworkState.applyHonest] using hc2 says simpa only [NetworkState.applyHonest, Adjudicator.tick_statusOf] using hc2), hst, hlt1,
                    by (simpa? [NetworkState.applyHonest] using hcross says simpa only [NetworkState.applyHonest, Adjudicator.tick_now] using hcross)⟩)) hgen
              · have hfin : (Sq.applyHonest (.wait dq)).chain.finalizedWith c.address = some Ω := by
                  simp only [NetworkState.applyHonest, Adjudicator.finalizedWith_channel,
                    FixedPart.address_eq, Adjudicator.tick_statusOf, Adjudicator.tick_now, hc2,
                    ChannelStatus.finalizedWith_challenged, if_pos (not_lt.mp hcross), ← hst, hout]
                exact (hcontq Sq hroundq).finalized_eq hfin
            · -- Any other running challenge: `p` waits first.
              by_cases hcross : Sp.chain.now + dp < ch1.deadline
              · exact ihp Sp hroundp (Sp.applyHonest (.wait dp)) .refl rfl hUq Sq hSq hnq
                  (Or.inl (Or.inr ⟨r, ch1, ch2, by (simpa? [NetworkState.applyHonest] using hc1 says simpa only [NetworkState.applyHonest, Adjudicator.tick_statusOf] using hc1),
                    hc2, hst, by (simpa? [NetworkState.applyHonest] using hcross says simpa only [NetworkState.applyHonest, Adjudicator.tick_now] using hcross), hlt2⟩)) hgen
              · have hfin : (Sp.applyHonest (.wait dp)).chain.finalizedWith c.address =
                    some ch1.state.outcome := by
                  simp only [NetworkState.applyHonest, Adjudicator.finalizedWith_channel,
                    FixedPart.address_eq, Adjudicator.tick_statusOf, Adjudicator.tick_now, hc1,
                    ChannelStatus.finalizedWith_challenged, if_pos (not_lt.mp hcross)]
                exact absurd ((hcontp Sp hroundp).finalized_eq hfin) hout

/-- Nitro-22. Nitro:612-614: "The definition of finalizability excludes the case
    where two different finalizable outcomes are held by different
    participants, as in this case at least one participant's strategy would
    be beatable by the other participant's strategy." The proof plays the two
    strategies together, each in its own game (`finalizable_joint`). -/
theorem finalizable_unique (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Nitro.ReachableNetwork apps Ts) (hvn : v = n.state.views)
    (c : FixedPart) (p q : Participant) (hpq : p ≠ q) (Ω Ω' : Outcome E)
    (hp : Finalizable apps (Ts.T p) c Ω (v p)) (hq : Finalizable apps (Ts.T q) c Ω' (v q)) :
    Ω = Ω' := by
  obtain_reach ⟨n, hr⟩ := n
  subst hvn
  have hsig := Nitro.network_received_signers hr
  have hvouch := Nitro.network_received_voucher_signers ⟨_, hr⟩
  exact finalizable_joint hpq (Ts.ok p).toCapable (Ts.ok q).toCapable hp (n.views p) .refl rfl hq
    (n.views q) .refl rfl (ChanAgreeOrFin.refl c n.chain)
    ⟨fun r hr' => ⟨hsig p p r hr', hsig p q r hr'⟩, fun r hr' => ⟨hsig q p r hr', hsig q q r hr'⟩,
      fun r hr' v hv => ⟨hvouch p p r hr' v hv, hvouch p q r hr' v hv⟩,
      fun r hr' v hv => ⟨hvouch q p r hr' v hv, hvouch q q r hr' v hv⟩⟩

/-- Nitro-22. Nitro:597-611: "exactly one of the following statements is true
    about a channel χ at any point in time: 1. Finalized outcome ... 2. One
    participant has multiple finalizable outcomes ... 3. Multiple participants
    share one finalizable outcome ... 4. No finalizable outcomes." -/
theorem channel_finalizability_cases (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Nitro.ReachableNetwork apps Ts)
    (hvn : v = n.state.views) (c : FixedPart) (p0 : Participant) :
    (∃ Ω, (v p0).Finalized c Ω) ∨
    (∃ p, p ∈ c.participants ∧ (∃ Ω, Finalizable apps (Ts.T p) c Ω (v p)) ∧
      ∀ q, q ∈ c.participants → q ≠ p → ∀ Ω, ¬ Finalizable apps (Ts.T q) c Ω (v q)) ∨
    (∃ Ω p q, p ∈ c.participants ∧ q ∈ c.participants ∧ p ≠ q ∧
      Finalizable apps (Ts.T p) c Ω (v p) ∧ Finalizable apps (Ts.T q) c Ω (v q) ∧
      ∀ r, r ∈ c.participants → ∀ Ω', Finalizable apps (Ts.T r) c Ω' (v r) → Ω' = Ω) ∨
    (∀ p, p ∈ c.participants → ∀ Ω, ¬ Finalizable apps (Ts.T p) c Ω (v p)) := by
  obtain_reach ⟨n, hr⟩ := n
  by_cases hex : ∃ p ∈ c.participants, ∃ Ω, Finalizable apps (Ts.T p) c Ω (v p)
  · obtain ⟨p, hp, Ω, hΩ⟩ := hex
    by_cases hother :
        ∀ q, q ∈ c.participants → q ≠ p → ∀ Ω', ¬ Finalizable apps (Ts.T q) c Ω' (v q)
    · exact Or.inr (Or.inl ⟨p, hp, ⟨Ω, hΩ⟩, hother⟩)
    · push_neg at hother
      obtain ⟨q, hq, hqp, Ω', hΩ'⟩ := hother
      have heq : Ω = Ω' :=
        finalizable_unique apps Ts v ⟨n, hr⟩ hvn c p q hqp.symm Ω Ω' hΩ hΩ'
      refine Or.inr (Or.inr (Or.inl ⟨Ω, p, q, hp, hq, hqp.symm, hΩ, heq ▸ hΩ', ?_⟩))
      intro r hr' Ω'' hΩ''
      by_cases hrp : r = p
      · subst hrp
        have heq2 : Ω' = Ω'' := finalizable_unique apps Ts v ⟨n, hr⟩ hvn c q r hqp Ω' Ω'' hΩ' hΩ''
        exact (heq.trans heq2).symm
      · exact (finalizable_unique apps Ts v ⟨n, hr⟩ hvn c p r (fun h => hrp h.symm) Ω Ω'' hΩ hΩ'').symm
  · push_neg at hex
    exact Or.inr (Or.inr (Or.inr hex))

/-- Nitro-23, ForceMove-A14. Nitro:637-640: "When a single conclusion proof is known to
    each participant ... the channel is in the concluded state." The
    concluded outcome is universally finalizable. -/
theorem concluded_universally_finalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Nitro.ReachableNetwork apps Ts)
    (hvn : v = n.state.views) (c : FixedPart) (Ω : Outcome E) (hc : apps c.appDef = consensusRules)
    (h : Concluded v c Ω)
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = Ω)
    (hchain : ∀ p, (v p).chain.finalizedWith c.address = none ∨ (v p).Finalized c Ω)
    (hdur : ∀ p, 2 * (Ts.T p).ε ≤ c.challengeDuration)
    (hpend : ∀ p, (v p).DeadlineAfter c (Ts.T p).ε) :
    UniversallyFinalizable apps Ts v c Ω := by
  obtain_reach ⟨n, hr⟩ := n
  subst hvn
  intro p hp
  obtain ⟨ss, hh, hproof, hΩ⟩ := h p hp
  exact UnbeatableIn.mono (fun _ _ => trivial)
    (conclusion_proof_finalizable apps (Ts.T p) (Ts.ok p)
      ⟨(n.views p), (Nitro.network_views_participant_reachable ⟨_, hr⟩ p)⟩ ⟨c, hdur p⟩ ss Ω hc hp hh hproof hΩ
      (hsent p) (hchain p) (hpend p))

/-- The safety invariant used by `consensus_enabled_outcomes`: under the
    consensus app, with `p` holding `ss` (`ss.state.outcome = Ω1`), the
    channel `c` is either already finalized with `Ω1` or `Ω2`, genuinely
    open, or challenged by a candidate that is either itself safe
    (`Ω1`/`Ω2`) or strictly below `ss.state.turnNum` and not yet expired
    relative to `nowNet`'s clock. `statusNet` carries the status read;
    `nowNet` carries the clock a pending challenge's deadline is compared
    against (the two differ mid-round: `consensus_round_safe` reads status
    at the round's start and compares against the round's end). -/
def ConsensusSafe {p : Participant} (c : FixedPart) (ss : SignedState E) (Ω1 Ω2 : Outcome E)
    (statusNet nowNet : NetworkState E p) : Prop :=
  statusNet.chain.finalizedWith c.address = some Ω1 ∨
  statusNet.chain.finalizedWith c.address = some Ω2 ∨
  (statusNet.chain.finalizedWith c.address = none ∧
    ((∃ t, statusNet.chain.statusOf c = .open t) ∨
     (∃ t ch, statusNet.chain.statusOf c = .challenged t ch ∧
       (ch.state.outcome = Ω1 ∨ ch.state.outcome = Ω2 ∨
        (t < ss.state.turnNum ∧ nowNet.chain.now < ch.deadline)))))

/-- Over a round's adversary play, what `p` has received only grows, by
    induction on `NetworkState.applyAdv_received_subset`. -/
theorem Threat.RoundSeq.received_subset {apps : Apps E} {p : Participant} {T : Threat E p}
    {t : Time} {pending : List (Op E)} {net net' : NetworkState E p}
    (h : Threat.RoundSeq apps T t pending net net') : ∀ r ∈ net.received, r ∈ net'.received := by
  induction h with
  | nil => exact fun r hr => hr
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    exact fun r hr => ih r (NetworkState.applyAdv_received_subset apps net1 (.land op) r hr)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    exact fun r hr => ih r (NetworkState.applyAdv_received_subset apps net1 (.tick dt) r hr)
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    exact fun r hr => ih r (NetworkState.applyAdv_received_subset apps net1 m r hr)

omit [DecidableEq E] in
/-- A state `p` holds stays held as `sent` stays the same and `received`
    only grows: every witness signer carried by `net.Holds ss` is carried
    by `net'.Holds ss` too. -/
theorem NetworkState.Holds.mono {p : Participant} {net net' : NetworkState E p}
    {ss : SignedState E} (hsent : net.sent = net'.sent)
    (hrecv : ∀ r ∈ net.received, r ∈ net'.received) (h : net.Holds ss) : net'.Holds ss := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun q hq => ?_, fun v hv q hq => ?_⟩
  · rcases h1 q hq with ⟨hqp, s, hs, hse⟩ | ⟨r, hr, hre, hrq⟩
    · exact Or.inl ⟨hqp, s, hsent ▸ hs, hse⟩
    · exact Or.inr ⟨r, hrecv r hr, hre, hrq⟩
  · rcases h2 v hv q hq with ⟨hqp, s, hs, hse⟩ | ⟨r, hr, hre⟩
    · exact Or.inl ⟨hqp, s, hsent ▸ hs, hse⟩
    · exact Or.inr ⟨r, hrecv r hr, hre⟩

/-- `UnbeatableIn` is monotone in its goal: a strategy for `G1` is a strategy
    for any `G2` it implies pointwise. Used to restate a reached
    `CanObtain`-style balance bound in terms of a smaller original balance. -/
theorem UnbeatableIn.imp {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G1 G2 : NetworkState E p → Prop} {net : NetworkState E p}
    (himp : ∀ {net'}, G1 net' → G2 net') (hU : UnbeatableIn apps T allowed G1 net) :
    UnbeatableIn apps T allowed G2 net := by
  induction hU with
  | done hG => exact .done (himp hG)
  | move m hm hfeas _ ih => exact .move m hm hfeas ih

/-- `UnbeatableIn` composes sequentially: a strategy reaching `G1`, followed
    by a strategy from every `G1`-state reaching `G2`, is a strategy reaching
    `G2`. Used to chain a `FundedFor` strategy (reaching a directly-funded
    state) with a `directly_funded_pays` payout from that state. -/
theorem UnbeatableIn.bind {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G1 G2 : NetworkState E p → Prop} {net : NetworkState E p}
    (hU1 : UnbeatableIn apps T allowed G1 net)
    (hcont : ∀ {net'}, G1 net' → UnbeatableIn apps T allowed G2 net') :
    UnbeatableIn apps T allowed G2 net := by
  induction hU1 with
  | done hG => exact hcont hG
  | move m hm hfeas _ ih => exact .move m hm hfeas ih

/-- `c`'s entry for `d` and `o`'s own total through one successful on-chain
    step, with no funding assumption: same argument as `directly_funded_step`
    with every use of `o.total ≤ s.balances.get c.address` dropped (it is
    never read to derive `hf'`, `hd'` or the growth bound, only to re-derive
    itself for the next step). `o`'s own total never grows: a deposit and an
    unrelated transfer or reclaim leave it exactly as is; a transfer paying
    out of `c` only lowers it (`Allocation.total_reduceOwed`); a reclaim onto
    `c` removes a guarantee entry worth exactly what it adds to the two
    destinations (`Adjudicator.reclaim_some`'s `oV.amountAt 0 + oV.amountAt 1
    = x`), so its total is unchanged (the same inequalities
    `directly_funded_step` already derives bound it both ways). Used by
    `finalizable_funded_pays` to carry `c`'s finalized outcome, unshrunk,
    from `net` to wherever a `FundedFor` strategy first directly funds it. -/
theorem funded_entry_step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c : FixedPart} {o : Allocation E} {d : E} {amt : Coins}
    (hf : s.finalOutcome c.address = some (.allocation o))
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩)
    (h : s.apply apps caller op = some s') :
    ∃ o' amt', s'.finalOutcome c.address = some (.allocation o') ∧
      o'.total ≤ o.total ∧
      o'.find (.external d) = some ⟨.external d, .alloc amt'⟩ ∧
      s.balances.get (.external d) + amt ≤ s'.balances.get (.external d) + amt' := by
  have hf0 : (s.statusOf c).finalOutcome s.now = some (.allocation o) := by
    (simpa? [FixedPart.address_eq] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hf)
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf0]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c', hac', -⟩, -, hb, -, hs, hn⟩ := Adjudicator.deposit_some h
    have had : a ≠ (Address.external d : Address E) := by rw [hac']; intro hh; cases hh
    refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
    · (simpa? [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_of_status hs, hn] using hf)
    · rw [hb, Balances.get_add, if_neg (Ne.symm had)]
  | transfer a b =>
    by_cases hac : a = c
    · subst hac
      obtain ⟨o'', amt'', x, hf'', hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
        Adjudicator.transfer_some h
      rw [hf] at hf''
      simp only [Option.some.injEq, Outcome.allocation.injEq] at hf''
      subst hf''
      have hfo' : s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) := by
        have hstatc : s'.statusOf a = (s.statusOf a).withOutcome (.allocation (o.reduceOwed b x)) :=
          by rw [Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_pos rfl]
        (simp? [FixedPart.address_eq, hstatc] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, ChannelStatus.finalOutcome_withOutcome])
      have hxb : x ≤ o.owed b := hxeq ▸ paidTo_first_entry_only _ _ _
      have htot := Allocation.total_reduceOwed o b hxb
      have hcd : (Address.external d : Address E) ≠ a.address := by
        rw [FixedPart.address_eq]; intro hh; cases hh
      have hfind' := Allocation.find_reduceOwed o b (Address.external d) x
      by_cases hbd : (Address.external d : Address E) = b
      · subst hbd
        rw [if_pos rfl, hd] at hfind'
        simp only [Option.map_some] at hfind'
        have hxamt : x ≤ amt := by
          have heq : o.owed (Address.external d) = amt := by (simp? [Allocation.owed, hd] says simp only [Allocation.owed, hd, Option.map_some, Entry.amount_mk, Item.amount_alloc, Option.getD_some])
          rw [heq] at hxb; exact hxb
        have htot' : (o.reduceOwed (Address.external d) x).total ≤ o.total := Nat.le.intro htot
        refine ⟨o.reduceOwed (Address.external d) x, amt - x, hfo', htot', hfind', ?_⟩
        rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_pos rfl]
        (grind? says grind only)
      · rw [if_neg hbd] at hfind'
        have htot' : (o.reduceOwed b x).total ≤ o.total := Nat.le.intro htot
        refine ⟨o.reduceOwed b x, amt, hfo', htot', by rw [hfind']; exact hd, ?_⟩
        rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_neg hbd]
    · obtain ⟨o'', amt'', x, hf'', hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
        Adjudicator.transfer_some h
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac)]
      have hcd : (Address.external d : Address E) ≠ a.address := by
        rw [FixedPart.address_eq]; intro hh; cases hh
      refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add]
        by_cases hbd : (Address.external d : Address E) = b
        · rw [if_pos hbd]; (grind? says grind only)
        · rw [if_neg hbd]
  | reclaim l v =>
    by_cases hcl : l = c
    · subst hcl
      obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      rw [hf] at hL
      simp only [Option.some.injEq, Outcome.allocation.injEq] at hL
      subst hL
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      have hfo' : s'.finalOutcome l.address = some (.allocation
          (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address)) := by
        have hstatl : s'.statusOf l = (s.statusOf l).withOutcome (.allocation
            (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address)) := by
          rw [hsucc, Adjudicator.statusOf_setStatus, if_pos rfl]
        (simp? [FixedPart.address_eq, hstatl] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatl, ChannelStatus.finalOutcome_withOutcome])
      have h1 : (o.addTo left (oV.amountAt 0)).total ≤ o.total + oV.amountAt 0 :=
        Allocation.total_addTo_le _ _ _
      have h2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).total ≤
          (o.addTo left (oV.amountAt 0)).total + oV.amountAt 1 :=
        Allocation.total_addTo_le _ _ _
      have h3 : o.owed v.address ≤ (o.addTo left (oV.amountAt 0)).owed v.address :=
        Allocation.owed_addTo_ge _ _ _ _
      have h4 : (o.addTo left (oV.amountAt 0)).owed v.address ≤
          ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).owed v.address :=
        Allocation.owed_addTo_ge _ _ _ _
      have h5 := Allocation.total_remove_le
        ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)) v.address
      have hvo : o.owed v.address = x := by
        simp only [Allocation.owed, hfind, Option.map_some, Option.getD_some, Entry.amount_mk,
          Item.amount_guarantee]
      have had : (Address.external d : Address E) ≠ v.address := by intro hh; cases hh
      have hfind1 : (o.addTo left (oV.amountAt 0)).find (Address.external d) =
          some ⟨Address.external d, .alloc (if (Address.external d : Address E) = left
            then amt + oV.amountAt 0 else amt)⟩ := by
        by_cases hld : (Address.external d : Address E) = left
        · rw [if_pos hld, ← hld, Allocation.find_addTo_self, hd]; (simp? says simp only [Option.map_some, Entry.amount_mk, Item.amount_alloc])
        · rw [if_neg hld, Allocation.find_addTo_of_ne _ _ hld, hd]
      have hfind2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).find
          (Address.external d) = some ⟨Address.external d, .alloc
            ((if (Address.external d : Address E) = left then amt + oV.amountAt 0 else amt) +
              (if (Address.external d : Address E) = right then oV.amountAt 1 else 0))⟩ := by
        by_cases hrd : (Address.external d : Address E) = right
        · rw [if_pos hrd, ← hrd, Allocation.find_addTo_self, hfind1]; (simp? says simp only [Option.map_some, Entry.amount_mk, Item.amount_alloc])
        · rw [if_neg hrd, Allocation.find_addTo_of_ne _ _ hrd, hfind1]; (simp? says simp only [add_zero])
      have hfind3 : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
          v.address).find (Address.external d) = some ⟨Address.external d, .alloc
            ((if (Address.external d : Address E) = left then amt + oV.amountAt 0 else amt) +
              (if (Address.external d : Address E) = right then oV.amountAt 1 else 0))⟩ := by
        rw [Allocation.find_remove, if_neg had, hfind2]
      have htotR : x ≤ ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).owed
          v.address := hvo ▸ le_trans h3 h4
      have htotB : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).total ≤
          o.total + x := by
        calc ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).total
            ≤ (o.addTo left (oV.amountAt 0)).total + oV.amountAt 1 := h2
          _ ≤ o.total + oV.amountAt 0 + oV.amountAt 1 := Nat.add_le_add_right h1 _
          _ = o.total + (oV.amountAt 0 + oV.amountAt 1) := by rw [Nat.add_assoc]
          _ = o.total + x := by rw [hxeq]
      have htot' : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
          v.address).total ≤ o.total := by
        have hstepA : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
            v.address).total + ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).owed
            v.address ≤ o.total + x := le_trans h5 htotB
        have hstepB : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
            v.address).total + x ≤
            (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
              v.address).total +
              ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).owed v.address :=
          Nat.add_le_add_left htotR _
        exact Nat.le_of_add_le_add_right (le_trans hstepB hstepA)
      refine ⟨_, _, hfo', htot', hfind3, ?_⟩
      rw [hbal']
      split <;> split <;> (grind? says grind only)
    · obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcl)]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']
  | challenge c' proof candidate =>
    obtain ⟨⟨-, -, -, hm⟩, hsucc⟩ := Adjudicator.challenge_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      rw [Adjudicator.mode_eq] at hm
      rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hfin <;> cases hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']
  | checkpoint c' proof candidate =>
    obtain ⟨⟨ho, -, -, -⟩, hsucc⟩ := Adjudicator.checkpoint_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      exact ho hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']
  | conclude c' ss =>
    obtain ⟨⟨ho, -⟩, hsucc⟩ := Adjudicator.conclude_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      exact ho hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']
  | tick dt =>
    have hs' : s.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
    subst hs'
    refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
    · (simpa? [FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt) says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.tick_statusOf, Adjudicator.tick_now] using ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt))
    · (simp? says simp only [Adjudicator.tick_balances, Std.le_refl])

/-- One remaining pending call's own feasibility carries across one
    adversary move: `sent` is untouched and `received` only grows
    (`NetworkState.applyAdv_sent`, `NetworkState.applyAdv_received_subset`),
    and `Op.HonestFeasible`, for every op besides `deposit`/`tick`, only
    reads `net.Holds`, monotone in exactly those two facts
    (`NetworkState.Holds.mono`). Used by `funded_entry_round`'s `land`
    case, to carry every op still pending forward past the one that just
    landed. -/
theorem Op.HonestFeasible.applyAdv {apps : Apps E} {p : Participant} {net : NetworkState E p}
    (m : AdvMove E) {op : Op E} (hfeas : op.HonestFeasible net) :
    op.HonestFeasible (net.applyAdv apps m) := by
  cases op with
  | deposit a e x => exact hfeas
  | tick dt => exact hfeas
  | transfer _ _ | reclaim _ _ | challenge _ _ _ | checkpoint _ _ _ | conclude _ _ =>
    exact fun ss hss => NetworkState.Holds.mono (NetworkState.applyAdv_sent apps net m).symm
      (NetworkState.applyAdv_received_subset apps net m) (hfeas ss hss)

/-- An op's own feasibility carries across a whole round, the same way as
    one step (`Op.HonestFeasible.applyAdv`), using the round's own
    `sent`/`received` monotonicity (`Threat.RoundSeq.sent_eq`,
    `Threat.RoundSeq.received_subset`) directly instead of composing one
    step at a time. Used by `HonestMove.Feasible.round`. -/
theorem Op.HonestFeasible.round {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (hseq : Threat.RoundSeq apps T t pending net net') {op : Op E}
    (hfeas : op.HonestFeasible net) : op.HonestFeasible net' := by
  cases op with
  | deposit a e x => exact hfeas
  | tick dt => exact hfeas
  | transfer _ _ | reclaim _ _ | challenge _ _ _ | checkpoint _ _ _ | conclude _ _ =>
    exact fun ss hss => NetworkState.Holds.mono hseq.sent_eq.symm hseq.received_subset
      (hfeas ss hss)

/-- A move's own feasibility, read call by call: `.wait` has none; a
    `.react r`'s feasibility starts with `∀op∈r.calls,
    op.HonestFeasible net`. Used by `funded_entry_unbeatable`'s `move`
    case, so `funded_entry_round` gets its feasibility hypothesis from
    `hfeas` without naming `net` or `m` explicitly (avoiding a `cases m`
    on a hypothesis that outlives the match). -/
theorem HonestMove.Feasible.calls {apps : Apps E} {p : Participant} {net : NetworkState E p}
    {m : HonestMove E} (hfeas : m.Feasible apps net) : ∀ op ∈ m.calls, op.HonestFeasible net := by
  cases m with
  | react r => exact hfeas.1
  | wait dt => (simp? [HonestMove.calls] says simp only [HonestMove.calls, List.not_mem_nil, IsEmpty.forall_iff, implies_true])

/-- Over a whole adversary round, `funded_entry_step`'s invariant holds, and
    the round also keeps `Nitro.participant`-reachability: a `land` is the
    machine's own second disjunct (`op.HonestFeasible`, carried this far,
    one step at a time, by `Op.HonestFeasible.applyAdv`, from every call
    still pending at the round's start — the caller's hypothesis); a
    `tick`/`other` step is the third disjunct, `T.feasible` directly
    (`Machine.Reachable.tail`). Used by `funded_entry_unbeatable`. -/
theorem funded_entry_round {apps : Apps E} {p : Participant} {T : Threat E p} (c : FixedPart)
    (d : E) :
    ∀ {net net' : NetworkState E p} {t : Time} {pending : List (Op E)},
      Threat.RoundSeq apps T t pending net net' →
      (∀ op ∈ pending, op.HonestFeasible net) →
      (Nitro.participant apps T).Reachable net →
      ∀ {o : Allocation E} {amt : Coins},
        net.chain.finalOutcome c.address = some (.allocation o) →
        o.find (.external d) = some ⟨.external d, .alloc amt⟩ →
        (Nitro.participant apps T).Reachable net' ∧
        ∃ o' amt', net'.chain.finalOutcome c.address = some (.allocation o') ∧
          o'.total ≤ o.total ∧
          o'.find (.external d) = some ⟨.external d, .alloc amt'⟩ ∧
          net.chain.balances.get (.external d) + amt ≤
            net'.chain.balances.get (.external d) + amt' := by
  intro net net' t pending hseq
  induction hseq with
  | nil => intro _ hR o amt hf hd; exact ⟨hR, o, amt, hf, le_refl _, hd, le_refl _⟩
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro hpfeas hR o amt hf hd
    have hopfeas : op.HonestFeasible net1 := hpfeas op (by (simp? [hsplit] says simp only [hsplit, List.mem_append, List.mem_cons, true_or, or_true]))
    have hR1 : (Nitro.participant apps T).Reachable (net1.applyAdv apps (.land op)) :=
      Machine.Reachable.tail hR (Or.inr (Or.inl ⟨op, hopfeas, rfl⟩))
    have hpfeas' : ∀ op' ∈ l1 ++ l2, op'.HonestFeasible (net1.applyAdv apps (.land op)) := by
      intro op' hop'
      refine Op.HonestFeasible.applyAdv (.land op) (hpfeas op' ?_)
      simp only [hsplit, List.mem_append, List.mem_cons] at hop' ⊢
      tauto
    have hstep : ∃ o1 amt1, (net1.applyAdv apps (.land op)).chain.finalOutcome c.address =
        some (.allocation o1) ∧ o1.total ≤ o.total ∧
        o1.find (.external d) = some ⟨.external d, .alloc amt1⟩ ∧
        net1.chain.balances.get (.external d) + amt ≤
          (net1.applyAdv apps (.land op)).chain.balances.get (.external d) + amt1 := by
      cases hm : net1.chain.apply apps p op with
      | none => exact ⟨o, amt, by simp only [NetworkState.applyAdv, hm]; exact hf, le_refl _,
          hd, by simp only [NetworkState.applyAdv, hm]; exact le_refl _⟩
      | some s' =>
        obtain ⟨o1, amt1, hf1, htot1, hd1, hle1⟩ := funded_entry_step hf hd hm
        exact ⟨o1, amt1, by simp only [NetworkState.applyAdv, hm]; exact hf1, htot1,
          hd1, by simp only [NetworkState.applyAdv, hm]; exact hle1⟩
    obtain ⟨o1, amt1, hf1, htot1, hd1, hle1⟩ := hstep
    obtain ⟨hR2, o2, amt2, hf2, htot2, hd2, hle2⟩ := ih hpfeas' hR1 hf1 hd1
    exact ⟨hR2, o2, amt2, hf2, le_trans htot2 htot1, hd2, le_trans hle1 hle2⟩
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hpfeas hR o amt hf hd
    have hR1 : (Nitro.participant apps T).Reachable (net1.applyAdv apps (.tick dt)) :=
      Machine.Reachable.tail hR (Or.inr (Or.inr (Or.inl ⟨.tick dt, hfeas,
        (fun op h => by cases h), rfl⟩)))
    have hpfeas' : ∀ op' ∈ pending, op'.HonestFeasible (net1.applyAdv apps (.tick dt)) :=
      fun op' hop' => Op.HonestFeasible.applyAdv (.tick dt) (hpfeas op' hop')
    refine ih hpfeas' hR1 ?_ ?_
    · simpa [NetworkState.applyAdv, FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono
          (show (net1.chain.statusOf c).finalOutcome net1.chain.now = some (.allocation o) by
            simpa [FixedPart.address_eq] using hf)
          (Nat.le_add_right net1.chain.now dt)
    · (simpa? [NetworkState.applyAdv] using hd says simpa only using hd)
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hpfeas hR o amt hf hd
    have hR1 : (Nitro.participant apps T).Reachable (net1.applyAdv apps m) :=
      Machine.Reachable.tail hR (Or.inr (Or.inr (Or.inl ⟨m, hfeas, hnoland, rfl⟩)))
    have hpfeas' : ∀ op' ∈ pending, op'.HonestFeasible (net1.applyAdv apps m) :=
      fun op' hop' => Op.HonestFeasible.applyAdv m (hpfeas op' hop')
    cases m with
    | chain caller op =>
      cases hm : net1.chain.apply apps caller op with
      | none =>
        have hf' : (net1.applyAdv apps (.chain caller op)).chain.finalOutcome c.address =
            some (.allocation o) := by simp only [NetworkState.applyAdv, hm]; exact hf
        have hd' : o.find (.external d) = some ⟨.external d, .alloc amt⟩ := hd
        have hres := ih hpfeas' hR1 hf' hd'
        (simpa? [NetworkState.applyAdv, hm] using hres says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, exists_and_left, NetworkState.applyAdv, hm] using hres)
      | some s' =>
        obtain ⟨o1, amt1, hf1, htot1, hd1, hle1⟩ := funded_entry_step hf hd hm
        have hf1' : (net1.applyAdv apps (.chain caller op)).chain.finalOutcome c.address =
            some (.allocation o1) := by simp only [NetworkState.applyAdv, hm]; exact hf1
        have hd1' : o1.find (.external d) = some ⟨.external d, .alloc amt1⟩ := hd1
        obtain ⟨hR2, o2, amt2, hf2, htot2, hd2, hle2⟩ := ih hpfeas' hR1 hf1' hd1'
        simp only [NetworkState.applyAdv, hm] at hle2
        exact ⟨hR2, o2, amt2, hf2, le_trans htot2 htot1, hd2, le_trans hle1 hle2⟩
    | deliver ss =>
      have hf' : (net1.applyAdv apps (.deliver ss)).chain.finalOutcome c.address =
          some (.allocation o) := by simp only [NetworkState.applyAdv]; exact hf
      have hd' : o.find (.external d) = some ⟨.external d, .alloc amt⟩ := hd
      have hres := ih hpfeas' hR1 hf' hd'
      (simpa? [NetworkState.applyAdv] using hres says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, exists_and_left, NetworkState.applyAdv] using hres)
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)

/-- One honest move keeps `funded_entry_step`'s invariant: a `.react r`
    never touches the chain at all (`NetworkState.applyHonest`; its calls
    land separately, through `Threat.RoundSeq.land`, which
    `funded_entry_round`'s own `land` case already covers); `.wait` only
    advances the clock (`ChannelStatus.finalOutcome_mono`). Used by
    `funded_entry_unbeatable`. -/
theorem funded_entry_honest_step {p : Participant}
    {net : NetworkState E p} (m : HonestMove E) {c : FixedPart} {o : Allocation E}
    {d : E} {amt : Coins}
    (hf : net.chain.finalOutcome c.address = some (.allocation o))
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    ∃ o' amt', (net.applyHonest m).chain.finalOutcome c.address = some (.allocation o') ∧
      o'.total ≤ o.total ∧
      o'.find (.external d) = some ⟨.external d, .alloc amt'⟩ ∧
      net.chain.balances.get (.external d) + amt ≤
        (net.applyHonest m).chain.balances.get (.external d) + amt' := by
  cases m with
  | react r =>
    exact ⟨o, amt, by simp only [NetworkState.applyHonest]; exact hf, le_refl _, hd, le_refl _⟩
  | wait dt =>
    refine ⟨o, amt, ?_, le_refl _, hd, ?_⟩
    · simpa [NetworkState.applyHonest, FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono
          (show (net.chain.statusOf c).finalOutcome net.chain.now = some (.allocation o) by
            simpa [FixedPart.address_eq] using hf)
          (Nat.le_add_right net.chain.now dt)
    · (simp? [NetworkState.applyHonest] says simp only [NetworkState.applyHonest, Adjudicator.tick_balances, Std.le_refl])


/-- One round of adversary play keeps an honest move feasible: `.wait` is
    always feasible; a `.react r`'s feasibility is "every call in `r.calls`
    is `Op.HonestFeasible`", each carried forward by `Op.HonestFeasible.round`,
    and "every send satisfies `HonestSend`": the round keeps `sent`
    (`Threat.RoundSeq.sent_eq`) and only grows `received`
    (`Threat.RoundSeq.received_subset`), so every held pre-fund state stays held.
    Used by `funded_entry_unbeatable`: the committed move's own feasibility
    (checked before the round) still holds at the state it is actually
    applied to (after the round). -/
theorem HonestMove.Feasible.round {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (hseq : Threat.RoundSeq apps T t pending net net') {m : HonestMove E}
    (hfeas : m.Feasible apps net) : m.Feasible apps net' := by
  cases m with
  | react r =>
    have hsub : ∀ x ∈ net.sent, x ∈ net'.sent := fun x hx => by rw [hseq.sent_eq]; exact hx
    refine ⟨fun op hop => Op.HonestFeasible.round hseq (hfeas.1 op hop), fun st hst => ?_⟩
    rw [hseq.sent_eq]
    have hm := NetworkState.held_mono (apps := apps) fun _ h => h.of_subset hsub hseq.received_subset
    exact (hfeas.2 st hst).mono (fun _ hx => hx) hm.1 hm.2
  | wait dt => trivial

/-- A `FundedFor`-shaped `UnbeatableIn` tree, run from a state where `c` is
    finalized with `o` and `o` already pays `d` its `amt`, reaches a
    `DirectlyFundedWith c x` state that is STILL reachable, still finalized
    with some `o'` whose total has not grown past `o`'s (`funded_entry_step`,
    `funded_entry_round`, `funded_entry_honest_step`, chained through every
    honest move and adversary round the tree plays), still pays `d` at least
    `amt' ≥ amt`, and keeps the balance-at-`d` bookkeeping
    (`directly_funded_round`'s shape) all the way from `net`. Used by
    `finalizable_funded_pays`: `o'.total ≤ o.total ≤ x` then gives
    `net'.chain.DirectlyFunded c` via `o'` itself. -/
theorem funded_entry_unbeatable {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} (c : FixedPart) (x : Coins) (d : E) :
    ∀ {net : NetworkState E p},
      UnbeatableIn apps T allowed (fun net' => net'.chain.DirectlyFundedWith c x) net →
      (Nitro.participant apps T).Reachable net →
      ∀ {o : Allocation E} {amt : Coins},
        net.chain.finalOutcome c.address = some (.allocation o) →
        o.find (.external d) = some ⟨.external d, .alloc amt⟩ →
        UnbeatableIn apps T allowed
          (fun net' => (Nitro.participant apps T).Reachable net' ∧
            ∃ o' amt', net'.chain.finalOutcome c.address = some (.allocation o') ∧
              o'.total ≤ o.total ∧
              net'.chain.DirectlyFundedWith c x ∧
              o'.find (.external d) = some ⟨.external d, .alloc amt'⟩ ∧
              net.chain.balances.get (.external d) + amt ≤
                net'.chain.balances.get (.external d) + amt')
          net := by
  intro net hU
  induction hU with
  | done hG => intro hR o amt hf hd; exact .done ⟨hR, o, amt, hf, le_refl _, hG, hd, le_refl _⟩
  | move m hm hfeas _ ih =>
    intro hR o amt hf hd
    refine .move m hm hfeas ?_
    intro net' hround
    obtain ⟨hR1, o1, amt1, hf1, htot1, hd1, hle1⟩ :=
      funded_entry_round c d hround.1 hfeas.calls hR hf hd
    have hR2 : (Nitro.participant apps T).Reachable (net'.applyHonest m) :=
      Machine.Reachable.tail hR1 (Or.inl ⟨m, HonestMove.Feasible.round hround.1 hfeas, rfl⟩)
    obtain ⟨o2, amt2, hf2, htot2, hd2, hle2⟩ := funded_entry_honest_step m hf1 hd1
    refine UnbeatableIn.imp ?_ (ih net' hround hR2 hf2 hd2)
    rintro net'' ⟨hR3, o3, amt3, hf3, htot3, hG3, hd3, hle3⟩
    exact ⟨hR3, o3, amt3, hf3, le_trans htot3 (le_trans htot2 htot1), hG3, hd3,
      le_trans hle1 (le_trans hle2 hle3)⟩

/-- Nitro-17, Nitro-21, Nitro-16. Nitro:480-481 and Nitro:590-593: a finalized allocation
    in a channel funded for `p` pays `d` its allocation. The channel is
    finalized already: a strategy to finalize and a strategy to fund do not
    compose, because the second one starts from `net`.

    Design decision 2026-10-29: `net` is a reachable network state, for the
    same reason as `directly_funded_pays`. -/
theorem finalizable_funded_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : FixedPart) (o : Allocation E) (d : E)
    (hf : net.state.chain.finalOutcome c.address = some (.allocation o))
    (hfund : FundedFor apps T c o.total net.state) (amt : Coins)
    (hd : o.find (.external d) = some ⟨.external d, .alloc amt⟩) :
    CanObtain apps T (.external d) (net.state.chain.balances.get (.external d) + o.owed (.external d))
      net.state := by
  obtain_reach ⟨net, hr⟩ := net
  have howed : o.owed (Address.external d) = amt := by (simp? [Allocation.owed, hd] says simp only [Allocation.owed, hd, Option.map_some, Entry.amount_mk, Item.amount_alloc, Option.getD_some])
  rw [howed]
  have hU : UnbeatableIn apps T (fun _ => True)
      (fun net' => net'.chain.DirectlyFundedWith c o.total) net := hfund
  have hU2 := funded_entry_unbeatable c o.total d hU hr hf hd
  refine UnbeatableIn.bind hU2 ?_
  rintro net' ⟨hR', o', amt', hf', htot', hfund', hd', hle'⟩
  have hDF : net'.chain.DirectlyFunded c := ⟨o', hf', le_trans htot' hfund'⟩
  have hpay := directly_funded_pays apps T A ⟨net', hR'⟩ c o' d hf' hDF amt' hd'
  have howed' : o'.owed (Address.external d) = amt' := by (simp? [Allocation.owed, hd'] says simp only [Allocation.owed, hd', Option.map_some, Entry.amount_mk, Item.amount_alloc, Option.getD_some])
  rw [howed'] at hpay
  have hpayMono : UnbeatableIn apps T (fun _ => True)
      (fun net'' => net'.chain.balances.get (.external d) + amt' ≤
        net''.chain.balances.get (.external d)) net' :=
    UnbeatableIn.mono (fun _ _ => trivial) hpay
  refine UnbeatableIn.imp ?_ hpayMono
  intro net'' hle''
  exact le_trans hle' hle''

/-- The shared case analysis of `consensus_round_safe_nil` and
    `consensus_round_safe`, for one adversary move `m` that is not a
    `tick` and not a `land` (`Threat.RoundSeq.other`). `ConsensusSafe`
    over `net1`/`net2` carries across `m` to `net1.applyAdv apps m`/`net2`,
    and the round's own clock bound (`hεbound`) and `p`'s own sent-list
    bound (`hsent`) carry across `m` the same way. `hnow` is the clock bound of
    the rest of the round (`Threat.RoundSeq.now_le`). This is the shared core
    of the block that both theorems carried in full (`verification.md` §6a). -/
theorem consensus_round_safe_core {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω1 Ω2 : Outcome E}
    (hC : TimedConsensusMember apps p T.ε c) (hΩ1 : ss.state.outcome = Ω1)
    {net1 net2 : NetworkState E p} {m : AdvMove E}
    (hfeas : T.feasible net1 m) (hnotick : ∀ dt, m ≠ .tick dt) (hnoland : ∀ op, m ≠ .land op)
    (hεbound : net2.chain.now < net1.chain.now + T.ε)
    (hnow : (net1.applyAdv apps m).chain.now ≤ net2.chain.now)
    (hsent : ∀ t0 ∈ net1.sent, t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
      (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2))
    (hbase : ConsensusSafe c ss Ω1 Ω2 net1 net2) :
    net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε ∧
    (∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
      (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2)) ∧
    ConsensusSafe c ss Ω1 Ω2 (net1.applyAdv apps m) net2 := by
  have hboundM : (net1.applyAdv apps m).chain.now ≤ net2.chain.now := hnow
  have hsupp : ∀ (proof : SupportProof E) (cand : State E),
      (∀ u ∈ proof, p ∈ u.signers → ∃ x ∈ net1.sent, x.state = u.state) →
      (apps c.appDef).supports c proof cand = true →
      (cand.turnNum < ss.state.turnNum ∨ cand = ss.state ∨ cand.outcome = Ω2) ∧
      (cand.isFinal = true → cand.outcome = Ω1 ∨ cand.outcome = Ω2) := by
    intro proof cand hUl hs
    obtain ⟨x, hx, hxs, huc⟩ := hC.sent_cand hUl hs
    have hb := hsent x hx (by rw [hxs]; exact huc)
    rw [hxs] at hb
    exact hb
  have preserve_fin : ∀ {F : Outcome E}, net1.chain.finalizedWith c.address = some F →
      (net1.applyAdv apps m).chain.finalizedWith c.address = some F := by
    intro F hf
    cases m with
    | deliver _ => exact hf
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | chain caller op =>
      simp only [NetworkState.applyAdv]
      cases h : net1.chain.apply apps caller op with
      | none => (simpa? using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
      | some s' => exact Adjudicator.finalizedWith_apply h hf
  have hconclude : ∀ (caller : Participant) (ss' : SignedState E) (s' : Adjudicator E),
      T.feasible net1 (.chain caller (.conclude c ss')) →
      net1.chain.apply apps caller (.conclude c ss') = some s' →
      s'.finalizedWith c.address = some Ω1 ∨ s'.finalizedWith c.address = some Ω2 := by
    intro caller ss' s' hfeas' h
    obtain ⟨⟨-, hproof'⟩, rfl⟩ := Adjudicator.conclude_some h
    have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hC.mem)
    have hmem : ss' ∈ (Op.conclude c ss').proofStates := by (simp? [Op.proofStates] says simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false])
    obtain ⟨x, hxmem, hxeq⟩ :=
      (hbounds.unforgeable net1 caller (.conclude c ss') hfeas' ss' hmem).1 hp'
    have hΩ' := (hsent x hxmem (by rw [hxeq]; exact hproof'.1)).2 (by rw [hxeq]; exact hproof'.2.1)
    rw [hxeq] at hΩ'
    rcases hΩ' with h1 | h2
    · exact Or.inl (by
        (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.statusOf_setStatus, h1] says simp only [h1, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized]))
    · exact Or.inr (by
        (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.statusOf_setStatus, h2] says simp only [h2, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized]))
  have hcheckpoint : ∀ (proof : SupportProof E) (cand : State E) (s' : Adjudicator E),
      net1.chain.checkpoint apps c proof cand = some s' →
      ∃ t', s'.statusOf c = .open t' ∧ s'.finalizedWith c.address = none := by
    intro proof cand s' h
    obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
    refine ⟨cand.turnNum, by rw [Adjudicator.statusOf_setStatus, if_pos rfl], ?_⟩
    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_open])
  have hchallenge : ∀ (caller : Participant) (proof : SupportProof E) (cand : State E)
      (s' : Adjudicator E), T.feasible net1 (.chain caller (.challenge c proof cand)) →
      net1.chain.apply apps caller (.challenge c proof cand) = some s' →
      s'.finalizedWith c.address = some Ω1 ∨ s'.finalizedWith c.address = some Ω2 ∨
      (s'.finalizedWith c.address = none ∧
        ∃ t' ch', s'.statusOf c = .challenged t' ch' ∧
          (ch'.state.outcome = Ω1 ∨ ch'.state.outcome = Ω2 ∨
           (t' < ss.state.turnNum ∧ net2.chain.now < ch'.deadline))) := by
    intro caller proof cand s' hfeas' h
    obtain ⟨⟨-, hs, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
    have hUl : ∀ u ∈ proof, p ∈ u.signers → ∃ x ∈ net1.sent, x.state = u.state :=
      fun u hmem hsig =>
        (hbounds.unforgeable net1 caller (.challenge c proof cand) hfeas' u hmem).1 hsig
    obtain ⟨hcl1, -⟩ := hsupp proof cand hUl hs
    have hself0 : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
    have hpos : 0 < c.challengeDuration := lt_of_lt_of_le T.ε_pos (le_trans hself0 hC.timed)
    refine Or.inr (Or.inr ⟨?_, cand.turnNum,
      ⟨cand, net1.chain.now + c.challengeDuration⟩, ?_, ?_⟩)
    · (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
        Adjudicator.statusOf_setStatus, ChannelStatus.finalizedWith_challenged,
        not_le.mpr (Nat.lt_add_of_pos_right hpos)] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_challenged, not_le.mpr (Nat.lt_add_of_pos_right hpos)])
    · (simp? [Adjudicator.statusOf_setStatus] says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])
    · by_cases hsafe2 : cand.outcome = Ω1 ∨ cand.outcome = Ω2
      · rcases hsafe2 with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
      · refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · rcases hcl1 with hlt | heq | hΩ2'
          · exact hlt
          · exact (hsafe2 (Or.inl (by rw [heq]; exact hΩ1))).elim
          · exact (hsafe2 (Or.inr hΩ2')).elim
        · have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
          have hge : T.ε ≤ c.challengeDuration := le_trans hself hC.timed
          exact lt_of_lt_of_le hεbound (Nat.add_le_add_left hge net1.chain.now)
  have step : ConsensusSafe c ss Ω1 Ω2 net1 net2 →
      ConsensusSafe c ss Ω1 Ω2 (net1.applyAdv apps m) net2 := by
    intro hbase1
    rcases hbase1 with hf1 | hf2 | ⟨hfn, hstruct⟩
    · exact Or.inl (preserve_fin hf1)
    · exact Or.inr (Or.inl (preserve_fin hf2))
    · rcases hstruct with ⟨t, ho⟩ | ⟨t, ch, hst, hdisj⟩
      · cases m with
        | deliver _ => exact Or.inr (Or.inr ⟨hfn, Or.inl ⟨t, ho⟩⟩)
        | tick dt => exact absurd rfl (hnotick dt)
        | land op => exact absurd rfl (hnoland op)
        | chain caller op =>
          simp only [NetworkState.applyAdv]
          cases h : net1.chain.apply apps caller op with
          | none => exact Or.inr (Or.inr ⟨hfn, Or.inl ⟨t, ho⟩⟩)
          | some s' =>
            have hfo1 : net1.chain.finalOutcome c.address = none := by
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
                ChannelStatus.finalOutcome_open]
            cases op with
            | deposit a e x =>
              obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
              have hstatusc' : s'.statusOf c = .open t := by
                rw [Adjudicator.statusOf_of_status hs]; exact ho
              exact Or.inr (Or.inr ⟨by
                (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
                Or.inl ⟨t, hstatusc'⟩⟩)
            | tick dt =>
              have hs' : net1.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
              subst hs'
              have hstatusc' : (net1.chain.tick dt).statusOf c = .open t := by
                rw [Adjudicator.tick_statusOf]; exact ho
              exact Or.inr (Or.inr ⟨by
                (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', Adjudicator.tick_now, ChannelStatus.finalizedWith_open]),
                Or.inl ⟨t, hstatusc'⟩⟩)
            | transfer a b =>
              by_cases hac : a = c
              · subst hac
                obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
              · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                have hstatusc' : s'.statusOf c = .open t := by
                  rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                    if_neg (Ne.symm hac)]
                  exact ho
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
                  Or.inl ⟨t, hstatusc'⟩⟩)
            | reclaim l v =>
              by_cases hlc : l = c
              · subst hlc
                obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                have hstatusc' : s'.statusOf c = .open t := by
                  rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                  exact ho
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
                  Or.inl ⟨t, hstatusc'⟩⟩)
            | challenge c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                rcases hchallenge caller proof cand s' hfeas h with
                  hr1 | hr2 | ⟨hn, t', ch', hst', hd'⟩
                · exact Or.inl hr1
                · exact Or.inr (Or.inl hr2)
                · exact Or.inr (Or.inr ⟨hn, Or.inr ⟨t', ch', hst', hd'⟩⟩)
              · obtain ⟨-, hseq⟩ := Adjudicator.challenge_some h
                have hstatusc' : s'.statusOf c = .open t := by
                  rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact ho
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
                  Or.inl ⟨t, hstatusc'⟩⟩)
            | checkpoint c' proof cand =>
              by_cases hcc : c' = c
              · subst hcc
                obtain ⟨t', ht', hfz'⟩ := hcheckpoint proof cand s' h
                exact Or.inr (Or.inr ⟨hfz', Or.inl ⟨t', ht'⟩⟩)
              · obtain ⟨-, hseq⟩ := Adjudicator.checkpoint_some h
                have hstatusc' : s'.statusOf c = .open t := by
                  rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact ho
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
                  Or.inl ⟨t, hstatusc'⟩⟩)
            | conclude c' ss' =>
              by_cases hcc : c' = c
              · subst hcc
                rcases hconclude caller ss' s' hfeas h with hr1 | hr2
                · exact Or.inl hr1
                · exact Or.inr (Or.inl hr2)
              · obtain ⟨-, hseq⟩ := Adjudicator.conclude_some h
                have hstatusc' : s'.statusOf c = .open t := by
                  rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact ho
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
                  Or.inl ⟨t, hstatusc'⟩⟩)
      · have hnotexp : ¬ ch.deadline ≤ net1.chain.now := by
          intro hle
          have hcontra : net1.chain.finalizedWith c.address = some ch.state.outcome := by
            (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
              ChannelStatus.finalizedWith_challenged, hle] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst, ChannelStatus.finalizedWith_challenged, hle, ↓reduceIte])
          rw [hfn] at hcontra; exact absurd hcontra (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
        have hfo1 : net1.chain.finalOutcome c.address = none := by
          (simp? [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
            ChannelStatus.finalOutcome_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst, ChannelStatus.finalOutcome_challenged, hnotexp, ↓reduceIte])
        rcases hdisj with h1 | h2 | ⟨hltC, hddC⟩
        · cases m with
          | deliver _ => exact Or.inr (Or.inr ⟨hfn, Or.inr ⟨t, ch, hst, Or.inl h1⟩⟩)
          | tick dt => exact absurd rfl (hnotick dt)
          | land op => exact absurd rfl (hnoland op)
          | chain caller op =>
            simp only [NetworkState.applyAdv]
            cases h : net1.chain.apply apps caller op with
            | none => exact Or.inr (Or.inr ⟨hfn, Or.inr ⟨t, ch, hst, Or.inl h1⟩⟩)
            | some s' =>
              cases op with
              | deposit a e x =>
                obtain ⟨-, -, -, -, hs, hn⟩ := Adjudicator.deposit_some h
                have hstatusc' : s'.statusOf c = .challenged t ch := by
                  rw [Adjudicator.statusOf_of_status hs]; exact hst
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                    ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                  Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
              | tick dt =>
                have hs' : net1.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
                subst hs'
                by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
                · exact Or.inl (by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                      Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                      hexp2, h1] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte, h1]))
                · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
                  · (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                      Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                      hexp2] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte])
                  · rw [Adjudicator.tick_statusOf]; exact hst
              | transfer a b =>
                by_cases hac : a = c
                · subst hac
                  obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, hs, hn, _, _⟩ := Adjudicator.transfer_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                      if_neg (Ne.symm hac)]
                    exact hst
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
              | reclaim l v =>
                by_cases hlc : l = c
                · subst hlc
                  obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                    exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hs']; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
              | challenge c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  rcases hchallenge caller proof cand s' hfeas h with
                    hr1 | hr2 | ⟨hn, t', ch', hst', hd'⟩
                  · exact Or.inl hr1
                  · exact Or.inr (Or.inl hr2)
                  · exact Or.inr (Or.inr ⟨hn, Or.inr ⟨t', ch', hst', hd'⟩⟩)
                · obtain ⟨-, hseq⟩ := Adjudicator.challenge_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hseq]; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
              | checkpoint c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  obtain ⟨t', ht', hfz'⟩ := hcheckpoint proof cand s' h
                  exact Or.inr (Or.inr ⟨hfz', Or.inl ⟨t', ht'⟩⟩)
                · obtain ⟨-, hseq⟩ := Adjudicator.checkpoint_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hseq]; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
              | conclude c' ss' =>
                by_cases hcc : c' = c
                · subst hcc
                  rcases hconclude caller ss' s' hfeas h with hr1 | hr2
                  · exact Or.inl hr1
                  · exact Or.inr (Or.inl hr2)
                · obtain ⟨-, hseq⟩ := Adjudicator.conclude_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hseq]; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inl h1⟩⟩)
        · cases m with
          | deliver _ => exact Or.inr (Or.inr ⟨hfn, Or.inr ⟨t, ch, hst, Or.inr (Or.inl h2)⟩⟩)
          | tick dt => exact absurd rfl (hnotick dt)
          | land op => exact absurd rfl (hnoland op)
          | chain caller op =>
            simp only [NetworkState.applyAdv]
            cases h : net1.chain.apply apps caller op with
            | none => exact Or.inr (Or.inr ⟨hfn, Or.inr ⟨t, ch, hst, Or.inr (Or.inl h2)⟩⟩)
            | some s' =>
              cases op with
              | deposit a e x =>
                obtain ⟨-, -, -, -, hs, hn⟩ := Adjudicator.deposit_some h
                have hstatusc' : s'.statusOf c = .challenged t ch := by
                  rw [Adjudicator.statusOf_of_status hs]; exact hst
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                    ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                  Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
              | tick dt =>
                have hs' : net1.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
                subst hs'
                by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
                · exact Or.inr (Or.inl (by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                      Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                      hexp2, h2] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte, h2])))
                · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
                  · (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                      Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                      hexp2] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte])
                  · rw [Adjudicator.tick_statusOf]; exact hst
              | transfer a b =>
                by_cases hac : a = c
                · subst hac
                  obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, hs, hn, _, _⟩ := Adjudicator.transfer_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                      if_neg (Ne.symm hac)]
                    exact hst
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
              | reclaim l v =>
                by_cases hlc : l = c
                · subst hlc
                  obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                    exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hs']; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
              | challenge c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  rcases hchallenge caller proof cand s' hfeas h with
                    hr1 | hr2 | ⟨hn, t', ch', hst', hd'⟩
                  · exact Or.inl hr1
                  · exact Or.inr (Or.inl hr2)
                  · exact Or.inr (Or.inr ⟨hn, Or.inr ⟨t', ch', hst', hd'⟩⟩)
                · obtain ⟨-, hseq⟩ := Adjudicator.challenge_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hseq]; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
              | checkpoint c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  obtain ⟨t', ht', hfz'⟩ := hcheckpoint proof cand s' h
                  exact Or.inr (Or.inr ⟨hfz', Or.inl ⟨t', ht'⟩⟩)
                · obtain ⟨-, hseq⟩ := Adjudicator.checkpoint_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hseq]; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
              | conclude c' ss' =>
                by_cases hcc : c' = c
                · subst hcc
                  rcases hconclude caller ss' s' hfeas h with hr1 | hr2
                  · exact Or.inl hr1
                  · exact Or.inr (Or.inl hr2)
                · obtain ⟨-, hseq⟩ := Adjudicator.conclude_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  have hn : s'.now = net1.chain.now := by
                    rw [hseq]; exact Adjudicator.setStatus_now _ _ _
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn,
                      ChannelStatus.finalizedWith_challenged, hnotexp] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', hn, ChannelStatus.finalizedWith_challenged, hnotexp, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inl h2)⟩⟩)
        · cases m with
          | deliver _ => exact Or.inr (Or.inr ⟨hfn, Or.inr ⟨t, ch, hst, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
          | tick dt => exact absurd rfl (hnotick dt)
          | land op => exact absurd rfl (hnoland op)
          | chain caller op =>
            simp only [NetworkState.applyAdv]
            cases h : net1.chain.apply apps caller op with
            | none => exact Or.inr (Or.inr ⟨hfn, Or.inr ⟨t, ch, hst, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
            | some s' =>
              have hdl : s'.now < ch.deadline := by
                have := hboundM; (simpa? [NetworkState.applyAdv, h] using lt_of_le_of_lt this hddC says simpa only [gt_iff_lt, NetworkState.applyAdv, h] using lt_of_le_of_lt this hddC)
              cases op with
              | deposit a e x =>
                obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
                have hstatusc' : s'.statusOf c = .challenged t ch := by
                  rw [Adjudicator.statusOf_of_status hs]; exact hst
                exact Or.inr (Or.inr ⟨by
                  (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                    ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte]),
                  Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
              | tick dt =>
                have hs' : net1.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
                subst hs'
                have hdl' : net1.chain.now + dt < ch.deadline := by
                  (simpa? [Adjudicator.tick_now] using hdl says simpa only [Adjudicator.tick_now] using hdl)
                refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
                · (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                    Adjudicator.tick_statusOf, hst, ChannelStatus.finalizedWith_challenged,
                    not_le.mpr hdl'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, not_le.mpr hdl', ↓reduceIte])
                · rw [Adjudicator.tick_statusOf]; exact hst
              | transfer a b =>
                by_cases hac : a = c
                · subst hac
                  obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                      if_neg (Ne.symm hac)]
                    exact hst
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                      ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
              | reclaim l v =>
                by_cases hlc : l = c
                · subst hlc
                  obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
                  rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
                · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hs', Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
                    exact hst
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                      ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
              | challenge c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  rcases hchallenge caller proof cand s' hfeas h with
                    hr1 | hr2 | ⟨hn, t', ch', hst', hd'⟩
                  · exact Or.inl hr1
                  · exact Or.inr (Or.inl hr2)
                  · exact Or.inr (Or.inr ⟨hn, Or.inr ⟨t', ch', hst', hd'⟩⟩)
                · obtain ⟨-, hseq⟩ := Adjudicator.challenge_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                      ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
              | checkpoint c' proof cand =>
                by_cases hcc : c' = c
                · subst hcc
                  obtain ⟨t', ht', hfz'⟩ := hcheckpoint proof cand s' h
                  exact Or.inr (Or.inr ⟨hfz', Or.inl ⟨t', ht'⟩⟩)
                · obtain ⟨-, hseq⟩ := Adjudicator.checkpoint_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                      ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
              | conclude c' ss' =>
                by_cases hcc : c' = c
                · subst hcc
                  rcases hconclude caller ss' s' hfeas h with hr1 | hr2
                  · exact Or.inl hr1
                  · exact Or.inr (Or.inl hr2)
                · obtain ⟨-, hseq⟩ := Adjudicator.conclude_some h
                  have hstatusc' : s'.statusOf c = .challenged t ch := by
                    rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hst
                  exact Or.inr (Or.inr ⟨by
                    (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc',
                      ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte]),
                    Or.inr ⟨t, ch, hstatusc', Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
  have hbase' := step hbase
  have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
    lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
  have hsent' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
      (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2) := by
    rw [NetworkState.applyAdv_sent]; exact hsent
  exact ⟨hεbound', hsent', hbase'⟩

/-- `ConsensusSafe` over a round's play with nothing of `p`'s own still
    pending: every operation that reaches channel `c` here is an adversary
    one, not `p`'s own checkpoint, so the invariant carries exactly as
    `hsupp`/`hconclude`/`hcheckpoint`/`hchallenge` bound it, with no land
    case to handle (`pending = []` rules it out structurally). Used by
    `consensus_round_safe` for the adversary play before `p`'s own
    checkpoint call lands, and after. -/
theorem consensus_round_safe_nil {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω1 Ω2 : Outcome E}
    (hC : TimedConsensusMember apps p T.ε c) (hΩ1 : ss.state.outcome = Ω1) :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.TimedRun apps T t [] net net' →
      (∀ t0 ∈ net.sent, t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
        (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2)) →
      ConsensusSafe c ss Ω1 Ω2 net net' → ConsensusSafe c ss Ω1 Ω2 net' net' := by
  intro net net' t ⟨hseq, hεb⟩
  revert hεb
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; (simp? at hsplit says simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hsent hbase
    have hboundM : (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).chain.now ≤
        net2.chain.now := hrest.now_le
    have step : ConsensusSafe c ss Ω1 Ω2 net1 net2 →
        ConsensusSafe c ss Ω1 Ω2 (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)) net2 := by
      intro hbase1
      rcases hbase1 with hf1 | hf2 | ⟨hfn, hstruct⟩
      · exact Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf1)
              (Nat.le_add_right _ dt))
      · exact Or.inr (Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf2)
              (Nat.le_add_right _ dt)))
      · rcases hstruct with ⟨t, ho⟩ | ⟨t, ch, hst, hdisj⟩
        · have hstatusc' : (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).chain.statusOf c =
              .open t := by (simpa? [NetworkState.applyAdv] using ho says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using ho)
          exact Or.inr (Or.inr ⟨by
            (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
            Or.inl ⟨t, hstatusc'⟩⟩)
        · have hnotexp : ¬ ch.deadline ≤ net1.chain.now := by
            intro hle
            have hcontra : net1.chain.finalizedWith c.address = some ch.state.outcome := by
              (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, hle] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst, ChannelStatus.finalizedWith_challenged, hle, ↓reduceIte])
            rw [hfn] at hcontra; exact absurd hcontra (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
          rcases hdisj with h1 | h2 | ⟨hltC, hddC⟩
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inl (by
                (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h1] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte, h1]))
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
              · (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte])
              · (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst)
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inr (Or.inl (by
                (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h2] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte, h2])))
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
              · (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte])
              · (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst)
          · have hdl : net1.chain.now + dt < ch.deadline := by
              have := hboundM
              (simpa? [NetworkState.applyAdv, Adjudicator.tick_now] using lt_of_le_of_lt this hddC says simpa only [gt_iff_lt, NetworkState.applyAdv, Adjudicator.tick_now] using lt_of_le_of_lt this hddC)
            refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
            · (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte])
            · (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst)
    have hbase' := step hbase
    have hεbound' : net2.chain.now <
        (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).sent,
        t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
        (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2) := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih hpnil hεbound' hsent' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hsent hbase
    obtain ⟨hεbound', hsent', hbase'⟩ :=
      consensus_round_safe_core hbounds hC hΩ1 hfeas hnotick hnoland hεbound hrest.now_le hsent hbase
    exact ih hpnil hεbound' hsent' hbase'

/-- Over a round that lands `p`'s one pending call, `ConsensusSafe` is
    preserved to the round's end (`nowNet = net'`, self-referential): any
    candidate on channel `c` that carries `p`'s genuine signature is, via
    `hbounds.unforgeable`, a state `p` itself sent (`hsent` bounds it:
    below `ss.state.turnNum`, exactly `ss.state`, or at outcome `Ω2` — and,
    if final, at outcome `Ω1` or `Ω2`). A `conclude` on `c` always needs a
    final candidate, so it always lands on `Ω1` or `Ω2`. A `checkpoint` on
    `c`, by anyone, always clears to `.open` if it succeeds at all
    (`Adjudicator.checkpoint`'s own success semantics), safe unconditionally
    — including `p`'s own checkpoint call landing (`Threat.RoundSeq.land`):
    it either fails (state unchanged, whatever `ConsensusSafe` sub-case held
    before still holds) or succeeds (clears to `.open ss.state.turnNum`,
    the open sub-case, which carries no turn bound of its own). A fresh
    `challenge`/re-`challenge` on `c` lands at a candidate that is itself
    safe, or strictly below `ss.state.turnNum` with a deadline
    `c.challengeDuration ≥ 2 * T.ε` past the round's own clock — enough to
    survive the rest of this round (`hεbound`). Used by
    `consensus_enabled_outcomes`. -/
theorem consensus_round_safe {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} {ss : SignedState E} {Ω1 Ω2 : Outcome E}
    (hC : TimedConsensusMember apps p T.ε c) (hΩ1 : ss.state.outcome = Ω1)
    {net net' : NetworkState E p} (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.TimedRun apps T t [Op.checkpoint c [ss] ss.state] net net') :
    (∀ t0 ∈ net.sent, t0.state.channel = c →
      (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
      (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2)) →
    ConsensusSafe c ss Ω1 Ω2 net net' → ConsensusSafe c ss Ω1 Ω2 net' net' := by
  obtain ⟨hseq, hεb⟩ := hseq; revert hεb
  clear ht
  generalize heq : ([Op.checkpoint c [ss] ss.state] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => cases heq
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro hεbound hsent hbase
    cases heq
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨hopeq, -⟩ := hsplit
        subst hopeq
        have hbase_land :
            ConsensusSafe c ss Ω1 Ω2
              (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))) net2 := by
          cases hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) with
          | none => (simpa? [NetworkState.applyAdv, hop] using hbase says simpa only [NetworkState.applyAdv, hop] using hbase)
          | some s' =>
            obtain ⟨⟨-, -, -, -⟩, hseq'⟩ := Adjudicator.checkpoint_some hop
            refine Or.inr (Or.inr ⟨?_, Or.inl ⟨ss.state.turnNum, ?_⟩⟩)
            · (simp? [NetworkState.applyAdv, hop, hseq', FixedPart.address_eq,
                Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus] says simp only [NetworkState.applyAdv, hop, hseq', FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_open])
            · (simp? [NetworkState.applyAdv, hop, hseq', Adjudicator.statusOf_setStatus] says simp only [NetworkState.applyAdv, hop, hseq', Adjudicator.statusOf_setStatus, ↓reduceIte])
        have hεbound' : net2.chain.now <
            (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).chain.now + T.ε :=
          lt_of_lt_of_le hεbound
            (Nat.add_le_add_right
              (NetworkState.applyAdv_now_le apps net1 (.land (Op.checkpoint c [ss] ss.state))) T.ε)
        have hsent_land : ∀ t0 ∈
            (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).sent,
            t0.state.channel = c →
            (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
            (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2) := by
          rw [NetworkState.applyAdv_sent]; exact hsent
        exact consensus_round_safe_nil hbounds hC hΩ1 ⟨hrest, hεbound'⟩ hsent_land hbase_land
      · (simp? at hsplit says simp only [List.nil_append, List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at hsplit)
    · (simp? at hsplit says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hsent hbase
    have hboundM : (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).chain.now ≤
        net2.chain.now := hrest.now_le
    have step : ConsensusSafe c ss Ω1 Ω2 net1 net2 →
        ConsensusSafe c ss Ω1 Ω2 (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)) net2 := by
      intro hbase1
      rcases hbase1 with hf1 | hf2 | ⟨hfn, hstruct⟩
      · exact Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf1)
              (Nat.le_add_right _ dt))
      · exact Or.inr (Or.inl (by
          simpa [NetworkState.applyAdv, FixedPart.address_eq] using
            ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf2)
              (Nat.le_add_right _ dt)))
      · rcases hstruct with ⟨t, ho⟩ | ⟨t, ch, hst, hdisj⟩
        · have hstatusc' : (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).chain.statusOf c =
              .open t := by (simpa? [NetworkState.applyAdv] using ho says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using ho)
          exact Or.inr (Or.inr ⟨by
            (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc'] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatusc', ChannelStatus.finalizedWith_open]),
            Or.inl ⟨t, hstatusc'⟩⟩)
        · have hnotexp : ¬ ch.deadline ≤ net1.chain.now := by
            intro hle
            have hcontra : net1.chain.finalizedWith c.address = some ch.state.outcome := by
              (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
                ChannelStatus.finalizedWith_challenged, hle] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst, ChannelStatus.finalizedWith_challenged, hle, ↓reduceIte])
            rw [hfn] at hcontra; exact absurd hcontra (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
          rcases hdisj with h1 | h2 | ⟨hltC, hddC⟩
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inl (by
                (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h1] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte, h1]))
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inl h1⟩⟩)
              · (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte])
              · (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst)
          · by_cases hexp2 : ch.deadline ≤ net1.chain.now + dt
            · exact Or.inr (Or.inl (by
                (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2, h2] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte, h2])))
            · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inl h2)⟩⟩)
              · (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                  Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                  ChannelStatus.finalizedWith_challenged, hexp2] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hexp2, ↓reduceIte])
              · (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst)
          · have hdl : net1.chain.now + dt < ch.deadline := by
              have := hboundM
              (simpa? [NetworkState.applyAdv, Adjudicator.tick_now] using lt_of_le_of_lt this hddC says simpa only [gt_iff_lt, NetworkState.applyAdv, Adjudicator.tick_now] using lt_of_le_of_lt this hddC)
            refine Or.inr (Or.inr ⟨?_, Or.inr ⟨t, ch, ?_, Or.inr (Or.inr ⟨hltC, hddC⟩)⟩⟩)
            · (simp? [NetworkState.applyAdv, FixedPart.address_eq,
                Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst,
                ChannelStatus.finalizedWith_challenged, not_le.mpr hdl] says simp only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hst, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, not_le.mpr hdl, ↓reduceIte])
            · (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hst)
    have hbase' := step hbase
    have hεbound' : net2.chain.now <
        (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt : AdvMove E)).sent,
        t0.state.channel = c →
        (t0.state.turnNum < ss.state.turnNum ∨ t0.state = ss.state ∨ t0.state.outcome = Ω2) ∧
        (t0.state.isFinal = true → t0.state.outcome = Ω1 ∨ t0.state.outcome = Ω2) := by
      rw [NetworkState.applyAdv_sent]; exact hsent
    exact ih heq hεbound' hsent' hbase'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hsent hbase
    obtain ⟨hεbound', hsent', hbase'⟩ :=
      consensus_round_safe_core hbounds hC hΩ1 hfeas hnotick hnoland hεbound hrest.now_le hsent hbase
    exact ih heq hεbound' hsent' hbase'
/-- `ConsensusSafe` without the risky "stale but not yet expired" challenged
    sub-case: finalized with `Ω1`/`Ω2`, open, or challenged with an
    already-safe candidate. This is what every state `consensus_enabled_outcomes`
    reaches via its strategy actually satisfies: the one sub-case `ConsensusSafe`
    allows beyond this (a stale challenge below `ss.state.turnNum`, not yet
    past its deadline) is a transient that `p`'s own checkpoint always clears
    within the same round it appears (`consensus_checkpoint_resolves`), so it
    never survives as the invariant entering the next round. Unlike
    `ConsensusSafe` it names no clock: nothing in it depends on one. -/
def ConsensusSafe0 {p : Participant} (c : FixedPart) (Ω1 Ω2 : Outcome E) (n : NetworkState E p) :
    Prop :=
  n.chain.finalizedWith c.address = some Ω1 ∨
  n.chain.finalizedWith c.address = some Ω2 ∨
  (n.chain.finalizedWith c.address = none ∧
    ((∃ t, n.chain.statusOf c = .open t) ∨
     (∃ t ch, n.chain.statusOf c = .challenged t ch ∧
       (ch.state.outcome = Ω1 ∨ ch.state.outcome = Ω2))))

omit [DecidableEq E] in
/-- `ConsensusSafe0` holds at any clock: the only `ConsensusSafe` sub-case
    that reads `nowNet`'s clock (a stale challenge's deadline) is exactly the
    sub-case `ConsensusSafe0` excludes. -/
theorem ConsensusSafe0.toConsensusSafe {p : Participant} {c : FixedPart} {ss : SignedState E}
    {Ω1 Ω2 : Outcome E} {n : NetworkState E p} (h : ConsensusSafe0 c Ω1 Ω2 n)
    (n' : NetworkState E p) : ConsensusSafe c ss Ω1 Ω2 n n' := by
  rcases h with h1 | h2 | ⟨hfz, hopen | ⟨t, ch, hst, h1 | h2⟩⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨hfz, Or.inl hopen⟩)
  · exact Or.inr (Or.inr ⟨hfz, Or.inr ⟨t, ch, hst, Or.inl h1⟩⟩)
  · exact Or.inr (Or.inr ⟨hfz, Or.inr ⟨t, ch, hst, Or.inr (Or.inl h2)⟩⟩)

/-- Over a round's play with nothing of `p`'s own still pending, the turn
    record never drops: `turnNumRecord_monotone` bounds every single
    on-chain step, and a `tick` never touches `status` at all. The one
    exception `turnNumRecord_monotone` carries (a `conclude` that finalizes
    `c`) is absorbed into the `finalizedWith` disjunct here. Used by
    `consensus_checkpoint_resolves`. -/
theorem consensus_checkpoint_resolves_nil {apps : Apps E} {p : Participant} {T : Threat E p}
    {c : FixedPart} {ss : SignedState E} :
    ∀ {net net' : NetworkState E p} {t : Time}, Threat.RoundSeq apps T t [] net net' →
      (ss.state.turnNum ≤ (net.chain.statusOf c).turnNumRecord ∨
        ∃ Ω, net.chain.finalizedWith c.address = some Ω) →
      ss.state.turnNum ≤ (net'.chain.statusOf c).turnNumRecord ∨
        ∃ Ω, net'.chain.finalizedWith c.address = some Ω := by
  intro net net' t hseq
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; (simp? at hsplit says simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hbase
    apply ih hpnil
    rcases hbase with hle | ⟨Ω, hΩ⟩
    · exact Or.inl (by (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hle says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hle))
    · exact Or.inr ⟨Ω, by
        simpa [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          Adjudicator.tick_statusOf, Adjudicator.tick_now] using
          ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hΩ)
            (Nat.le_add_right net1.chain.now dt)⟩
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hbase
    apply ih hpnil
    cases m with
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | deliver ss' =>
      rcases hbase with hle | ⟨Ω, hΩ⟩
      · exact Or.inl (by (simpa? [NetworkState.applyAdv] using hle says simpa only [NetworkState.applyAdv] using hle))
      · exact Or.inr ⟨Ω, by (simpa? [NetworkState.applyAdv] using hΩ says simpa only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hΩ)⟩
    | chain caller op =>
      simp only [NetworkState.applyAdv]
      cases h : net1.chain.apply apps caller op with
      | none =>
        rcases hbase with hle | ⟨Ω, hΩ⟩
        · exact Or.inl (by (simpa? [h] using hle says simpa only using hle))
        · exact Or.inr ⟨Ω, by (simpa? [h] using hΩ says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hΩ)⟩
      | some s' =>
        rcases hbase with hle | ⟨Ω, hΩ⟩
        · rcases turnNumRecord_monotone apps net1.chain s' c ⟨caller, op, net1.chain, s', h⟩
            with hmono | hconc
          · exact Or.inl (le_trans hle hmono)
          · obtain ⟨caller', ss', -, hfin⟩ := hconc
            have hsome : (s'.finalizedWith c.address).isSome := by
              rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                ChannelStatus.finalizedWith_isSome_iff, ← ChannelStatus.mode_eq_finalized_iff,
                ← Adjudicator.mode_eq]
              exact hfin
            obtain ⟨Ω', hΩ'⟩ := Option.isSome_iff_exists.mp hsome
            exact Or.inr ⟨Ω', hΩ'⟩
        · exact Or.inr ⟨Ω, Adjudicator.finalizedWith_apply h hΩ⟩

/-- `p`'s own checkpoint with `ss` always lands with the turn record at
    least `ss.state.turnNum`, or `c` finalized. Within the round, the
    `land` step shows it directly: `checkpoint` either fails because `c`
    is already finalized (`ChannelStatus.mode_eq_finalized_iff`), or fails
    because the turn record was already at or above `ss.state.turnNum`
    (the only other way `checkpoint`'s preconditions can fail, since
    `hall`/`hchan` make `consensusRules.supports` hold unconditionally for
    `[ss] ss.state`), or succeeds and sets the record to exactly
    `ss.state.turnNum`. `consensus_checkpoint_resolves_nil` then carries
    this forward (never backward: `turnNumRecord_monotone`) through the
    rest of the round. Combined with `consensus_round_safe`'s own
    `ConsensusSafe c ss Ω1 Ω2 net' net'`, the risky stale-challenge
    sub-case (`t < ss.state.turnNum`, read at the SAME `net'`) is
    impossible: either `net'` is finalized (contradicting that sub-case's
    own `finalizedWith = none`), or `ss.state.turnNum ≤
    (net'.chain.statusOf c).turnNumRecord`, and that reads the SAME
    `.challenged t ch` status, so `t = (net'.chain.statusOf
    c).turnNumRecord ≥ ss.state.turnNum`, contradicting `t <
    ss.state.turnNum`. Used by `consensus_enabled_outcomes` to fold
    `ConsensusSafe` back to `ConsensusSafe0`, the loop invariant, every
    round. -/
theorem consensus_checkpoint_resolves {apps : Apps E} {p : Participant} {T : Threat E p}
    {c : FixedPart} {ss : SignedState E} (hC : ConsensusMember apps p c)
    (hchan : ss.state.channel = c) (hall : ss.ByAll)
    {net net' : NetworkState E p} (t : Time) (ht : t = net.chain.now)
    (hseq : Threat.RoundSeq apps T t [Op.checkpoint c [ss] ss.state] net net') :
    ss.state.turnNum ≤ (net'.chain.statusOf c).turnNumRecord ∨
      ∃ Ω, net'.chain.finalizedWith c.address = some Ω := by
  clear ht
  generalize heq : ([Op.checkpoint c [ss] ss.state] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => cases heq
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    cases heq
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨hopeq, -⟩ := hsplit
        subst hopeq
        have hbase_land : ss.state.turnNum ≤
            ((net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).chain.statusOf
              c).turnNumRecord ∨
            ∃ Ω, (net1.applyAdv apps (AdvMove.land (Op.checkpoint c [ss] ss.state))).chain.finalizedWith
              c.address = some Ω := by
          by_cases hlt0 : (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum
          · by_cases hmode : net1.chain.mode c = .finalized
            · have hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) = none := by
                rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
                rw [if_neg]
                rintro ⟨hio, -, -, -⟩
                rw [ChannelStatus.IsOpen, ← Adjudicator.mode_eq] at hio
                exact hio hmode
              right
              have hsome : (net1.chain.finalizedWith c.address).isSome := by
                rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                  ChannelStatus.finalizedWith_isSome_iff, ← ChannelStatus.mode_eq_finalized_iff,
                  ← Adjudicator.mode_eq]
                exact hmode
              obtain ⟨Ω, hΩ⟩ := Option.isSome_iff_exists.mp hsome
              exact ⟨Ω, by simp only [NetworkState.applyAdv, hop]; exact hΩ⟩
            · have hcond : (net1.chain.statusOf c).IsOpen net1.chain.now ∧
                  (apps c.appDef).supports c [ss] ss.state = true ∧ ss.state.channel = c ∧
                  (net1.chain.statusOf c).turnNumRecord < ss.state.turnNum :=
                ⟨by rw [ChannelStatus.IsOpen, ← Adjudicator.mode_eq]; exact hmode,
                  by rw [hC.app]; (simp? [consensusRules, hchan, hall] says simp only [consensusRules, decide_true, hchan, Bool.and_self, hall]), hchan, hlt0⟩
              have hop : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) =
                  some (net1.chain.setStatus c (.open ss.state.turnNum)) := by
                rw [Adjudicator.apply_checkpoint]; unfold Adjudicator.checkpoint
                rw [if_pos hcond]
              left
              (simp? [NetworkState.applyAdv, hop, Adjudicator.statusOf_setStatus] says simp only [NetworkState.applyAdv, hop, Adjudicator.statusOf_setStatus, ↓reduceIte, ChannelStatus.turnNumRecord_open, Std.le_refl])
          · cases hcc : net1.chain.apply apps p (Op.checkpoint c [ss] ss.state) with
            | none => left; (simpa? [NetworkState.applyAdv, hcc] using not_lt.mp hlt0 says simpa only [NetworkState.applyAdv, hcc] using not_lt.mp hlt0)
            | some s' =>
              rcases turnNumRecord_monotone apps net1.chain s' c
                ⟨p, Op.checkpoint c [ss] ss.state, net1.chain, s', hcc⟩ with hmono | hconc
              · left
                simp only [NetworkState.applyAdv, hcc]
                exact le_trans (not_lt.mp hlt0) hmono
              · right
                obtain ⟨caller', ss', -, hfin⟩ := hconc
                have hsome : (s'.finalizedWith c.address).isSome := by
                  rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
                    ChannelStatus.finalizedWith_isSome_iff, ← ChannelStatus.mode_eq_finalized_iff,
                    ← Adjudicator.mode_eq]
                  exact hfin
                obtain ⟨Ω, hΩ⟩ := Option.isSome_iff_exists.mp hsome
                exact ⟨Ω, by simp only [NetworkState.applyAdv, hcc]; exact hΩ⟩
        exact consensus_checkpoint_resolves_nil hrest hbase_land
      · (simp? at hsplit says simp only [List.nil_append, List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at hsplit)
    · (simp? at hsplit says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih => exact ih heq
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih => exact ih heq

/-- Nitro-49 (consensus game, Nitro:660-688), SATP-08, docs-0020-01. Nitro:684-688:
    "Throughout the only enabled outcomes for any participant are Ω1 and Ω2.
    In particular, a participant has the finalizable outcome [χ ↦ Ω1]_p
    until they approve the transition, and then enabled outcomes
    [χ ↦ Ω1, Ω2]_(p) until they receive the final state." Under the
    consensus app: a participant who holds an all-signed state with `Ω1`,
    signed no other state at that turn or above except with `Ω2`, and signed
    final states only with `Ω1` or `Ω2`, has only `Ω1` and `Ω2` enabled.

    Proved by exhibiting `p`'s strategy to prevent any other outcome `Ω` from
    finalizing: checkpoint with `ss` whenever `p` still holds it (always, by
    `NetworkState.Holds.mono`: `p`'s own moves never touch `sent`, and
    `received` only grows), else wait. `consensus_round_safe` keeps
    `ConsensusSafe` across a round of adversary play; `consensus_checkpoint_resolves`
    folds `p`'s subsequent checkpoint back to `ConsensusSafe0`, the loop
    invariant this maintains at every state `Run` reaches. Since `Ω ∉ {Ω1,
    Ω2}`, `ConsensusSafe` after any round rules out `Ω` finalizing. -/
theorem consensus_enabled_outcomes (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (c : TimedChannel T.ε) (ss : SignedState E)
    (Ω1 Ω2 : Outcome E) (hc : apps (c : FixedPart).appDef = consensusRules)
    (hp : p ∈ (c : FixedPart).participants)
    (hh : net.state.Holds ss) (hall : ss.ByAll) (hchan : ss.state.channel = (c : FixedPart))
    (hΩ1 : ss.state.outcome = Ω1)
    (hsent : ∀ t ∈ net.state.sent, t.state.channel = (c : FixedPart) →
      (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
      (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2))
    (hst : (∃ t, net.state.chain.statusOf (c : FixedPart) = .open t ∧ t ≤ ss.state.turnNum) ∨
      (∃ t ch, net.state.chain.statusOf (c : FixedPart) = .challenged t ch ∧
        (t < ss.state.turnNum ∨ ch.state = ss.state) ∧ net.state.chain.now + T.ε ≤ ch.deadline))
    (Ω : Outcome E) (hen : Enabled apps T (c : FixedPart) Ω net.state) : Ω = Ω1 ∨ Ω = Ω2 := by
  obtain_reach ⟨net, hr⟩ := net
  obtain ⟨c, hdur⟩ := c
  by_contra hΩne
  push Not at hΩne
  obtain ⟨hΩne1, hΩne2⟩ := hΩne
  have hen' : ¬ Prevents apps T (fun net' => net'.Finalized c Ω) net := hen
  apply hen'
  classical
  set σ : Strategy E p :=
    fun n => if n.Holds ss then HonestMove.chain (.checkpoint c [ss] ss.state) else .wait 0
    with hσdef
  have hfeas : ∀ n, (σ n).Feasible apps n := by
    intro n
    by_cases hn : n.Holds ss
    · rw [hσdef]; simp only [if_pos hn, HonestMove.Feasible_chain, Op.HonestFeasible,
        Op.proofStates, List.mem_singleton]
      intro ss' hss'; rw [hss']; exact hn
    · rw [hσdef]; (simp? [if_neg hn, HonestMove.Feasible] says simp only [HonestMove.Feasible, if_neg hn])
  have hbase_net : ∀ {n2' : NetworkState E p}, n2'.chain.now < net.chain.now + T.ε →
      ConsensusSafe c ss Ω1 Ω2 net n2' := by
    intro n2' hlt
    rcases hst with ⟨t, ho, -⟩ | ⟨t, ch, hst', hdisj, hdd⟩
    · have hfz : net.chain.finalizedWith c.address = none := by
        (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, ho] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, ho, ChannelStatus.finalizedWith_open])
      exact Or.inr (Or.inr ⟨hfz, Or.inl ⟨t, ho⟩⟩)
    · have hεpos := T.ε_pos
      have hndl : net.chain.now < ch.deadline :=
        lt_of_lt_of_le (Nat.lt_add_of_pos_right hεpos) hdd
      have hfz : net.chain.finalizedWith c.address = none := by
        (simp? [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst',
          ChannelStatus.finalizedWith_challenged, not_le.mpr hndl] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst', ChannelStatus.finalizedWith_challenged, not_le.mpr hndl, ↓reduceIte])
      refine Or.inr (Or.inr ⟨hfz, Or.inr ⟨t, ch, hst', ?_⟩⟩)
      rcases hdisj with hlt' | heq
      · exact Or.inr (Or.inr ⟨hlt', lt_of_lt_of_le hlt hdd⟩)
      · exact Or.inl (by rw [heq]; exact hΩ1)
  have hinv : ∀ {n1 : NetworkState E p}, Run apps T σ net n1 →
      n1.sent = net.sent ∧ n1.Holds ss ∧ (n1 = net ∨ ConsensusSafe0 c Ω1 Ω2 n1) := by
    intro n1 hr
    induction hr with
    | refl => exact ⟨rfl, hh, Or.inl rfl⟩
    | @round n1' n2 hrun hround ih =>
      obtain ⟨hsentEq, hholds, hsafe0⟩ := ih
      have hσeq : σ n1' = .chain (.checkpoint c [ss] ss.state) := by
        rw [hσdef]; simp only [if_pos hholds]
      rw [hσeq] at hround
      obtain ⟨hseq, hεbound⟩ := hround
      simp only [HonestMove.calls_chain] at hseq
      have hsafeStart : ConsensusSafe c ss Ω1 Ω2 n1' n2 := by
        rcases hsafe0 with rfl | hsafe0'
        · exact hbase_net hεbound
        · exact hsafe0'.toConsensusSafe n2
      have hsentNow : ∀ t ∈ n1'.sent, t.state.channel = c →
          (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
          (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2) := by
        rw [hsentEq]; exact hsent
      have hsafe2 : ConsensusSafe c ss Ω1 Ω2 n2 n2 :=
        consensus_round_safe A.toBounds ⟨⟨hc, hp⟩, hdur⟩ hΩ1 n1'.chain.now rfl ⟨hseq, hεbound⟩ hsentNow
          hsafeStart
      have hturn : ss.state.turnNum ≤ (n2.chain.statusOf c).turnNumRecord ∨
          ∃ Ω, n2.chain.finalizedWith c.address = some Ω :=
        consensus_checkpoint_resolves ⟨hc, hp⟩ hchan hall n1'.chain.now rfl hseq
      have hsafe0' : ConsensusSafe0 c Ω1 Ω2 n2 := by
        rcases hsafe2 with h1 | h2 | ⟨hfz, hopen | ⟨t, ch, hst, hsafe1 | hsafeΩ2 | ⟨hlt, -⟩⟩⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hfz, Or.inl hopen⟩)
        · exact Or.inr (Or.inr ⟨hfz, Or.inr ⟨t, ch, hst, Or.inl hsafe1⟩⟩)
        · exact Or.inr (Or.inr ⟨hfz, Or.inr ⟨t, ch, hst, Or.inr hsafeΩ2⟩⟩)
        · exfalso
          rcases hturn with hge | ⟨Ω', hΩ'⟩
          · rw [hst, ChannelStatus.turnNumRecord_challenged] at hge
            exact absurd hge (not_le.mpr hlt)
          · rw [hΩ'] at hfz; exact absurd hfz (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
      have hsent2 : n2.sent = n1'.sent := hseq.sent_eq
      have hholds' : n2.Holds ss :=
        NetworkState.Holds.mono hsent2.symm hseq.received_subset hholds
      rw [hσeq, NetworkState.applyHonest_chain]
      exact ⟨by rw [hsent2]; exact hsentEq, hholds', Or.inr hsafe0'⟩
  refine ⟨σ, hfeas, ?_⟩
  intro n1 n2 hrun hround hfin
  obtain ⟨hsentEq, hholds1, hsafe0⟩ := hinv hrun
  have hσeq1 : σ n1 = .chain (.checkpoint c [ss] ss.state) := by
    rw [hσdef]; simp only [if_pos hholds1]
  rw [hσeq1] at hround
  obtain ⟨hseq, hεbound⟩ := hround
  simp only [HonestMove.calls_chain] at hseq
  have hsafeStart : ConsensusSafe c ss Ω1 Ω2 n1 n2 := by
    rcases hsafe0 with rfl | hsafe0'
    · exact hbase_net hεbound
    · exact hsafe0'.toConsensusSafe n2
  have hsentNow : ∀ t ∈ n1.sent, t.state.channel = c →
      (t.state.turnNum < ss.state.turnNum ∨ t.state = ss.state ∨ t.state.outcome = Ω2) ∧
      (t.state.isFinal = true → t.state.outcome = Ω1 ∨ t.state.outcome = Ω2) := by
    rw [hsentEq]; exact hsent
  have hsafe2 : ConsensusSafe c ss Ω1 Ω2 n2 n2 :=
    consensus_round_safe A.toBounds ⟨⟨hc, hp⟩, hdur⟩ hΩ1 n1.chain.now rfl ⟨hseq, hεbound⟩ hsentNow
      hsafeStart
  have hfin' : n2.chain.finalizedWith c.address = some Ω := hfin
  rcases hsafe2 with h1 | h2 | ⟨hfz, -⟩
  · exact hΩne1 (Option.some_inj.mp (hfin'.symm.trans h1))
  · exact hΩne2 (Option.some_inj.mp (hfin'.symm.trans h2))
  · rw [hfz] at hfin'; exact absurd hfin' (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- A round with no call of `p` pending, against a transfer-only adversary
    (`Threat.TransfersOnly`, Nitro:779-781), is one `applyAll` of transfers
    on the chain: `tick` and `deliver` are not feasible, and `land` needs a
    pending call. Used by `Threat.Round.transfer_applyAll`. -/
theorem Threat.RoundSeq.transfers {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    (hT : T.TransfersOnly) {net net' : NetworkState E p} (h : T.RoundSeq apps t [] net net') :
    ∃ A, OnlyTransfers A ∧ net'.chain = Adjudicator.applyAll apps A net.chain := by
  generalize hp : ([] : List (Op E)) = pending at h
  induction h with
  | nil => exact ⟨[], by (simp? [OnlyTransfers] says simp only [OnlyTransfers, List.not_mem_nil, IsEmpty.forall_iff, implies_true]), rfl⟩
  | land hsplit _ _ => subst hp; (simp? at hsplit says simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | tick hfeas _ _ _ =>
    obtain ⟨_, _, _, h⟩ := hT _ _ hfeas
    cases h
  | @other pending n n' m hfeas _ _ _ ih =>
    obtain ⟨caller, a, b, rfl⟩ := hT _ _ hfeas
    obtain ⟨A, hA, heq⟩ := ih hp
    refine ⟨(caller, .transfer a b) :: A, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨a, b, rfl⟩
      · exact hA e he
    · rw [heq, NetworkState.applyAdv_chain_chain]; rfl

/-- A round of `p`'s one-transfer move against a transfer-only adversary
    (`Threat.TransfersOnly`, Nitro:779-781) is one `applyAll` of transfers
    on the chain: the adversary's transfers, `p`'s transfer, then the
    adversary's transfers (`Threat.Round.single`,
    `Threat.RoundSeq.transfers`). Used by `turbo_replay_unbeatable` and
    `turbo_value_upper_bound`. -/
theorem Threat.Round.transfer_applyAll {apps : Apps E} {p : Participant} {T : Threat E p}
    (hT : T.TransfersOnly) {a : FixedPart} {b : Address E} {net net' : NetworkState E p}
    (h : T.Round apps (HonestMove.chain (.transfer a b)) net net') :
    ∃ ops, OnlyTransfers ops ∧ (p, Op.transfer a b) ∈ ops ∧
      net'.chain = Adjudicator.applyAll apps ops net.chain := by
  obtain ⟨n1, h1, h2⟩ := Threat.Round.single h
  obtain ⟨A1, hA1, e1⟩ := h1.transfers hT
  obtain ⟨A2, hA2, e2⟩ := h2.transfers hT
  refine ⟨A1 ++ (p, .transfer a b) :: A2, fun e he => ?_,
    List.mem_append_right _ List.mem_cons_self, ?_⟩
  · rcases List.mem_append.1 he with he | he
    · exact hA1 e he
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨a, b, rfl⟩
      · exact hA2 e he
  · rw [e2, NetworkState.applyAdv_land_chain, e1, Adjudicator.applyAll_append]; rfl

/-- Nitro:842-843: "calling transfers out of order does not affect the
    ultimate result", in the form the strategy needs. When `L` is a
    subsequence of the transfer list `L'`, playing `L'` from a state ahead
    of `sp` stays ahead of playing `L` from `sp`
    (`Adjudicator.Ahead.transfer_right` for each transfer only in `L'`,
    `Adjudicator.Ahead.transfer` for each transfer in both). Used by
    `turbo_replay_unbeatable`. -/
theorem Adjudicator.Ahead.applyAll_sublist (apps : Apps E) {L L' : List (Participant × Op E)}
    (hsub : L.Sublist L') (hL' : OnlyTransfers L') :
    ∀ {sp sg : Adjudicator E}, sp.Ahead sg →
      (Adjudicator.applyAll apps L sp).Ahead (Adjudicator.applyAll apps L' sg) := by
  induction hsub with
  | slnil => exact fun h => h
  | @cons l1 l2 e _ ih =>
    intro sp sg h
    obtain ⟨a, b, he⟩ := hL' e List.mem_cons_self
    obtain ⟨caller, op⟩ := e
    simp only at he
    subst he
    simp only [Adjudicator.applyAll, Adjudicator.apply_transfer]
    exact ih (fun e' he' => hL' e' (List.mem_cons_of_mem _ he')) (h.transfer_right a b)
  | @cons_cons l1 l2 e _ ih =>
    intro sp sg h
    obtain ⟨a, b, he⟩ := hL' e List.mem_cons_self
    obtain ⟨caller, op⟩ := e
    simp only at he
    subst he
    simp only [Adjudicator.applyAll, Adjudicator.apply_transfer]
    exact ih (fun e' he' => hL' e' (List.mem_cons_of_mem _ he')) (h.transfer a b)

/-- The strategy of `turbo_redistribution_unbeatable`: `p` replays `ops`, one
    transfer per round. The chain stays ahead of the state `sp` that `ops`
    reaches with no interference: each round lands `p`'s transfer between
    two adversary transfer lists (`Threat.Round.transfer_applyAll`), and
    `Adjudicator.Ahead.applyAll_sublist`
    keeps the order. An external balance is never lower in a state ahead
    (`Adjudicator.Ahead.get_external_le`). -/
theorem turbo_replay_unbeatable (apps : Apps E) {p : Participant} (T : Threat E p)
    (hT : T.TransfersOnly) (d : E) (x : Coins) :
    ∀ ops : List (Participant × Op E), OnlyTransfers ops →
      ∀ (sp : Adjudicator E) (net : NetworkState E p), sp.Ahead net.chain →
        x ≤ (Adjudicator.applyAll apps ops sp).balances.get (.external d) →
        CanObtainIn apps T HonestMove.IsTransfer (.external d) x net := by
  intro ops
  induction ops with
  | nil => intro _ sp net h hx; exact .done (le_trans hx (h.get_external_le d))
  | cons o L ih =>
    intro hops sp net h hx
    obtain ⟨a, b, ho⟩ := hops o List.mem_cons_self
    refine .move (HonestMove.chain (.transfer a b)) ⟨a, b, rfl, rfl⟩
      (by (simp? [Op.HonestFeasible, Op.proofStates] says simp only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.not_mem_nil, IsEmpty.forall_iff, implies_true])) ?_
    intro net' hround
    rw [NetworkState.applyHonest_chain]
    obtain ⟨ops, hall, hmem, hchain⟩ := hround.transfer_applyAll hT
    have hstep := Adjudicator.Ahead.applyAll_sublist apps
      (List.singleton_sublist.2 hmem) hall h
    rw [← hchain] at hstep
    obtain ⟨q, op⟩ := o
    simp only at ho
    subst ho
    refine ih (fun e he => hops e (List.mem_cons_of_mem _ he)) ((sp.transfer a b).getD sp) net'
      ?_ ?_
    · (simpa? [Adjudicator.applyAll] using hstep says simpa only [Adjudicator.applyAll, Adjudicator.apply_transfer] using hstep)
    · (simpa? [Adjudicator.applyAll] using hx says simpa only [Adjudicator.applyAll, Adjudicator.apply_transfer] using hx)

/-- Nitro-30, Nitro-16. Nitro:775-777: "reasoning about redistribution is easy
    in Turbo: if you can find one strategy to move a certain amount into an
    address, then no-one else can prevent this from occurring." A transfer
    sequence that reaches balance `x` at the external destination `d` gives
    an unbeatable transfer-only strategy against a transfer-only adversary
    (Nitro:779-781). A channel target is excluded: the adversary can pay a
    finalized channel's coins onward in the same round. -/
theorem turbo_redistribution_unbeatable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : Nitro.ReachableParticipant apps T)
    (hdag : net.state.chain.IsDAG)
    (ops : List (Participant × Op E)) (hops : OnlyTransfers ops) (d : E) (x : Coins)
    (hgoal : x ≤ (Adjudicator.applyAll apps ops net.state.chain).balances.get (.external d)) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) x net.state := by
  obtain_reach ⟨net, hr⟩ := net
  exact turbo_replay_unbeatable apps T hT d x ops hops net.chain net (Adjudicator.Ahead.refl _)
    hgoal

/-- Under the consensus app, a channel's status never moves while its
    participant `p` has sent nothing: a successful `challenge`, `checkpoint`
    or `conclude` on `c` needs a state signed by every one of `c`'s
    participants (`consensusRules.supports`, `ConclusionProof`), so by
    `p ∈ c.participants` it needs `p`'s genuine signature; `Bounds.unforgeable`
    then needs a witness in `p`'s `sent`, which starts and stays empty.
    `deposit` and `tick` never touch `status`; `transfer` and `reclaim` on
    `c` need `c` already finalized, which it never is. Restated against the
    explicit-time game's `Threat.RoundSeq` (design decision 2026-10-29): the
    old `T.FeasibleSeq`/`advs : List (AdvMove E)` shape is gone; `p` never
    issues a call here (`participant_can_prevent_cycles`'s strategy is
    always `.wait 0`), so `pending` is always `[]` and the `land` case of
    `Threat.RoundSeq` never fires. Used by `participant_can_prevent_cycles`.
    -/
theorem consensus_channel_stays_open {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c : FixedPart} (hc : apps c.appDef = consensusRules)
    (hp : p ∈ c.participants) :
    ∀ {net net' : NetworkState E p} {t : Time} {t0 : Nat}, Threat.RoundSeq apps T t [] net net' →
      net.sent = [] → net.chain.statusOf c = .open t0 →
      net'.chain.statusOf c = .open t0 := by
  intro net net' t t0 hseq
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ hbase; exact hbase
  | land hsplit _ _ => rw [← hpnil] at hsplit; (simp? at hsplit says simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hsent1 hbase1
    have hsent1' : (net1.applyAdv apps (AdvMove.tick dt)).sent = [] := by
      rw [NetworkState.applyAdv_sent]; exact hsent1
    have step : (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c = .open t0 := by
      (simpa? [NetworkState.applyAdv] using hbase1 says simpa only [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hbase1)
    exact ih hpnil hsent1' step
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hsent1 hbase1
    have hsent1' : (net1.applyAdv apps m).sent = [] := by
      rw [NetworkState.applyAdv_sent]; exact hsent1
    have step : (net1.applyAdv apps m).chain.statusOf c = .open t0 := by
      cases m with
      | deliver ss' => exact hbase1
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | chain caller op =>
        simp only [NetworkState.applyAdv]
        cases h : net1.chain.apply apps caller op with
        | none => exact hbase1
        | some s' =>
          have hfo1 : net1.chain.finalOutcome c.address = none := by
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hbase1,
              ChannelStatus.finalOutcome_open]
          have hU : ∀ ss' ∈ op.proofStates, p ∈ ss'.signers →
              ∃ x ∈ net1.sent, x.state = ss'.state :=
            fun ss' hmem hsig => (hbounds.unforgeable net1 caller op hfeas ss' hmem).1 hsig
          cases op with
          | deposit a e x =>
            obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
            rw [Adjudicator.statusOf_of_status hs]; exact hbase1
          | tick dt' =>
            have hs' : net1.chain.tick dt' = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
            subst hs'; rw [Adjudicator.tick_statusOf]; exact hbase1
          | transfer a b =>
            by_cases hac : a = c
            · subst hac
              obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
              rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
            · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
              rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                if_neg (Ne.symm hac)]
              exact hbase1
          | reclaim l v =>
            by_cases hlc : l = c
            · subst hlc
              obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
              rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
            · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
              rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
              exact hbase1
          | challenge c' proof candidate =>
            by_cases hcc : c' = c
            · exfalso; subst hcc
              obtain ⟨⟨-, hs, -, -⟩, -⟩ := Adjudicator.challenge_some h
              obtain ⟨x, hx, -⟩ := ConsensusMember.sent_cand ⟨hc, hp⟩ hU hs
              rw [hsent1] at hx; exact absurd hx List.not_mem_nil
            · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
              exact hbase1
          | checkpoint c' proof candidate =>
            by_cases hcc : c' = c
            · exfalso; subst hcc
              obtain ⟨⟨-, hs, -, -⟩, -⟩ := Adjudicator.checkpoint_some h
              obtain ⟨x, hx, -⟩ := ConsensusMember.sent_cand ⟨hc, hp⟩ hU hs
              rw [hsent1] at hx; exact absurd hx List.not_mem_nil
            · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
              exact hbase1
          | conclude c' ss' =>
            by_cases hcc : c' = c
            · exfalso; subst hcc
              obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
              have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hp)
              have hmem : ss' ∈ (Op.conclude c' ss').proofStates := by (simp? [Op.proofStates] says simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false])
              obtain ⟨x, hx, -⟩ := hU ss' hmem hp'
              rw [hsent1] at hx; exact absurd hx List.not_mem_nil
            · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
              exact hbase1
    exact ih hpnil hsent1' step

/-- Nitro-32. Nitro:792-794: "While it is technically possible to create outcomes
    with cycles, it is also possible for any participant in the channel to
    prevent this from happening." Under the consensus app a participant who
    signs no state can keep every cycle away from its open channels. -/
theorem participant_can_prevent_cycles (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : Nitro.ReachableParticipant apps T)
    (hc : ∀ c : FixedPart, p ∈ c.participants → apps c.appDef = consensusRules)
    (hopen : ∀ c : FixedPart, p ∈ c.participants → ∃ t, net.state.chain.statusOf c = .open t)
    (hdag : net.state.chain.IsDAG) (hsent : net.state.sent = []) :
    Prevents apps T (fun net' => ∃ c : FixedPart, p ∈ c.participants ∧
      Relation.TransGen net'.chain.Edge c.address c.address) net.state := by
  obtain_reach ⟨net, _hr⟩ := net
  have hinv : ∀ {m : NetworkState E p}, Run apps T (fun _ => .wait 0) net m →
      m.sent = [] ∧ ∀ c' : FixedPart, p ∈ c'.participants → ∀ t,
        net.chain.statusOf c' = .open t → m.chain.statusOf c' = .open t := by
    intro m hm
    induction hm with
    | refl => exact ⟨hsent, fun c' _ t ht => ht⟩
    | @round n1 n2 hrun hround ih =>
      obtain ⟨ihsent, ihopen⟩ := ih
      obtain ⟨hseq, -⟩ := hround
      have hsent2 : n2.sent = [] := hseq.sent_eq.trans ihsent
      refine ⟨by (simpa? [NetworkState.applyHonest] using hsent2 says simpa only [NetworkState.applyHonest] using hsent2), fun c' hpc' t ht => ?_⟩
      have hopen2 := consensus_channel_stays_open A.toBounds (hc c' hpc') hpc' hseq ihsent
        (ihopen c' hpc' t ht)
      (simpa? [NetworkState.applyHonest, Adjudicator.tick_statusOf] using hopen2 says simpa only [NetworkState.applyHonest, Adjudicator.tick_statusOf] using hopen2)
  refine ⟨fun _ => .wait 0, fun _ => trivial, fun n1 n2 hrun hround hcyc => ?_⟩
  obtain ⟨c, hpc, hcyc⟩ := hcyc
  obtain ⟨t, ht⟩ := hopen c hpc
  obtain ⟨hsent1, hopen1⟩ := hinv hrun
  obtain ⟨hseq, -⟩ := hround
  have hopenN2 : n2.chain.statusOf c = .open t :=
    consensus_channel_stays_open A.toBounds (hc c hpc) hpc hseq hsent1 (hopen1 c hpc t ht)
  obtain ⟨y, hey, -⟩ := Relation.TransGen.head'_iff.1 hcyc
  obtain ⟨-, e, he, -⟩ := hey
  (simp? [Adjudicator.allocationOf, hopenN2, ChannelStatus.finalOutcome_open] at he says simp only [Adjudicator.allocationOf, FixedPart.address_eq, Adjudicator.finalOutcome_channel, hopenN2, ChannelStatus.finalOutcome_open, List.not_mem_nil] at he)

/-! ### The symbolic terminal state

    `turbo_value_upper_bound` reasons about every possible sequence of real
    `transfer` calls from `s`. This section builds one witness state that
    stands in for "the algorithm already ran everywhere": `symbolicTerminal`
    sets every already-finalized channel's stored outcome to the allocation
    `chainPay` computes for it (`symbolicAlloc`), and every required
    address's balance to the coins `chainPay` leaves unspent
    (`symbolicLeftover`). `chainPay_exhausted` then reads as "a real
    `transfer` call on this state moves zero coins"
    (`symbolicTerminal_transfer_unmoved_of_matches`). -/

/-- `paidTo` reads only the deduplicated allocation (`Allocation.paidTo`'s
    own definition goes through `o.dedup`), so it agrees with `paidTo` on
    the allocation's own `dedup`. -/
theorem Allocation.paidTo_dedup (o : Allocation E) (hg : Coins) (d : Address E) :
    o.paidTo hg d = o.dedup.paidTo hg d := by
  rw [Allocation.paidTo_eq_get, Allocation.paidTo_eq_get,
    Allocation.dedup_eq_self_of_nodup (Allocation.dedup_nodup o)]

/-- `chainPay`'s result does not depend on whether its starting allocation
    is deduplicated: `find` is dedup-agnostic (`find_dedup`), so both runs
    take the same branch at every step; `.2` (the leftover) matches
    directly by induction, and `.1` (the paid allocation) matches up to
    `dedup` (`dedup_reduceOwed` commutes `dedup` past the one step that
    changes, `paidTo_dedup` keeps the step's own amount the same). Needed
    because a channel's stored outcome has no proven `Nodup` invariant:
    `symbolicAlloc` chains from the raw outcome (`AheadOf.kind` needs the
    raw entry list), while `symbolicLeftover`, `requiredNodes` and
    `chainPay_exhausted` all read the deduplicated view. -/
theorem Allocation.chainPay_dedup (ds : List (Address E)) (o : Allocation E) (hg : Coins) :
    (Allocation.chainPay ds o hg).1.dedup = (Allocation.chainPay ds o.dedup hg).1 ∧
    (Allocation.chainPay ds o hg).2 = (Allocation.chainPay ds o.dedup hg).2 := by
  induction ds generalizing o hg with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    rw [Allocation.chainPay_cons, Allocation.chainPay_cons]
    have hfeq : o.dedup.find d = o.find d := Allocation.find_dedup o d
    cases hfo : o.find d with
    | none => rw [hfeq, hfo]; exact ih o hg
    | some e =>
      rw [hfeq, hfo]
      obtain ⟨dd, item⟩ := e
      cases item with
      | guarantee amt ps => dsimp only; exact ih o hg
      | alloc amt =>
        dsimp only
        have hpaidTo : o.paidTo hg d = o.dedup.paidTo hg d := Allocation.paidTo_dedup o hg d
        rw [hpaidTo]
        have hded : (o.reduceOwed d (o.dedup.paidTo hg d)).dedup =
            o.dedup.reduceOwed d (o.dedup.paidTo hg d) := by
          rw [← hpaidTo]; exact Allocation.dedup_reduceOwed o d (o.paidTo hg d)
        obtain ⟨ih1, ih2⟩ := ih (o.reduceOwed d (o.dedup.paidTo hg d)) (hg - o.dedup.paidTo hg d)
        rw [hded] at ih1 ih2
        exact ⟨ih1, ih2⟩

/-- The leftover component of `chainPay_dedup`, named for direct use. -/
theorem Allocation.chainPay_leftover_eq_dedup (ds : List (Address E)) (o : Allocation E)
    (hg : Coins) :
    (Allocation.chainPay ds o hg).2 = (Allocation.chainPay ds o.dedup hg).2 :=
  (Allocation.chainPay_dedup ds o hg).2

/-- Pay `c`'s own stored allocation through its own destinations, in `c`'s
    own priority order, out of the algorithm's recorded value at `c`
    (`turboValueAlong`). Chains from the RAW stored outcome, not its
    `dedup`: a channel's stored outcome has no proven `Nodup` invariant
    anywhere in the model, and `AheadOf.kind` (`symbolicAlloc_AheadOf`)
    needs to match the raw entry list `o` found in `s.finalOutcome`, not a
    shorter, deduplicated view of it. The allocation `chainPay` leaves
    behind; `symbolicAlloc_dedup_dest_eq` reads its `dedup`. -/
noncomputable def Adjudicator.symbolicAlloc (s : Adjudicator E) (order : List (Address E))
    (c : Address E) : Allocation E :=
  match s.finalOutcome c with
  | some (.allocation o) =>
    (Allocation.chainPay ((s.allocationOf c).map Entry.dest) o (s.turboValueAlong order c)).1
  | none => []

/-- The coins `chainPay` leaves unspent after paying `c`'s own allocation
    out of `turboValueAlong order c`. -/
noncomputable def Adjudicator.symbolicLeftover (s : Adjudicator E) (order : List (Address E))
    (c : Address E) : Coins :=
  (Allocation.chainPay ((s.allocationOf c).map Entry.dest) (s.allocationOf c)
    (s.turboValueAlong order c)).2

/-- The balances of the symbolic terminal state: `chainPay`'s leftover at
    every address `turbo_value_upper_bound` can ever query
    (`requiredNodes`, deduped: every address with a nonzero balance or a
    nonempty allocation in `s`, `active_mem_requiredNodes`).
    `symbolicTerminal_balances_get` reads this list at an arbitrary
    address, inside or outside `requiredNodes s`. -/
noncomputable def Adjudicator.symbolicBalances (s : Adjudicator E) (order : List (Address E)) :
    Balances E :=
  (requiredNodes s).dedup.map (fun m => (m, s.symbolicLeftover order m))

/-- The symbolic terminal state: `chainPay`'s leftover at every required
    address, and every already-finalized channel's stored outcome
    rewritten to the allocation `chainPay` computes for it. A channel `s`
    itself has not finalized is untouched. -/
noncomputable def Adjudicator.symbolicTerminal (s : Adjudicator E) (order : List (Address E)) :
    Adjudicator E where
  balances := s.symbolicBalances order
  held := s.held
  status := s.status.map (fun p =>
    if (p.2.finalOutcome s.now).isSome
    then (p.1, p.2.withOutcome (.allocation (s.symbolicAlloc order p.1.address)))
    else p)
  now := s.now

/-- `List.lookup` on a list built as `(key, f key)` pairs: `some (f a)`
    when `a` is one of the keys, `none` otherwise. -/
theorem lookup_map_address (l : List (Address E)) (f : Address E → Coins) (a : Address E) :
    (l.map (fun k => (k, f k))).lookup a = if a ∈ l then some (f a) else none := by
  induction l with
  | nil => (simp? says simp only [List.map_nil, List.lookup_nil, List.not_mem_nil, ↓reduceIte])
  | cons b t ih =>
    simp only [List.map_cons, List.lookup_cons]
    by_cases h : a = b
    · subst h; (simp? says simp only [BEq.rfl, List.mem_cons, true_or, ↓reduceIte])
    · (simp? [beq_false_of_ne h, h, ih] says simp only [beq_false_of_ne h, ih, List.mem_cons, h, false_or])

/-- A destination of a node's own allocation is a required node, the same
    way `edge_mem_requiredNodes` reads an `Edge`'s target, but without the
    `isExternal = false` restriction `Edge` carries: `requiredNodes`'s own
    `flatMap` piece does not need it either. -/
theorem Adjudicator.dest_mem_requiredNodes (s : Adjudicator E) (c m : Address E) (e : Entry E)
    (he : e ∈ s.allocationOf c) (hed : e.dest = m) : m ∈ requiredNodes s := by
  have hcactive : s.allocationOf c ≠ [] := fun hemp => by rw [hemp] at he; exact List.not_mem_nil he
  obtain ⟨cc, hceq⟩ : ∃ cc : FixedPart, c = cc.address := by
    cases c with
    | external dd => (simp? [Adjudicator.allocationOf, Adjudicator.finalOutcome] at hcactive says simp only [allocationOf, finalOutcome, ne_eq, not_true_eq_false] at hcactive)
    | channel cc => exact ⟨cc, rfl⟩
  subst hceq
  obtain ⟨st, hmemstatus, -⟩ := channel_active_mem_status s cc hcactive
  unfold requiredNodes
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(cc, st), hmemstatus, ?_⟩
  rw [← hed]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- An address outside `requiredNodes s` has no balance and no allocation
    in `s` (`active_mem_requiredNodes`'s contrapositive), and no node
    credits it either (`dest_mem_requiredNodes`'s contrapositive on
    `CreditsTo`): `turboValueAlong_eq_add_credits` then reads its Turbo
    Value as `0`, and `chainPay` on the empty allocation leaves `0`
    unspent. -/
theorem Adjudicator.symbolicLeftover_eq_zero_of_not_mem_requiredNodes (s : Adjudicator E)
    (order : List (Address E)) (hord : s.IsTopologicalOrder order)
    (m : Address E) (h : m ∉ requiredNodes s) :
    s.symbolicLeftover order m = 0 := by
  have hnact : s.balances.get m = 0 ∧ s.allocationOf m = [] := by
    by_contra hcon
    rw [not_and_or] at hcon
    exact h (active_mem_requiredNodes s m hcon)
  obtain ⟨hbal0, halloc0⟩ := hnact
  have hcred0 : ∀ c, ¬ s.CreditsTo c m = true := by
    intro c hcc
    unfold Adjudicator.CreditsTo at hcc
    cases hfind : (s.allocationOf c).find m with
    | none => rw [hfind] at hcc; (simp? at hcc says simp only [Option.elim_none, Bool.false_eq_true] at hcc)
    | some e =>
      have hed : e.dest = m := Allocation.find_dest hfind
      have he : e ∈ s.allocationOf c := by
        unfold Allocation.find at hfind
        exact List.mem_of_find?_eq_some hfind
      exact h (Adjudicator.dest_mem_requiredNodes s c m e he hed)
  have htv : s.turboValueAlong order m = 0 := by
    rw [turboValueAlong_eq_add_credits s hord.isDAG order hord m, hbal0]
    have hfnil : order.filter (s.CreditsTo · m) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c _
      exact hcred0 c
    rw [hfnil]
    (simp? says simp only [List.map_nil, List.sum_nil, add_zero])
  unfold Adjudicator.symbolicLeftover
  rw [halloc0, List.map_nil]
  exact htv

/-- Point 1. Reading `(s.symbolicTerminal order).balances` at any address:
    `s.symbolicLeftover order m` whether or not `m` is a required node
    (`symbolicLeftover_eq_zero_of_not_mem_requiredNodes` covers the
    "outside" case). -/
theorem Adjudicator.symbolicTerminal_balances_get (s : Adjudicator E) (order : List (Address E))
    (hord : s.IsTopologicalOrder order) (m : Address E) :
    (s.symbolicTerminal order).balances.get m = s.symbolicLeftover order m := by
  show Balances.get (s.symbolicBalances order) m = s.symbolicLeftover order m
  unfold Adjudicator.symbolicBalances Balances.get
  rw [lookup_map_address (requiredNodes s).dedup (fun n => s.symbolicLeftover order n) m]
  by_cases hmem : m ∈ (requiredNodes s).dedup
  · rw [if_pos hmem]; (simp? says simp only [Option.getD_some])
  · rw [if_neg hmem]
    exact (Adjudicator.symbolicLeftover_eq_zero_of_not_mem_requiredNodes s order hord m
      (fun hc => hmem (List.mem_dedup.mpr hc))).symm

/-- `(s.symbolicTerminal order).statusOf c`: `s.statusOf c` rewritten with
    `withOutcome` when `s` itself already finalized `c`, untouched
    otherwise. The map `symbolicTerminal`'s `status` field applies keeps
    every key, so `List.lookup` on it reduces to `List.lookup` on
    `s.status` with the same transform applied to the found value. -/
theorem Adjudicator.symbolicTerminal_statusOf (s : Adjudicator E) (order : List (Address E))
    (c : FixedPart) :
    (s.symbolicTerminal order).statusOf c =
      if ((s.statusOf c).finalOutcome s.now).isSome
      then (s.statusOf c).withOutcome (.allocation (s.symbolicAlloc order c.address))
      else s.statusOf c := by
  unfold Adjudicator.statusOf Adjudicator.symbolicTerminal
  dsimp only
  have hfun : (fun p : FixedPart × ChannelStatus E => if (p.2.finalOutcome s.now).isSome
      then (p.1, p.2.withOutcome (.allocation (s.symbolicAlloc order p.1.address))) else p)
      = (fun p => (p.1, if (p.2.finalOutcome s.now).isSome
          then p.2.withOutcome (.allocation (s.symbolicAlloc order p.1.address)) else p.2)) := by
    funext p
    obtain ⟨k, v⟩ := p
    by_cases hcond : (v.finalOutcome s.now).isSome <;> simp [hcond]
  rw [hfun]
  generalize hl : s.status = l
  clear hl
  induction l with
  | nil => (simp? says simp only [FixedPart.address_eq, List.map_nil, List.lookup_nil, Option.getD_none, ChannelStatus.finalOutcome_open, Option.isSome_none, Bool.false_eq_true, ↓reduceIte])
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.lookup_cons]
    by_cases h : c = k
    · subst h
      by_cases hcond : (v.finalOutcome s.now).isSome
      · (simp? [hcond] says simp only [BEq.rfl, hcond, ↓reduceIte, FixedPart.address_eq, Option.getD_some])
      · (simp? [hcond] says simp only [BEq.rfl, hcond, Bool.false_eq_true, ↓reduceIte, Option.getD_some])
    · (simp? [beq_false_of_ne h] says simp only [beq_false_of_ne h, FixedPart.address_eq])
      exact ih

/-- Point 2. `(s.symbolicTerminal order).finalOutcome` at a channel
    address: `s`'s own `finalOutcome` there, with the allocation replaced
    by `symbolicAlloc` when `s` already finalized that channel
    (`ChannelStatus.finalOutcome_withOutcome` reads `some` unconditionally,
    independent of `now`, once `withOutcome` has run). -/
theorem Adjudicator.symbolicTerminal_finalOutcome (s : Adjudicator E) (order : List (Address E))
    (c : FixedPart) :
    (s.symbolicTerminal order).finalOutcome c.address =
      if (s.finalOutcome c.address).isSome
      then some (.allocation (s.symbolicAlloc order c.address))
      else s.finalOutcome c.address := by
  have hnow : (s.symbolicTerminal order).now = s.now := rfl
  have hthis : (s.symbolicTerminal order).finalOutcome c.address =
      ((s.symbolicTerminal order).statusOf c).finalOutcome (s.symbolicTerminal order).now := rfl
  rw [hthis, hnow, Adjudicator.symbolicTerminal_statusOf]
  have hfc : s.finalOutcome c.address = (s.statusOf c).finalOutcome s.now := rfl
  rw [hfc]
  by_cases hcond : ((s.statusOf c).finalOutcome s.now).isSome
  · rw [if_pos hcond, if_pos hcond]
    exact ChannelStatus.finalOutcome_withOutcome _ _ _
  · rw [if_neg hcond, if_neg hcond]

omit [DecidableEq E] in
/-- Two allocations with the same entry kinds have the same destinations
    (`Entry.kind`'s first component is `Entry.dest`). -/
theorem Allocation.map_dest_of_map_kind {og op : Allocation E}
    (h : og.map Entry.kind = op.map Entry.kind) : og.map Entry.dest = op.map Entry.dest := by
  have hdest : ∀ o : Allocation E, (o.map Entry.kind).map Prod.fst = o.map Entry.dest := by
    intro o; rw [List.map_map]; rfl
  rw [← hdest og, ← hdest op, h]

/-- `symbolicAlloc`'s `dedup` has exactly `allocationOf`'s own
    destinations: `chainPay_dedup` reads `symbolicAlloc`'s `dedup` as the
    chain from the already-deduplicated outcome, and `chainPay_AheadOf`'s
    `kind` field (`AheadOf.refl`, the reflexive instance) then matches
    that chain's destinations to the deduplicated outcome's own. -/
theorem Adjudicator.symbolicAlloc_dedup_dest_eq (s : Adjudicator E) (order : List (Address E))
    (c : Address E) :
    (s.symbolicAlloc order c).dedup.map Entry.dest = (s.allocationOf c).map Entry.dest := by
  unfold Adjudicator.symbolicAlloc Adjudicator.allocationOf
  cases hfo : s.finalOutcome c with
  | none => (simp? [Allocation.dedup] says simp only [Allocation.dedup, Allocation.dedupFrom_nil, List.map_nil])
  | some outcome =>
    cases outcome with
    | allocation o =>
      dsimp only
      rw [(Allocation.chainPay_dedup (o.dedup.map Entry.dest) o (s.turboValueAlong order c)).1]
      have hahead := Allocation.chainPay_AheadOf (o.dedup.map Entry.dest) o.dedup o.dedup
        (s.turboValueAlong order c) (Allocation.AheadOf.refl _ _)
      exact Allocation.map_dest_of_map_kind hahead.kind

/-- Point 3. `(s.symbolicTerminal order).allocationOf c`: `symbolicAlloc`'s
    `dedup` when `s` already finalized `c`, the empty allocation
    otherwise (`Adjudicator.allocationOf` always reads through `.dedup`,
    so this is the raw `symbolicAlloc` dereferenced the same way `s`'s own
    `allocationOf` dereferences its raw stored outcome). -/
theorem Adjudicator.symbolicTerminal_allocationOf (s : Adjudicator E) (order : List (Address E))
    (c : Address E) :
    (s.symbolicTerminal order).allocationOf c =
      if (s.finalOutcome c).isSome then (s.symbolicAlloc order c).dedup else [] := by
  cases c with
  | external e =>
    have h1 : (s.symbolicTerminal order).allocationOf (Address.external e) = [] :=
      allocationOf_eq_nil_of_isExternal _ rfl
    have h2 : s.finalOutcome (Address.external e : Address E) = none := rfl
    rw [h1, h2]; (simp? says simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte])
  | channel cc =>
    show (s.symbolicTerminal order).allocationOf cc.address =
      if (s.finalOutcome cc.address).isSome then (s.symbolicAlloc order cc.address).dedup else []
    unfold Adjudicator.allocationOf
    rw [Adjudicator.symbolicTerminal_finalOutcome]
    split_ifs with hcond
    · rfl
    · rw [Option.not_isSome_iff_eq_none.mp hcond]

/-- `symbolicTerminal`'s own allocation at any address has the same
    destinations as `s`'s: `symbolicAlloc_dedup_dest_eq` when `s`
    finalized it, both sides empty otherwise. -/
theorem Adjudicator.symbolicTerminal_allocationOf_dest_eq (s : Adjudicator E)
    (order : List (Address E)) (n : Address E) :
    ((s.symbolicTerminal order).allocationOf n).map Entry.dest = (s.allocationOf n).map Entry.dest := by
  rw [Adjudicator.symbolicTerminal_allocationOf]
  split_ifs with hcond
  · exact Adjudicator.symbolicAlloc_dedup_dest_eq s order n
  · have hnil : s.allocationOf n = [] := by
      unfold Adjudicator.allocationOf
      rw [Option.not_isSome_iff_eq_none.mp hcond]
    rw [hnil]

/-- `symbolicTerminal`'s edge relation is `s`'s own, since both read the
    same destinations (`symbolicTerminal_allocationOf_dest_eq`). -/
theorem Adjudicator.symbolicTerminal_Edge_iff (s : Adjudicator E) (order : List (Address E))
    (n d : Address E) :
    (s.symbolicTerminal order).Edge n d ↔ s.Edge n d := by
  have hdest := s.symbolicTerminal_allocationOf_dest_eq order n
  unfold Adjudicator.Edge
  constructor
  · rintro ⟨hext, e, he, hed⟩
    refine ⟨hext, ?_⟩
    have hmem : d ∈ ((s.symbolicTerminal order).allocationOf n).map Entry.dest :=
      List.mem_map.mpr ⟨e, he, hed⟩
    rw [hdest] at hmem
    obtain ⟨e', he', hed'⟩ := List.mem_map.mp hmem
    exact ⟨e', he', hed'⟩
  · rintro ⟨hext, e, he, hed⟩
    refine ⟨hext, ?_⟩
    have hmem : d ∈ (s.allocationOf n).map Entry.dest := List.mem_map.mpr ⟨e, he, hed⟩
    rw [← hdest] at hmem
    obtain ⟨e', he', hed'⟩ := List.mem_map.mp hmem
    exact ⟨e', he', hed'⟩

/-- Setting an entry's owed amount down by `0` is a no-op, at the exact
    entry `find` reaches: the matched entry is already `.alloc amt`, so
    rewriting its item to `.alloc (amt - 0)` reproduces it. -/
theorem Allocation.reduceOwed_zero_of_find_alloc {o : Allocation E} {d : Address E} {amt : Coins}
    (h : o.find d = some ⟨d, .alloc amt⟩) : o.reduceOwed d 0 = o := by
  induction o with
  | nil => (simp? [Allocation.find] at h says simp only [find, List.find?_nil, reduceCtorEq] at h)
  | cons e t ih =>
    rw [Allocation.find_cons] at h
    rw [Allocation.reduceOwed_cons]
    by_cases he : e.dest = d
    · rw [if_pos he] at h ⊢
      have he' : e = (⟨d, .alloc amt⟩ : Entry E) := Option.some.inj h
      subst he'
      (simp? says simp only [Entry.amount_mk, Item.amount_alloc, tsub_zero])
    · rw [if_neg he] at h ⊢
      rw [ih h]

/-- `symbolicAlloc` is `AheadOf` the raw outcome it chains from, with
    `symbolicLeftover` as the budget it leaves behind: `chainPay_AheadOf`
    applied reflexively (`og = op = o`, `AheadOf.refl`), bridged from
    `symbolicAlloc`'s and `symbolicLeftover`'s two different internal
    chains (raw-start vs. deduped-start) by `chainPay_leftover_eq_dedup`. -/
theorem Adjudicator.symbolicAlloc_AheadOf (s : Adjudicator E) (order : List (Address E))
    (c : FixedPart) (o : Allocation E) (hfo : s.finalOutcome c.address = some (.allocation o)) :
    (s.symbolicAlloc order c.address).AheadOf o (s.symbolicLeftover order c.address) := by
  have halloc : s.allocationOf c.address = o.dedup := by
    unfold Adjudicator.allocationOf; rw [hfo]
  have hahead := Allocation.chainPay_AheadOf ((s.allocationOf c.address).map Entry.dest) o o
    (s.turboValueAlong order c.address) (Allocation.AheadOf.refl _ _)
  have hleftover : (Allocation.chainPay ((s.allocationOf c.address).map Entry.dest) o
      (s.turboValueAlong order c.address)).2 = s.symbolicLeftover order c.address := by
    unfold Adjudicator.symbolicLeftover
    rw [Allocation.chainPay_leftover_eq_dedup _ o, halloc]
  unfold Adjudicator.symbolicAlloc
  rw [hfo]
  dsimp only
  rw [hleftover] at hahead
  exact hahead

/-- The `x = 0` fact `symbolicTerminal_transfer_unmoved_of_matches` needs: a real
    `transfer` call reads `o.find b`/`o.paidTo` off `symbolicAlloc`'s raw
    shape, but `paidTo` only ever depends on the deduplicated view
    (`paidTo_dedup`), and that deduplicated view is exactly the `chainPay`
    run `chainPay_exhausted` already covers (`chainPay_dedup`,
    `s.allocationOf c.address = o.dedup`). -/
theorem Adjudicator.symbolicAlloc_paidTo_eq_zero (s : Adjudicator E) (order : List (Address E))
    (c : FixedPart) (b : Address E) (amt : Coins)
    (hfind : (s.symbolicAlloc order c.address).find b = some (⟨b, .alloc amt⟩ : Entry E)) :
    (s.symbolicAlloc order c.address).paidTo (s.symbolicLeftover order c.address) b = 0 := by
  rw [Allocation.paidTo_dedup]
  cases hfo : s.finalOutcome c.address with
  | none =>
    exfalso
    have hsa : s.symbolicAlloc order c.address = [] := by
      unfold Adjudicator.symbolicAlloc; rw [hfo]
    rw [hsa] at hfind
    (simp? [Allocation.find] at hfind says simp only [Allocation.find, List.find?_nil, reduceCtorEq] at hfind)
  | some outcome =>
    cases outcome with
    | allocation o_test =>
      have halloc : s.allocationOf c.address = o_test.dedup := by
        unfold Adjudicator.allocationOf; rw [hfo]
      have hsa : s.symbolicAlloc order c.address =
          (Allocation.chainPay (o_test.dedup.map Entry.dest) o_test
            (s.turboValueAlong order c.address)).1 := by
        unfold Adjudicator.symbolicAlloc; rw [hfo, halloc]
      have hleftover : s.symbolicLeftover order c.address =
          (Allocation.chainPay (o_test.dedup.map Entry.dest) o_test.dedup
            (s.turboValueAlong order c.address)).2 := by
        unfold Adjudicator.symbolicLeftover; rw [halloc]
      rw [hsa] at hfind ⊢
      rw [hleftover]
      have hded1 := (Allocation.chainPay_dedup (o_test.dedup.map Entry.dest) o_test
        (s.turboValueAlong order c.address)).1
      have hexh := Allocation.chainPay_exhausted o_test.dedup (s.turboValueAlong order c.address) b
      have hfindo : (Allocation.chainPay (o_test.dedup.map Entry.dest) o_test.dedup
          (s.turboValueAlong order c.address)).1.find b = some (⟨b, .alloc amt⟩ : Entry E) := by
        rw [← hded1, Allocation.find_dedup]; exact hfind
      rw [hfindo] at hexh
      simp only [Option.elim, Item.isGuarantee, Bool.false_eq_true, false_or] at hexh
      rw [hded1]
      exact hexh

/-- Point 5. `Adjudicator.TransferExhausted` demands raw `Balances E` list
    equality (`s'.balances = s.balances`), not a reading-level fact.
    `Balances.set` always moves its key to the front of the list
    (`Balances.add`/`Balances.sub` both reduce to it), so setting two
    different keys to their own current value, as a successful `transfer`
    call's `payTo` then balance-debit always does, reorders a multi-key
    list: `decide` refutes `(l.add k1 0).sub k2 0 = l` on a 3-key `l` with
    `k2` not already `l`'s head. `symbolicTerminal`'s own `balances` has
    one key per `requiredNodes`, so two already-finalized ledger channels
    with distinct payer addresses break literal `TransferExhausted` for
    any choice of that list's order. The usable, provably true fact instead
    mirrors `transfer_exhausted_fixed`'s own conclusion: a real `transfer`
    call that "succeeds" on the symbolic terminal state pays `0` coins
    (`chainPay_exhausted`, through `symbolicTerminal_balances_get` and
    `symbolicTerminal_finalOutcome`), so every address's *reading*
    (`finalOutcome`, `balances.get`) is unchanged, even though the stored
    list can reorder. A state `u` that reads the same as the symbolic terminal state
    (same `finalOutcome`, same `balances.get` everywhere) absorbs a transfer the same way. -/
theorem symbolicTerminal_transfer_unmoved_of_matches (s : Adjudicator E) (order : List (Address E))
    (hord : s.IsTopologicalOrder order) (u : Adjudicator E)
    (hfo : ∀ n, u.finalOutcome n = (s.symbolicTerminal order).finalOutcome n)
    (hbl : ∀ n, u.balances.get n = (s.symbolicTerminal order).balances.get n)
    {a : FixedPart} {b : Address E} {u' : Adjudicator E} (h : u.transfer a b = some u') :
    (∀ n : Address E, u'.finalOutcome n = u.finalOutcome n) ∧
    (∀ n : Address E, u'.balances.get n = u.balances.get n) := by
  set sg := s.symbolicTerminal order with hsgdef
  obtain ⟨o, amt, x, hf, hfind, hk, hbfund, hx, hfoeff, hbal, -, -⟩ := Adjudicator.transfer_effect h
  have hfo2 := Adjudicator.symbolicTerminal_finalOutcome s order a
  rw [← hsgdef, ← hfo a.address] at hfo2
  have heq : some (Outcome.allocation o) =
      if (s.finalOutcome a.address).isSome then some (.allocation (s.symbolicAlloc order a.address))
      else s.finalOutcome a.address := hf.symm.trans hfo2
  by_cases hcond : (s.finalOutcome a.address).isSome
  · rw [if_pos hcond] at heq
    have hoeq : o = s.symbolicAlloc order a.address := by
      injection heq with heq'
      injection heq'
    have hx0 : x = 0 := by
      have hbg : u.balances.get a.address = s.symbolicLeftover order a.address := by
        rw [hbl a.address]
        exact s.symbolicTerminal_balances_get order hord a.address
      rw [hx, hbg, hoeq]
      exact s.symbolicAlloc_paidTo_eq_zero order a b amt (hoeq ▸ hfind)
    refine ⟨fun n => ?_, fun n => ?_⟩
    · cases n with
      | external e => (simp? [Adjudicator.finalOutcome] says simp only [Adjudicator.finalOutcome])
      | channel c =>
        rw [← FixedPart.address_eq]
        have hc := hfoeff c
        by_cases hca : c = a
        · subst hca
          rw [hc, if_pos rfl, hx0, Allocation.reduceOwed_zero_of_find_alloc hfind, hf]
        · rw [hc, if_neg hca]
    · have hbd := hbal n
      rw [hx0] at hbd
      simp only [ite_self, Nat.add_zero] at hbd
      exact hbd
  · rw [if_neg hcond] at heq
    have hsome : (s.finalOutcome a.address).isSome = true := by rw [← heq]; rfl
    exact absurd hsome hcond



theorem symbolicTerminal_applyAll_unmoved (s : Adjudicator E) (order : List (Address E))
    (hord : s.IsTopologicalOrder order) (apps : Apps E)
    (ops : List (Participant × Op E)) (hops : OnlyTransfers ops) (u : Adjudicator E)
    (hfo : ∀ n, u.finalOutcome n = (s.symbolicTerminal order).finalOutcome n)
    (hbl : ∀ n, u.balances.get n = (s.symbolicTerminal order).balances.get n) :
    (∀ n, (Adjudicator.applyAll apps ops u).finalOutcome n = (s.symbolicTerminal order).finalOutcome n) ∧
    (∀ n, (Adjudicator.applyAll apps ops u).balances.get n = (s.symbolicTerminal order).balances.get n) := by
  induction ops generalizing u with
  | nil => exact ⟨hfo, hbl⟩
  | cons hd rest ih =>
    obtain ⟨a, b, hb⟩ := hops hd List.mem_cons_self
    obtain ⟨caller, op⟩ := hd
    have hb' : op = Op.transfer a b := hb
    have hOT : OnlyTransfers rest := fun e he => hops e (List.mem_cons_of_mem _ he)
    show (∀ n, (Adjudicator.applyAll apps rest ((u.apply apps caller op).getD u)).finalOutcome n =
        (s.symbolicTerminal order).finalOutcome n) ∧
      (∀ n, (Adjudicator.applyAll apps rest ((u.apply apps caller op).getD u)).balances.get n =
        (s.symbolicTerminal order).balances.get n)
    rw [hb', Adjudicator.apply_transfer]
    cases hstep : u.transfer a b with
    | none => simp only [Option.getD_none]; exact ih hOT u hfo hbl
    | some u' =>
      simp only [Option.getD_some]
      have := symbolicTerminal_transfer_unmoved_of_matches s order hord u hfo hbl hstep
      exact ih hOT u' (fun n => (this.1 n).trans (hfo n)) (fun n => (this.2 n).trans (hbl n))

/-- Point 6. `dueTotal` never rises along a list of real transfer calls:
    `transfer_effect`'s `dueTotal` field absorbs each call, and a reverted
    call (`apply = none`) leaves `u` unchanged. -/
theorem dueTotal_applyAll_le (apps : Apps E) {ops : List (Participant × Op E)}
    (hops : OnlyTransfers ops) (u : Adjudicator E) (d : Address E) :
    (Adjudicator.applyAll apps ops u).dueTotal d ≤ u.dueTotal d := by
  induction ops generalizing u with
  | nil => (simp? [Adjudicator.applyAll] says simp only [Adjudicator.applyAll, Std.le_refl])
  | cons hd rest ih =>
    obtain ⟨a, b, hb⟩ := hops hd List.mem_cons_self
    obtain ⟨caller, op⟩ := hd
    have hb' : op = Op.transfer a b := hb
    have hOT : OnlyTransfers rest := fun e he => hops e (List.mem_cons_of_mem _ he)
    show (Adjudicator.applyAll apps rest ((u.apply apps caller op).getD u)).dueTotal d ≤ u.dueTotal d
    rw [hb', Adjudicator.apply_transfer]
    cases hstep : u.transfer a b with
    | none => simp only [Option.getD_none]; exact ih hOT u
    | some u' =>
      simp only [Option.getD_some]
      refine le_trans (ih hOT u') ?_
      obtain ⟨o, amt, x, hf, hfind, hk, hbf, hx, hfo, hbal, hdt, howed⟩ := Adjudicator.transfer_effect hstep
      calc u'.dueTotal d ≤ u'.dueTotal d + (if d = a.address then x else 0) := Nat.le_add_right _ _
        _ = u.dueTotal d := hdt d

theorem Ahead_right_congr {sp sg sg' : Adjudicator E}
    (hfo : ∀ n, sg.finalOutcome n = sg'.finalOutcome n) (hbal : ∀ n, sg.balances.get n = sg'.balances.get n)
    (h : sp.Ahead sg) : sp.Ahead sg' := by
  have hdueeq : ∀ d, sg.dueTotal d = sg'.dueTotal d := fun d => by
    unfold Adjudicator.dueTotal; rw [hfo d]
  have howedeq : ∀ (c : FixedPart) (d : Address E), sg.owedBy c d = sg'.owedBy c d := fun c d => by
    unfold Adjudicator.owedBy; rw [hfo c.address]
  refine ⟨fun c => ?_, fun d L hL => ?_⟩
  · have hc := h.chan c
    rw [FixedPart.address_eq] at hc ⊢
    rw [hfo (Address.channel c), hbal (Address.channel c)] at hc
    exact hc
  · have hf := h.flow d L hL
    rw [hdueeq d, hbal d] at hf
    rw [show (L.map (sg.owedBy · d)) = (L.map (sg'.owedBy · d)) from
      List.map_congr_left (fun x _ => howedeq x d)] at hf
    exact hf

/-- At each address `m`, the symbolic terminal balance plus what `s` owes
    at `m` is the algorithm's value at `m` plus what the symbolic terminal
    state owes at `m`. `chainPay_dedup_total_conservation` gives the
    finalized channel
    case. Other addresses have no allocation, so `chainPay` keeps the full
    value. -/
theorem Adjudicator.symbolicTerminal_conservation (s : Adjudicator E) (order : List (Address E))
    (hord : s.IsTopologicalOrder order) (m : Address E) :
    (s.symbolicTerminal order).balances.get m + s.dueTotal m =
      s.turboValueAlong order m + (s.symbolicTerminal order).dueTotal m := by
  rw [s.symbolicTerminal_balances_get order hord m]
  unfold Adjudicator.symbolicLeftover
  cases m with
  | external e =>
    have h : s.allocationOf (.external e) = [] := allocationOf_eq_nil_of_isExternal _ rfl
    (simp? [h, Allocation.chainPay, Adjudicator.dueTotal, Adjudicator.finalOutcome] says simp only [h, List.map_nil, Allocation.chainPay, dueTotal, finalOutcome, add_zero])
  | channel c =>
    rw [← FixedPart.address_eq]
    have hfo := s.symbolicTerminal_finalOutcome order c
    cases hf : s.finalOutcome c.address with
    | none =>
      simp only [hf, Option.isSome_none, Bool.false_eq_true, if_false] at hfo
      have halloc : s.allocationOf c.address = [] := by unfold Adjudicator.allocationOf; rw [hf]
      have h1 : s.dueTotal c.address = 0 := by unfold Adjudicator.dueTotal; rw [hf]
      have h2 : (s.symbolicTerminal order).dueTotal c.address = 0 := by
        unfold Adjudicator.dueTotal; rw [hfo]
      rw [halloc, h1, h2]
      rfl
    | some outcome =>
      obtain ⟨o⟩ := outcome
      rw [hf] at hfo
      have halloc : s.allocationOf c.address = o.dedup := by
        unfold Adjudicator.allocationOf; rw [hf]
      have hsa : s.symbolicAlloc order c.address =
          (Allocation.chainPay (o.dedup.map Entry.dest) o (s.turboValueAlong order c.address)).1 := by
        unfold Adjudicator.symbolicAlloc; rw [hf, halloc]
      have hdd := (Allocation.chainPay_dedup (o.dedup.map Entry.dest) o
        (s.turboValueAlong order c.address)).1
      obtain ⟨hcons, hle⟩ := Allocation.chainPay_dedup_total_conservation
        (o.dedup.map Entry.dest) o.dedup (s.turboValueAlong order c.address)
      have hself : ∀ o' : Allocation E, o'.dedup.dedup = o'.dedup := fun o' =>
        Allocation.dedup_eq_self_of_nodup (Allocation.dedup_nodup o')
      rw [← hdd, hself, hself] at hcons hle
      simp only [Adjudicator.dueTotal, hf, hfo, Option.isSome_some, if_true, halloc, hsa]
      unfold Coins at *
      omega

/-- What `s` owes `d` through channel `c` is at most what the symbolic
    terminal state owes, plus the algorithm's credit from `c` to `d`
    (`Allocation.owed_le_chainPay_owed_add` on `c`'s deduplicated
    allocation). -/
theorem Adjudicator.symbolicTerminal_owedBy_le (s : Adjudicator E) (order : List (Address E))
    (c : FixedPart) (d : Address E) :
    s.owedBy c d ≤ (s.symbolicTerminal order).owedBy c d +
      if s.CreditsTo c.address d then
        (s.allocationOf c.address).paidTo (s.turboValueAlong order c.address) d
      else 0 := by
  have hfo := s.symbolicTerminal_finalOutcome order c
  cases hf : s.finalOutcome c.address with
  | none => unfold Adjudicator.owedBy; rw [hf]; exact Nat.zero_le _
  | some outcome =>
    obtain ⟨o⟩ := outcome
    rw [hf] at hfo
    have halloc : s.allocationOf c.address = o.dedup := by
      unfold Adjudicator.allocationOf; rw [hf]
    have hsa : s.symbolicAlloc order c.address =
        (Allocation.chainPay (o.dedup.map Entry.dest) o (s.turboValueAlong order c.address)).1 := by
      unfold Adjudicator.symbolicAlloc; rw [hf, halloc]
    have hdd := (Allocation.chainPay_dedup (o.dedup.map Entry.dest) o
      (s.turboValueAlong order c.address)).1
    have h := Allocation.owed_le_chainPay_owed_add o.dedup (Allocation.dedup_nodup o)
      (s.turboValueAlong order c.address) d
    rw [← hdd, Allocation.owed_dedup, Allocation.owed_dedup] at h
    simp only [Adjudicator.owedBy, hf, hfo, Option.isSome_some, if_true, hsa,
      Adjudicator.CreditsTo, halloc]
    (simpa? using h says simpa only [FixedPart.address_eq, Allocation.find_dedup, ge_iff_le] using h)

/-- Point 7. The symbolic terminal state is ahead of `s`. `chan`:
    `symbolicAlloc_AheadOf`. `flow`: `symbolicTerminal_conservation` turns
    the claim into "the credits of the channels in `L` are at most the
    algorithm's credits to `d`". `symbolicTerminal_owedBy_le` bounds each
    channel, and `sum_le_sum_of_support_subset` bounds the sum by the sum
    along `order` (`turboValueAlong_eq_add_credits`). -/
theorem Adjudicator.symbolicTerminal_Ahead (s : Adjudicator E) (order : List (Address E))
    (hord : s.IsTopologicalOrder order) :
    s.Ahead (s.symbolicTerminal order) := by
  set sg := s.symbolicTerminal order with hsg
  refine ⟨fun c => ?_, fun d L hL => ?_⟩
  · have hfo := s.symbolicTerminal_finalOutcome order c
    rw [← hsg] at hfo
    cases hf : s.finalOutcome c.address with
    | none => rw [hf] at hfo; rw [hfo]; exact .none
    | some outcome =>
      obtain ⟨o⟩ := outcome
      rw [hf] at hfo
      rw [hfo]
      simp only [Option.isSome_some, if_true]
      refine .some ?_
      rw [hsg, s.symbolicTerminal_balances_get order hord]
      exact s.symbolicAlloc_AheadOf order c o hf
  · let g : Address E → Coins := fun m =>
      if s.CreditsTo m d then (s.allocationOf m).paidTo (s.turboValueAlong order m) d else 0
    have hsumL : (L.map (s.owedBy · d)).sum ≤
        (L.map (sg.owedBy · d)).sum + ((L.map FixedPart.address).map g).sum := by
      rw [List.map_map, ← List.sum_map_add]
      exact List.sum_le_sum fun c _ => s.symbolicTerminal_owedBy_le order c d
    have hsupp : ((L.map FixedPart.address).map g).sum ≤
        ((order.filter (s.CreditsTo · d)).map g).sum := by
      refine sum_le_sum_of_support_subset _ _
        (hL.map fun a b h => Address.channel.inj h) (hord.1.filter _) g fun m _ hgm => ?_
      have hcr : s.CreditsTo m d = true := by
        by_contra hcr; exact hgm (by (simp? [g, hcr] says simp only [hcr, Bool.false_eq_true, ↓reduceIte, g]))
      refine List.mem_filter.mpr ⟨hord.2.2 m (Or.inr fun hnil => hgm ?_), hcr⟩
      (simp? [g, hnil, Allocation.paidTo, Allocation.dedup] says simp only [Allocation.paidTo, Allocation.dedup, hnil, Allocation.dedupFrom_nil, Allocation.payout_nil, List.filter_nil, List.map_nil, List.sum_nil, ite_self, g])
    have hfilt : ((order.filter (s.CreditsTo · d)).map g).sum =
        ((order.filter (s.CreditsTo · d)).map
          (fun c => (s.allocationOf c).paidTo (s.turboValueAlong order c) d)).sum := by
      congr 1
      refine List.map_congr_left fun m hm => ?_
      (simp? [g, (List.mem_filter.mp hm).2] says simp only [(List.mem_filter.mp hm).2, ↓reduceIte, g])
    have htv := turboValueAlong_eq_add_credits s hord.isDAG order hord d
    have hcons := s.symbolicTerminal_conservation order hord d
    rw [← hsg] at hcons
    unfold Coins at *
    omega

/-- In the transfer-only game, on a DAG of outcomes, no strategy tree
    reaches more at `n` than the Turbo Value Algorithm gives `n` along a
    topological order. Every network state, with no reachability premise:
    the state after a deposit is not reachable in the transfer-only game,
    and `deposit_bounds_value` reads its value. -/
theorem turboValueAlong_upper_bound (apps : Apps E) {p : Participant} (T : Threat E p)
    (hT : T.TransfersOnly) (net : NetworkState E p) (n : Address E)
    {order : List (Address E)} (hord : net.chain.IsTopologicalOrder order) {x : Coins}
    (h : UnbeatableIn apps T HonestMove.IsTransfer (fun net' => x ≤ net'.chain.balances.get n)
      net) :
    x ≤ net.chain.turboValueAlong order n := by
  -- `sg` is ahead of every state `p`'s strategy reaches: the adversary's
  -- and `p`'s transfers move nothing on `sg`
  -- (`symbolicTerminal_applyAll_unmoved`), and `Ahead.applyAll_sublist`
  -- keeps the start state ahead. `dueTotal` at `n` never rises
  -- (`dueTotal_applyAll_le`). At the end, `Ahead.flow` at `n` with
  -- `symbolicTerminal_conservation` bounds the balance by the value.
  set sg := net.chain.symbolicTerminal order with hsg
  have hcons := net.chain.symbolicTerminal_conservation order hord n
  rw [← hsg] at hcons
  suffices hsuff : ∀ {net2 : NetworkState E p},
      UnbeatableIn apps T HonestMove.IsTransfer (fun net' => x ≤ net'.chain.balances.get n) net2 →
      net2.chain.Ahead sg → net2.chain.dueTotal n ≤ net.chain.dueTotal n →
      x ≤ net.chain.turboValueAlong order n from
    hsuff h (net.chain.symbolicTerminal_Ahead order hord) le_rfl
  intro net2 h2
  induction h2 with
  | @done net2 hgoal =>
    intro hag hdt
    have hflow := hag.flow n [] List.nodup_nil
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hflow
    unfold Coins at *
    omega
  | @move net2 m hallow hfeas _ ih =>
    intro hag hdt
    cases m with
    | wait dt => exact (hallow : False).elim
    | react r =>
      obtain ⟨a, b, hc, hs⟩ := hallow
      obtain ⟨calls, sends⟩ := r
      simp only at hc hs
      subst hc hs
      obtain ⟨net', hround⟩ := Threat.Round.exists T hfeas
      have hih := ih net' hround
      have hm : (HonestMove.react ⟨[Op.transfer a b], []⟩ : HonestMove E) =
          HonestMove.chain (.transfer a b) := rfl
      rw [hm, NetworkState.applyHonest_chain] at hih
      rw [hm] at hround
      obtain ⟨ops, hall, -, hchain⟩ := hround.transfer_applyAll hT
      have hmatch := symbolicTerminal_applyAll_unmoved net.chain order hord apps _ hall sg
        (fun _ => rfl) (fun _ => rfl)
      rw [hchain] at hih
      exact hih (Ahead_right_congr hmatch.1 hmatch.2
          (Adjudicator.Ahead.applyAll_sublist apps (List.Sublist.refl _) hall hag))
        (le_trans (dueTotal_applyAll_le apps hall _ n) hdt)

/-- Nitro-33, Nitro-34, Nitro-32. Nitro:836-837: "it is impossible to find a strategy
    that gives any node a value higher than allocated by this algorithm."
    In the transfer-only game (Nitro:779-781), on a DAG of outcomes. -/
theorem turbo_value_upper_bound (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : Nitro.ReachableParticipant apps T)
    (hdag : net.state.chain.IsDAG) (n : Address E) (v x : Coins)
    (hv : net.state.chain.TurboValue n v)
    (h : CanObtainIn apps T HonestMove.IsTransfer n x net.state) : x ≤ v := by
  obtain ⟨order, hord, rfl⟩ := hv
  exact turboValueAlong_upper_bound apps T hT net.state n hord h

/-- The Turbo Value Algorithm, run as transfers. Paying every node of a node
    list, in list order, to each destination of its own allocation gives
    every external destination the algorithm's value along that list
    (`Adjudicator.turboValues`). Turbo scope makes each payout a legal
    transfer (a ledger source, a fundable destination, no guarantee), and
    the DAG excludes a channel that pays itself. -/
theorem TurboOutcomeNetwork.transfers_reach_turboValues (s : TurboOutcomeNetwork E)
    (apps : Apps E) (q : Participant) (order : List (Address E))
    (hord : s.chain.IsTopologicalOrder order) :
    ∃ ops, OnlyTransfers ops ∧ ∀ d : E,
      (Adjudicator.applyAll apps ops s.chain).balances.get (.external d) =
        s.chain.turboValueAlong order (.external d) := by
  obtain ⟨⟨s, hdag⟩, hscope⟩ := s
  -- `chainPay` never raises what an allocation owes.
  have hle : ∀ (ds : List (Address E)) (og : Allocation E) (hg : Coins) (m : Address E),
      (Allocation.chainPay ds og hg).1.owed m ≤ og.owed m := by
    intro ds
    induction ds with
    | nil => intro og hg m; exact le_rfl
    | cons e ds ih =>
      intro og hg m
      rw [Allocation.chainPay_cons]
      split
      · refine le_trans (ih _ _ m) ?_
        rw [Allocation.owed_reduceOwed]
        split_ifs with h
        · rw [h]
          exact Nat.sub_le _ _
        · exact le_rfl
      · exact ih _ _ m
  -- What an allocation owes `m` is what it still owes after paying its own
  -- destinations, plus its payment to `m`.
  have hsplit : ∀ (og : Allocation E), (og.map Entry.dest).Nodup → ∀ (hg : Coins) (m : Address E),
      og.owed m = (Allocation.chainPay (og.map Entry.dest) og hg).1.owed m +
        if (og.find m).elim false (fun e => !e.item.isGuarantee) then og.paidTo hg m else 0 := by
    intro og hnd hg m
    cases hf : og.find m with
    | none =>
      have hm : m ∉ og.map Entry.dest := Allocation.find_eq_none.mp hf
      (simp? [Allocation.owed, Allocation.chainPay_find_unchanged _ og hg m hm, hf] says simp only [Allocation.owed, hf, Option.map_none, Option.getD_none, Allocation.chainPay_find_unchanged _ og hg m hm, Option.elim_none, Bool.false_eq_true, ↓reduceIte, add_zero])
    | some e =>
      obtain ⟨de, item⟩ := e
      have hde : de = m := Allocation.find_dest hf
      subst hde
      cases item with
      | alloc amt =>
        have h := Allocation.chainPay_owed_eq og hnd hg de amt hf
        have h1 := hle (og.map Entry.dest) og hg de
        have hg' : ((some (⟨de, .alloc amt⟩ : Entry E)).elim false
            (fun e => !e.item.isGuarantee)) = true := rfl
        rw [if_pos hg']
        unfold Coins at *
        omega
      | guarantee x ps =>
        have hg' : ¬ (((some (⟨de, .guarantee x ps⟩ : Entry E)).elim false
            (fun e => !e.item.isGuarantee)) = true) := by (simp? [Item.isGuarantee] says simp only [Item.isGuarantee, Option.elim_some, Bool.not_true, Bool.false_eq_true, not_false_eq_true])
        rw [if_neg hg', Nat.add_zero, Allocation.chainPay_owed_of_find_guarantee _ og hg de x ps hf]
  -- Transfers from `c` to each destination of `ds`, in order, move what
  -- `chainPay` computes.
  have hrun : ∀ (c : FixedPart) (ds : List (Address E)) (o : Allocation E) (u : Adjudicator E),
      (∀ b ∈ ds, c.kind = .ledger ∧ b.fundable = true ∧ b ≠ c.address) →
      u.finalOutcome c.address = some (.allocation o) →
      (∀ c' : FixedPart, c' ≠ c →
        (Adjudicator.applyAll apps (ds.map fun b => (q, Op.transfer c b)) u).finalOutcome
          c'.address = u.finalOutcome c'.address) ∧
      (∀ m, m ≠ c.address →
        (Adjudicator.applyAll apps (ds.map fun b => (q, Op.transfer c b)) u).balances.get m +
          (Allocation.chainPay ds o (u.balances.get c.address)).1.owed m =
        u.balances.get m + o.owed m) := by
    intro c ds
    induction ds with
    | nil => intro o u _ _; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    | cons b ds ih =>
      intro o u hds hfo
      obtain ⟨hk, hfund, hbc⟩ := hds b List.mem_cons_self
      have hds' : ∀ b' ∈ ds, c.kind = .ledger ∧ b'.fundable = true ∧ b' ≠ c.address :=
        fun b' hb' => hds b' (List.mem_cons_of_mem _ hb')
      simp only [List.map_cons, Adjudicator.applyAll, Adjudicator.apply_transfer]
      rw [Allocation.chainPay_cons]
      cases hfind : o.find b with
      | none =>
        have ht : u.transfer c b = none := by
          rw [Adjudicator.transfer, if_pos ⟨hk, hfund⟩, hfo]
          (simp? [hfind] says simp only [hfind])
        simp only [ht, Option.getD_none]
        exact ih o u hds' hfo
      | some e =>
        obtain ⟨eb, item⟩ := e
        cases item with
        | guarantee y ps =>
          have ht : u.transfer c b = none := by
            rw [Adjudicator.transfer, if_pos ⟨hk, hfund⟩, hfo]
            (simp? [hfind] says simp only [hfind])
          simp only [ht, Option.getD_none]
          exact ih o u hds' hfo
        | alloc amt =>
          cases ht : u.transfer c b with
          | none =>
            exfalso
            rw [Adjudicator.transfer, if_pos ⟨hk, hfund⟩, hfo] at ht
            (simp? [hfind] at ht says simp only [hfind, FixedPart.address_eq, Adjudicator.payTo_balances, Adjudicator.setStatus_balances, Adjudicator.payTo_held, Adjudicator.setStatus_held, Adjudicator.payTo_status, Adjudicator.payTo_now, Adjudicator.setStatus_now, reduceCtorEq] at ht)
          | some u1 =>
            simp only [Option.getD_some]
            obtain ⟨o', amt', x, hf', -, -, -, hx, hfoeff, hbal, -, -⟩ :=
              Adjudicator.transfer_effect ht
            rw [hfo] at hf'
            have hoo : o' = o := by
              injection hf' with h
              injection h with h
              exact h.symm
            subst hoo
            have hfo1 : u1.finalOutcome c.address = some (.allocation (o'.reduceOwed b x)) := by
              have h := hfoeff c
              rw [if_pos rfl] at h
              exact h
            have hc1 : u1.balances.get c.address = u.balances.get c.address - x := by
              have h := hbal c.address
              rw [if_pos rfl, if_neg (Ne.symm hbc)] at h
              unfold Coins at *
              omega
            obtain ⟨ih1, ih2⟩ := ih (o'.reduceOwed b x) u1 hds' hfo1
            refine ⟨fun c' hc' => (ih1 c' hc').trans ?_, fun m hm => ?_⟩
            · have h := hfoeff c'
              rw [if_neg hc'] at h
              exact h
            · have h2 := ih2 m hm
              have hbm := hbal m
              rw [if_neg hm] at hbm
              have hxo : x ≤ o'.owed b := hx ▸ Allocation.paidTo_le_owed _ _ _
              rw [hc1] at h2
              rw [← hx]
              rw [Allocation.owed_reduceOwed] at h2
              by_cases hmb : m = b
              · subst hmb
                rw [if_pos rfl] at h2 hbm
                unfold Coins at *
                omega
              · rw [if_neg hmb] at h2 hbm
                unfold Coins at *
                omega
  -- The whole node list, by induction: an unprocessed node, or an external
  -- one, holds the algorithm's running value; an unprocessed channel keeps
  -- its outcome.
  have hmain : ∀ (L : List (Address E)), L.Nodup → ∀ (u : Adjudicator E) (V : Balances E),
      (∀ c : FixedPart, (c.address : Address E) ∈ L →
        u.finalOutcome c.address = s.finalOutcome c.address) →
      (∀ m, (m ∈ L ∨ m.isExternal = true) → u.balances.get m = V.get m) →
      ∃ ops, OnlyTransfers ops ∧ ∀ d : E,
        (Adjudicator.applyAll apps ops u).balances.get (.external d) =
          (s.turboValues L V).get (.external d) := by
    intro L
    induction L with
    | nil =>
      intro _ u V _ hV
      exact ⟨[], fun _ h => absurd h List.not_mem_nil, fun d => hV _ (Or.inr rfl)⟩
    | cons n rest ih =>
      intro hnd u V hfo hV
      obtain ⟨hnr, hndr⟩ := List.nodup_cons.mp hnd
      by_cases hnil : s.allocationOf n = []
      · obtain ⟨ops, hops, hres⟩ := ih hndr u V
          (fun c hc => hfo c (List.mem_cons_of_mem _ hc))
          (fun m hm => hV m (hm.imp_left (List.mem_cons_of_mem _)))
        refine ⟨ops, hops, fun d => ?_⟩
        rw [hres d]
        simp only [Adjudicator.turboValues, hnil, payoutValues]
      · obtain ⟨c, rfl⟩ : ∃ c : FixedPart, n = c.address := by
          cases n with
          | external e => exact absurd (allocationOf_eq_nil_of_isExternal s rfl) hnil
          | channel c => exact ⟨c, rfl⟩
        obtain ⟨o, hfo_s, halloc⟩ : ∃ o, s.finalOutcome c.address = some (.allocation o) ∧
            s.allocationOf c.address = o.dedup := by
          unfold Adjudicator.allocationOf at hnil ⊢
          cases hf : s.finalOutcome c.address with
          | none => rw [hf] at hnil; exact absurd rfl hnil
          | some out => obtain ⟨o⟩ := out; exact ⟨o, rfl, rfl⟩
        have hk : c.kind = .ledger := hscope.1 c hnil
        have hdsok : ∀ b ∈ o.dedup.map Entry.dest,
            c.kind = .ledger ∧ b.fundable = true ∧ b ≠ c.address := by
          intro b hb
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
          rw [← halloc] at he
          obtain ⟨-, hled⟩ := hscope.2 c.address e he
          refine ⟨hk, ?_, ?_⟩
          · cases hed : e.dest with
            | external _ => rfl
            | channel c' => (simp? [Address.fundable, hled c' hed] says simp only [Address.fundable, hled c' hed, decide_true])
          · intro hcyc
            have hedge : s.Edge c.address c.address :=
              ⟨Address.isExternal_channel c, e, he, hcyc⟩
            exact hdag.irrefl _ (Relation.TransGen.single hedge)
        have hu_c : u.finalOutcome c.address = some (.allocation o) :=
          (hfo c List.mem_cons_self).trans hfo_s
        obtain ⟨hr1, hr2⟩ := hrun c (o.dedup.map Entry.dest) o u hdsok hu_c
        have hfo1 : ∀ c' : FixedPart, (c'.address : Address E) ∈ rest →
            (Adjudicator.applyAll apps ((o.dedup.map Entry.dest).map fun b => (q, Op.transfer c b))
              u).finalOutcome c'.address = s.finalOutcome c'.address := by
          intro c' hc'
          have hne : c' ≠ c := fun h => hnr (h ▸ hc')
          rw [hr1 c' hne]
          exact hfo c' (List.mem_cons_of_mem _ hc')
        have hV1 : ∀ m, (m ∈ rest ∨ m.isExternal = true) →
            (Adjudicator.applyAll apps ((o.dedup.map Entry.dest).map fun b => (q, Op.transfer c b))
              u).balances.get m =
            (payoutValues V (V.get c.address) (s.allocationOf c.address)).get m := by
          intro m hm
          have hmc : m ≠ c.address := by
            rintro rfl
            rcases hm with h | h
            · exact hnr h
            · exact absurd h (by (simp? says simp only [FixedPart.address_eq, Address.isExternal_channel, Bool.false_eq_true, not_false_eq_true]))
          have h2 := hr2 m hmc
          have hVm := hV m (hm.imp_left (List.mem_cons_of_mem _))
          have hVc := hV c.address (Or.inl List.mem_cons_self)
          have howm : (Allocation.chainPay (o.dedup.map Entry.dest) o
              (u.balances.get c.address)).1.owed m =
              (Allocation.chainPay (o.dedup.map Entry.dest) o.dedup
                (u.balances.get c.address)).1.owed m := by
            rw [← (Allocation.chainPay_dedup _ o _).1, Allocation.owed_dedup]
          rw [howm, hVc, hVm, ← Allocation.owed_dedup o m] at h2
          have hsp := hsplit o.dedup (Allocation.dedup_nodup o) (V.get c.address) m
          rw [payoutValues_get_eq_add_paidTo _ _ _ (allocationOf_nodup s c.address), halloc]
          generalize (if (o.dedup.find m).elim false (fun e => !e.item.isGuarantee) then
            o.dedup.paidTo (V.get c.address) m else 0) = g at hsp ⊢
          unfold Coins at *
          omega
        obtain ⟨ops, hops, hres⟩ := ih hndr _ _ hfo1 hV1
        refine ⟨((o.dedup.map Entry.dest).map fun b => (q, Op.transfer c b)) ++ ops, ?_,
          fun d => ?_⟩
        · intro e he
          rcases List.mem_append.mp he with he | he
          · obtain ⟨b, -, rfl⟩ := List.mem_map.mp he
            exact ⟨c, b, rfl⟩
          · exact hops e he
        · rw [Adjudicator.applyAll_append, hres d]
          rfl
  obtain ⟨ops, hops, hres⟩ := hmain order hord.1 s s.balances (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨ops, hops, hres⟩

/-- In the transfer-only game, on a Turbo outcome network, the value at an
    external destination is the Turbo Value Algorithm's value: `p` plays the
    algorithm's own transfers (`TurboOutcomeNetwork.transfers_reach_turboValues`,
    `turbo_replay_unbeatable`), and no strategy gets more
    (`turboValueAlong_upper_bound`). Every network state, with no
    reachability premise, as `turboValueAlong_upper_bound`. -/
theorem turboValueAlong_valueIn (apps : Apps E) {p : Participant} (T : Threat E p)
    (hT : T.TransfersOnly) (net : NetworkState E p) (hturbo : net.chain.IsTurboOutcomeNetwork)
    (d : E) {v : Coins} (hv : net.chain.TurboValue (.external d) v) :
    ValueIn apps T HonestMove.IsTransfer d net v := by
  obtain ⟨order, hord, rfl⟩ := hv
  obtain ⟨ops, hops, hres⟩ :=
    TurboOutcomeNetwork.transfers_reach_turboValues ⟨⟨_, hturbo.1⟩, hturbo.2⟩ apps p order hord
  exact ⟨turbo_replay_unbeatable apps T hT d _ ops hops net.chain net (Adjudicator.Ahead.refl _)
      (hres d).ge,
    fun _ hz => turboValueAlong_upper_bound apps T hT net _ hord hz⟩

/-- Nitro-33, Nitro-35, Nitro-18. Nitro:837-839: "It is also not hard to construct a
    strategy for a node to obtain the value allocated by the algorithm, if
    necessary by actually implementing the algorithm up until that node." In
    the transfer-only game, for an external destination. -/
theorem turbo_value_achievable (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : Nitro.ReachableParticipant apps T)
    (hturbo : net.state.chain.IsTurboOutcomeNetwork) (d : E) (v : Coins)
    (hv : net.state.chain.TurboValue (.external d) v) :
    CanObtainIn apps T HonestMove.IsTransfer (.external d) v net.state := by
  obtain ⟨order, hord, rfl⟩ := hv
  obtain ⟨ops, hops, hres⟩ :=
    TurboOutcomeNetwork.transfers_reach_turboValues ⟨⟨_, hturbo.1⟩, hturbo.2⟩ apps p order hord
  exact turbo_redistribution_unbeatable apps T B hT hcap net hturbo.1 ops hops d _ (hres d).ge

/-- Nitro-18, Nitro-33, Nitro-34, Nitro-35. Nitro:482-484 with Nitro:835-839: on a Turbo DAG
    the value at `d` in the transfer-only game is the algorithm's value of
    `d`. -/
theorem turbo_value_is_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : Nitro.ReachableParticipant apps T)
    (hturbo : net.state.chain.IsTurboOutcomeNetwork) (d : E) (v : Coins)
    (hv : net.state.chain.TurboValue (.external d) v) :
ValueIn apps T HonestMove.IsTransfer d net.state v :=
  ⟨turbo_value_achievable apps T B hT hcap net hturbo d v hv,
    fun y hy => turbo_value_upper_bound apps T B hT hcap net hturbo.1 (.external d) v y hv hy⟩

/-- A deposit changes no allocation, so it changes no edge of the outcome
    network. -/
theorem Adjudicator.edge_deposit {s s' : Adjudicator E} {a : Address E} {e y : Coins}
    (hd : s.deposit a e y = some s') : s'.Edge = s.Edge := by
  funext n m
  simp only [Adjudicator.Edge, Adjudicator.allocationOf_deposit hd]

/-- A deposit keeps a Turbo outcome network: the network reads only the
    allocations, and a deposit changes none. -/
theorem Adjudicator.IsTurboOutcomeNetwork.deposit {s s' : Adjudicator E} {a : Address E}
    {e y : Coins} (h : s.IsTurboOutcomeNetwork) (hd : s.deposit a e y = some s') :
    s'.IsTurboOutcomeNetwork := by
  refine ⟨?_, ?_⟩
  · unfold Adjudicator.IsDAG
    rw [Adjudicator.edge_deposit hd]
    exact h.1
  · unfold Adjudicator.TurboScope
    simp only [Adjudicator.allocationOf_deposit hd]
    exact h.2

/-- Nitro-31. Nitro:785-787: "a deposit into the system cannot reduce the value of
    any address and cannot increase the value of any address by more than the
    value of the deposit." Design decision 2026-11-01: the claim is read in
    the scope the paper gives it, the transfer-only game (Nitro:779-781,
    "strategies and counter-strategies involving transfer operations only")
    on a Turbo outcome network (Nitro:790-795, a DAG), as for
    `turbo_value_achievable`. Both values are the Turbo Value Algorithm's
    value along one order (`turboValueAlong_valueIn`). A deposit changes no
    allocation and no edge, so a topological order of the chain after the
    deposit is one of the chain before it, and along that order the deposit
    raises the value by 0 to `y` (`Adjudicator.turboValueAlong_deposit`). -/
theorem deposit_bounds_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (hT : T.TransfersOnly) (net : Nitro.ReachableParticipant apps T)
    (hturbo : net.state.chain.IsTurboOutcomeNetwork)
    (c : FixedPart) (d : E) (y x x' : Coins)
    (s' : Adjudicator E) (e : Coins) (hd : net.state.chain.deposit c.address e y = some s')
    (hv : ValueIn apps T HonestMove.IsTransfer d net.state x)
    (hv' : ValueIn apps T HonestMove.IsTransfer d { net.state with chain := s' } x') :
    x ≤ x' ∧ x' ≤ x + y := by
  obtain ⟨-, -, hb, -, -, -⟩ := Adjudicator.deposit_some hd
  have hturbo' : s'.IsTurboOutcomeNetwork := hturbo.deposit hd
  obtain ⟨order, hord'⟩ := exists_valid_topo_order s' hturbo'.1
  have hord : net.state.chain.IsTopologicalOrder order := by
    refine ⟨hord'.1, fun n m he => hord'.2.1 n m (by rw [Adjudicator.edge_deposit hd]; exact he),
      fun n hn => hord'.2.2 n ?_⟩
    rcases hn with hbal | hal
    · left
      rw [hb, Balances.get_add]
      split
      · next h =>
        rw [h] at hbal
        unfold Coins at *
        omega
      · exact hbal
    · right
      rw [Adjudicator.allocationOf_deposit hd]
      exact hal
  obtain ⟨hlo, hhi⟩ := Adjudicator.turboValueAlong_deposit hd hord d
  have h1 := turboValueAlong_valueIn apps T hT net.state hturbo d ⟨order, hord, rfl⟩
  have h2 : ValueIn apps T HonestMove.IsTransfer d { net.state with chain := s' }
      (s'.turboValueAlong order (.external d)) :=
    turboValueAlong_valueIn apps T hT _ hturbo' d ⟨order, hord', rfl⟩
  have hx1 := h1.2 x hv.1
  have hx2 := hv.2 _ h1.1
  have hx3 := h2.2 x' hv'.1
  have hx4 := hv'.2 _ h2.1
  unfold Coins at *
  omega

/-- `OnlyTransfers` never changes which destinations a channel's own
    allocation lists (only the amounts move). -/
theorem allocationOf_dest_applyAll (apps : Apps E) :
    ∀ (ops : List (Participant × Op E)), OnlyTransfers ops →
    ∀ (u : Adjudicator E) (n : Address E),
      ((Adjudicator.applyAll apps ops u).allocationOf n).map Entry.dest =
        (u.allocationOf n).map Entry.dest := by
  intro ops
  induction ops with
  | nil => intro _ u n; rfl
  | cons hd rest ih =>
    intro hops u n
    obtain ⟨a, b, hb⟩ := hops hd List.mem_cons_self
    obtain ⟨caller, op⟩ := hd
    have hb' : op = Op.transfer a b := hb
    have hOT : OnlyTransfers rest := fun e he => hops e (List.mem_cons_of_mem _ he)
    show ((Adjudicator.applyAll apps rest ((u.apply apps caller op).getD u)).allocationOf n).map
      Entry.dest = (u.allocationOf n).map Entry.dest
    rw [hb', Adjudicator.apply_transfer]
    cases hstep : u.transfer a b with
    | none => simp only [Option.getD_none]; exact ih hOT u n
    | some u' =>
      simp only [Option.getD_some]
      rw [ih hOT u' n]
      obtain ⟨o, amt, x, hf, hfind, -, -, -, hfo, -, -, -⟩ := Adjudicator.transfer_effect hstep
      cases n with
      | external e => (simp? [Adjudicator.allocationOf, Adjudicator.finalOutcome] says simp only [Adjudicator.allocationOf, Adjudicator.finalOutcome, List.map_nil])
      | channel c =>
        have hc := hfo c
        rw [FixedPart.address_eq] at hc
        by_cases hca : c = a
        · subst hca
          rw [FixedPart.address_eq] at hf
          unfold Adjudicator.allocationOf
          rw [hc, if_pos rfl, hf]
          dsimp only
          rw [Allocation.dedup_reduceOwed, Allocation.reduceOwed_map_dest]
        · unfold Adjudicator.allocationOf
          rw [hc, if_neg hca]

theorem Edge_applyAll_iff (apps : Apps E) {ops : List (Participant × Op E)} (hops : OnlyTransfers ops)
    (s : Adjudicator E) (n d : Address E) :
    (Adjudicator.applyAll apps ops s).Edge n d ↔ s.Edge n d := by
  have hdest := allocationOf_dest_applyAll apps ops hops s n
  unfold Adjudicator.Edge
  constructor
  · rintro ⟨hext, e, he, hed⟩
    refine ⟨hext, ?_⟩
    have hmem : d ∈ ((Adjudicator.applyAll apps ops s).allocationOf n).map Entry.dest :=
      List.mem_map.mpr ⟨e, he, hed⟩
    rw [hdest] at hmem
    obtain ⟨e', he', hed'⟩ := List.mem_map.mp hmem
    exact ⟨e', he', hed'⟩
  · rintro ⟨hext, e, he, hed⟩
    refine ⟨hext, ?_⟩
    have hmem : d ∈ (s.allocationOf n).map Entry.dest := List.mem_map.mpr ⟨e, he, hed⟩
    rw [← hdest] at hmem
    obtain ⟨e', he', hed'⟩ := List.mem_map.mp hmem
    exact ⟨e', he', hed'⟩

theorem IsDAG_applyAll_iff (apps : Apps E) {ops : List (Participant × Op E)} (hops : OnlyTransfers ops)
    (s : Adjudicator E) :
    (Adjudicator.applyAll apps ops s).IsDAG ↔ s.IsDAG := by
  unfold Adjudicator.IsDAG Acyclic
  constructor
  · intro h
    refine ⟨fun n hn => h.irrefl n ?_⟩
    exact Relation.TransGen.mono (fun x y hxy => (Edge_applyAll_iff apps hops s x y).mpr hxy) n n hn
  · intro h
    refine ⟨fun n hn => h.irrefl n ?_⟩
    exact Relation.TransGen.mono (fun x y hxy => (Edge_applyAll_iff apps hops s x y).mp hxy) n n hn

/-- An entry of `o.reduceOwed d x` is an entry of `o`, or an entry of `o`
    with the same destination and an `alloc` item. -/
theorem Allocation.mem_reduceOwed {o : Allocation E} {d : Address E} {x : Coins} {e : Entry E}
    (he : e ∈ o.reduceOwed d x) :
    e ∈ o ∨ ∃ e₀ ∈ o, e.dest = e₀.dest ∧ ∃ k, e.item = .alloc k := by
  induction o with
  | nil => exact absurd he List.not_mem_nil
  | cons f rest ih =>
    rw [Allocation.reduceOwed_cons] at he
    by_cases hf : f.dest = d
    · rw [if_pos hf] at he
      rcases List.mem_cons.mp he with rfl | hr
      · exact .inr ⟨f, List.mem_cons_self, rfl, _, rfl⟩
      · exact .inl (List.mem_cons_of_mem f hr)
    · rw [if_neg hf] at he
      rcases List.mem_cons.mp he with rfl | hr
      · exact .inl List.mem_cons_self
      · rcases ih hr with h1 | ⟨e₀, he₀, hd, hk⟩
        · exact .inl (List.mem_cons_of_mem f h1)
        · exact .inr ⟨e₀, List.mem_cons_of_mem f he₀, hd, hk⟩

/-- A successful `transfer` keeps a state in Turbo scope: it keeps every
    destination list and writes only `alloc` items. -/
theorem Adjudicator.TurboScope.transfer {s s' : Adjudicator E} {a : FixedPart} {b : Address E}
    (hs : s.TurboScope) (h : s.transfer a b = some s') : s'.TurboScope := by
  refine ⟨fun c hc => hs.1 c fun h0 => hc ?_, fun n e he => ?_⟩
  · have hd := Adjudicator.allocationOf_dest_transfer h (.channel c)
    rw [h0, List.map_nil] at hd
    exact List.map_eq_nil_iff.mp hd
  · by_cases hn : n = a.address
    · obtain ⟨x, hx⟩ := Adjudicator.allocationOf_transfer_self h
      rw [hn, hx] at he
      rcases Allocation.mem_reduceOwed he with he' | ⟨e₀, he₀, hd, k, hk⟩
      · exact hs.2 _ e he'
      · exact ⟨by rw [hk]; rfl, fun c hc => (hs.2 _ e₀ he₀).2 c (hd.symm.trans hc)⟩
    · rw [Adjudicator.allocationOf_transfer_ne h hn] at he
      exact hs.2 n e he

/-- A successful `transfer` keeps a Turbo outcome network. -/
theorem Adjudicator.IsTurboOutcomeNetwork.transfer {s s' : Adjudicator E} {a : FixedPart}
    {b : Address E} (hs : s.IsTurboOutcomeNetwork) (h : s.transfer a b = some s') :
    s'.IsTurboOutcomeNetwork :=
  ⟨hs.1.transfer h, hs.2.transfer h⟩

/-- The paying channel of a successful `transfer` has a nonempty allocation. -/
theorem Adjudicator.allocationOf_transfer_source {s s' : Adjudicator E} {a : FixedPart}
    {b : Address E} (h : s.transfer a b = some s') : s.allocationOf a.address ≠ [] := by
  obtain ⟨o, _, _, hf, hfind, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_effect h
  intro h0
  unfold Adjudicator.allocationOf at h0
  rw [hf] at h0
  change o.dedup = [] at h0
  have h2 := Allocation.find_dedup o b
  rw [h0, hfind] at h2
  cases h2

/-- A topological order of the state after a successful `transfer` lists the
    paying channel, and it is a topological order of the state before the
    transfer: the edges agree, and every node the earlier state must list is
    a node of the later state (a transfer lowers no balance but the paying
    channel's, which has an allocation). -/
theorem Adjudicator.IsTopologicalOrder.of_transfer {s s' : Adjudicator E} {a : FixedPart}
    {b : Address E} (h : s.transfer a b = some s') {order : List (Address E)}
    (hord : s'.IsTopologicalOrder order) :
    a.address ∈ order ∧ s.IsTopologicalOrder order := by
  obtain ⟨hnd, hedge, hmem⟩ := hord
  have hne : ∀ m, s.allocationOf m ≠ [] → s'.allocationOf m ≠ [] := by
    intro m hm h0
    have hd := Adjudicator.allocationOf_dest_transfer h m
    rw [h0, List.map_nil] at hd
    exact hm (List.map_eq_nil_iff.mp hd.symm)
  have ha : a.address ∈ order := hmem _ (.inr (hne _ (Adjudicator.allocationOf_transfer_source h)))
  refine ⟨ha, hnd, fun n m hnm => hedge n m ((Adjudicator.Edge_transfer_iff h n m).mpr hnm),
    fun n hn => ?_⟩
  rcases hn with hb | hn
  · by_cases hna : n = a.address
    · rw [hna]; exact ha
    · obtain ⟨_, _, _, -, -, -, -, -, -, hbal, -, -⟩ := Adjudicator.transfer_effect h
      have h1 := hbal n
      rw [if_neg hna, Nat.add_zero] at h1
      refine hmem n (.inl fun h0 => hb ?_)
      rw [h0] at h1
      exact (Nat.eq_zero_of_add_eq_zero h1.symm).1
  · exact hmem n (.inr (hne n hn))

/-- A value is unique: it is the maximum of what `p` can obtain. -/
theorem ValueIn.eq {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {d : E} {net : NetworkState E p} {x y : Coins}
    (hx : ValueIn apps T allowed d net x) (hy : ValueIn apps T allowed d net y) : x = y :=
  Nat.le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)

/-- Nitro-31. Nitro:787-789: "Withdrawals can only occur from participant
    addresses and are the only way funds can leave these addresses, so cannot
    affect values elsewhere." go-nitro has no withdrawal: a payout is the
    transfer of a finalized entry to an external destination `q`. Design
    decision 2026-11-01: the claim has the scope of its own paragraph, the
    transfer-only game (Nitro:779-781) on a Turbo outcome network
    (Nitro:790-795). There the value at `d` is the Turbo value
    (`turbo_value_is_value`, on both chains: the payout is `p`'s own landed
    call, so the state after it is reachable), and the payout leaves the
    Turbo value at every external destination unchanged
    (`Adjudicator.turboValueAlong_transfer`). Renamed from
    `payout_to_other_affects_only_owner`: the
    statement covers every destination. -/
theorem payout_preserves_value (apps : Apps E) {p : Participant} (T : Threat E p)
    (B : Bounds apps p T) (hT : T.TransfersOnly) (hcap : T.CapableTransfers)
    (net : Nitro.ReachableParticipant apps T)
    (hturbo : net.state.chain.IsTurboOutcomeNetwork) (d q : E)
    (a : FixedPart) (s' : Adjudicator E) (h : net.state.chain.transfer a (.external q) = some s')
    (x : Coins) :
    ValueIn apps T HonestMove.IsTransfer d net.state x ↔
      ValueIn apps T HonestMove.IsTransfer d { net.state with chain := s' } x := by
  have hstep : (Nitro.participant apps T).step net.state { net.state with chain := s' } := by
    refine Or.inr (Or.inl ⟨.transfer a (.external q), (fun _ hss => by cases hss), ?_⟩)
    rw [NetworkState.applyAdv_land_some apps (by rw [Adjudicator.apply_transfer]; exact h)]
    rfl
  have hturbo' : s'.IsTurboOutcomeNetwork := hturbo.transfer h
  obtain ⟨order, hord⟩ := exists_valid_topo_order s' hturbo'.1
  obtain ⟨ha, hord0⟩ := hord.of_transfer h
  have H' := turbo_value_is_value apps T B hT hcap (net.step hstep) hturbo' d _ ⟨order, hord, rfl⟩
  have H := turbo_value_is_value apps T B hT hcap net hturbo d _
    ⟨order, hord0, (Adjudicator.turboValueAlong_transfer h hord ha (fun h => by cases h)).symm⟩
  exact ⟨fun hx => (hx.eq H) ▸ H', fun hx => (hx.eq H') ▸ H⟩

/-- An exhausted DAG state is a fixed point of `transfer`: the call that
    "succeeds" moves zero coins, so the state (read through `finalOutcome`
    and `balances.get`) does not move either. -/
theorem transfer_exhausted_fixed {t : Adjudicator E} (hdag : t.IsDAG) (hexh : t.TransferExhausted)
    {a : FixedPart} {b : Address E} {t' : Adjudicator E} (h : t.transfer a b = some t') :
    (∀ n, t'.finalOutcome n = t.finalOutcome n) ∧ (∀ n, t'.balances.get n = t.balances.get n) := by
  obtain ⟨o, amt, x, hf, hfind, hk, hbfund, hx, hfo, hbal, -, -⟩ := Adjudicator.transfer_effect h
  have hbne : b ≠ (a.address : Address E) := by
    intro hcontra
    have hbmem : b ∈ o.dedup.map Entry.dest := by
      have h1 : o.dedup.find b ≠ none := by rw [Allocation.find_dedup, hfind]; (simp? says simp only [ne_eq, reduceCtorEq, not_false_eq_true])
      by_contra hcon
      exact h1 (Allocation.find_eq_none.mpr hcon)
    have hedge : t.Edge a.address b := by
      refine ⟨?_, ?_⟩
      · rw [hcontra, FixedPart.address_eq]; exact Address.isExternal_channel a
      · unfold Adjudicator.allocationOf
        rw [hf]
        obtain ⟨e, he, hed⟩ := List.mem_map.mp hbmem
        exact ⟨e, he, hed⟩
    rw [hcontra] at hedge
    exact hdag.irrefl a.address (Relation.TransGen.single hedge)
  have hxeq : t'.balances.get b = t.balances.get b + x := by
    have hb := hbal b
    rw [FixedPart.address_eq] at hbne
    (simpa? [hbne] using hb says simpa only [FixedPart.address_eq, hbne, ↓reduceIte, add_zero] using hb)
  have hsame : t'.balances.get b = t.balances.get b := by
    rw [hexh a b t' h]
  have hx0 : x = 0 := by
    rw [hsame] at hxeq
    unfold Coins at *
    omega
  refine ⟨fun n => ?_, fun n => ?_⟩
  · cases n with
    | external e => (simp? [Adjudicator.finalOutcome] says simp only [Adjudicator.finalOutcome])
    | channel c =>
      have hc := hfo c
      rw [FixedPart.address_eq] at hc
      by_cases hca : c = a
      · subst hca
        rw [FixedPart.address_eq] at hf
        rw [hc, if_pos rfl, hx0, hf]
        congr 2
        exact Allocation.reduceOwed_zero_of_find_alloc hfind
      · rw [hc, if_neg hca]
  · have hb := hbal n
    rw [hx0] at hb
    simp only [ite_self, Nat.add_zero] at hb
    exact hb

/-- The amount a deduped allocation's own first entry is, for an entry
    reached by deduplication, is exactly what `owed` reads at its
    destination. -/
theorem Allocation.owed_eq_amount_of_mem_dedup {o : Allocation E} {e : Entry E} (he : e ∈ o.dedup) :
    o.owed e.dest = e.amount := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem he
  have hfind := Allocation.find_of_getElem? (Allocation.dedup_nodup o) hj
  rw [Allocation.find_dedup] at hfind
  unfold Allocation.owed
  rw [hfind]
  rfl

theorem Allocation.dedup_total_eq_sum_owed (o : Allocation E) :
    o.dedup.total = ((o.dedup.map Entry.dest).map o.owed).sum := by
  unfold Allocation.total
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  exact (Allocation.owed_eq_amount_of_mem_dedup he).symm

theorem Allocation.dedup_total_eq_of_dest_owed {o o' : Allocation E}
    (hd : o.dedup.map Entry.dest = o'.dedup.map Entry.dest) (hw : ∀ d, o.owed d = o'.owed d) :
    o.dedup.total = o'.dedup.total := by
  rw [Allocation.dedup_total_eq_sum_owed, Allocation.dedup_total_eq_sum_owed, hd]
  congr 1
  apply List.map_congr_left
  intro d _
  exact hw d


theorem transfer_pointwise_absorbed {u t : Adjudicator E}
    (hfo : ∀ n, u.finalOutcome n = t.finalOutcome n) (hbal : ∀ n, u.balances.get n = t.balances.get n)
    (hdag : t.IsDAG) (hexh : t.TransferExhausted) (a : FixedPart) (b : Address E) :
    u.transfer a b = none ∨
    ∃ u', u.transfer a b = some u' ∧ (∀ n, u'.finalOutcome n = t.finalOutcome n) ∧
      (∀ n, u'.balances.get n = t.balances.get n) := by
  cases ht : t.transfer a b with
  | none =>
    left
    by_contra hcon
    obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp hcon
    obtain ⟨o, amt, x, hf, hfind, hk, hbfund, -, -, -, -, -⟩ := Adjudicator.transfer_effect hu'
    have hft : t.finalOutcome a.address = some (.allocation o) := by rw [← hfo a.address]; exact hf
    exact Adjudicator.transfer_ne_none hk hbfund hft hfind ht
  | some t' =>
    right
    obtain ⟨o, amt, x, hf, hfind, hk, hbfund, hx, hfot, hbalt, -, -⟩ := Adjudicator.transfer_effect ht
    have hfu : u.finalOutcome a.address = some (.allocation o) := (hfo a.address).trans hf
    have hune : u.transfer a b ≠ none := Adjudicator.transfer_ne_none hk hbfund hfu hfind
    obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp hune
    obtain ⟨o', amt', x', hf', hfind', -, -, hx', hfou, hbalu, -, -⟩ := Adjudicator.transfer_effect hu'
    have hoeq : o' = o := by
      have heq2 : (some (Outcome.allocation o') : Option (Outcome E)) = some (Outcome.allocation o) :=
        hf'.symm.trans hfu
      injection heq2 with heq3
      injection heq3
    have hxeq : x' = x := by rw [hx', hx, hoeq, hbal a.address]
    have hmatcht' : (∀ n, u'.finalOutcome n = t'.finalOutcome n) ∧ (∀ n, u'.balances.get n = t'.balances.get n) := by
      constructor
      · intro n
        cases n with
        | external e => (simp? [Adjudicator.finalOutcome] says simp only [Adjudicator.finalOutcome])
        | channel c =>
          have h1 := hfou c
          have h2 := hfot c
          rw [hoeq, hxeq, FixedPart.address_eq] at h1
          rw [FixedPart.address_eq] at h2
          by_cases hca : c = a
          · rw [if_pos hca] at h1; rw [if_pos hca] at h2; rw [h1, h2]
          · rw [if_neg hca] at h1; rw [if_neg hca] at h2
            rw [h1, h2, hfo (Address.channel c)]
      · intro n
        have h1 := hbalu n
        have h2 := hbalt n
        have h3 := hbal n
        rw [hxeq] at h1
        by_cases hca : n = a.address
        · rw [if_pos hca] at h1 h2
          by_cases hcb : n = b
          · rw [if_pos hcb] at h1 h2; unfold Coins at h1 h2 h3 ⊢; omega
          · rw [if_neg hcb] at h1 h2; unfold Coins at h1 h2 h3 ⊢; omega
        · rw [if_neg hca] at h1 h2
          by_cases hcb : n = b
          · rw [if_pos hcb] at h1 h2; unfold Coins at h1 h2 h3 ⊢; omega
          · rw [if_neg hcb] at h1 h2; unfold Coins at h1 h2 h3 ⊢; omega
    have hmatcht := transfer_exhausted_fixed hdag hexh ht
    exact ⟨u', hu', fun n => (hmatcht'.1 n).trans (hmatcht.1 n), fun n => (hmatcht'.2 n).trans (hmatcht.2 n)⟩

/-- Starting from a state that matches `t` pointwise, running any further
    `OnlyTransfers` list leaves the pointwise reading of `t` unchanged,
    because `t` is itself an exhausted fixed point. -/
theorem applyAll_pointwise_absorbed {t : Adjudicator E} (hdag : t.IsDAG) (hexh : t.TransferExhausted)
    (apps : Apps E) :
    ∀ (ops : List (Participant × Op E)), OnlyTransfers ops →
    ∀ (u : Adjudicator E), (∀ n, u.finalOutcome n = t.finalOutcome n) →
      (∀ n, u.balances.get n = t.balances.get n) →
      (∀ n, (Adjudicator.applyAll apps ops u).finalOutcome n = t.finalOutcome n) ∧
      (∀ n, (Adjudicator.applyAll apps ops u).balances.get n = t.balances.get n) := by
  intro ops
  induction ops with
  | nil => intro _ u hfo hbal; exact ⟨hfo, hbal⟩
  | cons hd rest ih =>
    intro hops u hfo hbal
    obtain ⟨a, b, hb⟩ := hops hd List.mem_cons_self
    obtain ⟨caller, op⟩ := hd
    have hb' : op = Op.transfer a b := hb
    have hOT : OnlyTransfers rest := fun e he => hops e (List.mem_cons_of_mem _ he)
    show (∀ n, (Adjudicator.applyAll apps rest ((u.apply apps caller op).getD u)).finalOutcome n = t.finalOutcome n) ∧
      (∀ n, (Adjudicator.applyAll apps rest ((u.apply apps caller op).getD u)).balances.get n = t.balances.get n)
    rw [hb', Adjudicator.apply_transfer]
    rcases transfer_pointwise_absorbed hfo hbal hdag hexh a b with hnone | ⟨u', hu', hfo', hbal'⟩
    · rw [hnone, Option.getD_none]
      exact ih hOT u hfo hbal
    · rw [hu', Option.getD_some]
      exact ih hOT u' hfo' hbal'

/-- An exhausted DAG state is unmoved (pointwise) by any further
    `OnlyTransfers` list. -/
theorem applyAll_exhausted_absorbed {t : Adjudicator E} (hdag : t.IsDAG) (hexh : t.TransferExhausted)
    (apps : Apps E) {ops : List (Participant × Op E)} (hops : OnlyTransfers ops) :
    (∀ n, (Adjudicator.applyAll apps ops t).finalOutcome n = t.finalOutcome n) ∧
    (∀ n, (Adjudicator.applyAll apps ops t).balances.get n = t.balances.get n) :=
  applyAll_pointwise_absorbed hdag hexh apps ops hops t (fun _ => rfl) (fun _ => rfl)

theorem balances_eq_of_mutual_ahead {t1 t2 : Adjudicator E} (h12 : t1.Ahead t2) (h21 : t2.Ahead t1)
    (hdest : ∀ c : FixedPart, (t1.allocationOf c.address).map Entry.dest =
      (t2.allocationOf c.address).map Entry.dest)
    (a : Address E) : t1.balances.get a = t2.balances.get a := by
  cases a with
  | external e => exact le_antisymm (h12.get_external_le e) (h21.get_external_le e)
  | channel c =>
    have hch12 := h12.chan c
    have hch21 := h21.chan c
    rw [FixedPart.address_eq] at hch12 hch21
    have hflow12 := h12.flow (Address.channel c) [] List.nodup_nil
    have hflow21 := h21.flow (Address.channel c) [] List.nodup_nil
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hflow12 hflow21
    cases hfo1 : t1.finalOutcome (Address.channel c) with
    | none =>
      cases hfo2 : t2.finalOutcome (Address.channel c) with
      | none =>
        have hd1 : t1.dueTotal (Address.channel c) = 0 := by unfold Adjudicator.dueTotal; rw [hfo1]
        have hd2 : t2.dueTotal (Address.channel c) = 0 := by unfold Adjudicator.dueTotal; rw [hfo2]
        rw [hd1, hd2] at hflow12 hflow21
        show t1.balances.get (Address.channel c) = t2.balances.get (Address.channel c)
        unfold Coins at hflow12 hflow21 ⊢
        omega
      | some o2 => rw [hfo1, hfo2] at hch12; cases hch12
    | some o1 =>
      cases hfo2 : t2.finalOutcome (Address.channel c) with
      | none => rw [hfo1, hfo2] at hch12; cases hch12
      | some o2 =>
        rw [hfo1, hfo2] at hch12 hch21
        cases hch12 with
        | some hrel12 =>
          cases hch21 with
          | some hrel21 =>
            cases o1 with
            | allocation al1 =>
              cases o2 with
              | allocation al2 =>
                have how2 : ∀ d, al2.owed d ≤ al1.owed d := hrel12.owed_le
                have how1 : ∀ d, al1.owed d ≤ al2.owed d := hrel21.owed_le
                have howeq : ∀ d, al1.owed d = al2.owed d := fun d => le_antisymm (how1 d) (how2 d)
                have hdc := hdest c
                unfold Adjudicator.allocationOf at hdc
                rw [FixedPart.address_eq] at hdc
                rw [hfo1, hfo2] at hdc
                simp only at hdc
                have hdt1 : t1.dueTotal (Address.channel c) = al1.dedup.total :=
                  Adjudicator.dueTotal_of hfo1
                have hdt2 : t2.dueTotal (Address.channel c) = al2.dedup.total :=
                  Adjudicator.dueTotal_of hfo2
                have hdteq : al1.dedup.total = al2.dedup.total :=
                  Allocation.dedup_total_eq_of_dest_owed hdc howeq
                rw [hdt1, hdt2, hdteq] at hflow12 hflow21
                show t1.balances.get (Address.channel c) = t2.balances.get (Address.channel c)
                unfold Coins at hflow12 hflow21 ⊢
                omega

/-- Nitro-36. Nitro:842-843: "calling transfers out of order does not affect the
    ultimate result." Two exhausted transfer sequences from one Turbo state
    give the same balances. Proved for every DAG outcome network, not only in
    Turbo scope (`ArmadaLean/Types/Outcome.lean`, module comment). -/
theorem turbo_order_independent (apps : Apps E) (s : DAGOutcomeNetwork E)
    (ops1 ops2 : List (Participant × Op E)) (h1 : OnlyTransfers ops1)
    (h2 : OnlyTransfers ops2)
    (hx1 : (Adjudicator.applyAll apps ops1 (s : Adjudicator E)).TransferExhausted)
    (hx2 : (Adjudicator.applyAll apps ops2 (s : Adjudicator E)).TransferExhausted)
    (a : Address E) :
    (Adjudicator.applyAll apps ops1 (s : Adjudicator E)).balances.get a =
      (Adjudicator.applyAll apps ops2 (s : Adjudicator E)).balances.get a := by
  obtain ⟨s, hdag⟩ := s
  have hdag1 : (Adjudicator.applyAll apps ops1 s).IsDAG := (IsDAG_applyAll_iff apps h1 s).mpr hdag
  have hdag2 : (Adjudicator.applyAll apps ops2 s).IsDAG := (IsDAG_applyAll_iff apps h2 s).mpr hdag
  have hOT12 : OnlyTransfers (ops1 ++ ops2) := by
    intro e he; rcases List.mem_append.mp he with he | he
    · exact h1 e he
    · exact h2 e he
  have hOT21 : OnlyTransfers (ops2 ++ ops1) := by
    intro e he; rcases List.mem_append.mp he with he | he
    · exact h2 e he
    · exact h1 e he
  have htC_eq : Adjudicator.applyAll apps (ops1 ++ ops2) s =
      Adjudicator.applyAll apps ops2 (Adjudicator.applyAll apps ops1 s) :=
    Adjudicator.applyAll_append apps ops1 ops2 s
  have htC_match := applyAll_exhausted_absorbed hdag1 hx1 apps h2
  rw [← htC_eq] at htC_match
  have htC'_eq : Adjudicator.applyAll apps (ops2 ++ ops1) s =
      Adjudicator.applyAll apps ops1 (Adjudicator.applyAll apps ops2 s) :=
    Adjudicator.applyAll_append apps ops2 ops1 s
  have htC'_match := applyAll_exhausted_absorbed hdag2 hx2 apps h1
  rw [← htC'_eq] at htC'_match
  have hsub2 : ops2.Sublist (ops1 ++ ops2) := List.sublist_append_right ops1 ops2
  have hsub1 : ops1.Sublist (ops2 ++ ops1) := List.sublist_append_right ops2 ops1
  have hahead_t2_tC : (Adjudicator.applyAll apps ops2 s).Ahead (Adjudicator.applyAll apps (ops1 ++ ops2) s) :=
    Adjudicator.Ahead.applyAll_sublist apps hsub2 hOT12 (Adjudicator.Ahead.refl s)
  have hahead_t1_tC' : (Adjudicator.applyAll apps ops1 s).Ahead (Adjudicator.applyAll apps (ops2 ++ ops1) s) :=
    Adjudicator.Ahead.applyAll_sublist apps hsub1 hOT21 (Adjudicator.Ahead.refl s)
  have ht21 : (Adjudicator.applyAll apps ops2 s).Ahead (Adjudicator.applyAll apps ops1 s) :=
    Ahead_right_congr htC_match.1 htC_match.2 hahead_t2_tC
  have ht12 : (Adjudicator.applyAll apps ops1 s).Ahead (Adjudicator.applyAll apps ops2 s) :=
    Ahead_right_congr htC'_match.1 htC'_match.2 hahead_t1_tC'
  have hdest : ∀ c : FixedPart, ((Adjudicator.applyAll apps ops1 s).allocationOf c.address).map Entry.dest =
      ((Adjudicator.applyAll apps ops2 s).allocationOf c.address).map Entry.dest := fun c =>
    (allocationOf_dest_applyAll apps ops1 h1 s c.address).trans
      (allocationOf_dest_applyAll apps ops2 h2 s c.address).symm
  exact balances_eq_of_mutual_ahead ht12 ht21 hdest a

/-- Nitro-33, Nitro-36, Nitro-32. Nitro:819 "Choose a topological ordering":
    on a DAG a topological ordering exists (Nitro:798-799) and the
    algorithm's value does not depend on which one is chosen, so
    `TurboValue` is a function. -/
theorem turbo_value_exists_unique (s : DAGOutcomeNetwork E) (n : Address E) :
    (∃ v, (s : Adjudicator E).TurboValue n v) ∧
      ∀ v w, (s : Adjudicator E).TurboValue n v → (s : Adjudicator E).TurboValue n w → v = w := by
  obtain ⟨s, hdag⟩ := s
  obtain ⟨order0, horder0⟩ := exists_valid_topo_order s hdag
  refine ⟨⟨s.turboValueAlong order0 n, order0, horder0, rfl⟩, ?_⟩
  rintro v w ⟨order1, horder1, rfl⟩ ⟨order2, horder2, rfl⟩
  unfold Adjudicator.turboValueAlong
  obtain ⟨hnd1, hedge1, hactive1⟩ := horder1
  obtain ⟨hnd2, hedge2, hactive2⟩ := horder2
  rw [turboValues_filter_activeAlloc s order1 s.balances,
    turboValues_filter_activeAlloc s order2 s.balances]
  have hcharmem : ∀ (order : List (Address E)),
      (∀ x, (s.balances.get x ≠ 0 ∨ s.allocationOf x ≠ []) → x ∈ order) →
      ∀ x, x ∈ order.filter (fun x => !(s.allocationOf x).isEmpty) ↔ s.allocationOf x ≠ [] := by
    intro order hactive x
    rw [List.mem_filter]
    constructor
    · rintro ⟨-, hpx⟩
      (simpa? using hpx says simpa only [ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] using hpx)
    · intro hx
      exact ⟨hactive x (Or.inr hx), by (simp? [hx] says simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq, hx, not_false_eq_true])⟩
  have hmem1 := hcharmem order1 hactive1
  have hmem2 := hcharmem order2 hactive2
  have hmem' : ∀ x, x ∈ order1.filter (fun x => !(s.allocationOf x).isEmpty) ↔
      x ∈ order2.filter (fun x => !(s.allocationOf x).isEmpty) := fun x => by
    rw [hmem1, hmem2]
  have hext1 : ∀ x ∈ order1.filter (fun x => !(s.allocationOf x).isEmpty), x.isExternal = false := by
    intro x hx
    have hxa : s.allocationOf x ≠ [] := (hmem1 x).mp hx
    cases x with
    | external d =>
      exact absurd (show s.allocationOf (Address.external d) = [] from rfl) hxa
    | channel c => rfl
  have hvalid1 : ∀ m d, m ∈ order1.filter (fun x => !(s.allocationOf x).isEmpty) →
      d ∈ order1.filter (fun x => !(s.allocationOf x).isEmpty) → s.Edge m d →
      ∃ i j : Nat, (order1.filter (fun x => !(s.allocationOf x).isEmpty))[i]? = some m ∧
        (order1.filter (fun x => !(s.allocationOf x).isEmpty))[j]? = some d ∧ i < j := by
    intro m d hm hd hmd
    obtain ⟨i, j, hi, hj, hij⟩ := hedge1 m d hmd
    exact before_filter hnd1 _ hi hj hij (List.mem_filter.mp hm).2 (List.mem_filter.mp hd).2
  have hvalid2 : ∀ m d, m ∈ order2.filter (fun x => !(s.allocationOf x).isEmpty) →
      d ∈ order2.filter (fun x => !(s.allocationOf x).isEmpty) → s.Edge m d →
      ∃ i j : Nat, (order2.filter (fun x => !(s.allocationOf x).isEmpty))[i]? = some m ∧
        (order2.filter (fun x => !(s.allocationOf x).isEmpty))[j]? = some d ∧ i < j := by
    intro m d hm hd hmd
    obtain ⟨i, j, hi, hj, hij⟩ := hedge2 m d hmd
    exact before_filter hnd2 _ hi hj hij (List.mem_filter.mp hm).2 (List.mem_filter.mp hd).2
  exact turboValues_order_indep s hdag
    (order1.filter (fun x => !(s.allocationOf x).isEmpty)).length
    (order1.filter (fun x => !(s.allocationOf x).isEmpty)) rfl (hnd1.filter _)
    (order2.filter (fun x => !(s.allocationOf x).isEmpty)) (hnd2.filter _) hmem' hext1
    hvalid1 hvalid2 s.balances n

/- Out of scope: a Nitro 2019 §5.3-§5.4 sub-channel
    construction. SATP assumes this result as a precondition: "In this paper, we
    assume as a precondition that all ledger channels are fully-funded – each item
    listed in its outcome" (SATP:385-388). go-nitro has no objective that funds a
    sub-channel from a ledger allocation (`protocols/readme.md`). Armada does not
    depend on this theorem. Restore only if Armada funds sub-channels by the Nitro
    2019 §5.3-§5.4 construction.

/-- Nitro-37, Nitro-47, docs-0060-07, docs-0080-08. Nitro:859-865: "χ is funded with 6 coins by
    L for both A and B ... Once it is on-chain, the transfer operation
    T(L, χ, 6) is all that is required to make χ directly funded. From the
    Turbo redistribution result, we know that this redistribution strategy is
    unbeatable." G16 (`docs/nitro-repair-2026-10-27.md`, defect 23): the
    adversary can transfer `L → χ` and then `χ → q` within one prefix, so
    `χ` must not finalize during the strategy, as `ledger_partial_withdrawal`
    already requires of its receiving ledger.
    χ is a ledger channel, because transfer credits only a fundable channel (Adjudicator.transfer, Address.fundable) and a channel funded by an allocation is a ledger channel (nitro-repair §6.3).
    Out of scope: a Nitro 2019 §5.3-§5.4 sub-channel construction.
    SATP assumes its result as a precondition (SATP:385-388), and go-nitro has no objective that
    runs it. The statement stays for reference. Armada does not depend on it. -/
theorem ledger_offload_funds_subchannel (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Nitro.ReachableNetwork apps Ts)
    (hvn : v = n.state.views) (w : LedgerWithSub E) (hw : w.Holds apps Ts v)
    (hχk : w.χ.kind = .ledger)
    (hχopen : ∀ p, (v p).chain.finalOutcome w.χ.address = none)
    (hχsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = w.χ → t.state.isFinal = false) :
    FundedFor apps (Ts.T w.A) w.χ w.c (v w.A) ∧ FundedFor apps (Ts.T w.B) w.χ w.c (v w.B) := by
  sorry
-/

/- Out of scope: a Nitro 2019 §5.3-§5.4 sub-channel
    construction. SATP assumes this result as a precondition: "In this paper, we
    assume as a precondition that all ledger channels are fully-funded – each item
    listed in its outcome" (SATP:385-388). go-nitro has no objective that funds a
    sub-channel from a ledger allocation (`protocols/readme.md`). Armada does not
    depend on this theorem. Restore only if Armada funds sub-channels by the Nitro
    2019 §5.3-§5.4 construction.

/-- Nitro-49 (Nitro:891-922, §5.4.1 Opening a Sub-channel), docs-0060-07. From
    `⟦L : x⟧, [L ↦ (A : a, B : b)]_{A,B}` and `[χ ↦ (A : a', B : b')]_{A,B}`
    with `a' ≤ a`, `b' ≤ b`, the update
    `[L ↦ (A : a − a', B : b − b', χ : a' + b')]_{A,B}` preserves the value
    of `A` and `B` at their destinations `dA` and `dB`.
    Out of scope: a Nitro 2019 §5.3-§5.4 sub-channel construction.
    SATP assumes its result as a precondition (SATP:385-388), and go-nitro has no objective that
    runs it. The statement stays for reference. Armada does not depend on it. -/
theorem subchannel_open_value_preserving (apps : Apps E) (Ts : Threats E apps) (v v' : Views E)
    (n : Nitro.ReachableNetwork apps Ts)
    (hvn : v = n.state.views) (n' : Nitro.ReachableNetwork apps Ts)
    (hvn' : v' = n'.state.views)
    (A B : Participant) (dA dB : E) (L χ : FixedPart)
    (a b a' b' : Coins) (ha : a' ≤ a) (hb : b' ≤ b)
    (hLk : L.kind = .ledger) (hLc : L.RunsConsensus apps) (hLp : L.participants = [A, B])
    (hχp : χ.participants = [A, B])
    (hbal : v.HoldsBalance L.address (a + b)) (hbal' : v'.HoldsBalance L.address (a + b))
    (h1 : v.FinalizableBy apps Ts L (.allocation [alloc (.external dA) a, alloc (.external dB) b])
      [A, B])
    (h2 : v.FinalizableBy apps Ts χ
      (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B])
    (h3 : v'.FinalizableBy apps Ts L
      (.allocation [alloc (.external dA) (a - a'), alloc (.external dB) (b - b'),
        alloc χ.address (a' + b')]) [A, B])
    (h4 : v'.FinalizableBy apps Ts χ
      (.allocation [alloc (.external dA) a', alloc (.external dB) b']) [A, B])
    (hother : ∀ p, p = A ∨ p = B → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T A) dA (v A) (v' A) ∧ SameValue apps (Ts.T B) dB (v B) (v' B) := by
  sorry
-/

/- Out of scope: a Nitro 2019 §5.3-§5.4 sub-channel
    construction. SATP assumes this result as a precondition: "In this paper, we
    assume as a precondition that all ledger channels are fully-funded – each item
    listed in its outcome" (SATP:385-388). go-nitro has no objective that funds a
    sub-channel from a ledger allocation (`protocols/readme.md`). Armada does not
    depend on this theorem. Restore only if Armada funds sub-channels by the Nitro
    2019 §5.3-§5.4 construction.

/-- Nitro-49 (Nitro:939-957, §5.4.2 Closing a Sub-channel), docs-0080-07. From
    `[L ↦ (A : a, B : b, χ : c)]_{A,B}` and the concluded
    `[χ ↦ (A : a', B : b')]_{A,B}` with `a' + b' = c`, the update
    `[L ↦ (A : a + a', B : b + b')]_{A,B}` preserves the value of `A` and
    `B`.
    Out of scope: a Nitro 2019 §5.3-§5.4 sub-channel construction.
    SATP assumes its result as a precondition (SATP:385-388), and go-nitro has no objective that
    runs it. The statement stays for reference. Armada does not depend on it. -/
theorem subchannel_close_value_preserving (apps : Apps E) (Ts : Threats E apps) (v v' : Views E)
    (n : Nitro.ReachableNetwork apps Ts)
    (hvn : v = n.state.views) (n' : Nitro.ReachableNetwork apps Ts)
    (hvn' : v' = n'.state.views)
    (w : LedgerWithSub E) (a' b' : Coins)
    (hc : a' + b' = w.c) (hw : w.Holds apps Ts v)
    (hχ : v.FinalizableBy apps Ts w.χ
      (.allocation [alloc (.external w.dA) a', alloc (.external w.dB) b']) [w.A, w.B])
    (h3 : v'.FinalizableBy apps Ts w.L
      (.allocation [alloc (.external w.dA) (w.a + a'), alloc (.external w.dB) (w.b + b')])
      [w.A, w.B])
    (hbal' : v'.HoldsBalance w.L.address (w.a + w.b + w.c))
    (hother : ∀ p, p = w.A ∨ p = w.B → (v p).chain = (v' p).chain) :
    SameValue apps (Ts.T w.A) w.dA (v w.A) (v' w.A) ∧
      SameValue apps (Ts.T w.B) w.dB (v w.B) (v' w.B) := by
  sorry
-/

/-- Nitro-49 (Nitro:959-995, §5.4.3 Topping Up a Ledger Channel), docs-0060-05.
    Nitro:982-985: moving `A`'s entry to the end with the larger total
    `a + a'` "is a safe operation due to the precedence rules: as the channel
    is currently underfunded A would still only receive a if the outcome went
    to chain." The reordered outcome affords `A` exactly `a`. -/
theorem ledger_topup_reorder_safe (A B χ : Address E) (a b c a' : Coins) (hAB : A ≠ B)
    (hAχ : A ≠ χ) (hBχ : B ≠ χ) :
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] A = a ∧
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] B = b ∧
    Allocation.paidTo (a + b + c) [alloc B b, alloc χ c, alloc A (a + a')] χ = c := by
  have hd : Allocation.dedup [alloc B b, alloc χ c, alloc A (a + a')] =
      [alloc B b, alloc χ c, alloc A (a + a')] := by
    (simp? [Allocation.dedup, Allocation.dedupFrom, alloc, hAB, hAχ, Ne.symm hBχ] says simp only [Allocation.dedup, Allocation.dedupFrom, alloc, List.not_mem_nil, ↓reduceIte, List.mem_cons, Ne.symm hBχ, or_self, hAχ, hAB])
  refine ⟨?_, ?_, ?_⟩
  · have := Allocation.paidTo_of_getElem? (held := a + b + c) hd (j := 2) (f := alloc A (a + a')) rfl
    refine this.trans ?_; (simp? [alloc, Allocation.total, Entry.amount] says simp only [Entry.amount, alloc, Item.amount_alloc, Allocation.total, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]); (grind? says grind only [= min_def, #eec5, #00b3])
  · have := Allocation.paidTo_of_getElem? (held := a + b + c) hd (j := 0) (f := alloc B b) rfl
    refine this.trans ?_; (simp? [alloc, Allocation.total, Entry.amount] says simp only [Entry.amount, alloc, Item.amount_alloc, Allocation.total, List.take_zero, List.map_nil, List.sum_nil, tsub_zero, inf_eq_left]); (grind? says grind only)
  · have := Allocation.paidTo_of_getElem? (held := a + b + c) hd (j := 1) (f := alloc χ c) rfl
    refine this.trans ?_; (simp? [alloc, Allocation.total, Entry.amount] says simp only [Entry.amount, alloc, Item.amount_alloc, Allocation.total, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, inf_eq_left]); (grind? says grind only [#0a9b])

/-- Nitro-49 (Nitro:989-995, §5.4.3 steps 3-4), Nitro-04, docs-0060-05.
    After the deposit `D_L(a')`, made with `expectedHeld = a + b + c` (the
    ledger's holding `A` saw), the reordered outcome is fully funded: every
    entry, including `A`'s raised one, is affordable in full. -/
theorem ledger_topup_deposit_funds (s s' : Adjudicator E) (L : FixedPart) (A B χ : Address E)
    (a b c a' : Coins) (hAB : A ≠ B) (hAχ : A ≠ χ) (hBχ : B ≠ χ)
    (hheld : s.balances.get L.address = a + b + c)
    (hd : s.deposit L.address (a + b + c) a' = some s') :
    s'.balances.get L.address = a + b + c + a' ∧
    Allocation.paidTo (s'.balances.get L.address) [alloc B b, alloc χ c, alloc A (a + a')] A =
      a + a' ∧
    Allocation.paidTo (s'.balances.get L.address) [alloc A (a + a'), alloc B b, alloc χ c] A =
      a + a' := by
  obtain ⟨-, -, hb, -⟩ := Adjudicator.deposit_some hd
  have hL : s'.balances.get L.address = a + b + c + a' := by rw [hb, Balances.get_add, if_pos rfl, hheld]
  refine ⟨hL, ?_, ?_⟩
  · have hd1 : Allocation.dedup [alloc B b, alloc χ c, alloc A (a + a')] =
        [alloc B b, alloc χ c, alloc A (a + a')] := by
      (simp? [Allocation.dedup, Allocation.dedupFrom, alloc, hAB, hAχ, Ne.symm hBχ] says simp only [Allocation.dedup, Allocation.dedupFrom, alloc, List.not_mem_nil, ↓reduceIte, List.mem_cons, Ne.symm hBχ, or_self, hAχ, hAB])
    rw [hL]
    refine (Allocation.paidTo_of_getElem? hd1 (j := 2) (f := alloc A (a + a')) rfl).trans ?_
    (simp? [alloc, Allocation.total, Entry.amount] says simp only [Entry.amount, alloc, Item.amount_alloc, Allocation.total, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, inf_eq_left]); (grind? says grind only [#685f])
  · have hd2 : Allocation.dedup [alloc A (a + a'), alloc B b, alloc χ c] =
        [alloc A (a + a'), alloc B b, alloc χ c] := by
      (simp? [Allocation.dedup, Allocation.dedupFrom, alloc, Ne.symm hAB, Ne.symm hAχ, Ne.symm hBχ] says simp only [Allocation.dedup, Allocation.dedupFrom, alloc, List.not_mem_nil, ↓reduceIte, List.mem_cons, Ne.symm hAB, or_self, Ne.symm hBχ, Ne.symm hAχ])
    rw [hL]
    refine (Allocation.paidTo_of_getElem? hd2 (j := 0) (f := alloc A (a + a')) rfl).trans ?_
    (simp? [alloc, Allocation.total, Entry.amount] says simp only [Entry.amount, alloc, Item.amount_alloc, Allocation.total, List.take_zero, List.map_nil, List.sum_nil, tsub_zero, Nat.add_min_add_right, Nat.add_right_cancel_iff, inf_eq_left]); (grind? says grind only)

/-- While channel `c` has no recorded finalization, its own balance can only
    grow over one successful on-chain step: a `deposit` only ever adds; a
    `transfer` can pay INTO `c.address` (if it is the destination) but can
    only pay OUT of a channel whose own `finalOutcome` is already `some`
    (`Adjudicator.transfer_some`'s own `hf` field), which `hopen` rules out
    for `c` itself; `reclaim`, `challenge`, `checkpoint`, `conclude` and
    `tick` never touch `balances` at all (`Adjudicator.setStatus_balances`,
    `Adjudicator.tick_balances`). Used by `balance_mono_open_step`. -/
theorem balances_mono_while_open_step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c : FixedPart} (hopen : s.finalOutcome c.address = none)
    (h : s.apply apps caller op = some s') :
    s.balances.get c.address ≤ s'.balances.get c.address := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, hb, -, -, -⟩ := Adjudicator.deposit_some h
    rw [hb, Balances.get_add]
    by_cases hca : c.address = a
    · rw [if_pos hca]; (grind? says grind only)
    · rw [if_neg hca]
  | transfer a b =>
    by_cases hac : a = c
    · subst hac
      obtain ⟨o, amt, x, hf, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
      rw [hopen] at hf; (simp? at hf says simp only [reduceCtorEq] at hf)
    · obtain ⟨o, amt, x, hf, hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ := Adjudicator.transfer_some h
      have hca : (c.address : Address E) ≠ a.address := by
        intro hh; injection hh with hh'; exact hac hh'.symm
      rw [hbal, Balances.get_sub, if_neg hca, Balances.get_add]
      by_cases hbc : c.address = b
      · rw [if_pos hbc]; (grind? says grind only)
      · rw [if_neg hbc]
  | reclaim l v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsucc, _, _⟩ := Adjudicator.reclaim_some h
    rw [hsucc]; exact le_refl _
  | challenge c' proof cand =>
    obtain ⟨-, hsucc⟩ := Adjudicator.challenge_some h
    rw [hsucc]; exact le_refl _
  | checkpoint c' proof cand =>
    obtain ⟨-, hsucc⟩ := Adjudicator.checkpoint_some h
    rw [hsucc]; exact le_refl _
  | conclude c' ss' =>
    obtain ⟨-, hsucc⟩ := Adjudicator.conclude_some h
    rw [hsucc]; exact le_refl _
  | tick dt =>
    have hs' : s.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
    subst hs'
    exact le_refl _

/-- One successful on-chain step from a state where channel `c` has no
    final outcome and its balance covers `o.total`. Either `c` stays open
    with `o.total` still covered: a `deposit` only adds, a `transfer` or
    `reclaim` on `c` needs `c` finalized (`hnone` rules it out), and every
    other operation leaves `c`'s balance. Or the step is the one that first
    finalizes `c` (a `conclude`, a `challenge` with zero duration, or a
    `tick` past the deadline): that step writes no balance, and it records
    the same outcome `Ω₀` as the final outcome and as the finalization
    outcome. Used by `pays_step`. -/
theorem open_step {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    {c : FixedPart} {o : Allocation E} (h : s.apply apps caller op = some s')
    (hnone : s.finalOutcome c.address = none) (hfund0 : o.total ≤ s.balances.get c.address) :
    (s'.finalOutcome c.address = none ∧ o.total ≤ s'.balances.get c.address) ∨
      (∃ Ω₀, s'.finalizedWith c.address = some Ω₀ ∧ s'.finalOutcome c.address = some Ω₀ ∧
        o.total ≤ s'.balances.get c.address) := by
  cases op with
    | deposit a e x =>
      left
      obtain ⟨⟨c', hac', -⟩, -, hb, -, hs, hn⟩ := Adjudicator.deposit_some h
      refine ⟨?_, ?_⟩
      · (simpa? [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hnone says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_of_status hs, hn] using hnone)
      · rw [hb, Balances.get_add]
        by_cases hca : c.address = a
        · rw [if_pos hca]; (grind? says grind only)
        · rw [if_neg hca]; exact hfund0
    | transfer a b =>
      by_cases hac : a = c
      · subst hac
        obtain ⟨oo, amtt, x, hf, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
        rw [hnone] at hf; (simp? at hf says simp only [reduceCtorEq] at hf)
      · left
        obtain ⟨oo, amtt, x, hf, hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
          Adjudicator.transfer_some h
        have hca : (c.address : Address E) ≠ a.address := by
          intro hh; injection hh with hh'; exact hac hh'.symm
        refine ⟨?_, ?_⟩
        · (simpa? [FixedPart.address_eq, Adjudicator.statusOf_of_status hstat,
            Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac), hnow] using hnone says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac), hnow] using hnone)
        · rw [hbal, Balances.get_sub, if_neg hca, Balances.get_add]
          by_cases hbc : c.address = b
          · rw [if_pos hbc]; (grind? says grind only)
          · rw [if_neg hbc]; exact hfund0
    | reclaim l v =>
      by_cases hcl : l = c
      · subst hcl
        obtain ⟨oL, -, -, -, -, hL, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
        rw [hnone] at hL; (simp? at hL says simp only [reduceCtorEq] at hL)
      · left
        obtain ⟨oL, oV, x, left, right, hL, hV, hfind, hne1, hne2, hxeq, hsucc, hlk, hvk⟩ :=
          Adjudicator.reclaim_some h
        have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
        refine ⟨?_, ?_⟩
        · (simpa? [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcl)] using hnone says simpa only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcl), Adjudicator.setStatus_now] using hnone)
        · rw [hbal']; exact hfund0
    | challenge c' proof cand =>
      by_cases hcc : c' = c
      · subst hcc
        obtain ⟨-, hsucc⟩ := Adjudicator.challenge_some h
        have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
        by_cases hz : s.now + c'.challengeDuration ≤ s.now
        · right
          refine ⟨cand.outcome, ?_, ?_, ?_⟩
          · (simp? [hsucc, Adjudicator.finalizedWith_channel, FixedPart.address_eq,
              ChannelStatus.finalizedWith_challenged, hz] says simp only [hsucc, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_challenged, hz])
          · (simp? [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              ChannelStatus.finalOutcome_challenged, hz] says simp only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_challenged, hz])
          · rw [hbal']; exact hfund0
        · left
          refine ⟨?_, ?_⟩
          · (simp? [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              ChannelStatus.finalOutcome_challenged, hz] says simp only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_challenged, hz])
          · rw [hbal']; exact hfund0
      · left
        obtain ⟨-, hsucc⟩ := Adjudicator.challenge_some h
        refine ⟨?_, ?_⟩
        · (simpa? [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcc)] using hnone says simpa only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc), Adjudicator.setStatus_now] using hnone)
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
    | checkpoint c' proof cand =>
      left
      by_cases hcc : c' = c
      · subst hcc
        obtain ⟨-, hsucc⟩ := Adjudicator.checkpoint_some h
        refine ⟨?_, ?_⟩
        · (simp? [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq] says simp only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_open])
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
      · obtain ⟨-, hsucc⟩ := Adjudicator.checkpoint_some h
        refine ⟨?_, ?_⟩
        · (simpa? [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcc)] using hnone says simpa only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc), Adjudicator.setStatus_now] using hnone)
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
    | conclude c' ss' =>
      by_cases hcc : c' = c
      · subst hcc
        right
        obtain ⟨-, hsucc⟩ := Adjudicator.conclude_some h
        have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
        refine ⟨ss'.state.outcome, ?_, ?_, ?_⟩
        · (simp? [hsucc, Adjudicator.finalizedWith_channel, FixedPart.address_eq] says simp only [hsucc, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalizedWith_finalized])
        · (simp? [hsucc, Adjudicator.finalOutcome_channel, FixedPart.address_eq] says simp only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_finalized])
        · rw [hbal']; exact hfund0
      · left
        obtain ⟨-, hsucc⟩ := Adjudicator.conclude_some h
        refine ⟨?_, ?_⟩
        · (simpa? [FixedPart.address_eq, hsucc, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hcc)] using hnone says simpa only [hsucc, FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc), Adjudicator.setStatus_now] using hnone)
        · have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
          rw [hbal']; exact hfund0
    | tick dt =>
      have hs' : s.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
      subst hs'
      rcases hstat : s.statusOf c with t' | ⟨t', ch⟩ | ⟨t', f, oo⟩
      · left
        refine ⟨?_, ?_⟩
        · (simp? [Adjudicator.finalOutcome_channel, FixedPart.address_eq,
            Adjudicator.tick_statusOf, hstat] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.tick_statusOf, hstat, Adjudicator.tick_now, ChannelStatus.finalOutcome_open])
        · (simpa? using hfund0 says simpa only [Adjudicator.tick_balances, FixedPart.address_eq] using hfund0)
      · by_cases hz : ch.deadline ≤ s.now + dt
        · right
          refine ⟨ch.state.outcome, ?_, ?_, ?_⟩
          · (simp? [Adjudicator.finalizedWith_channel, FixedPart.address_eq,
              Adjudicator.tick_statusOf, hstat, ChannelStatus.finalizedWith_challenged, hz] says simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hstat, Adjudicator.tick_now, ChannelStatus.finalizedWith_challenged, hz, ↓reduceIte])
          · (simp? [Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              Adjudicator.tick_statusOf, hstat, ChannelStatus.finalOutcome_challenged, hz] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.tick_statusOf, hstat, Adjudicator.tick_now, ChannelStatus.finalOutcome_challenged, hz, ↓reduceIte])
          · (simpa? using hfund0 says simpa only [Adjudicator.tick_balances, FixedPart.address_eq] using hfund0)
        · left
          refine ⟨?_, ?_⟩
          · (simp? [Adjudicator.finalOutcome_channel, FixedPart.address_eq,
              Adjudicator.tick_statusOf, hstat, ChannelStatus.finalOutcome_challenged, hz] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.tick_statusOf, hstat, Adjudicator.tick_now, ChannelStatus.finalOutcome_challenged, hz, ↓reduceIte])
          · (simpa? using hfund0 says simpa only [Adjudicator.tick_balances, FixedPart.address_eq] using hfund0)
      · exfalso
        have hcontra : s.finalOutcome c.address = some oo := by
          (simp? [Adjudicator.finalOutcome_channel, FixedPart.address_eq, hstat] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, ChannelStatus.finalOutcome_finalized])
        rw [hcontra] at hnone; (simp? at hnone says simp only [reduceCtorEq] at hnone)


/-- Over an arbitrary round of play (`pending` is whatever `p`'s own
    reaction this round is — none of it ever `Op.targets`-ing `c2`), a
    consensus-app channel `c2` that `p` belongs to, that `p` has never
    sent a final state of, that is not yet finalized, and whose every
    outstanding challenge's deadline is at least the fixed floor `D`,
    stays exactly so by the round's end `net'`, PROVIDED `net'.chain.now`
    itself is still below `D`. An adversary's `conclude` on `c2` needs
    `p`'s own genuine signature on a final state (`ConclusionProof`'s
    `ByAll`, `Bounds.unforgeable`), which `p` never gave
    (`hsent`'s `isFinal = false`); a `transfer`/`reclaim` reading `c2` as
    the already-finalized source needs `c2.finalOutcome` already `some`,
    contradicting `hc2none`; a fresh `challenge`/`checkpoint` on `c2` gets
    a deadline `now + c2.challengeDuration`, and `now ≤ net'.chain.now <
    D ≤ now + c2.challengeDuration` since `2 * T.ε ≤ c2.challengeDuration`
    needs only `D ≤ now + 2 * T.ε`, which holds because `D`'s own
    definition (`ledger_partial_withdrawal`) gives `D ≤ v0now + 2 * T.ε`
    and `v0now ≤ now` (`hlo`, threaded forward). Used by
    `ledger_partial_withdrawal`, once for the round that lands its own
    `conclude` on `L` (`c2 = L'`, untouched by that call) and once for
    the round that lands its own `transfer` paying `L'` (`c2 = L'`,
    touched only in balance, never in status: `Op.targets`'s `transfer`
    case reads only the transfer's own source channel). -/
theorem channel_stays_open_round {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {c2 : FixedPart} (hC2 : TimedConsensusMember apps p T.ε c2)
    {D v0now : Time} (hD : D ≤ v0now + 2 * T.ε) :
    ∀ {net net' : NetworkState E p} {t : Time} {pending : List (Op E)},
      Threat.RoundSeq apps T t pending net net' →
      (∀ op ∈ pending, ¬ Op.targets op c2) →
      (∀ op ∈ pending, ∀ dt, op ≠ Op.tick dt) →
      net'.chain.now < D →
      v0now ≤ net.chain.now →
      net.chain.finalOutcome c2.address = none →
      (∀ t0 ch, net.chain.statusOf c2 = .challenged t0 ch → D ≤ ch.deadline) →
      (∀ t0 ∈ net.sent, t0.state.channel = c2 → t0.state.isFinal = false) →
      net'.chain.finalOutcome c2.address = none ∧
        (∀ t0 ch, net'.chain.statusOf c2 = .challenged t0 ch → D ≤ ch.deadline) ∧
        (∀ t0 ∈ net'.sent, t0.state.channel = c2 → t0.state.isFinal = false) := by
  intro net net' t pending hseq
  induction hseq with
  | nil => intro _ _ _ _ hfo hfl hsent; exact ⟨hfo, hfl, hsent⟩
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro hpend hpnotick hDbound hlo hfo hfl hsent
    have hmem : op ∈ pending := by
      rw [hsplit]; exact List.mem_append_right l1 List.mem_cons_self
    have hop2 : ¬ Op.targets op c2 := hpend op hmem
    have hopnt : ∀ dt, op ≠ Op.tick dt := hpnotick op hmem
    have hpend' : ∀ op' ∈ l1 ++ l2, ¬ Op.targets op' c2 := by
      intro op' hop'
      apply hpend
      rw [hsplit]
      rcases List.mem_append.1 hop' with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
    have hpnotick' : ∀ op' ∈ l1 ++ l2, ∀ dt, op' ≠ Op.tick dt := by
      intro op' hop' dt
      apply hpnotick op'
      rw [hsplit]
      rcases List.mem_append.1 hop' with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
    have hstat : (net1.applyAdv apps (.land op)).chain.statusOf c2 = net1.chain.statusOf c2 := by
      simp only [NetworkState.applyAdv]
      cases h : net1.chain.apply apps p op with
      | none => rfl
      | some s' => exact statusOf_apply_of_not_targets h hop2
    have hnow : (net1.applyAdv apps (.land op)).chain.now = net1.chain.now := by
      simp only [NetworkState.applyAdv]
      cases h : net1.chain.apply apps p op with
      | none => rfl
      | some s' => exact Adjudicator.apply_now_eq_of_not_tick hopnt h
    have hfo' : (net1.applyAdv apps (.land op)).chain.finalOutcome c2.address = none := by
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hnow]
      (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
    have hfl' : ∀ t0 ch, (net1.applyAdv apps (.land op)).chain.statusOf c2 = .challenged t0 ch →
        D ≤ ch.deadline := by rw [hstat]; exact hfl
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (.land op)).sent, t0.state.channel = c2 →
        t0.state.isFinal = false := by rw [NetworkState.applyAdv_sent]; exact hsent
    have hlo' : v0now ≤ (net1.applyAdv apps (.land op)).chain.now := by rw [hnow]; exact hlo
    exact ih hpend' hpnotick' hDbound hlo' hfo' hfl' hsent'
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hpend hpnotick hDbound hlo hfo hfl hsent
    have hstat : (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c2 = net1.chain.statusOf c2 := by
      (simp? [NetworkState.applyAdv] says simp only [NetworkState.applyAdv, Adjudicator.tick_statusOf])
    have hadv : (net1.applyAdv apps (AdvMove.tick dt)).chain.now ≤ net2.chain.now := by
      (simpa? using hrest.now_le says simpa only using hrest.now_le)
    have hfo' : (net1.applyAdv apps (AdvMove.tick dt)).chain.finalOutcome c2.address = none := by
      have hfo0 : (net1.chain.statusOf c2).finalOutcome net1.chain.now = none := by
        (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat]
      rcases hst : net1.chain.statusOf c2 with s | ⟨t0, ch⟩ | ⟨t0, f, o⟩
      · (simp? [ChannelStatus.finalOutcome] says simp only [ChannelStatus.finalOutcome])
      · have hdl := hfl t0 ch hst
        have hlt : (net1.applyAdv apps (AdvMove.tick dt)).chain.now < ch.deadline :=
          lt_of_le_of_lt hadv (lt_of_lt_of_le hDbound hdl)
        simp only [ChannelStatus.finalOutcome, if_neg (not_le.mpr hlt)]
      · rw [hst] at hfo0; (simp? [ChannelStatus.finalOutcome] at hfo0 says simp only [ChannelStatus.finalOutcome, reduceCtorEq] at hfo0)
    have hfl' : ∀ t0 ch, (net1.applyAdv apps (AdvMove.tick dt)).chain.statusOf c2 = .challenged t0 ch →
        D ≤ ch.deadline := by rw [hstat]; exact hfl
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps (AdvMove.tick dt)).sent, t0.state.channel = c2 →
        t0.state.isFinal = false := by rw [NetworkState.applyAdv_sent]; exact hsent
    have hlo' : v0now ≤ (net1.applyAdv apps (AdvMove.tick dt)).chain.now :=
      le_trans hlo (NetworkState.applyAdv_now_le apps net1 (.tick dt))
    exact ih hpend hpnotick hDbound hlo' hfo' hfl' hsent'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hpend hpnotick hDbound hlo hfo hfl hsent
    have step : (net1.applyAdv apps m).chain.finalOutcome c2.address = none ∧
        (∀ t0 ch, (net1.applyAdv apps m).chain.statusOf c2 = .challenged t0 ch → D ≤ ch.deadline) := by
      cases m with
      | tick dt => exact absurd rfl (hnotick dt)
      | land op => exact absurd rfl (hnoland op)
      | deliver _ => (simpa? [NetworkState.applyAdv] using And.intro hfo hfl says simpa only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalOutcome_channel] using And.intro hfo hfl)
      | chain caller op =>
        simp only [NetworkState.applyAdv]
        cases h : net1.chain.apply apps caller op with
        | none => exact ⟨hfo, hfl⟩
        | some s' =>
          cases op with
          | deposit a e x =>
            have hop2 : ¬ Op.targets (Op.deposit a e x) c2 := by (simp? [Op.targets] says simp only [Op.targets, not_false_eq_true])
            have hntk : ∀ dt, Op.deposit a e x ≠ Op.tick dt := by intro dt heq; cases heq
            have hstat := statusOf_apply_of_not_targets h hop2
            have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
            refine ⟨?_, by rw [hstat]; exact hfl⟩
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
            (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
          | tick dt' =>
            have hstat : s'.statusOf c2 = net1.chain.statusOf c2 := by
              have hs' : net1.chain.tick dt' = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
              rw [← hs']; rfl
            have heq : (net1.applyAdv apps (AdvMove.chain caller (Op.tick dt'))).chain = s' := by
              (simp? [NetworkState.applyAdv, h] says simp only [NetworkState.applyAdv, h])
            have hadv : s'.now ≤ net2.chain.now := by
              have := hrest.now_le; rw [heq] at this; exact this
            have hfo0 : (net1.chain.statusOf c2).finalOutcome net1.chain.now = none := by
              (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
            refine ⟨?_, by rw [hstat]; exact hfl⟩
            simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat]
            rcases hst : net1.chain.statusOf c2 with s | ⟨t0, ch⟩ | ⟨t0, f, o⟩
            · (simp? [ChannelStatus.finalOutcome] says simp only [ChannelStatus.finalOutcome])
            · have hdl := hfl t0 ch hst
              have hlt : s'.now < ch.deadline := lt_of_le_of_lt hadv (lt_of_lt_of_le hDbound hdl)
              simp only [ChannelStatus.finalOutcome, if_neg (not_le.mpr hlt)]
            · rw [hst] at hfo0; (simp? [ChannelStatus.finalOutcome] at hfo0 says simp only [ChannelStatus.finalOutcome, reduceCtorEq] at hfo0)
          | transfer a b =>
            by_cases hop2 : Op.targets (Op.transfer a b) c2
            · exfalso
              simp only [Op.targets] at hop2; subst hop2
              obtain ⟨o, -, -, hfo2, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
              rw [hfo] at hfo2; exact absurd hfo2 (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
            · have hntk : ∀ dt, Op.transfer a b ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
          | reclaim rl rv =>
            by_cases hop2 : Op.targets (Op.reclaim (E := E) rl rv) c2
            · exfalso
              simp only [Op.targets] at hop2; subst hop2
              obtain ⟨oL, -, -, -, -, hfo2, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
              rw [hfo] at hfo2; exact absurd hfo2 (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
            · have hntk : ∀ dt, Op.reclaim (E := E) rl rv ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
          | challenge c' proof cand =>
            by_cases hop2 : Op.targets (Op.challenge c' proof cand) c2
            · simp only [Op.targets] at hop2; subst hop2
              obtain ⟨-, hsucc⟩ := Adjudicator.challenge_some h
              have hsnow : s'.now = net1.chain.now := by rw [hsucc]; rfl
              have hge : D ≤ net1.chain.now + c'.challengeDuration :=
                le_trans (le_trans hD (Nat.add_le_add_right hlo (2 * T.ε)))
                  (Nat.add_le_add_left hC2.timed net1.chain.now)
              refine ⟨?_, ?_⟩
              · rw [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hsnow, hsucc,
                  Adjudicator.statusOf_setStatus, if_pos rfl]
                have hself0 : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
                have hpos : 0 < c'.challengeDuration := lt_of_lt_of_le T.ε_pos (le_trans hself0 hC2.timed)
                have hndz : ¬ net1.chain.now + c'.challengeDuration ≤ net1.chain.now :=
                  not_le.mpr (Nat.lt_add_of_pos_right hpos)
                simp only [ChannelStatus.finalOutcome, if_neg hndz]
              · intro t0 ch hc
                rw [hsucc, Adjudicator.statusOf_setStatus, if_pos rfl] at hc
                simp only [ChannelStatus.challenged.injEq] at hc
                rw [← hc.2]; exact hge
            · have hntk : ∀ dt, Op.challenge c' proof cand ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
          | checkpoint c' proof cand =>
            by_cases hop2 : Op.targets (Op.checkpoint c' proof cand) c2
            · simp only [Op.targets] at hop2; subst hop2
              obtain ⟨-, hsucc⟩ := Adjudicator.checkpoint_some h
              refine ⟨?_, ?_⟩
              · rw [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hsucc,
                  Adjudicator.statusOf_setStatus, if_pos rfl]
                (simp? [ChannelStatus.finalOutcome] says simp only [ChannelStatus.finalOutcome])
              · intro t0 ch hc
                rw [hsucc, Adjudicator.statusOf_setStatus, if_pos rfl] at hc
                cases hc
            · have hntk : ∀ dt, Op.checkpoint c' proof cand ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
          | conclude c' ss' =>
            by_cases hop2 : Op.targets (Op.conclude c' ss') c2
            · exfalso
              simp only [Op.targets] at hop2; subst hop2
              obtain ⟨⟨-, hproof'⟩, -⟩ := Adjudicator.conclude_some h
              have hp' : p ∈ ss'.signers := hproof'.2.2 p (hproof'.1 ▸ hC2.mem)
              have hmem2 : ss' ∈ (Op.conclude c' ss').proofStates := by (simp? [Op.proofStates] says simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false])
              obtain ⟨t', htmem, hteq⟩ :=
                (hbounds.unforgeable net1 caller (.conclude c' ss') hfeas ss' hmem2).1 hp'
              have hnf := hsent t' htmem (by rw [hteq]; exact hproof'.1)
              have hxfinal : t'.state.isFinal = true := by rw [hteq]; exact hproof'.2.1
              rw [hnf] at hxfinal; exact absurd hxfinal (by (simp? says simp only [Bool.false_eq_true, not_false_eq_true]))
            · have hntk : ∀ dt, Op.conclude c' ss' ≠ Op.tick dt := by intro dt heq; cases heq
              have hstat := statusOf_apply_of_not_targets h hop2
              have hn := Adjudicator.apply_now_eq_of_not_tick hntk h
              refine ⟨?_, by rw [hstat]; exact hfl⟩
              simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstat, hn]
              (simpa? [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hfo)
    have hsent' : ∀ t0 ∈ (net1.applyAdv apps m).sent, t0.state.channel = c2 →
        t0.state.isFinal = false := by rw [NetworkState.applyAdv_sent]; exact hsent
    have hlo' : v0now ≤ (net1.applyAdv apps m).chain.now :=
      le_trans hlo (NetworkState.applyAdv_now_le apps net1 m)
    exact ih hpend hpnotick hDbound hlo' step.1 step.2 hsent'

/-- Once `c`'s own outcome is finalized, it never goes back to `none`:
    `Adjudicator.finalizedWith_apply` shows the FIXED finalization value
    is permanent over one step; `ChannelStatus.finalizedWith_isSome_iff`
    converts between "finalized at all" (`finalizedWith`) and "has a
    stored outcome" (`finalOutcome`) at each end, since the two coincide
    (`isSome`-wise) for every `ChannelStatus` constructor. Used by
    `finalOutcome_ne_none_steps`. -/
theorem finalOutcome_isSome_apply {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') {c : FixedPart}
    (hs : s.finalOutcome c.address ≠ none) : s'.finalOutcome c.address ≠ none := by
  have hiso : (s.finalizedWith c.address).isSome := by
    rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
      ChannelStatus.finalizedWith_isSome_iff]
    rw [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hs
    exact Option.isSome_iff_ne_none.mpr hs
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hiso
  have hf' := Adjudicator.finalizedWith_apply h hf
  rw [FixedPart.address_eq, Adjudicator.finalOutcome_channel]
  rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel] at hf'
  have hiso' : ((s'.statusOf c).finalizedWith s'.now).isSome := by rw [hf']; rfl
  rw [ChannelStatus.finalizedWith_isSome_iff] at hiso'
  exact Option.isSome_iff_ne_none.mp hiso'

/-- `directly_funded_step` generalized from an external destination `d : E`
    to any channel destination `d : FixedPart` not itself yet finalized
    (`hdopen`): every case where the original used `Address.external d`'s
    own impossibility of equalling a channel address, this uses `hdopen`
    instead — a transfer or reclaim reading `d.address` as an
    ALREADY-finalized source/subchannel contradicts `hdopen` directly (via
    the very fact, `hf`/`hV`, that step's own precondition supplies). The
    conclusion drops the original's exact-tracking (never needed — only
    the `≥` bound is used downstream) in favor of `by_cases` at every spot
    a deposit or an unrelated transfer could, harmlessly, ALSO pay
    `d.address`. Used by `funded_step_addr`. -/
theorem directly_funded_step_open {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c d : FixedPart} {o : Allocation E} {amt : Coins}
    (hf : s.finalOutcome c.address = some (.allocation o))
    (ht : o.total ≤ s.balances.get c.address)
    (hdopen : s.finalOutcome d.address = none)
    (hd : o.find d.address = some ⟨d.address, .alloc amt⟩)
    (h : s.apply apps caller op = some s') :
    ∃ o' amt', s'.finalOutcome c.address = some (.allocation o') ∧
      o'.total ≤ s'.balances.get c.address ∧
      o'.find d.address = some ⟨d.address, .alloc amt'⟩ ∧
      s.balances.get d.address + amt ≤ s'.balances.get d.address + amt' := by
  have hf0 : (s.statusOf c).finalOutcome s.now = some (.allocation o) := by
    (simpa? [FixedPart.address_eq] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] using hf)
  have hfin : (s.statusOf c).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, hf0]; rfl
  cases op with
  | deposit a e x =>
    obtain ⟨⟨c', hac', -⟩, -, hb, -, hs, hn⟩ := Adjudicator.deposit_some h
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · (simpa? [FixedPart.address_eq, Adjudicator.statusOf_of_status hs, hn] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_of_status hs, hn] using hf)
    · rw [hb, Balances.get_add]
      by_cases hca : c.address = a
      · rw [if_pos hca]; (grind? says grind only)
      · rw [if_neg hca]; exact ht
    · rw [hb, Balances.get_add]
      by_cases hda : d.address = a
      · rw [if_pos hda]; (grind? says grind only)
      · rw [if_neg hda]
  | transfer a b =>
    by_cases hac : a = c
    · subst hac
      obtain ⟨o'', amt'', x, hf'', hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
        Adjudicator.transfer_some h
      rw [hf] at hf''
      simp only [Option.some.injEq, Outcome.allocation.injEq] at hf''
      subst hf''
      have hfo' : s'.finalOutcome a.address = some (.allocation (o.reduceOwed b x)) := by
        have hstatc : s'.statusOf a = (s.statusOf a).withOutcome (.allocation (o.reduceOwed b x)) :=
          by rw [Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_pos rfl]
        (simp? [FixedPart.address_eq, hstatc] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, ChannelStatus.finalOutcome_withOutcome])
      have hxb : x ≤ o.owed b := hxeq ▸ paidTo_first_entry_only _ _ _
      have htot := Allocation.total_reduceOwed o b hxb
      have hxh : x ≤ s.balances.get a.address := hxeq ▸ Allocation.paidTo_le_held _ _ _
      have hcd : (d.address : Address E) ≠ a.address := by
        intro hh; rw [hh, hf] at hdopen; (simp? at hdopen says simp only [reduceCtorEq] at hdopen)
      have hfind' := Allocation.find_reduceOwed o b d.address x
      by_cases hbd : d.address = b
      · subst hbd
        rw [if_pos rfl, hd] at hfind'
        simp only [Option.map_some] at hfind'
        have hxamt : x ≤ amt := by
          have heq : o.owed d.address = amt := by rw [Allocation.owed, hd]; rfl
          rw [heq] at hxb; exact hxb
        refine ⟨o.reduceOwed d.address x, amt - x, hfo', ?_, hfind', ?_⟩
        · rw [hbal, Balances.get_sub, if_pos rfl]
          by_cases hba : (d.address : Address E) = a.address
          · rw [hba, Balances.get_add, if_pos rfl]; (grind? says grind only)
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; (grind? says grind only)
        · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_pos rfl]
          (grind? says grind only)
      · rw [if_neg hbd] at hfind'
        refine ⟨o.reduceOwed b x, amt, hfo', ?_, by rw [hfind']; exact hd, ?_⟩
        · rw [hbal, Balances.get_sub, if_pos rfl]
          by_cases hba : b = a.address
          · rw [hba, Balances.get_add, if_pos rfl]; (grind? says grind only [#5d85])
          · rw [Balances.get_add, if_neg (Ne.symm hba)]; (grind? says grind only)
        · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add, if_neg hbd]
    · obtain ⟨o'', amt'', x, hf'', hfind, hxeq, hbal, -, hstat, hnow, hak, hbf⟩ :=
        Adjudicator.transfer_some h
      have haddr : (c.address : Address E) ≠ a.address := by
        intro hh; injection hh with hh'; exact hac hh'.symm
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [Adjudicator.statusOf_of_status hstat, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac)]
      have hcd : (d.address : Address E) ≠ a.address := by
        intro hh; rw [hh, hf''] at hdopen; (simp? at hdopen says simp only [reduceCtorEq] at hdopen)
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal, Balances.get_sub, if_neg haddr, Balances.get_add]
        by_cases hbc : c.address = b
        · rw [if_pos hbc]; (grind? says grind only)
        · rw [if_neg hbc]; exact ht
      · rw [hbal, Balances.get_sub, if_neg hcd, Balances.get_add]
        by_cases hbd : d.address = b
        · rw [if_pos hbd]; (grind? says grind only)
        · rw [if_neg hbd]
  | reclaim l v =>
    by_cases hcl : l = c
    · subst hcl
      obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      rw [hf] at hL
      simp only [Option.some.injEq, Outcome.allocation.injEq] at hL
      subst hL
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      have hfo' : s'.finalOutcome l.address = some (.allocation
          (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address)) := by
        have hstatl : s'.statusOf l = (s.statusOf l).withOutcome (.allocation
            (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address)) := by
          rw [hsucc, Adjudicator.statusOf_setStatus, if_pos rfl]
        (simp? [FixedPart.address_eq, hstatl] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatl, ChannelStatus.finalOutcome_withOutcome])
      have h1 : (o.addTo left (oV.amountAt 0)).total ≤ o.total + oV.amountAt 0 :=
        Allocation.total_addTo_le _ _ _
      have h2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).total ≤
          (o.addTo left (oV.amountAt 0)).total + oV.amountAt 1 :=
        Allocation.total_addTo_le _ _ _
      have h3 : o.owed v.address ≤ (o.addTo left (oV.amountAt 0)).owed v.address :=
        Allocation.owed_addTo_ge _ _ _ _
      have h4 : (o.addTo left (oV.amountAt 0)).owed v.address ≤
          ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).owed v.address :=
        Allocation.owed_addTo_ge _ _ _ _
      have h5 := Allocation.total_remove_le
        ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)) v.address
      have hvo : o.owed v.address = x := by
        simp only [Allocation.owed, hfind, Option.map_some, Option.getD_some, Entry.amount_mk,
          Item.amount_guarantee]
      have had : (d.address : Address E) ≠ v.address := by
        intro hh
        rw [hh] at hdopen
        have hiso : (s.finalizedWith v.address).isSome := by rw [hV]; rfl
        rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
          ChannelStatus.finalizedWith_isSome_iff] at hiso
        rw [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hdopen
        rw [hdopen] at hiso
        (simp? at hiso says simp only [Option.isSome_none, Bool.false_eq_true] at hiso)
      have hfind1 : (o.addTo left (oV.amountAt 0)).find d.address =
          some ⟨d.address, .alloc (if d.address = left
            then amt + oV.amountAt 0 else amt)⟩ := by
        by_cases hld : d.address = left
        · rw [if_pos hld, ← hld, Allocation.find_addTo_self, hd]; (simp? says simp only [FixedPart.address_eq, Option.map_some, Entry.amount_mk, Item.amount_alloc])
        · rw [if_neg hld, Allocation.find_addTo_of_ne _ _ hld, hd]
      have hfind2 : ((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).find
          d.address = some ⟨d.address, .alloc
            ((if d.address = left then amt + oV.amountAt 0 else amt) +
              (if d.address = right then oV.amountAt 1 else 0))⟩ := by
        by_cases hrd : d.address = right
        · rw [if_pos hrd, ← hrd, Allocation.find_addTo_self, hfind1]; (simp? says simp only [FixedPart.address_eq, Option.map_some, Entry.amount_mk, Item.amount_alloc])
        · rw [if_neg hrd, Allocation.find_addTo_of_ne _ _ hrd, hfind1]; (simp? says simp only [FixedPart.address_eq, add_zero])
      have hfind3 : (((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove
          v.address).find d.address = some ⟨d.address, .alloc
            ((if d.address = left then amt + oV.amountAt 0 else amt) +
              (if d.address = right then oV.amountAt 1 else 0))⟩ := by
        rw [Allocation.find_remove, if_neg had, hfind2]
      refine ⟨_, _, hfo', ?_, hfind3, ?_⟩
      · rw [hbal']; (grind? says grind only)
      · rw [hbal']
        split <;> split <;> (grind? says grind only)
    · obtain ⟨oL, oV, x, left, right, hL, hV, hfind, -, -, hxeq, hsucc, hlk, hvk⟩ :=
        Adjudicator.reclaim_some h
      have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcl)]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | challenge c' proof candidate =>
    obtain ⟨⟨-, -, -, hm⟩, hsucc⟩ := Adjudicator.challenge_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      rw [Adjudicator.mode_eq] at hm
      rcases hm with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at hfin <;> cases hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | checkpoint c' proof candidate =>
    obtain ⟨⟨ho, -, -, -⟩, hsucc⟩ := Adjudicator.checkpoint_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      exact ho hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | conclude c' ss =>
    obtain ⟨⟨ho, -⟩, hsucc⟩ := Adjudicator.conclude_some h
    by_cases hcc : c = c'
    · exfalso
      subst hcc
      exact ho hfin
    · have hstatc : s'.statusOf c = s.statusOf c := by
        rw [hsucc, Adjudicator.statusOf_setStatus, if_neg hcc]
      have hnow : s'.now = s.now := by rw [hsucc]; rfl
      have hbal' : s'.balances = s.balances := by rw [hsucc]; rfl
      refine ⟨o, amt, ?_, ?_, hd, ?_⟩
      · (simpa? [FixedPart.address_eq, hstatc, hnow] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hstatc, hnow] using hf)
      · rw [hbal']; exact ht
      · rw [hbal']
  | tick dt =>
    have hs' : s.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
    subst hs'
    refine ⟨o, amt, ?_, ?_, hd, ?_⟩
    · (simpa? [FixedPart.address_eq] using
        ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt) says simpa only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.tick_statusOf, Adjudicator.tick_now] using ChannelStatus.finalOutcome_mono hf0 (Nat.le_add_right s.now dt))
    · (simpa? using ht says simpa only [Adjudicator.tick_balances, FixedPart.address_eq] using ht)
    · (simp? says simp only [FixedPart.address_eq, Adjudicator.tick_balances, Std.le_refl])

/-- An adversary move changes the chain by at most one successful
    `Adjudicator.apply` (`Step`): `deliver` and a failed call leave the
    chain as it was. -/
theorem NetworkState.applyAdv_steps (apps : Apps E) {p : Participant} (net : NetworkState E p)
    (m : AdvMove E) : Relation.ReflTransGen (Step apps) net.chain (net.applyAdv apps m).chain := by
  cases m with
  | chain caller op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps caller op with
    | none => exact .refl
    | some s' => exact .single (Step.mk caller op net.chain s' h)
  | deliver ss => exact .refl
  | tick dt => exact .single (Step.mk p (.tick dt) net.chain (net.chain.tick dt) rfl)
  | land op =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps p op with
    | none => exact .refl
    | some s' => exact .single (Step.mk p op net.chain s' h)

/-- A round's adversary play changes the chain only by successful steps
    (`NetworkState.applyAdv_steps`, by induction). -/
theorem Threat.RoundSeq.steps {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (h : Threat.RoundSeq apps T t pending net net') :
    Relation.ReflTransGen (Step apps) net.chain net'.chain := by
  induction h with
  | nil => exact .refl
  | land _ _ ih => exact (NetworkState.applyAdv_steps apps _ _).trans ih
  | tick _ _ _ ih => exact (NetworkState.applyAdv_steps apps _ _).trans ih
  | other _ _ _ _ ih => exact (NetworkState.applyAdv_steps apps _ _).trans ih

/-- A channel that has a final outcome keeps one over every run of steps
    (`finalOutcome_isSome_apply`, by induction). -/
theorem finalOutcome_ne_none_steps {apps : Apps E} {s s' : Adjudicator E}
    (h : Relation.ReflTransGen (Step apps) s s') {c : FixedPart}
    (hs : s.finalOutcome c.address ≠ none) : s'.finalOutcome c.address ≠ none := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih =>
    cases hstep with
    | mk caller op _ _ happly => exact finalOutcome_isSome_apply happly ih

/-- An address with no final outcome at the end of a run of steps has none
    at the start (`finalOutcome_ne_none_steps`). An external address never
    has a final outcome (`Adjudicator.finalOutcome`). -/
theorem finalOutcome_none_of_steps {apps : Apps E} {s s' : Adjudicator E}
    (h : Relation.ReflTransGen (Step apps) s s') {x : Address E}
    (hx : s'.finalOutcome x = none) : s.finalOutcome x = none := by
  cases x with
  | external d => rfl
  | channel c =>
    by_contra hs
    exact finalOutcome_ne_none_steps h (c := c) hs hx

omit [DecidableEq E] in
/-- A channel has no final outcome exactly when it is not finalized
    (`ChannelStatus.finalizedWith_isSome_iff`). -/
theorem finalOutcome_eq_none_iff {s : Adjudicator E} {c : FixedPart} :
    s.finalOutcome c.address = none ↔ s.finalizedWith c.address = none := by
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
    Adjudicator.finalizedWith_channel, ← Option.not_isSome_iff_eq_none,
    ChannelStatus.finalizedWith_isSome_iff]

/-- An address with no final outcome loses no coins in one step: an
    external destination only gains (`paid_out_monotone`), and an open
    channel pays out nothing (`balances_mono_while_open_step`). -/
theorem balance_mono_open_step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {x : Address E} (hx : s.finalOutcome x = none)
    (h : s.apply apps caller op = some s') : s.balances.get x ≤ s'.balances.get x := by
  cases x with
  | external d => exact paid_out_monotone apps s s' (Step.mk caller op s s' h) d
  | channel c => exact balances_mono_while_open_step (c := c) hx h

/-- `balance_mono_open_step` over a run of steps that ends with `x` open. -/
theorem balance_mono_open_steps {apps : Apps E} {s s' : Adjudicator E}
    (h : Relation.ReflTransGen (Step apps) s s') {x : Address E}
    (hx : s'.finalOutcome x = none) : s.balances.get x ≤ s'.balances.get x := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih =>
    cases hstep with
    | mk caller op _ _ happly =>
      have hmid := finalOutcome_none_of_steps (.single (Step.mk caller op _ _ happly)) hx
      exact le_trans (ih hmid) (balance_mono_open_step hmid happly)

/-- `directly_funded_step` for a destination address `x` with no final
    outcome: an external destination (`directly_funded_step`) or an open
    channel (`directly_funded_step_open`). -/
theorem funded_step_addr {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c : FixedPart} {o : Allocation E} {x : Address E} {amt : Coins}
    (hf : s.finalOutcome c.address = some (.allocation o))
    (ht : o.total ≤ s.balances.get c.address) (hx : s.finalOutcome x = none)
    (hd : o.find x = some ⟨x, .alloc amt⟩) (h : s.apply apps caller op = some s') :
    ∃ o' amt', s'.finalOutcome c.address = some (.allocation o') ∧
      o'.total ≤ s'.balances.get c.address ∧
      o'.find x = some ⟨x, .alloc amt'⟩ ∧
      s.balances.get x + amt ≤ s'.balances.get x + amt' := by
  cases x with
  | external d => exact directly_funded_step hf ht hd h
  | channel d => exact directly_funded_step_open (d := d) hf ht hx hd h

/-- The slack invariant of a ledger channel `c` that pays an address `x`:
    `c` is finalized with `.allocation o`, its current allocation `o1` is
    covered by its balance, and the balance of `x` plus the entry of `x` in
    `o1` is at least `B`. -/
abbrev Adjudicator.PaysAtLeast (s : Adjudicator E) (c : FixedPart) (o : Allocation E)
    (x : Address E) (B : Coins) : Prop :=
  s.finalizedWith c.address = some (.allocation o) ∧
    ∃ o1 amt1, s.finalOutcome c.address = some (.allocation o1) ∧
      o1.total ≤ s.balances.get c.address ∧ o1.find x = some ⟨x, .alloc amt1⟩ ∧
      B ≤ s.balances.get x + amt1

/-- The slack invariant stays over one step while `x` has no final outcome
    (`Adjudicator.finalizedWith_apply`, `funded_step_addr`). -/
theorem Adjudicator.PaysAtLeast.step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c : FixedPart} {o : Allocation E} {x : Address E} {B : Coins}
    (hp : s.PaysAtLeast c o x B) (hx : s.finalOutcome x = none)
    (h : s.apply apps caller op = some s') : s'.PaysAtLeast c o x B := by
  obtain ⟨hfz, o1, amt1, hf1, ht1, hd1, hB1⟩ := hp
  obtain ⟨o', amt', hf', ht', hd', hle⟩ := funded_step_addr hf1 ht1 hx hd1 h
  exact ⟨Adjudicator.finalizedWith_apply h hfz, o', amt', hf', ht', hd', le_trans hB1 hle⟩

/-- `Adjudicator.PaysAtLeast.step` over a run of steps that ends with `x`
    open. -/
theorem Adjudicator.PaysAtLeast.steps {apps : Apps E} {s s' : Adjudicator E}
    (h : Relation.ReflTransGen (Step apps) s s') {c : FixedPart} {o : Allocation E}
    {x : Address E} {B : Coins} (hx : s'.finalOutcome x = none) (hp : s.PaysAtLeast c o x B) :
    s'.PaysAtLeast c o x B := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih =>
    cases hstep with
    | mk caller op _ _ happly =>
      have hmid := finalOutcome_none_of_steps (.single (Step.mk caller op _ _ happly)) hx
      exact (ih hmid).step hmid happly

/-- The three phases of a ledger channel `c` with the conclusion outcome
    `.allocation o`, seen from a destination `x` with the entry `amt0` in
    `o` and the starting balance `B`: `c` is open with `o.total` covered and
    `x` holds at least `B`; or the slack invariant holds for `B + amt0`; or
    `c` is finalized with an outcome other than `.allocation o`. -/
abbrev Adjudicator.PayPhase (s : Adjudicator E) (c : FixedPart) (o : Allocation E)
    (x : Address E) (amt0 B : Coins) : Prop :=
  (s.finalOutcome c.address = none ∧ o.total ≤ s.balances.get c.address ∧
      B ≤ s.balances.get x) ∨
    s.PaysAtLeast c o x (B + amt0) ∨
    ∃ Ω₀, s.finalizedWith c.address = some Ω₀ ∧ Ω₀ ≠ .allocation o

/-- One step keeps `Adjudicator.PayPhase` while `x` has no final outcome.
    While `c` is open, `c` keeps `o.total` covered (`open_step`) and `x`
    keeps `B` (`balance_mono_open_step`). The step that first finalizes `c`
    with `.allocation o` records `o` as the current allocation, so the
    slack invariant starts with the entry `amt0`. A finalized outcome never
    changes (`Adjudicator.finalizedWith_apply`). -/
theorem Adjudicator.PayPhase.step {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} {c : FixedPart} {o : Allocation E} {x : Address E} {amt0 B : Coins}
    (hd0 : o.find x = some ⟨x, .alloc amt0⟩) (hx : s.finalOutcome x = none)
    (h : s.apply apps caller op = some s') (hph : s.PayPhase c o x amt0 B) :
    s'.PayPhase c o x amt0 B := by
  rcases hph with ⟨hnone, ht, hB⟩ | hp | ⟨Ω₀, hfz, hne⟩
  · have hBx : B ≤ s'.balances.get x := le_trans hB (balance_mono_open_step hx h)
    rcases open_step h hnone ht with ⟨hnone', ht'⟩ | ⟨Ω₀, hfz', hf', ht'⟩
    · exact Or.inl ⟨hnone', ht', hBx⟩
    · by_cases hΩ : Ω₀ = .allocation o
      · subst hΩ
        exact Or.inr (Or.inl ⟨hfz', o, amt0, hf', ht', hd0, Nat.add_le_add_right hBx amt0⟩)
      · exact Or.inr (Or.inr ⟨Ω₀, hfz', hΩ⟩)
  · exact Or.inr (Or.inl (hp.step hx h))
  · exact Or.inr (Or.inr ⟨Ω₀, Adjudicator.finalizedWith_apply h hfz, hne⟩)

/-- `Adjudicator.PayPhase.step` over a run of steps that ends with `x`
    open. -/
theorem Adjudicator.PayPhase.steps {apps : Apps E} {s s' : Adjudicator E}
    (h : Relation.ReflTransGen (Step apps) s s') {c : FixedPart} {o : Allocation E}
    {x : Address E} {amt0 B : Coins} (hd0 : o.find x = some ⟨x, .alloc amt0⟩)
    (hx : s'.finalOutcome x = none) (hph : s.PayPhase c o x amt0 B) :
    s'.PayPhase c o x amt0 B := by
  induction h with
  | refl => exact hph
  | tail _ hstep ih =>
    cases hstep with
    | mk caller op _ _ happly =>
      have hmid := finalOutcome_none_of_steps (.single (Step.mk caller op _ _ happly)) hx
      exact (ih hmid).step hd0 hmid happly

/-- When `c` is finalized with `.allocation o`, the only phase left is the
    slack invariant: an open `c` is not finalized
    (`finalOutcome_eq_none_iff`), and a finalized outcome is unique. -/
theorem Adjudicator.PayPhase.pays {s : Adjudicator E} {c : FixedPart} {o : Allocation E}
    {x : Address E} {amt0 B : Coins} (hΩ : s.finalizedWith c.address = some (.allocation o))
    (hph : s.PayPhase c o x amt0 B) : s.PaysAtLeast c o x (B + amt0) := by
  rcases hph with ⟨hnone, -, -⟩ | hp | ⟨Ω₀, hfz, hne⟩
  · rw [finalOutcome_eq_none_iff, hΩ] at hnone
    cases hnone
  · exact hp
  · exact absurd (Option.some.inj (hfz.symm.trans hΩ)) hne

/-- The round that lands `p`'s own `transfer c x` pays `x` its slack. The
    slack invariant holds up to the landing
    (`Adjudicator.PaysAtLeast.steps`). The landing pays `x` its whole entry,
    because `c`'s balance covers its allocation (`transfer_can_happen`).
    After the landing, `x` has no final outcome, so it loses no coins
    (`balance_mono_open_steps`). -/
theorem transfer_round_pays {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {c : FixedPart} {o : Allocation E} {x : Address E} {B : Coins}
    (hk : c.kind = .ledger) (hxf : x.fundable = true) (hxc : x ≠ c.address)
    {net net' : NetworkState E p} (hseq : Threat.RoundSeq apps T t [.transfer c x] net net')
    (hx : net'.chain.finalOutcome x = none) (hpays : net.chain.PaysAtLeast c o x B) :
    B ≤ net'.chain.balances.get x := by
  obtain ⟨m, h1, h2⟩ := Threat.RoundSeq.peel_one _ net net' hseq
  have hxm := finalOutcome_none_of_steps
    ((NetworkState.applyAdv_steps apps m (.land (.transfer c x))).trans h2.steps) hx
  obtain ⟨-, o1, amt1, hf1, ht1, hd1, hB1⟩ := hpays.steps h1.steps hxm
  obtain ⟨s', hs', hbal⟩ := transfer_can_happen m.chain c x o1 amt1 hk hxf hf1 hd1
  have happly : m.chain.apply apps p (.transfer c x) = some s' := by
    rw [Adjudicator.apply_transfer]; exact hs'
  have hchain : (m.applyAdv apps (.land (.transfer c x))).chain = s' := by
    (simp? [NetworkState.applyAdv, happly] says simp only [NetworkState.applyAdv, happly])
  have hmono := balance_mono_open_steps h2.steps hx
  rw [hchain, hbal, if_neg hxc] at hmono
  have hpaid : amt1 ≤ o1.paidTo (m.chain.balances.get c.address) x := by
    have hsub : o1.dedup.total ≤ o1.total :=
      Allocation.total_le_of_sublist (Allocation.dedupFrom_sublist [] o1)
    have hdedup_le : o1.dedup.total ≤ m.chain.balances.get c.address := le_trans hsub ht1
    have howed1 : o1.owed x = amt1 := by (simp? [Allocation.owed, hd1] says simp only [Allocation.owed, hd1, Option.map_some, Entry.amount_mk, Item.amount_alloc, Option.getD_some])
    have hdedup_owed : o1.dedup.owed x = amt1 := by rw [Allocation.owed_dedup]; exact howed1
    have hle := Allocation.owed_le_payout_get hdedup_le x
    rw [hdedup_owed] at hle
    rwa [Allocation.paidTo_eq_get]
  exact le_trans hB1 (le_trans (Nat.add_le_add_left hpaid _) hmono)

/-- Nitro:1046-1047 for a ledger channel `c` with a conclusion proof for
    `.allocation o`: `p` concludes `c` (`conclude_round_finalized`), then
    transfers the entry of `x` (`transfer_round_pays`). No move waits.
    `x` gains its whole entry `amt0` over the two rounds if no adversary
    play in the two rounds gives `x` a final outcome (`hxopen`). In the
    first round, `c` keeps its balance until it finalizes with
    `.allocation o` (`Adjudicator.PayPhase.steps`). -/
theorem conclude_transfer_pays (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (net : NetworkState E p) {c : FixedPart} {ss : SignedState E}
    {o : Allocation E} {x : Address E} {amt0 : Coins}
    (hk : c.kind = .ledger) (hp : p ∈ c.participants) (hh : net.Holds ss)
    (hproof : ConclusionProof c ss) (hΩ : ss.state.outcome = .allocation o)
    (hsent : ∀ t ∈ net.sent, t.state.channel = c → t.state.isFinal = true →
      t.state.outcome = .allocation o)
    (hopen : net.chain.finalizedWith c.address = none)
    (hdur : 2 * T.ε ≤ c.challengeDuration) (hpend : net.DeadlineAfter c T.ε)
    (htot : o.total ≤ net.chain.balances.get c.address)
    (hd : o.find x = some ⟨x, .alloc amt0⟩) (hxf : x.fundable = true) (hxc : x ≠ c.address)
    (hxopen : ∀ n1 n2 : NetworkState E p,
      Threat.RoundSeq apps T net.chain.now [.conclude c ss] net n1 →
      n1.chain.now < net.chain.now + T.ε →
      Threat.RoundSeq apps T n1.chain.now [.transfer c x] n1 n2 →
      n2.chain.now < n1.chain.now + T.ε → n2.chain.finalOutcome x = none) :
    UnbeatableNoWait apps T
      (fun net' => net.chain.balances.get x + amt0 ≤ net'.chain.balances.get x) net := by
  refine UnbeatableIn.move (.chain (.conclude c ss)) trivial
    (by (simpa? [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hh says simpa only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hh)) ?_
  intro n1 hround1
  obtain ⟨hseq1, hε1⟩ := hround1
  simp only [HonestMove.calls_chain] at hseq1
  simp only [NetworkState.applyHonest_chain]
  refine UnbeatableIn.move (.chain (.transfer c x)) trivial
    (by (simp? [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] says simp only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.not_mem_nil, IsEmpty.forall_iff, implies_true])) ?_
  intro n2 hround2
  obtain ⟨hseq2, hε2⟩ := hround2
  simp only [HonestMove.calls_chain] at hseq2
  have hx2 := hxopen n1 n2 hseq1 hε1 hseq2 hε2
  have hx1 := finalOutcome_none_of_steps hseq2.steps hx2
  have hfin := conclude_round_finalized A.toBounds hp hdur hproof hΩ ⟨hseq1, hε1⟩ hsent hopen hpend
  have hph : n1.chain.PayPhase c o x amt0 (net.chain.balances.get x) :=
    Adjudicator.PayPhase.steps hseq1.steps hd hx1
      (Or.inl ⟨finalOutcome_eq_none_iff.mpr hopen, htot, le_refl _⟩)
  apply UnbeatableIn.done
  (simpa? using transfer_round_pays hk hxf hxc hseq2 hx2 (hph.pays hfin) says simpa only [NetworkState.applyHonest_chain] using transfer_round_pays hk hxf hxc hseq2 hx2 (hph.pays hfin))

/-- Nitro-49 (Nitro:997-1047, §5.4.4 Partial Withdrawal from a Ledger Channel).
    Nitro:1046-1047: "A was able to withdraw their funds instantly, without
    having to wait for the channel timeout." With the conclusion proof for
    `[L ↦ (L' : a + b + c, A : a')]_{A,B}` and `⟦L : x⟧`, `A` obtains `a'`
    at `dA` with no wait, and `L'` is funded with `a + b + c` for `A` and
    `B`. `L'` cannot finalize before `L` pays it: no running challenge of
    `L'` ends within `2 * ε`, no participant signed a final state of `L'`,
    and a challenge of `L'` lasts at least `2 * ε`.

    Design decision 2026-10-29: `v` is `n.views` for a reachable `Network`
    `n` (`Nitro.network`); a reachable chain never holds coins in `χ`, a
    virtual-kind channel (`Reachable.balances_virtual_zero`,
    `Nitro.network_chain_reachable`), which is the unreachable
    counterexample's shape. `v` and `hv` stay as they were: the shorter
    restatement adds `n`, `hr` and the link `hvn`, rather than rewriting
    every one of this theorem's existing uses of `v` to `n.views`. -/
theorem ledger_partial_withdrawal (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Nitro.ReachableNetwork apps Ts)
    (hvn : v = n.state.views) (A B : Participant) (dA dB : E)
    (L L' : LedgerChannel) (hL'c : (L' : FixedPart).RunsConsensus apps) (χ : FixedPart)
    (a b c a' : Coins)
    (hLp : (L : FixedPart).participants = [A, B])
    (hL'p : (L' : FixedPart).participants = [A, B]) (hLL' : (L : FixedPart) ≠ (L' : FixedPart))
    (hbal : v.HoldsBalance (L : FixedPart).address (a + b + c + a'))
    (hconc : Concluded v (L : FixedPart)
      (.allocation [alloc (L' : FixedPart).address (a + b + c), alloc (.external dA) a']))
    (hsent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = (L : FixedPart) → t.state.isFinal = true →
      t.state.outcome =
        .allocation [alloc (L' : FixedPart).address (a + b + c), alloc (.external dA) a'])
    (hopen : ∀ p, (v p).chain.finalizedWith (L : FixedPart).address = none)
    (hdur : ∀ p, 2 * (Ts.T p).ε ≤ (L : FixedPart).challengeDuration ∧
      2 * (Ts.T p).ε ≤ (L' : FixedPart).challengeDuration)
    (hpend : ∀ p, (v p).DeadlineAfter (L : FixedPart) (Ts.T p).ε ∧
      (v p).DeadlineAfter (L' : FixedPart) (2 * (Ts.T p).ε))
    (hL'open : ∀ p, (v p).chain.finalOutcome (L' : FixedPart).address = none)
    (hL'sent : ∀ p, ∀ t ∈ (v p).sent, t.state.channel = (L' : FixedPart) → t.state.isFinal = false)
    (hL'out : v.FinalizableBy apps Ts (L' : FixedPart)
      (.allocation [alloc (.external dA) a, alloc (.external dB) b, alloc χ.address c]) [A, B]) :
    UnbeatableNoWait apps (Ts.T A)
      (fun net' => (v A).chain.balances.get (.external dA) + a' ≤
        net'.chain.balances.get (.external dA))
      (v A) ∧
    FundedFor apps (Ts.T A) (L' : FixedPart) (a + b + c) (v A) ∧
    FundedFor apps (Ts.T B) (L' : FixedPart) (a + b + c) (v B) := by
  obtain_reach ⟨n, hr⟩ := n
  obtain ⟨L, hLk⟩ := L
  obtain ⟨L', hL'k⟩ := L'
  dsimp only at hLp hL'p hLL' hbal hconc hsent hopen hdur hpend hL'open hL'sent hL'out hL'c ⊢
  have hA : A ∈ L.participants := by (simp? [hLp] says simp only [hLp, List.mem_cons, List.not_mem_nil, or_false, true_or])
  have hB : B ∈ L.participants := by (simp? [hLp] says simp only [hLp, List.mem_cons, List.not_mem_nil, or_false, or_true])
  have hA' : A ∈ L'.participants := by (simp? [hL'p] says simp only [hL'p, List.mem_cons, List.not_mem_nil, or_false, true_or])
  have hB' : B ∈ L'.participants := by (simp? [hL'p] says simp only [hL'p, List.mem_cons, List.not_mem_nil, or_false, or_true])
  have htot : ∀ p, Allocation.total [alloc L'.address (a + b + c), alloc (.external dA) a'] ≤
      (v p).chain.balances.get L.address := by
    intro p
    rw [hbal p]
    (simp? [Allocation.total, alloc] says simp only [Allocation.total, alloc, FixedPart.address_eq, List.map_cons, Entry.amount_mk, Item.amount_alloc, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Std.le_refl])
  have hfund : ∀ p, p ∈ L.participants → p ∈ L'.participants →
      FundedFor apps (Ts.T p) L' (a + b + c) (v p) := by
    intro p hp hp'
    obtain ⟨ss, hh, hproof, hΩ⟩ := hconc p hp
    have hxopen : ∀ n1 n2 : NetworkState E p,
        Threat.RoundSeq apps (Ts.T p) (v p).chain.now [.conclude L ss] (v p) n1 →
        n1.chain.now < (v p).chain.now + (Ts.T p).ε →
        Threat.RoundSeq apps (Ts.T p) n1.chain.now [.transfer L L'.address] n1 n2 →
        n2.chain.now < n1.chain.now + (Ts.T p).ε → n2.chain.finalOutcome L'.address = none := by
      intro n1 n2 hseq1 hε1 hseq2 hε2
      have hε2ε : (Ts.T p).ε ≤ 2 * (Ts.T p).ε := by rw [Nat.two_mul]; exact Nat.le_add_left _ _
      have hb1 : n1.chain.now < (v p).chain.now + 2 * (Ts.T p).ε :=
        lt_of_lt_of_le hε1 (Nat.add_le_add_left hε2ε _)
      have hb2 : n2.chain.now < (v p).chain.now + 2 * (Ts.T p).ε := by
        rw [Nat.two_mul, ← Nat.add_assoc]
        exact lt_of_lt_of_le hε2 (Nat.add_le_add_right (le_of_lt hε1) _)
      obtain ⟨hfo1, hfl1, hs1⟩ := channel_stays_open_round (Ts.ok p).toBounds ⟨⟨hL'c, hp'⟩, (hdur p).2⟩
        (D := (v p).chain.now + 2 * (Ts.T p).ε) (v0now := (v p).chain.now) le_rfl
        hseq1 (by (simpa? [Op.targets] using hLL' says simpa only [List.mem_cons, List.not_mem_nil, or_false, Op.targets, forall_eq, ne_eq] using hLL')) (by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, ne_eq, forall_eq, reduceCtorEq, not_false_eq_true, implies_true])) hb1 le_rfl (hL'open p)
        (hpend p).2 (hL'sent p)
      exact (channel_stays_open_round (Ts.ok p).toBounds ⟨⟨hL'c, hp'⟩, (hdur p).2⟩
        (D := (v p).chain.now + 2 * (Ts.T p).ε) (v0now := (v p).chain.now) le_rfl hseq2
        (by (simpa? [Op.targets] using hLL' says simpa only [FixedPart.address_eq, List.mem_cons, List.not_mem_nil, or_false, Op.targets, forall_eq, ne_eq] using hLL')) (by (simp? says simp only [FixedPart.address_eq, List.mem_cons, List.not_mem_nil, or_false, ne_eq, forall_eq, reduceCtorEq, not_false_eq_true, implies_true])) hb2 hseq1.now_le hfo1 hfl1 hs1).1
    have hU := conclude_transfer_pays apps (Ts.T p) (Ts.ok p) (v p) hLk hp hh hproof hΩ
      (hsent p) (hopen p) (hdur p).1 (hpend p).1 (htot p) (x := L'.address) (amt0 := a + b + c)
      (by (simp? [Allocation.find, alloc] says simp only [Allocation.find, FixedPart.address_eq, alloc, decide_true, List.find?_cons_of_pos])) (by (simpa? [Address.fundable] using hL'k says simpa only [Address.fundable, FixedPart.address_eq, decide_eq_true_eq] using hL'k))
      (by (simpa? [FixedPart.address_eq] using Ne.symm hLL' says simpa only [FixedPart.address_eq, ne_eq, Address.channel.injEq] using Ne.symm hLL')) hxopen
    exact UnbeatableIn.mono (fun _ _ => trivial)
      (UnbeatableIn.imp (G2 := fun net' => net'.chain.DirectlyFundedWith L' (a + b + c))
        (fun h => le_trans (Nat.le_add_left _ _) h) hU)
  refine ⟨?_, hfund A hA hA', hfund B hB hB'⟩
  obtain ⟨ss, hh, hproof, hΩ⟩ := hconc A hA
  exact conclude_transfer_pays apps (Ts.T A) (Ts.ok A) (v A) hLk hA hh hproof hΩ (hsent A)
    (hopen A) (hdur A).1 (hpend A).1 (htot A) (x := .external dA) (amt0 := a')
    (by (simp? [Allocation.find, alloc] says simp only [Allocation.find, alloc, FixedPart.address_eq, reduceCtorEq, decide_false, Bool.false_eq_true, not_false_eq_true, List.find?_cons_of_neg, decide_true, List.find?_cons_of_pos])) rfl (by (simp? says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])) (fun _ _ _ _ _ _ => rfl)

/-- SATP-19, SATP-18. SATP:707-709, SATP:734: "The following two requirements
    guarantee that intermediary's funds are invariant:
    `voucher1.alice + voucher1.bob == x`" and the same for `voucher2`. Every
    state that `validateOutcomeChange` supports keeps the funded total of the
    start state, and a changed outcome pays the start state's first two
    destinations. -/
theorem satp_outcome_change_keeps_total (c : FixedPart) (alice bob : Participant)
    (proof : SupportProof E) (candidate : State E)
    (h : validateOutcomeChange c alice bob proof candidate = true) (s0 : SignedState E)
    (h0 : proof.head? = some s0) :
    candidate.outcome.fundedTotal = s0.state.outcome.fundedTotal ∧
    (candidate ≠ s0.state → ∃ da db a b, s0.state.outcome.pairDests = some (da, db) ∧
      candidate.outcome = .allocation [⟨da, .alloc a⟩, ⟨db, .alloc b⟩] ∧
      a + b = s0.state.outcome.fundedTotal) := by
  have key : ∀ (st : State E) da db a b, st.outcome = .allocation [⟨da, .alloc a⟩, ⟨db, .alloc b⟩] →
      st.outcome.fundedTotal = a + b := by
    intro st da db a b hc; rw [hc]; rfl
  match proof, h, h0 with
  | [s], h, h0 =>
    simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.head?_cons, Option.some.injEq] at h0; subst h0
    rw [← h.2]; exact ⟨rfl, fun hne => absurd rfl hne⟩
  | [s, ch], h, h0 =>
    simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.head?_cons, Option.some.injEq] at h0; subst h0
    obtain ⟨da, db, a, b, hp, ho, hab⟩ := validChallenge_outcome h.1
    rw [← h.2]
    exact ⟨(key _ da db a b ho).trans hab, fun _ => ⟨da, db, a, b, hp, ho, hab⟩⟩
  | [s, ch, re], h, h0 =>
    simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.head?_cons, Option.some.injEq] at h0; subst h0
    obtain ⟨da, db, a, b, hp, ho, hab⟩ := validResponse_outcome h.1
    rw [← h.2]
    exact ⟨(key _ da db a b ho).trans hab, fun _ => ⟨da, db, a, b, hp, ho, hab⟩⟩

omit [DecidableEq E] in
/-- A state doubly signed by every participant of a route's virtual channel
    (the shape of `hsigned`'s conclusion) pays `alice` and `bob` a total of
    `a0 + b0`: the setup-state branch's `originalOutcome` is itself such a
    pair, with `a = a0`, `b = b0`. -/
theorem satp_pairOutcome_of_hsigned {da db : E} {a0 b0 : Coins} {st : State E}
    (h : (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome da db a0 b0) ∨
      (st.isFinal = true ∧ ∃ a b, PairOutcome da db st.outcome a b ∧ a + b = a0 + b0)) :
    ∃ a b, PairOutcome da db st.outcome a b ∧ a + b = a0 + b0 := by
  rcases h with ⟨-, heq⟩ | ⟨-, hp⟩
  · exact ⟨a0, b0, heq, rfl⟩
  · exact hp

omit [DecidableEq E] in
/-- A pair outcome's destinations and funded total, read off its shape. -/
theorem satp_pairOutcome_pairDests_total {da db : E} {Ω : Outcome E} {a b : Coins}
    (h : PairOutcome da db Ω a b) :
    Ω.pairDests = some (Address.external da, Address.external db) ∧ Ω.fundedTotal = a + b := by
  unfold PairOutcome at h; subst h; exact ⟨rfl, rfl⟩

omit [DecidableEq E] in
/-- `ByAll` and `SignedIn` combine into the exact membership `hsigned`
    needs: every participant's signature on the state is listed in
    `signed`. -/
theorem satp_signed_membership {signed : List (Participant × State E)} {ss : SignedState E}
    (hall : ss.ByAll) (hsig : ss.SignedIn signed) :
    ∀ q ∈ ss.state.channel.participants, (q, ss.state) ∈ signed :=
  fun q hq => hsig.1 q (hall q hq)

omit [DecidableEq E] in
/-- SATP:682-690 `validStart` unfolded: a start state is signed by everyone
    and carries the given channel. -/
theorem satp_validStart_byAll {c : FixedPart} {s : SignedState E} (h : validStart c s = true) :
    s.ByAll ∧ s.state.channel = c := by
  unfold validStart at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.2, h.2⟩
  · cases h

/-- Every `validChallenge` run starts from a `validStart` state. -/
theorem satp_validChallenge_start {c : FixedPart} {alice bob : Participant} {s ch : SignedState E}
    (h : validChallenge c alice bob s ch = true) : validStart c s = true := by
  unfold validChallenge at h
  split at h
  · simp only [Bool.and_eq_true] at h
    repeat (obtain ⟨h, -⟩ := h)
    exact h
  · cases h

/-- Every `validResponse` run starts from a `validStart` state. -/
theorem satp_validResponse_start {c : FixedPart} {alice bob : Participant} {s ch re : SignedState E}
    (h : validResponse c alice bob s ch re = true) : validStart c s = true := by
  apply satp_validChallenge_start (c := c) (alice := alice) (bob := bob) (ch := ch)
  unfold validResponse at h
  split at h
  · simp only [Bool.and_eq_true] at h
    repeat (obtain ⟨h, -⟩ := h)
    exact h
  · cases h

/-- `consensusRules.supports`, genuinely signed, pays `alice` and `bob` a
    total of `a0 + b0`, by `hsigned`. -/
theorem satp_consensus_pairOutcome {r : Route E} {alice bob : Participant}
    {signed : List (Participant × State E)}
    (hsigned : ∀ st : State E, (∀ q ∈ r.V.participants, (q, st) ∈ signed) → st.channel = r.V →
      (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (st.isFinal = true ∧ ∃ a b, PairOutcome (r.dest alice) (r.dest bob) st.outcome a b ∧
        a + b = r.a0 + r.b0))
    {proof : SupportProof E} {candidate : State E}
    (hcon : consensusRules.supports r.V proof candidate = true)
    (hsig : ∀ ss ∈ proof, ss.SignedIn signed) :
    ∃ a b, PairOutcome (r.dest alice) (r.dest bob) candidate.outcome a b ∧ a + b = r.a0 + r.b0 := by
  match proof, hcon with
  | [ssx], hcon =>
    simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
    obtain ⟨⟨hst, hchan⟩, hall⟩ := hcon
    have hsi : ssx.SignedIn signed := hsig ssx (List.mem_singleton_self ssx)
    have hmem := satp_signed_membership hall hsi
    rw [hchan] at hmem
    have hres := hsigned ssx.state hmem hchan
    rw [hst] at hres
    exact satp_pairOutcome_of_hsigned hres
  | [], hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
  | _ :: _ :: _, hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)

/-- A `validateOutcomeChange` run, genuinely signed from its start state,
    pays `alice` and `bob` a total of `a0 + b0`: `hsigned` gives the start
    state's own total, and `satp_outcome_change_keeps_total` carries it to
    the candidate. -/
theorem satp_validateOutcomeChange_pairOutcome {r : Route E} {alice bob : Participant}
    {signed : List (Participant × State E)}
    (hsigned : ∀ st : State E, (∀ q ∈ r.V.participants, (q, st) ∈ signed) → st.channel = r.V →
      (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (st.isFinal = true ∧ ∃ a b, PairOutcome (r.dest alice) (r.dest bob) st.outcome a b ∧
        a + b = r.a0 + r.b0))
    {proof : SupportProof E} {candidate : State E}
    (hval : validateOutcomeChange r.V alice bob proof candidate = true)
    (hsig : ∀ ss ∈ proof, ss.SignedIn signed) :
    ∃ a b, PairOutcome (r.dest alice) (r.dest bob) candidate.outcome a b ∧ a + b = r.a0 + r.b0 := by
  have hstart : ∃ s0 : SignedState E, s0 ∈ proof ∧ proof.head? = some s0 ∧
      validStart r.V s0 = true := by
    match proof, hval with
    | [s], hval =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hval
      exact ⟨s, by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false]), rfl, hval.1⟩
    | [s, ch], hval =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hval
      exact ⟨s, by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]), rfl, satp_validChallenge_start hval.1⟩
    | [s, ch, re], hval =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hval
      exact ⟨s, by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]), rfl, satp_validResponse_start hval.1⟩
  obtain ⟨s0, hmemp, h0, hs0⟩ := hstart
  obtain ⟨hall, hchan⟩ := satp_validStart_byAll hs0
  have hsi : s0.SignedIn signed := hsig s0 hmemp
  have hmem := satp_signed_membership hall hsi
  rw [hchan] at hmem
  obtain ⟨a, b, hp, hab⟩ := satp_pairOutcome_of_hsigned (hsigned s0.state hmem hchan)
  obtain ⟨hpd, hfundab⟩ := satp_pairOutcome_pairDests_total hp
  obtain ⟨-, hne⟩ := satp_outcome_change_keeps_total r.V alice bob proof candidate hval s0 h0
  by_cases hceq : candidate = s0.state
  · exact ⟨a, b, by rw [hceq]; exact hp, hab⟩
  · obtain ⟨da, db, a', b', hpd', hco, hab'⟩ := hne hceq
    have hdaeq : da = Address.external (r.dest alice) ∧ db = Address.external (r.dest bob) := by
      have heq := hpd'.symm.trans hpd
      (simpa? using heq says simpa only [Option.some.injEq, Prod.mk.injEq] using heq)
    obtain ⟨rfl, rfl⟩ := hdaeq
    refine ⟨a', b', hco, ?_⟩
    rw [hab', hfundab, hab]

/-- The content `satp_lemma_3_1` needs about `r.V`'s on-chain adjudication
    status: nothing pending while open, and while challenged or finalized,
    the stored outcome pays `alice` and `bob` a total of `a0 + b0`. Unlike
    `StatusOrigin`/`FinalizedTwoWays` (`Safety.lean`), which trace through
    plain `Reachable` and so forget which signatures are genuine, this
    threads `ReachableSigned`'s extra guarantee through the induction below. -/
def SatpOrigin (r : Route E) (alice bob : Participant) (s : Adjudicator E) : Prop :=
  match s.statusOf r.V with
  | .open _ => True
  | .challenged _ ch =>
      ∃ a b, PairOutcome (r.dest alice) (r.dest bob) ch.state.outcome a b ∧ a + b = r.a0 + r.b0
  | .finalized _ _ o =>
      ∃ a b, PairOutcome (r.dest alice) (r.dest bob) o a b ∧ a + b = r.a0 + r.b0

/-- `SatpOrigin` holds at every state `ReachableSigned` from genesis. A
    `deposit`, `tick`, `transfer` or `reclaim` never touches `r.V`'s status
    (a `transfer`'s or `reclaim`'s ledger argument has `kind = .ledger`,
    `r.V.kind = .virtual`); a `checkpoint` of `r.V` reopens it; a `challenge`
    or `conclude` of `r.V` is genuinely signed by every one of `r.V`'s
    participants (`ConclusionProof.ByAll`, or `consensusRules`/
    `validateOutcomeChange`'s own start state), so `hsigned` applies. -/
theorem satpOrigin_reachableSigned {apps : Apps E} {r : Route E} {alice bob : Participant}
    (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    {signed : List (Participant × State E)}
    (hsigned : ∀ st : State E, (∀ q ∈ r.V.participants, (q, st) ∈ signed) → st.channel = r.V →
      (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (st.isFinal = true ∧ ∃ a b, PairOutcome (r.dest alice) (r.dest bob) st.outcome a b ∧
        a + b = r.a0 + r.b0))
    {s : Adjudicator E} (hs : ReachableSigned apps signed s) :
    SatpOrigin r alice bob s := by
  obtain ⟨-, -, -, -, -, hVp, hVk, -⟩ := hr
  induction hs with
  | refl => unfold SatpOrigin; (simp? [Adjudicator.statusOf, Adjudicator.genesis] says simp only [Adjudicator.statusOf, Adjudicator.genesis, List.lookup_nil, Option.getD_none])
  | tail _ hstep ih =>
    cases hstep with
    | mk caller op _ _ hsig happ =>
    cases op with
    | deposit a e x =>
      obtain ⟨-, -, -, -, hst, -⟩ := Adjudicator.deposit_some happ
      unfold SatpOrigin
      rw [Adjudicator.statusOf_of_status hst]
      exact ih
    | tick dt =>
      simp only [Adjudicator.apply_tick, Option.some.injEq] at happ
      subst happ
      unfold SatpOrigin
      rw [Adjudicator.tick_statusOf]
      exact ih
    | transfer a b =>
      obtain ⟨_, _, _, _, _, _, _, _, hst, _, hak, _⟩ := Adjudicator.transfer_some happ
      have hne : r.V ≠ a := by rintro rfl; rw [hVk] at hak; cases hak
      unfold SatpOrigin
      rw [Adjudicator.statusOf_of_status hst, Adjudicator.statusOf_setStatus, if_neg hne]
      exact ih
    | reclaim l v =>
      obtain ⟨oL, oV, x, left, right, hfo, hfw, hfind, hne1, hne2, hsum, hseq, hlk, hvk⟩ :=
        Adjudicator.reclaim_some happ
      have hne : r.V ≠ l := by rintro rfl; rw [hVk] at hlk; cases hlk
      unfold SatpOrigin
      rw [hseq, Adjudicator.statusOf_setStatus, if_neg hne]
      exact ih
    | checkpoint c proof candidate =>
      obtain ⟨-, hseq⟩ := Adjudicator.checkpoint_some happ
      rcases eq_or_ne c r.V with hcc | hcc
      · subst hcc
        unfold SatpOrigin
        rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]; trivial
      · unfold SatpOrigin
        rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
        exact ih
    | challenge c proof candidate =>
      obtain ⟨⟨-, hsup, hchan, -⟩, hseq⟩ := Adjudicator.challenge_some happ
      rcases eq_or_ne c r.V with hcc | hcc
      · subst hcc
        unfold SatpOrigin
        rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
        rw [hV] at hsup
        have hsig' : ∀ ss ∈ proof, ss.SignedIn signed := hsig
        simp only [satpVirtualRules, hVp, halice, hbob] at hsup
        split_ifs at hsup with ht1 ht4
        · exact satp_consensus_pairOutcome hsigned hsup hsig'
        · simp only [Bool.and_eq_true] at hsup
          obtain ⟨hcon, -⟩ := hsup
          exact satp_consensus_pairOutcome hsigned hcon hsig'
        · exact satp_validateOutcomeChange_pairOutcome hsigned hsup hsig'
      · unfold SatpOrigin
        rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
        exact ih
    | conclude c ss =>
      obtain ⟨⟨-, hchan, -, hall⟩, hseq⟩ := Adjudicator.conclude_some happ
      rcases eq_or_ne c r.V with hcc | hcc
      · subst hcc
        unfold SatpOrigin
        rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
        have hsi : ss.SignedIn signed := hsig ss (List.mem_singleton_self ss)
        have hmem := satp_signed_membership hall hsi
        rw [hchan] at hmem
        exact satp_pairOutcome_of_hsigned (hsigned ss.state hmem hchan)
      · unfold SatpOrigin
        rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
        exact ih


/-- SATP-21, SATP-19 (Lemma 3.1, SATP:511-513; Lemma A.1, SATP:746-753). "Suppose V
    finalizes on-chain. Either V is finalized with version = 0 and its
    original outcome {A : A(a0), B : A(b0)} or it is finalized with an
    outcome {A : A(a), B : A(b)}, where a0 + b0 = a + b." `signed` lists the
    signatures that exist (`(q, st)`: `q` signed `st`), and the chain uses no
    other (SATP:168). The hypothesis is what honest peers sign
    (SATP:407-421, SATP:751-753): every state of `V` that every peer signed is
    a setup state with the original outcome, or a final state that keeps the
    total. -/
theorem satp_lemma_3_1 (apps : Apps E) (r : Route E) (alice bob : Participant)
    (hr : r.WellFormed apps) (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (signed : List (Participant × State E))
    (hsigned : ∀ st : State E, (∀ q ∈ r.V.participants, (q, st) ∈ signed) → st.channel = r.V →
      (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (st.isFinal = true ∧ ∃ a b, PairOutcome (r.dest alice) (r.dest bob) st.outcome a b ∧
        a + b = r.a0 + r.b0))
    (s : ReachableState (Nitro.signedChain apps signed)) (Ω : Outcome E)
    (hfin : s.state.finalOutcome r.V.address = some Ω) :
    ∃ Ω0, Redistributed Ω0 Ω ∧
      (((s.state.statusOf r.V).turnNumRecord = 0 ∧
        Ω0 = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
       (∃ a b, PairOutcome (r.dest alice) (r.dest bob) Ω0 a b ∧ a + b = r.a0 + r.b0)) := by
  obtain_reach ⟨s, hs : ReachableSigned apps signed s⟩ := s
  have horig := satpOrigin_reachableSigned hr hV halice hbob hsigned hs
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hfin
  unfold SatpOrigin at horig
  revert hfin horig
  cases s.statusOf r.V with
  | «open» t => (simp? says simp only [ChannelStatus.finalOutcome_open, reduceCtorEq, ChannelStatus.turnNumRecord_open, forall_const, IsEmpty.forall_iff])
  | challenged t ch =>
    intro hfin horig
    simp only [ChannelStatus.finalOutcome_challenged] at hfin
    split at hfin
    · cases hfin
      exact ⟨ch.state.outcome, Relation.ReflTransGen.refl, Or.inr horig⟩
    · cases hfin
  | finalized t f o =>
    intro hfin horig
    simp only [ChannelStatus.finalOutcome_finalized, Option.some.injEq] at hfin
    subst hfin
    exact ⟨o, Relation.ReflTransGen.refl, Or.inr horig⟩

/-- A fixed list's fold, over whichever of its entries name channel `c`,
    of the entry's own turn number under `max`, starting from `4`. A lower
    bound on every turn `satpVirtualRules` can ever let a candidate reuse
    from `l` directly (`virtualTurnBound_mem`), and itself at least `4`
    (`virtualTurnBound_ge`, the fixed cap `satpVirtualRules` never exceeds
    without it). -/
def virtualTurnBound (c : FixedPart) (l : List (SignedState E)) : Nat :=
  l.foldr (fun t acc => if t.state.channel = c then max t.state.turnNum acc else acc) 4

omit [DecidableEq E] in
theorem virtualTurnBound_ge (c : FixedPart) (l : List (SignedState E)) :
    4 ≤ virtualTurnBound c l := by
  induction l with
  | nil => exact le_refl _
  | cons y t ih =>
    simp only [virtualTurnBound, List.foldr_cons] at ih ⊢
    split
    · exact le_trans ih (le_max_right _ _)
    · exact ih

omit [DecidableEq E] in
theorem virtualTurnBound_mem (c : FixedPart) (x : SignedState E) :
    ∀ l : List (SignedState E), x ∈ l → x.state.channel = c →
      x.state.turnNum ≤ virtualTurnBound c l := by
  intro l
  induction l with
  | nil => intro hx; cases hx
  | cons y t ih =>
    intro hx hc
    simp only [virtualTurnBound, List.foldr_cons] at ih ⊢
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [if_pos hc]; exact le_max_left _ _
    · split
      · exact le_trans (ih hx hc) (le_max_right _ _)
      · exact ih hx hc

omit [DecidableEq E] in
/-- `satp_pairOutcome_of_hsigned`, without the `isFinal` conjunct `hsent`
    (a bound on `p`'s own sends, not a global signing fact) does not
    carry. -/
theorem satp_pairOutcome_of_hsent {da db : E} {a0 b0 : Coins} {st : State E}
    (h : (st.turnNum ≤ 1 ∧ st.outcome = originalOutcome da db a0 b0) ∨
      (∃ a b, PairOutcome da db st.outcome a b ∧ a + b = a0 + b0)) :
    ∃ a b, PairOutcome da db st.outcome a b ∧ a + b = a0 + b0 := by
  rcases h with ⟨-, heq⟩ | hp
  · exact ⟨a0, b0, heq, rfl⟩
  · exact hp

theorem satp_net_pairOutcome {p : Participant} {net : NetworkState E p} {r : Route E}
    {alice bob : Participant} {M : Nat} (h4M : 4 ≤ M)
    (hM : ∀ t ∈ net.sent, t.state.channel = r.V → t.state.turnNum ≤ M)
    (hVp : r.V.participants = r.peers) (hp : p ∈ r.peers)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hsent : ∀ t ∈ net.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0))
    {proof : SupportProof E} {candidate : State E}
    (hU : ∀ ss ∈ proof, net.Unforged ss)
    (hcon : satpVirtualRules.supports r.V proof candidate = true) :
    candidate.turnNum ≤ M ∧
    ∃ a b, PairOutcome (r.dest alice) (r.dest bob) candidate.outcome a b ∧ a + b = r.a0 + r.b0 := by
  have hpV : p ∈ r.V.participants := by rw [hVp]; exact hp
  have hconsensus : ∀ proof' : SupportProof E,
      consensusRules.supports r.V proof' candidate = true → (∀ ss ∈ proof', net.Unforged ss) →
      ∃ a b, PairOutcome (r.dest alice) (r.dest bob) candidate.outcome a b ∧ a + b = r.a0 + r.b0 := by
    intro proof' hcc hU'
    match proof', hcc with
    | [ssx], hcc =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcc
      obtain ⟨⟨hst, hchan⟩, hallc⟩ := hcc
      have hps : p ∈ ssx.signers := hallc p (by rw [hchan]; exact hpV)
      obtain ⟨x, hxmem, hxeq⟩ := (hU' ssx (List.mem_singleton_self ssx)).1 hps
      have hxchan : x.state.channel = r.V := by rw [hxeq]; exact hchan
      have hb := hsent x hxmem hxchan
      rw [hxeq, hst] at hb
      exact satp_pairOutcome_of_hsent hb
    | [], hcc => (simp? [consensusRules] at hcc says simp only [consensusRules, Bool.false_eq_true] at hcc)
    | _ :: _ :: _, hcc => (simp? [consensusRules] at hcc says simp only [consensusRules, Bool.false_eq_true] at hcc)
  have hheadV : r.V.participants.head? = some alice := by rw [hVp]; exact halice
  have hlastV : r.V.participants.getLast? = some bob := by rw [hVp]; exact hbob
  unfold satpVirtualRules at hcon
  simp only [hheadV, hlastV] at hcon
  split_ifs at hcon with ht1 ht4
  · exact ⟨by omega, hconsensus proof hcon hU⟩
  · simp only [Bool.and_eq_true] at hcon
    obtain ⟨hcon', -⟩ := hcon
    exact ⟨by omega, hconsensus proof hcon' hU⟩
  · match proof, hcon with
    | [s], hcon =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hcon
      obtain ⟨hvs, hceq⟩ := hcon
      obtain ⟨hallc, hchan⟩ := satp_validStart_byAll hvs
      have hps : p ∈ s.signers := hallc p (by rw [hchan]; exact hpV)
      obtain ⟨x, hxmem, hxeq⟩ := (hU s (List.mem_singleton_self s)).1 hps
      have hxchan : x.state.channel = r.V := by rw [hxeq]; exact hchan
      have hb := hsent x hxmem hxchan
      have heq : candidate = x.state := by rw [← hceq, hxeq]
      refine ⟨by rw [heq]; exact hM x hxmem hxchan, ?_⟩
      rw [← heq] at hb
      exact satp_pairOutcome_of_hsent hb
    | [s, ch], hcon =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hcon
      obtain ⟨hvc, hceq⟩ := hcon
      have hvs := satp_validChallenge_start hvc
      obtain ⟨hallc, hchan⟩ := satp_validStart_byAll hvs
      have hps : p ∈ s.signers := hallc p (by rw [hchan]; exact hpV)
      obtain ⟨x, hxmem, hxeq⟩ := (hU s (by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]))).1 hps
      have hxchan : x.state.channel = r.V := by rw [hxeq]; exact hchan
      have hb := hsent x hxmem hxchan
      rw [hxeq] at hb
      obtain ⟨a0', b0', hp0, hab0⟩ := satp_pairOutcome_of_hsent hb
      obtain ⟨hpd, hfundab⟩ := satp_pairOutcome_pairDests_total hp0
      obtain ⟨da, db, a, b, hpd', hco, hab'⟩ := validChallenge_outcome hvc
      have hdaeq : da = Address.external (r.dest alice) ∧ db = Address.external (r.dest bob) := by
        have heqd := hpd'.symm.trans hpd
        (simpa? using heqd says simpa only [Option.some.injEq, Prod.mk.injEq] using heqd)
      obtain ⟨rfl, rfl⟩ := hdaeq
      have hvc2 := hvc
      have hturn2 : ch.state.turnNum = 2 := by
        unfold validChallenge at hvc2
        split at hvc2
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hvc2; tauto
        · exact absurd hvc2 (by (simp? says simp only [Bool.false_eq_true, not_false_eq_true]))
      refine ⟨by rw [← hceq, hturn2]; omega, a, b, by rw [← hceq]; exact hco, by
        rw [hab', hfundab, hab0]⟩
    | [s, ch, re], hcon =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hcon
      obtain ⟨hvr, hceq⟩ := hcon
      have hvs := satp_validResponse_start hvr
      obtain ⟨hallc, hchan⟩ := satp_validStart_byAll hvs
      have hps : p ∈ s.signers := hallc p (by rw [hchan]; exact hpV)
      obtain ⟨x, hxmem, hxeq⟩ := (hU s (by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]))).1 hps
      have hxchan : x.state.channel = r.V := by rw [hxeq]; exact hchan
      have hb := hsent x hxmem hxchan
      rw [hxeq] at hb
      obtain ⟨a0', b0', hp0, hab0⟩ := satp_pairOutcome_of_hsent hb
      obtain ⟨hpd, hfundab⟩ := satp_pairOutcome_pairDests_total hp0
      obtain ⟨da, db, a, b, hpd', hco, hab'⟩ := validResponse_outcome hvr
      have hdaeq : da = Address.external (r.dest alice) ∧ db = Address.external (r.dest bob) := by
        have heqd := hpd'.symm.trans hpd
        (simpa? using heqd says simpa only [Option.some.injEq, Prod.mk.injEq] using heqd)
      obtain ⟨rfl, rfl⟩ := hdaeq
      have hvr2 := hvr
      have hturn3 : re.state.turnNum = 3 := by
        unfold validResponse at hvr2
        split at hvr2
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hvr2; tauto
        · exact absurd hvr2 (by (simp? says simp only [Bool.false_eq_true, not_false_eq_true]))
      refine ⟨by rw [← hceq, hturn3]; omega, a, b, by rw [← hceq]; exact hco, by
        rw [hab', hfundab, hab0]⟩

/-- The state `p`'s strategy maintains for `r.V`, from the moment it first
    challenges with the all-signed post-fund state: `.open` carries a
    reusable re-challenge witness (the proof and candidate of whichever
    checkpoint most recently won, held because D9 publishes a successful
    call's proof states and D7 lets a received state carry its voucher
    signatures, `holds_of_mem_received`); `.challenged` and
    `.finalized` carry a total-preserving pair outcome
    (`satp_net_pairOutcome`). The turn stays within `M`
    (`satp_net_pairOutcome`'s own bound). -/
def SatpFinalizeInv {p : Participant} (r : Route E) (alice bob : Participant) (M : Nat)
    (net : NetworkState E p) : Prop :=
  match net.chain.statusOf r.V with
  | .open t => t ≤ M ∧ ∃ proof : SupportProof E, ∃ candidate : State E,
      t ≤ candidate.turnNum ∧ candidate.turnNum ≤ M ∧
      satpVirtualRules.supports r.V proof candidate = true ∧ candidate.channel = r.V ∧
      (∀ ss ∈ proof, net.Holds ss) ∧
      ∃ a b, PairOutcome (r.dest alice) (r.dest bob) candidate.outcome a b ∧ a + b = r.a0 + r.b0
  | .challenged t ch => t ≤ M ∧
      ∃ a b, PairOutcome (r.dest alice) (r.dest bob) ch.state.outcome a b ∧ a + b = r.a0 + r.b0
  | .finalized _ f _ =>
      ∃ a b, PairOutcome (r.dest alice) (r.dest bob) f a b ∧ a + b = r.a0 + r.b0

/-- `SatpFinalizeInv` carries through any `AdvMove` that leaves `r.V`'s own
    status unchanged: the witness's `Holds` clause is the only net-specific
    part, and it is monotone (`NetworkState.Holds.mono`, `received` only
    ever grows, `sent` never changes, over any `AdvMove`). -/
theorem SatpFinalizeInv_unaffected (apps : Apps E) {p : Participant} {r : Route E}
    {alice bob : Participant} {M : Nat} {net : NetworkState E p} (m : AdvMove E)
    (hstatus : (net.applyAdv apps m).chain.statusOf r.V = net.chain.statusOf r.V)
    (hI : SatpFinalizeInv r alice bob M net) :
    SatpFinalizeInv r alice bob M (net.applyAdv apps m) := by
  unfold SatpFinalizeInv at hI ⊢
  rw [hstatus]
  cases hs : net.chain.statusOf r.V with
  | «open» t =>
    rw [hs] at hI
    obtain ⟨htM, proof, candidate, htc, hcM, hsup, hchanc, hHolds, hbnd⟩ := hI
    exact ⟨htM, proof, candidate, htc, hcM, hsup, hchanc,
      fun ss hss => NetworkState.Holds.mono (NetworkState.applyAdv_sent apps net m).symm
        (NetworkState.applyAdv_received_subset apps net m) (hHolds ss hss), hbnd⟩
  | challenged t ch => rwa [hs] at hI
  | finalized t f o => rwa [hs] at hI

theorem SatpFinalizeInv_deliver_step (apps : Apps E) {p : Participant} {r : Route E}
    {alice bob : Participant} {M : Nat} {net : NetworkState E p} (ss : SignedState E)
    (hI : SatpFinalizeInv r alice bob M net) :
    SatpFinalizeInv r alice bob M (net.applyAdv apps (.deliver ss)) :=
  SatpFinalizeInv_unaffected apps (.deliver ss) rfl hI

theorem SatpFinalizeInv_tick_step (apps : Apps E) {p : Participant} {r : Route E}
    {alice bob : Participant} {M : Nat} {net : NetworkState E p} (dt : Time)
    (hI : SatpFinalizeInv r alice bob M net) :
    SatpFinalizeInv r alice bob M (net.applyAdv apps (.tick dt)) :=
  SatpFinalizeInv_unaffected apps (.tick dt)
    (by simp only [NetworkState.applyAdv]; exact Adjudicator.tick_statusOf _ _ _) hI

/-- One adversary on-chain call preserves `SatpFinalizeInv`. A call
    touching a channel other than `r.V` leaves `r.V`'s status unchanged
    (`SatpFinalizeInv_unaffected`; a `transfer`/`reclaim` of `r.V` itself
    is impossible, `r.V.kind = .virtual` against their own `.kind = .ledger`
    guard). A `checkpoint`/`challenge`/`conclude` of `r.V` is bound by
    `satp_net_pairOutcome` (`Bounds.unforgeable` protects every proof
    state's genuine signer), and its proof states land in `received`
    (`holds_of_mem_received`), so the new `.open` status still carries a
    reusable witness. -/
theorem SatpFinalizeInv_chain_step {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {r : Route E} (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules) {alice bob : Participant}
    {M : Nat} (h4M : 4 ≤ M) (hp : p ∈ r.peers)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    {net : NetworkState E p}
    (hsent : ∀ t ∈ net.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0))
    (hM : ∀ t ∈ net.sent, t.state.channel = r.V → t.state.turnNum ≤ M)
    {net' : NetworkState E p} (hsent' : net'.sent = net.sent)
    {caller : Participant} {op : Op E} (hfeas : T.feasible net' (.chain caller op))
    (hI : SatpFinalizeInv r alice bob M net') :
    SatpFinalizeInv r alice bob M (net'.applyAdv apps (.chain caller op)) := by
  obtain ⟨-, -, -, -, -, hVp, hVk, -⟩ := hr
  have hpV : p ∈ r.V.participants := by rw [hVp]; exact hp
  have hU : ∀ ss ∈ op.proofStates, net'.Unforged ss := hbounds.unforgeable net' caller op hfeas
  have hsentN : ∀ t ∈ net'.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0) := by
    rw [hsent']; exact hsent
  have hMN : ∀ t ∈ net'.sent, t.state.channel = r.V → t.state.turnNum ≤ M := by
    rw [hsent']; exact hM
  cases op with
  | deposit a e x =>
    cases hop : net'.chain.apply apps caller (.deposit a e x) with
    | none => (simpa? [NetworkState.applyAdv, hop] using hI says simpa only [NetworkState.applyAdv, hop] using hI)
    | some s' =>
      obtain ⟨-, -, -, -, hst, -⟩ := Adjudicator.deposit_some hop
      exact SatpFinalizeInv_unaffected apps (.chain caller (.deposit a e x)) (by
        simp only [NetworkState.applyAdv, hop]; exact Adjudicator.statusOf_of_status hst r.V) hI
  | tick dt =>
    cases hop : net'.chain.apply apps caller (.tick dt) with
    | none => (simpa? [NetworkState.applyAdv, hop] using hI says simpa only [NetworkState.applyAdv, hop] using hI)
    | some s' =>
      have hs' : net'.chain.tick dt = s' := by (simpa? using hop says simpa only [Adjudicator.apply_tick, Option.some.injEq] using hop)
      exact SatpFinalizeInv_unaffected apps (.chain caller (.tick dt)) (by
        simp only [NetworkState.applyAdv, hop]; rw [← hs']; exact Adjudicator.tick_statusOf _ _ _) hI
  | transfer a b =>
    cases hop : net'.chain.apply apps caller (.transfer a b) with
    | none => (simpa? [NetworkState.applyAdv, hop] using hI says simpa only [NetworkState.applyAdv, hop] using hI)
    | some s' =>
      obtain ⟨_, _, _, _, _, _, _, _, hst, _, hak, _⟩ := Adjudicator.transfer_some hop
      have hne : r.V ≠ a := by rintro rfl; rw [hVk] at hak; cases hak
      exact SatpFinalizeInv_unaffected apps (.chain caller (.transfer a b)) (by
        simp only [NetworkState.applyAdv, hop]
        rw [Adjudicator.statusOf_of_status hst, Adjudicator.statusOf_setStatus, if_neg hne]) hI
  | reclaim l v =>
    cases hop : net'.chain.apply apps caller (.reclaim l v) with
    | none => (simpa? [NetworkState.applyAdv, hop] using hI says simpa only [NetworkState.applyAdv, hop] using hI)
    | some s' =>
      obtain ⟨oL, oV, x, left, right, hfo, hfw, hfind, hne1, hne2, hsum, hseq, hlk, hvk⟩ :=
        Adjudicator.reclaim_some hop
      have hne : r.V ≠ l := by rintro rfl; rw [hVk] at hlk; cases hlk
      exact SatpFinalizeInv_unaffected apps (.chain caller (.reclaim l v)) (by
        simp only [NetworkState.applyAdv, hop]
        rw [hseq, Adjudicator.statusOf_setStatus, if_neg hne]) hI
  | checkpoint c proof candidate =>
    cases hop : net'.chain.apply apps caller (.checkpoint c proof candidate) with
    | none => (simpa? [NetworkState.applyAdv, hop] using hI says simpa only [NetworkState.applyAdv, hop] using hI)
    | some s' =>
      obtain ⟨⟨-, hsup, hchanc, -⟩, hseq⟩ := Adjudicator.checkpoint_some hop
      rcases eq_or_ne c r.V with hcc | hcc
      · subst hcc
        rw [hV] at hsup
        have hUc : ∀ ss ∈ proof, net'.Unforged ss := fun ss hss => hU ss (by (simp? [Op.proofStates, hss] says simp only [Op.proofStates, hss]))
        obtain ⟨hcM, hbnd⟩ := satp_net_pairOutcome h4M hMN hVp hp halice hbob hsentN hUc hsup
        unfold SatpFinalizeInv
        simp only [NetworkState.applyAdv, hop]
        rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
        refine ⟨hcM, proof, candidate, le_refl _, hcM, hsup, hchanc, ?_, hbnd⟩
        intro ss hss
        apply holds_of_mem_received
        exact List.mem_append_left _ hss
      · exact SatpFinalizeInv_unaffected apps (.chain caller (.checkpoint c proof candidate)) (by
          simp only [NetworkState.applyAdv, hop]
          rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]) hI
  | challenge c proof candidate =>
    cases hop : net'.chain.apply apps caller (.challenge c proof candidate) with
    | none => (simpa? [NetworkState.applyAdv, hop] using hI says simpa only [NetworkState.applyAdv, hop] using hI)
    | some s' =>
      obtain ⟨⟨-, hsup, hchanc, -⟩, hseq⟩ := Adjudicator.challenge_some hop
      rcases eq_or_ne c r.V with hcc | hcc
      · subst hcc
        rw [hV] at hsup
        have hUc : ∀ ss ∈ proof, net'.Unforged ss := fun ss hss => hU ss (by (simp? [Op.proofStates, hss] says simp only [Op.proofStates, hss]))
        obtain ⟨hcM, hbnd⟩ := satp_net_pairOutcome h4M hMN hVp hp halice hbob hsentN hUc hsup
        unfold SatpFinalizeInv
        simp only [NetworkState.applyAdv, hop]
        rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
        exact ⟨hcM, hbnd⟩
      · exact SatpFinalizeInv_unaffected apps (.chain caller (.challenge c proof candidate)) (by
          simp only [NetworkState.applyAdv, hop]
          rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]) hI
  | conclude c ss =>
    cases hop : net'.chain.apply apps caller (.conclude c ss) with
    | none => (simpa? [NetworkState.applyAdv, hop] using hI says simpa only [NetworkState.applyAdv, hop] using hI)
    | some s' =>
      obtain ⟨⟨-, hchanc, -, hallc⟩, hseq⟩ := Adjudicator.conclude_some hop
      rcases eq_or_ne c r.V with hcc | hcc
      · subst hcc
        have hps : p ∈ ss.signers := hallc p (by rw [hchanc]; exact hpV)
        have hUss : net'.Unforged ss := hU ss (by (simp? [Op.proofStates] says simp only [Op.proofStates, List.mem_cons, List.not_mem_nil, or_false]))
        obtain ⟨x, hxmem, hxeq⟩ := hUss.1 hps
        have hxchan : x.state.channel = r.V := by rw [hxeq]; exact hchanc
        have hb := hsentN x hxmem hxchan
        rw [hxeq] at hb
        unfold SatpFinalizeInv
        simp only [NetworkState.applyAdv, hop]
        rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
        exact satp_pairOutcome_of_hsent hb
      · exact SatpFinalizeInv_unaffected apps (.chain caller (.conclude c ss)) (by
          simp only [NetworkState.applyAdv, hop]
          rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]) hI

/-- `SatpFinalizeInv` carries across a whole sub-round of pure adversary
    play (`Threat.RoundSeq` with nothing of `p`'s own pending). A direct
    call of `Threat.RoundSeq.nil_invariant` (`Strategy.lean`): the
    threaded invariant is `SatpFinalizeInv` together with `sent =
    net.sent`, since `SatpFinalizeInv_chain_step` needs that equality to
    read `hsent`/`hM` against the right network. -/
theorem SatpFinalizeInv_nil_roundSeq {apps : Apps E} {p : Participant} {T : Threat E p}
    (hbounds : Bounds apps p T) {r : Route E} (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules) {alice bob : Participant}
    {M : Nat} (h4M : 4 ≤ M) (hp : p ∈ r.peers)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    {net : NetworkState E p}
    (hsent : ∀ t ∈ net.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0))
    (hM : ∀ t ∈ net.sent, t.state.channel = r.V → t.state.turnNum ≤ M) :
    ∀ {t0 : Time} {net' net'' : NetworkState E p}, Threat.RoundSeq apps T t0 [] net' net'' →
      net'.sent = net.sent → SatpFinalizeInv r alice bob M net' →
      net''.sent = net.sent ∧ SatpFinalizeInv r alice bob M net'' := by
  intro t0 net' net'' hseq hsent' hI
  refine Threat.RoundSeq.nil_invariant
    (Inv := fun n => n.sent = net.sent ∧ SatpFinalizeInv r alice bob M n) hseq
    ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩
    ⟨hsent', hI⟩
  · intro n ss _ _ ⟨hs, hI1⟩
    exact ⟨by rw [NetworkState.applyAdv_sent]; exact hs, SatpFinalizeInv_deliver_step apps ss hI1⟩
  · intro n dt _ _ ⟨hs, hI1⟩
    exact ⟨by rw [NetworkState.applyAdv_sent]; exact hs, SatpFinalizeInv_tick_step apps dt hI1⟩
  · intro n caller op _ hfeas ⟨hs, hI1⟩
    exact ⟨by rw [NetworkState.applyAdv_sent]; exact hs,
      SatpFinalizeInv_chain_step hbounds hr hV h4M hp halice hbob hsent hM hs hfeas hI1⟩

/-- `turnNumRecord_monotone`, restated for one successful `Adjudicator.apply`:
    the turn record of `c` only grows, except a `conclude` of `c` itself,
    which finalizes it in the same step (no turn check at all, SATP:288-289).
    `satp_peers_can_finalize`'s own strategy never needs a numeric bound in
    THAT case: `SatpFinalizeInv`'s own `.finalized` case already carries the
    goal's own bound. -/
theorem turnNumRecord_mono_apply (apps : Apps E) {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} (c : FixedPart) (h : s.apply apps caller op = some s') :
    (s.statusOf c).turnNumRecord ≤ (s'.statusOf c).turnNumRecord ∨
    ∃ tr f o, s'.statusOf c = .finalized tr f o := by
  rcases turnNumRecord_monotone apps s s' c ⟨caller, op, s, s', h⟩ with hle | ⟨caller', ss, hcop, hfin⟩
  · exact Or.inl hle
  · right
    obtain ⟨-, hseq⟩ := Adjudicator.conclude_some hcop
    refine ⟨ss.state.turnNum, ss.state.outcome, ss.state.outcome, ?_⟩
    rw [hseq]; (simp? [Adjudicator.statusOf_setStatus] says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])

/-- Once a channel `c` with `c.kind ≠ .ledger` is finalized, every operation
    leaves it finalized with the same `turnNumRecord` and the same
    `finalizedWith` outcome, the two `SatpFinalizeInv` and the goal both
    read: `deposit`/`tick` never touch any channel's status; `transfer`/
    `reclaim` of `c` itself are impossible (`c.kind ≠ .ledger` against their
    own `.kind = .ledger` guard, so they can target only a DIFFERENT
    channel, leaving `c` untouched); `checkpoint`/`challenge`/`conclude` of
    `c` itself all need `IsOpen`, false once finalized; of a different
    channel they leave `c` untouched (`Adjudicator.statusOf_setStatus`'s
    `if_neg`). The THIRD field (the payout-adjusted stored outcome) can
    change, through a `transfer`/`reclaim` of a different channel than `c`
    reading `c`'s own finalized outcome to pay it out — it is not read by
    `SatpFinalizeInv` or by `satp_peers_can_finalize`'s own goal, so this
    theorem does not track it. -/
theorem statusOf_frozen_once_finalized {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} (c : FixedPart) (hck : c.kind ≠ .ledger) {tr : Nat} {f o : Outcome E}
    (hfin : s.statusOf c = .finalized tr f o) (h : s.apply apps caller op = some s') :
    ∃ o', s'.statusOf c = .finalized tr f o' := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hst, -⟩ := Adjudicator.deposit_some h
    exact ⟨o, by rw [Adjudicator.statusOf_of_status hst]; exact hfin⟩
  | tick dt =>
    have hs' : s.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
    exact ⟨o, by rw [← hs', Adjudicator.tick_statusOf]; exact hfin⟩
  | transfer a b =>
    have hne : a ≠ c := by rintro rfl; exact hck (by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hak, _⟩ := Adjudicator.transfer_some h; exact hak)
    obtain ⟨_, _, _, _, _, _, _, _, hst, _, _, _⟩ := Adjudicator.transfer_some h
    exact ⟨o, by
      rw [Adjudicator.statusOf_of_status hst, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)]
      exact hfin⟩
  | reclaim l v =>
    have hne : l ≠ c := by rintro rfl; exact hck (by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlk, _⟩ := Adjudicator.reclaim_some h; exact hlk)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hseq, _, _⟩ := Adjudicator.reclaim_some h
    exact ⟨o, by rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)]; exact hfin⟩
  | checkpoint c' proof cand =>
    by_cases hcc : c' = c
    · exfalso
      obtain ⟨⟨hIsOpen, -, -, -⟩, -⟩ := Adjudicator.checkpoint_some h
      rw [hcc, hfin] at hIsOpen
      (simp? [ChannelStatus.IsOpen, ChannelStatus.mode] at hIsOpen says simp only [ChannelStatus.IsOpen, ChannelStatus.mode, ne_eq, not_true_eq_false] at hIsOpen)
    · obtain ⟨-, hseq⟩ := Adjudicator.checkpoint_some h
      exact ⟨o, by
        rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hfin⟩
  | challenge c' proof cand =>
    by_cases hcc : c' = c
    · exfalso
      obtain ⟨⟨-, -, -, hmode⟩, -⟩ := Adjudicator.challenge_some h
      rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
        · rw [hcc, Adjudicator.mode_eq, hfin] at hm
          (simp? [ChannelStatus.mode] at hm says simp only [ChannelStatus.mode, reduceCtorEq] at hm)
    · obtain ⟨-, hseq⟩ := Adjudicator.challenge_some h
      exact ⟨o, by
        rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hfin⟩
  | conclude c' ss =>
    by_cases hcc : c' = c
    · exfalso
      obtain ⟨⟨hIsOpen, -, -, -⟩, -⟩ := Adjudicator.conclude_some h
      rw [hcc, hfin] at hIsOpen
      (simp? [ChannelStatus.IsOpen, ChannelStatus.mode] at hIsOpen says simp only [ChannelStatus.IsOpen, ChannelStatus.mode, ne_eq, not_true_eq_false] at hIsOpen)
    · obtain ⟨-, hseq⟩ := Adjudicator.conclude_some h
      exact ⟨o, by
        rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]; exact hfin⟩

/-- `statusOf_frozen_once_finalized`, over a whole `Threat.RoundSeq`: once a
    channel is finalized, it stays finalized with the same `turnNumRecord`
    and `finalizedWith` outcome for the rest of the round, by induction
    (`land`, `tick`, `other`'s `.chain`/`.deliver` each take one step; a
    failed call is a no-op). -/
theorem statusOf_frozen_once_finalized_roundSeq {apps : Apps E} {p : Participant} {T : Threat E p}
    (c : FixedPart) (hck : c.kind ≠ .ledger) :
    ∀ {t0 : Time} {pending : List (Op E)} {net net' : NetworkState E p},
      Threat.RoundSeq apps T t0 pending net net' →
      ∀ {tr : Nat} {f o : Outcome E}, net.chain.statusOf c = .finalized tr f o →
      ∃ o', net'.chain.statusOf c = .finalized tr f o' := by
  intro t0 pending net net' hseq
  induction hseq with
  | nil => exact fun hfin => ⟨_, hfin⟩
  | @land pending n1 n2 op l1 l2 hsplit hrest ih =>
    intro tr f o hfin
    cases hstep : n1.chain.apply apps p op with
    | none =>
      refine ih (tr := tr) (f := f) (o := o) ?_
      rw [NetworkState.applyAdv_land_none apps hstep]; exact hfin
    | some s' =>
      obtain ⟨o', ho'⟩ := statusOf_frozen_once_finalized c hck hfin hstep
      refine ih (tr := tr) (f := f) (o := o') ?_
      rw [NetworkState.applyAdv_land_some apps hstep]; exact ho'
  | @tick pending n1 n2 dt hfeas hgate hrest ih =>
    intro tr f o hfin
    refine ih (tr := tr) (f := f) (o := o) ?_
    rw [NetworkState.applyAdv_tick apps n1 dt, Adjudicator.tick_statusOf]
    exact hfin
  | @other pending n1 n2 m hfeas hnotick hnoland hrest ih =>
    intro tr f o hfin
    cases m with
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | deliver ss =>
      refine ih (tr := tr) (f := f) (o := o) ?_
      rw [NetworkState.applyAdv_deliver apps n1 ss]; exact hfin
    | chain caller op =>
      cases hstep : n1.chain.apply apps caller op with
      | none =>
        refine ih (tr := tr) (f := f) (o := o) ?_
        rw [NetworkState.applyAdv_chain_none apps hstep]; exact hfin
      | some s' =>
        obtain ⟨o', ho'⟩ := statusOf_frozen_once_finalized c hck hfin hstep
        refine ih (tr := tr) (f := f) (o := o') ?_
        rw [NetworkState.applyAdv_chain_some apps hstep]; exact ho'


/-- Over a whole `Threat.RoundSeq`, a channel `c` with `c.kind ≠ .ledger`'s
    turn record only grows, except once some step concludes it: from then
    on `statusOf_frozen_once_finalized_roundSeq` keeps the record and the
    `finalizedWith` outcome, which is all `SatpFinalizeInv`'s own
    `.finalized` case and `satp_peers_can_finalize`'s own goal ever read.
    `land`'s and `other`'s `.chain` are one `turnNumRecord_mono_apply` step
    each (a failed call is a no-op); `tick` and `.deliver` never touch `c`'s
    status at all. -/
theorem turnNumRecord_mono_roundSeq {apps : Apps E} {p : Participant} {T : Threat E p} {t0 : Time}
    {pending : List (Op E)} {net net' : NetworkState E p}
    (hseq : Threat.RoundSeq apps T t0 pending net net') (c : FixedPart) (hck : c.kind ≠ .ledger) :
    (net.chain.statusOf c).turnNumRecord ≤ (net'.chain.statusOf c).turnNumRecord ∨
    ∃ tr f o, net'.chain.statusOf c = .finalized tr f o := by
  induction hseq with
  | nil => exact Or.inl (le_refl _)
  | @land pending n1 n2 op l1 l2 hsplit hrest ih =>
    cases hstep : n1.chain.apply apps p op with
    | none =>
      rw [NetworkState.applyAdv_land_none apps hstep] at ih
      exact ih
    | some s' =>
      rcases turnNumRecord_mono_apply apps c hstep with hle | hfin
      · simp only [NetworkState.applyAdv_land_some apps hstep] at ih
        rcases ih with hle2 | hfin2
        · exact Or.inl (le_trans hle hle2)
        · exact Or.inr hfin2
      · obtain ⟨tr, f, o, hfeq⟩ := hfin
        have hfeq' : (n1.applyAdv apps (.land op)).chain.statusOf c = .finalized tr f o := by
          rw [NetworkState.applyAdv_land_some apps hstep]; exact hfeq
        obtain ⟨o', ho'⟩ := statusOf_frozen_once_finalized_roundSeq c hck hrest hfeq'
        exact Or.inr ⟨tr, f, o', ho'⟩
  | @tick pending n1 n2 dt hfeas hgate hrest ih =>
    rw [NetworkState.applyAdv_tick apps n1 dt, Adjudicator.tick_statusOf] at ih
    exact ih
  | @other pending n1 n2 m hfeas hnotick hnoland hrest ih =>
    cases m with
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | deliver ss => rw [NetworkState.applyAdv_deliver apps n1 ss] at ih; exact ih
    | chain caller op =>
      cases hstep : n1.chain.apply apps caller op with
      | none =>
        rw [NetworkState.applyAdv_chain_none apps hstep] at ih
        exact ih
      | some s' =>
        rcases turnNumRecord_mono_apply apps c hstep with hle | hfin
        · simp only [NetworkState.applyAdv_chain_some apps hstep] at ih
          rcases ih with hle2 | hfin2
          · exact Or.inl (le_trans hle hle2)
          · exact Or.inr hfin2
        · obtain ⟨tr, f, o, hfeq⟩ := hfin
          have hfeq' : (n1.applyAdv apps (.chain caller op)).chain.statusOf c = .finalized tr f o := by
            rw [NetworkState.applyAdv_chain_some apps hstep]; exact hfeq
          obtain ⟨o', ho'⟩ := statusOf_frozen_once_finalized_roundSeq c hck hrest hfeq'
          exact Or.inr ⟨tr, f, o', ho'⟩


/-- Once channel `c` with `c.kind ≠ .ledger` is challenged, a single
    successful op either leaves its status exactly as it was, or lands a
    strictly higher turn record (`checkpoint`'s and `challenge`'s own
    guards are both strict once past the open-mode equal-turn case —
    reusing the SAME candidate is excluded structurally, since `checkpoint`
    needs a turn strictly above the record and `challenge` from challenge
    mode needs the same), or finalizes it outright. `transfer`/`reclaim` of
    `c` are impossible, as in `statusOf_frozen_once_finalized`. -/
theorem statusOf_strict_apply {apps : Apps E} {s s' : Adjudicator E} {caller : Participant}
    {op : Op E} (c : FixedPart) (hck : c.kind ≠ .ledger) {T0 : Nat} {ch : Challenge E}
    (hchal : s.statusOf c = .challenged T0 ch) (h : s.apply apps caller op = some s') :
    s'.statusOf c = s.statusOf c ∨
    (s.statusOf c).turnNumRecord < (s'.statusOf c).turnNumRecord ∨
    ∃ tr f o, s'.statusOf c = .finalized tr f o := by
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hst, -⟩ := Adjudicator.deposit_some h
    exact Or.inl (Adjudicator.statusOf_of_status hst c)
  | tick dt =>
    have hs' : s.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
    exact Or.inl (by rw [← hs']; exact Adjudicator.tick_statusOf s dt c)
  | transfer a b =>
    have hne : a ≠ c := by rintro rfl; exact hck (by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hak, _⟩ := Adjudicator.transfer_some h; exact hak)
    obtain ⟨_, _, _, _, _, _, _, _, hst, _, _, _⟩ := Adjudicator.transfer_some h
    refine Or.inl ?_
    rw [Adjudicator.statusOf_of_status hst, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)]
  | reclaim l v =>
    have hne : l ≠ c := by rintro rfl; exact hck (by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlk, _⟩ := Adjudicator.reclaim_some h; exact hlk)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hseq, _, _⟩ := Adjudicator.reclaim_some h
    exact Or.inl (by rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hne)])
  | checkpoint c' proof cand =>
    by_cases hcc : c' = c
    · subst hcc
      obtain ⟨⟨-, -, -, hlt⟩, hseq⟩ := Adjudicator.checkpoint_some h
      right; left
      rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
      (simpa? using hlt says simpa only [ChannelStatus.turnNumRecord_open] using hlt)
    · obtain ⟨-, hseq⟩ := Adjudicator.checkpoint_some h
      exact Or.inl (by rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)])
  | challenge c' proof cand =>
    by_cases hcc : c' = c
    · subst hcc
      obtain ⟨⟨-, -, -, hmode⟩, hseq⟩ := Adjudicator.challenge_some h
      right; left
      rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
      rcases hmode with ⟨hm, -⟩ | ⟨-, hlt⟩
      · exfalso
        rw [Adjudicator.mode_eq, hchal] at hm
        simp only [ChannelStatus.mode] at hm
        split_ifs at hm <;> exact absurd hm (by decide)
      · (simpa? using hlt says simpa only [ChannelStatus.turnNumRecord_challenged] using hlt)
    · obtain ⟨-, hseq⟩ := Adjudicator.challenge_some h
      exact Or.inl (by rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)])
  | conclude c' ss =>
    by_cases hcc : c' = c
    · subst hcc
      obtain ⟨-, hseq⟩ := Adjudicator.conclude_some h
      exact Or.inr (Or.inr ⟨ss.state.turnNum, ss.state.outcome, ss.state.outcome, by
        rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]⟩)
    · obtain ⟨-, hseq⟩ := Adjudicator.conclude_some h
      exact Or.inl (by rw [hseq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)])

/-- `statusOf_strict_apply`, over a whole sub-round of pure adversary play
    (`pending = []`): the status stays exactly `.challenged T0 ch`, or the
    turn record strictly passes `T0`, or the channel finalizes. `land` is
    impossible with `pending = []`. -/
theorem statusOf_strict_roundSeq {apps : Apps E} {p : Participant} {T : Threat E p}
    (c : FixedPart) (hck : c.kind ≠ .ledger) {T0 : Nat} {ch : Challenge E} :
    ∀ {t0 : Time} {net net' : NetworkState E p}, Threat.RoundSeq apps T t0 [] net net' →
      net.chain.statusOf c = .challenged T0 ch →
      net'.chain.statusOf c = .challenged T0 ch ∨ T0 < (net'.chain.statusOf c).turnNumRecord ∨
        ∃ tr f o, net'.chain.statusOf c = .finalized tr f o := by
  intro t0 net net' hseq
  generalize hpnil : ([] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro hst; exact Or.inl hst
  | land hsplit _ _ => rw [← hpnil] at hsplit; (simp? at hsplit says simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending n1 n2 dt hfeas hgate hrest ih =>
    intro hst
    refine ih hpnil ?_
    rw [NetworkState.applyAdv_tick apps n1 dt, Adjudicator.tick_statusOf]
    exact hst
  | @other pending n1 n2 m hfeas hnotick hnoland hrest ih =>
    intro hst
    cases m with
    | tick dt => exact absurd rfl (hnotick dt)
    | land op => exact absurd rfl (hnoland op)
    | deliver ss =>
      refine ih hpnil ?_
      rw [NetworkState.applyAdv_deliver apps n1 ss]; exact hst
    | chain caller op =>
      cases hstep : n1.chain.apply apps caller op with
      | none =>
        refine ih hpnil ?_
        rw [NetworkState.applyAdv_chain_none apps hstep]; exact hst
      | some s' =>
        rcases statusOf_strict_apply c hck hst hstep with heq | hlt | hfin
        · refine ih hpnil ?_
          rw [NetworkState.applyAdv_chain_some apps hstep]
          rw [heq]; exact hst
        · rw [hst] at hlt
          simp only [ChannelStatus.turnNumRecord_challenged] at hlt
          have hle2 : (s'.statusOf c).turnNumRecord ≤
              (n2.chain.statusOf c).turnNumRecord ∨
              ∃ tr f o, n2.chain.statusOf c = .finalized tr f o := by
            have hmono := turnNumRecord_mono_roundSeq hrest c hck
            rw [NetworkState.applyAdv_chain_some apps hstep] at hmono
            exact hmono
          rcases hle2 with hle2 | hfin2
          · exact Or.inr (Or.inl (by omega))
          · exact Or.inr (Or.inr hfin2)
        · obtain ⟨tr, f, o, hfeq⟩ := hfin
          have hfeq' : (n1.applyAdv apps (.chain caller op)).chain.statusOf c = .finalized tr f o := by
            rw [NetworkState.applyAdv_chain_some apps hstep]; exact hfeq
          obtain ⟨o', ho'⟩ := statusOf_frozen_once_finalized_roundSeq c hck hrest hfeq'
          exact Or.inr (Or.inr ⟨tr, f, o', ho'⟩)



/-- SATP-21 (Lemma A.1, SATP:747-750, liveness half). "every party has signed a
    None state with version 1, in which case peers can take unilateral
    actions to ensure V finalized with an outcome {A : a, B : b}, where
    a0 + b0 = a + b." A peer who holds the all-signed post-fund state, signed
    only setup states and pair outcomes that keep the total, and sees `V`
    open at or below version 1, can force such a finalization. -/
theorem satp_peers_can_finalize (apps : Apps E) {p : Participant} (T : Threat E p)
    (A : Assumptions apps p T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules) (hp : p ∈ r.peers)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hdur : 2 * T.ε ≤ r.V.challengeDuration) (net : Nitro.ReachableParticipant apps T)
    (s1 : SignedState E)
    (hh : net.state.Holds s1) (hall : s1.ByAll) (hchan : s1.state.channel = r.V)
    (hv1 : s1.state.turnNum = 1)
    (h1 : s1.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0)
    (hsent : ∀ t ∈ net.state.sent, t.state.channel = r.V →
      (t.state.turnNum ≤ 1 ∧ t.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0) ∨
      (∃ a b, PairOutcome (r.dest alice) (r.dest bob) t.state.outcome a b ∧ a + b = r.a0 + r.b0))
    (hst : ∃ t, net.state.chain.statusOf r.V = .open t ∧ t ≤ 1) :
    Unbeatable apps T (fun net' => ∃ Ω a b, net'.Finalized r.V Ω ∧
      PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧ a + b = r.a0 + r.b0) net.state := by
  obtain_reach ⟨net, hnr⟩ := net
  have hr' := hr
  obtain ⟨-, -, -, -, -, hVp, hVk, -⟩ := hr'
  have hckV : r.V.kind ≠ .ledger := by rw [hVk]; decide
  have hpV : p ∈ r.V.participants := by rw [hVp]; exact hp
  set M := virtualTurnBound r.V net.sent with hM_def
  have h4M : 4 ≤ M := virtualTurnBound_ge r.V net.sent
  have hMb : ∀ t ∈ net.sent, t.state.channel = r.V → t.state.turnNum ≤ M :=
    fun t ht hc => virtualTurnBound_mem r.V t net.sent ht hc
  have hb1 : ∃ a b, PairOutcome (r.dest alice) (r.dest bob) s1.state.outcome a b ∧
      a + b = r.a0 + r.b0 := ⟨r.a0, r.b0, h1, rfl⟩
  have hsup1 : satpVirtualRules.supports r.V [s1] s1.state = true := by
    unfold satpVirtualRules
    have hheadV : r.V.participants.head? = some alice := by rw [hVp]; exact halice
    have hlastV : r.V.participants.getLast? = some bob := by rw [hVp]; exact hbob
    simp only [hheadV, hlastV]
    rw [if_pos (by rw [hv1])]
    (simp? [consensusRules, hchan, hall] says simp only [consensusRules, decide_true, hchan, Bool.and_self, hall])
  have hI0 : SatpFinalizeInv r alice bob M net := by
    obtain ⟨t, hopen, ht1⟩ := hst
    unfold SatpFinalizeInv
    rw [hopen]
    refine ⟨by omega, [s1], s1.state, by rw [hv1]; exact ht1, by rw [hv1]; omega, hsup1, hchan,
      ?_, hb1⟩
    intro ss hss
    rw [List.mem_singleton] at hss
    rw [hss]; exact hh
  -- Nested proof: the strong induction below needs `ih` in scope.
  have hnil : ∀ {t0 : Time} {n1 n2 : NetworkState E p}, Threat.RoundSeq apps T t0 [] n1 n2 →
      n1.sent = net.sent → SatpFinalizeInv r alice bob M n1 →
      n2.sent = net.sent ∧ SatpFinalizeInv r alice bob M n2 :=
    fun hseq => SatpFinalizeInv_nil_roundSeq A.toBounds hr hV h4M hp halice hbob hsent hMb hseq
  suffices hgo : ∀ budget : Nat, ∀ net' : NetworkState E p, net'.sent = net.sent →
      SatpFinalizeInv r alice bob M net' →
      M - (net'.chain.statusOf r.V).turnNumRecord ≤ budget →
      UnbeatableIn apps T (fun _ => True) (fun n => ∃ Ω a b, n.Finalized r.V Ω ∧ PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧
            a + b = r.a0 + r.b0) net' by
    exact hgo (M - (net.chain.statusOf r.V).turnNumRecord) net rfl hI0 (le_refl _)
  intro budget
  induction budget using Nat.strong_induction_on with
  | _ budget ih =>
    intro net' hsent' hI hbudget
    have doneFin : ∀ (n : NetworkState E p) (tr : Nat) (f o : Outcome E),
        SatpFinalizeInv r alice bob M n → n.chain.statusOf r.V = .finalized tr f o →
        UnbeatableIn apps T (fun _ => True) (fun n => ∃ Ω a b, n.Finalized r.V Ω ∧ PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧
            a + b = r.a0 + r.b0) n := by
      intro n tr f o hIn hfeq
      apply UnbeatableIn.done
      unfold SatpFinalizeInv at hIn
      rw [hfeq] at hIn
      obtain ⟨a, b, hpo, hab⟩ := hIn
      refine ⟨f, a, b, ?_, hpo, hab⟩
      show n.chain.finalizedWith r.V.address = some f
      simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hfeq,
        ChannelStatus.finalizedWith_finalized]
    have recurse : ∀ n : NetworkState E p, n.sent = net.sent → SatpFinalizeInv r alice bob M n →
        (M - (n.chain.statusOf r.V).turnNumRecord < budget ∨
          M < (n.chain.statusOf r.V).turnNumRecord) →
        UnbeatableIn apps T (fun _ => True) (fun n => ∃ Ω a b, n.Finalized r.V Ω ∧ PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧
            a + b = r.a0 + r.b0) n := by
      intro n hsn hIn hlt
      cases hsn' : n.chain.statusOf r.V with
      | finalized tr f o => exact doneFin n tr f o hIn hsn'
      | challenged tn ch =>
        have htM : tn ≤ M := by
          have h := hIn; unfold SatpFinalizeInv at h; rw [hsn'] at h; exact h.1
        rw [hsn', ChannelStatus.turnNumRecord_challenged] at hlt
        exact ih (M - tn) (by omega) n hsn hIn (by rw [hsn', ChannelStatus.turnNumRecord_challenged])
      | «open» tn =>
        have htM : tn ≤ M := by
          have h := hIn; unfold SatpFinalizeInv at h; rw [hsn'] at h; exact h.1
        rw [hsn', ChannelStatus.turnNumRecord_open] at hlt
        exact ih (M - tn) (by omega) n hsn hIn (by rw [hsn', ChannelStatus.turnNumRecord_open])
    have finishChallenged : ∀ (net2 : NetworkState E p) (T0 : Nat) (ch : Challenge E),
        net2.sent = net.sent → net2.chain.statusOf r.V = .challenged T0 ch → T0 ≤ M →
        (∃ a b, PairOutcome (r.dest alice) (r.dest bob) ch.state.outcome a b ∧
          a + b = r.a0 + r.b0) →
        M - T0 ≤ budget →
        UnbeatableIn apps T (fun _ => True) (fun n => ∃ Ω a b, n.Finalized r.V Ω ∧ PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧
            a + b = r.a0 + r.b0) net2 := by
      intro net2 T0 ch hsent2 hstatus2 hT0M hbnd2 hbudget2
      by_cases hexp : ch.deadline ≤ net2.chain.now
      · apply UnbeatableIn.done
        obtain ⟨a, b, hpo, hab⟩ := hbnd2
        refine ⟨ch.state.outcome, a, b, ?_, hpo, hab⟩
        show net2.chain.finalizedWith r.V.address = some ch.state.outcome
        simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hstatus2,
          ChannelStatus.finalizedWith_challenged, if_pos hexp]
      · rw [not_le] at hexp
        refine UnbeatableIn.move (.wait (ch.deadline - net2.chain.now)) trivial trivial ?_
        intro net3 hround2
        obtain ⟨hseq2, -⟩ := hround2
        have hI2 : SatpFinalizeInv r alice bob M net2 := by
          unfold SatpFinalizeInv; rw [hstatus2]; exact ⟨hT0M, hbnd2⟩
        obtain ⟨hsent3, hI3⟩ := hnil hseq2 hsent2 hI2
        have hItick : SatpFinalizeInv r alice bob M
            (net3.applyHonest (.wait (ch.deadline - net2.chain.now))) := by
          show SatpFinalizeInv r alice bob M
            (net3.applyAdv apps (.tick (ch.deadline - net2.chain.now)))
          exact SatpFinalizeInv_tick_step apps _ hI3
        have hsenttick : (net3.applyHonest (.wait (ch.deadline - net2.chain.now))).sent =
            net.sent := by
          show (net3.applyAdv apps (.tick (ch.deadline - net2.chain.now))).sent = net.sent
          rw [NetworkState.applyAdv_sent]; exact hsent3
        have hstatustick : (net3.applyHonest (.wait (ch.deadline - net2.chain.now))).chain.statusOf
            r.V = net3.chain.statusOf r.V := by
          show (net3.chain.tick (ch.deadline - net2.chain.now)).statusOf r.V =
            net3.chain.statusOf r.V
          exact Adjudicator.tick_statusOf _ _ _
        rcases statusOf_strict_roundSeq r.V hckV hseq2 hstatus2 with heqch | hgt | hfinr
        · apply UnbeatableIn.done
          have hmono3 : net2.chain.now ≤ net3.chain.now := hseq2.now_le
          obtain ⟨a, b, hpo, hab⟩ := hbnd2
          have hge : ch.deadline ≤ net3.chain.now + (ch.deadline - net2.chain.now) := by
            have heq1 : net2.chain.now + (ch.deadline - net2.chain.now) = ch.deadline :=
              Nat.add_sub_cancel' (le_of_lt hexp)
            calc ch.deadline = net2.chain.now + (ch.deadline - net2.chain.now) := heq1.symm
              _ ≤ net3.chain.now + (ch.deadline - net2.chain.now) := Nat.add_le_add_right hmono3 _
          refine ⟨ch.state.outcome, a, b, ?_, hpo, hab⟩
          show (net3.applyHonest (.wait (ch.deadline - net2.chain.now))).chain.finalizedWith
            r.V.address = some ch.state.outcome
          simp only [NetworkState.applyHonest]
          simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
            Adjudicator.tick_statusOf, heqch, Adjudicator.tick_now,
            ChannelStatus.finalizedWith_challenged, if_pos hge]
        · exact recurse _ hsenttick hItick (by rw [hstatustick]; omega)
        · obtain ⟨tr, f, o, hfeq⟩ := hfinr
          exact doneFin _ tr f o hItick (by rw [hstatustick]; exact hfeq)
    cases hstatus : net'.chain.statusOf r.V with
    | finalized t f o => exact doneFin net' t f o hI hstatus
    | challenged t ch =>
      rw [hstatus, ChannelStatus.turnNumRecord_challenged] at hbudget
      unfold SatpFinalizeInv at hI
      rw [hstatus] at hI
      obtain ⟨htM, hbnd⟩ := hI
      exact finishChallenged net' t ch hsent' hstatus htM hbnd hbudget
    | «open» t =>
      rw [hstatus, ChannelStatus.turnNumRecord_open] at hbudget
      have hIat := hI
      unfold SatpFinalizeInv at hI
      rw [hstatus] at hI
      obtain ⟨htM, proof, candidate, htc, hcM, hsup, hchanc, hHolds, hbnd⟩ := hI
      refine UnbeatableIn.move (.chain (.challenge r.V proof candidate)) trivial
        (by (simpa? [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hHolds says simpa only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates] using hHolds)) ?_
      intro net1 hround
      obtain ⟨net1a, hseq1, hseq2⟩ := Threat.Round.single hround
      obtain ⟨hsent1a, hI1a⟩ := hnil hseq1 hsent' hIat
      rw [NetworkState.applyHonest_chain]
      have hRest : ∀ {t0 : Time} {net_mid : NetworkState E p} (T0 : Nat) (ch0 : Challenge E),
          t ≤ T0 → T0 ≤ M →
          (∃ a b, PairOutcome (r.dest alice) (r.dest bob) ch0.state.outcome a b ∧
            a + b = r.a0 + r.b0) →
          net_mid.sent = net.sent →
          Threat.RoundSeq apps T t0 [] net_mid net1 →
          net_mid.chain.statusOf r.V = .challenged T0 ch0 →
          UnbeatableIn apps T (fun _ => True) (fun n => ∃ Ω a b, n.Finalized r.V Ω ∧ PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧
            a + b = r.a0 + r.b0) net1 := by
        intro t0 net_mid T0 ch0 htT0 hT0M hbndch0 hsentmid hseq hstatusmid
        have hImid : SatpFinalizeInv r alice bob M net_mid := by
          unfold SatpFinalizeInv; rw [hstatusmid]; exact ⟨hT0M, hbndch0⟩
        obtain ⟨hsent1, hI1⟩ := hnil hseq hsentmid hImid
        rcases statusOf_strict_roundSeq r.V hckV hseq hstatusmid with heqch | hgt | hfinr
        · exact finishChallenged net1 T0 ch0 hsent1 heqch hT0M hbndch0 (by omega)
        · exact recurse net1 hsent1 hI1 (by omega)
        · obtain ⟨tr, f, o, hfeq⟩ := hfinr
          exact doneFin net1 tr f o hI1 hfeq
      by_cases hpre : net1a.chain.ChallengePre apps p r.V proof candidate
      · have hstep : _ = some (net1a.chain.setStatus r.V (.challenged candidate.turnNum
            ⟨candidate, net1a.chain.now + r.V.challengeDuration⟩)) :=
          (Adjudicator.apply_challenge_equation apps p r.V proof candidate net1a.chain).trans
            (dif_pos hpre)
        have hmid : (net1a.applyAdv apps (.land (.challenge r.V proof candidate))).chain.statusOf
            r.V = .challenged candidate.turnNum
              ⟨candidate, net1a.chain.now + r.V.challengeDuration⟩ := by
          rw [NetworkState.applyAdv_land_some apps hstep, Adjudicator.statusOf_setStatus,
            if_pos rfl]
        have hsentmid : (net1a.applyAdv apps (.land (.challenge r.V proof candidate))).sent =
            net.sent := by rw [NetworkState.applyAdv_sent]; exact hsent1a
        exact hRest candidate.turnNum _ htc hcM hbnd hsentmid hseq2 hmid
      have hstep := (Adjudicator.apply_challenge_equation apps p r.V proof candidate
        net1a.chain).trans (dif_neg hpre)
      rw [NetworkState.applyAdv_land_none apps hstep] at hseq2
      obtain ⟨hsent1, hI1⟩ := hnil hseq2 hsent1a hI1a
      cases hstatus1a : net1a.chain.statusOf r.V with
      | finalized t1a f1a o1a =>
        obtain ⟨o1', ho1'⟩ := statusOf_frozen_once_finalized_roundSeq r.V hckV hseq2 hstatus1a
        exact doneFin net1 t1a f1a o1' hI1 ho1'
      | challenged t1a ch1a =>
        have hI1a' := hI1a
        unfold SatpFinalizeInv at hI1a'
        rw [hstatus1a] at hI1a'
        obtain ⟨ht1aM, hbnd1a⟩ := hI1a'
        have ht1at : t ≤ t1a := by
          rcases turnNumRecord_mono_roundSeq hseq1 r.V hckV with hle | hfin0
          · rw [hstatus, hstatus1a] at hle
            (simpa? using hle says simpa only [ChannelStatus.turnNumRecord_open, ChannelStatus.turnNumRecord_challenged] using hle)
          · obtain ⟨tr0, f0, o0, hfeq0⟩ := hfin0
            rw [hfeq0] at hstatus1a
            cases hstatus1a
        exact hRest t1a ch1a ht1at ht1aM hbnd1a hsent1a hseq2 hstatus1a
      | «open» t1a =>
        have hgt1 : candidate.turnNum < t1a := by
          by_contra hcon
          rw [not_lt] at hcon
          rw [Adjudicator.apply_challenge, challenge_can_happen apps _ p r.V proof candidate hpV
            (by rw [hV]; exact hsup) hchanc (Or.inl ⟨by rw [Adjudicator.mode_eq, hstatus1a]; rfl,
              by rw [hstatus1a, ChannelStatus.turnNumRecord_open]; exact hcon⟩)] at hstep
          cases hstep
        rcases turnNumRecord_mono_roundSeq hseq2 r.V hckV with hle | hfinr
        · rw [hstatus1a, ChannelStatus.turnNumRecord_open] at hle
          exact recurse net1 hsent1 hI1 (by omega)
        · obtain ⟨tr, f, o, hfeq⟩ := hfinr
          exact doneFin net1 tr f o hI1 hfeq

theorem validChallenge_turnNum {alice bob : Participant} {c : FixedPart} {s ch : SignedState E}
    (h : validChallenge c alice bob s ch = true) : ch.state.turnNum = 2 := by
  unfold validChallenge at h
  split at h
  · obtain ⟨⟨⟨⟨⟨hchan, hor⟩, hsig⟩, hav⟩, hbv⟩, hout⟩ := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    exact hchan.1.2
  · cases h

theorem validResponse_turnNum {alice bob : Participant} {c : FixedPart} {s ch re : SignedState E}
    (h : validResponse c alice bob s ch re = true) : re.state.turnNum = 3 := by
  unfold validResponse at h
  split at h
  · have h' := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    exact h'.1.1.1.1.1.1.1.1.1.2
  · cases h
/-- `conclude` on `r.V` can never succeed: it would need a `ByAll`, `isFinal` state signed by
    `P`, but `HoldsVirtualSetup` bounds every state `P` signs for `r.V` to `isFinal = false`. -/
theorem satpVirtual_conclude_fails {P : Participant} {r : Route E} {alice bob : Participant}
    {net : NetworkState E P} (hVs : HoldsVirtualSetup net r alice bob true)
    (hE : SatpEnds r alice bob P) {ss : SignedState E} (hconc : ConclusionProof r.V ss)
    (hU : ∀ ss' ∈ ([ss] : SupportProof E), P ∈ ss'.signers → ∃ x ∈ net.sent, x.state = ss'.state) :
    False := by
  obtain ⟨hchan, hfin, hall⟩ := hconc
  have hPsig : P ∈ ss.signers := hall P (hchan ▸ hE.mem)
  obtain ⟨x, hx, hxs⟩ := hU ss (List.mem_singleton_self _) hPsig
  obtain ⟨-, hxfin, -⟩ := hVs.1 x hx (by rw [hxs]; exact hchan)
  rw [hxs] at hxfin
  rw [hxfin] at hfin
  exact absurd hfin (by decide)

/-- Over a round with nothing of `P`'s own pending, `r.V`'s turn record
    never drops: `turnNumRecord_monotone` bounds every single on-chain
    step, and its one exception (a `conclude` that finalizes `r.V`) is
    impossible (`satpVirtual_conclude_fails`, since `P`'s own setup states
    are never final). -/
theorem Threat.RoundSeq.turnNumRecord_ge {apps : Apps E} {P : Participant} {T : Threat E P}
    (hbounds : Bounds apps P T) {r : Route E} {alice bob : Participant}
    (hE : SatpEnds r alice bob P) {t : Time} {net net' : NetworkState E P}
    (hVs : HoldsVirtualSetup net r alice bob true)
    (h : Threat.RoundSeq apps T t [] net net') :
    (net.chain.statusOf r.V).turnNumRecord ≤ (net'.chain.statusOf r.V).turnNumRecord := by
  generalize hpnil : ([] : List (Op E)) = pending at h
  induction h with
  | nil => exact le_refl _
  | land hsplit _ _ => rw [← hpnil] at hsplit; (simp? at hsplit says simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    have hVs' : HoldsVirtualSetup (net1.applyAdv apps (AdvMove.tick dt)) r alice bob true := by
      unfold HoldsVirtualSetup; rw [NetworkState.applyAdv_sent]; exact hVs
    have hstep := ih hVs' hpnil
    (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hstep says simpa only [ge_iff_le, NetworkState.applyAdv, Adjudicator.tick_statusOf] using hstep)
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    have hVs' : HoldsVirtualSetup (net1.applyAdv apps m) r alice bob true := by
      unfold HoldsVirtualSetup; rw [NetworkState.applyAdv_sent]; exact hVs
    have hstep := ih hVs' hpnil
    cases m with
    | tick dt =>
      (simpa? [NetworkState.applyAdv, Adjudicator.tick_statusOf] using hstep says simpa only [ge_iff_le, NetworkState.applyAdv, Adjudicator.tick_statusOf] using hstep)
    | deliver ss' =>
      (simpa? [NetworkState.applyAdv] using hstep says simpa only [ge_iff_le, NetworkState.applyAdv] using hstep)
    | land op => exact absurd rfl (hnoland op)
    | chain caller op =>
      cases hap : net1.chain.apply apps caller op with
      | none => (simpa? [NetworkState.applyAdv, hap] using hstep says simpa only [ge_iff_le, NetworkState.applyAdv, hap] using hstep)
      | some s' =>
        have hmono1 : (net1.chain.statusOf r.V).turnNumRecord ≤ (s'.statusOf r.V).turnNumRecord := by
          cases op with
          | conclude c' ss' =>
            by_cases hcc : c' = r.V
            · subst hcc
              exfalso
              obtain ⟨⟨-, hconcp⟩, -⟩ := Adjudicator.conclude_some hap
              exact satpVirtual_conclude_fails hVs hE hconcp
                (fun ss'' hmem hsig => (hbounds.unforgeable net1 caller (.conclude r.V ss')
                  hfeas ss'' hmem).1 hsig)
            · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some hap
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
          | deposit a e x =>
            obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some hap
            rw [Adjudicator.statusOf_of_status hs]
          | tick dt' =>
            have hs' : net1.chain.tick dt' = s' := by (simpa? using hap says simpa only [Adjudicator.apply_tick, Option.some.injEq] using hap)
            rw [← hs', Adjudicator.tick_statusOf]
          | transfer a b =>
            by_cases hac : a = r.V
            · subst hac
              obtain ⟨o, w1, w2, w3, w4, w5, w6, w7, hs, w9, w10, w11⟩ :=
                Adjudicator.transfer_some hap
              have hseq : s'.statusOf r.V =
                  (net1.chain.setStatus r.V ((net1.chain.statusOf r.V).withOutcome
                    (Outcome.allocation (o.reduceOwed b w2)))).statusOf r.V :=
                congrArg (fun A => (A.lookup r.V).getD (ChannelStatus.open 0)) hs
              rw [hseq, Adjudicator.statusOf_setStatus, if_pos rfl]
              rcases hcs : net1.chain.statusOf r.V with ct | ⟨ct, cch⟩ | ⟨ct, cf, co⟩ <;>
                (simp? [hcs, ChannelStatus.withOutcome, ChannelStatus.turnNumRecord] says simp only [ChannelStatus.turnNumRecord, ChannelStatus.withOutcome, Std.le_refl])
            · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some hap
              rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                if_neg (Ne.symm hac)]
          | reclaim l v =>
            by_cases hlc : l = r.V
            · subst hlc
              obtain ⟨oL, oV, x, left, right, hL, hVfo, hg, hl, hr, hxeq, hsr, hlk, hvk⟩ :=
                Adjudicator.reclaim_some hap
              rw [hsr, Adjudicator.statusOf_setStatus, if_pos rfl]
              rcases hcs : net1.chain.statusOf r.V with ct | ⟨ct, cch⟩ | ⟨ct, cf, co⟩ <;>
                (simp? [hcs, ChannelStatus.withOutcome, ChannelStatus.turnNumRecord] says simp only [ChannelStatus.turnNumRecord, ChannelStatus.withOutcome, FixedPart.address_eq, Std.le_refl])
            · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some hap
              rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)]
          | challenge c' proof cand =>
            by_cases hcc : c' = r.V
            · subst hcc
              obtain ⟨⟨-, -, -, hmode⟩, rfl⟩ := Adjudicator.challenge_some hap
              rw [Adjudicator.statusOf_setStatus, if_pos rfl, ChannelStatus.turnNumRecord_challenged]
              rcases hmode with ⟨-, hle⟩ | ⟨-, hlt⟩
              · exact hle
              · exact le_of_lt hlt
            · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some hap
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
          | checkpoint c' proof cand =>
            by_cases hcc : c' = r.V
            · subst hcc
              obtain ⟨⟨-, hs, -, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some hap
              rw [Adjudicator.statusOf_setStatus, if_pos rfl]
              simp only [ChannelStatus.turnNumRecord]
              exact le_of_lt hlt
            · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some hap
              rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)]
        have hcomb : (net1.chain.statusOf r.V).turnNumRecord ≤
            ((net1.applyAdv apps (.chain caller op)).chain.statusOf r.V).turnNumRecord := by
          simp only [NetworkState.applyAdv, hap]; exact hmono1
        exact le_trans hcomb hstep

/-- `r.V`'s status is not finalized: open, or challenged with its deadline still ahead of
    `now`. -/
def SatpLive {P : Participant} (r : Route E) (net : NetworkState E P) (now : Time) : Prop :=
  (∃ u, net.chain.statusOf r.V = .open u) ∨
  (∃ u ch, net.chain.statusOf r.V = .challenged u ch ∧ now < ch.deadline)

omit [DecidableEq E] in
/-- A live `r.V` (`SatpLive` at a time `e` not before the state's own clock) has no final
    outcome yet and is not finalized. -/
theorem SatpLive.notFinal {P : Participant} {r : Route E} {n : NetworkState E P} {e : Time}
    (hl : SatpLive r n e) (hg : n.chain.now ≤ e) :
    n.chain.finalOutcome r.V.address = none ∧ n.chain.finalizedWith r.V.address = none := by
  rcases hl with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
  · simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
      Adjudicator.finalizedWith_channel, hu, ChannelStatus.finalOutcome_open,
      ChannelStatus.finalizedWith_open, and_self]
  · have hlt : n.chain.now < ch.deadline := lt_of_le_of_lt hg hdd
    simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
      Adjudicator.finalizedWith_channel, hu, ChannelStatus.finalOutcome_challenged,
      ChannelStatus.finalizedWith_challenged, if_neg (not_le.mpr hlt), and_self]

/-- One adversary `.chain` call, from a state where `r.V` is not finalized: `r.V`'s record
    does not drop, and either `r.V`'s status is unchanged (the call failed, or it did not
    target `r.V`), or a `challenge` or `checkpoint` on `r.V` registered a candidate that
    `satpVirtualRules` supports, with its proof now held (`Op.latest_record_step`,
    `statusOf_apply_of_not_targets`). A `conclude` on `r.V` cannot succeed: it needs `P`'s own
    signature on a final state of `r.V`, and every `P`-signed proof state of the call is one
    `P` sent (`hU`, which `Bounds.unforgeable` gives for a feasible adversary call), while `P`
    sent no final state of `r.V` (`satpVirtual_conclude_fails`). Every SATP round family below
    reads its `.chain` step off this one lemma. -/
theorem satpV_record_step {apps : Apps E} {P : Participant} {r : Route E} {ε : Time}
    {alice bob : Participant} (hE : SatpVirtual apps ε r alice bob P) {n : NetworkState E P}
    (hVs : HoldsVirtualSetup n r alice bob true) {caller : Participant} {op : Op E}
    (hU : ∀ ss ∈ op.proofStates, P ∈ ss.signers → ∃ x ∈ n.sent, x.state = ss.state)
    (hlive : n.chain.finalOutcome r.V.address = none) :
    (n.chain.statusOf r.V).turnNumRecord ≤
      ((n.applyAdv apps (.chain caller op)).chain.statusOf r.V).turnNumRecord ∧
    ((n.applyAdv apps (.chain caller op)).chain.statusOf r.V = n.chain.statusOf r.V ∨
     (∃ proof cand, op = Op.challenge r.V proof cand ∧
       satpVirtualRules.supports r.V proof cand = true ∧
       (∀ ss ∈ proof, (n.applyAdv apps (.chain caller op)).Holds ss) ∧
       ((n.chain.mode r.V = .open ∧ (n.chain.statusOf r.V).turnNumRecord ≤ cand.turnNum) ∨
        (n.chain.mode r.V = .challenge ∧ (n.chain.statusOf r.V).turnNumRecord < cand.turnNum)) ∧
       (n.applyAdv apps (.chain caller op)).chain.statusOf r.V =
         .challenged cand.turnNum ⟨cand, n.chain.now + r.V.challengeDuration⟩) ∨
     (∃ proof cand, op = Op.checkpoint r.V proof cand ∧
       satpVirtualRules.supports r.V proof cand = true ∧
       (∀ ss ∈ proof, (n.applyAdv apps (.chain caller op)).Holds ss) ∧
       (n.chain.statusOf r.V).turnNumRecord < cand.turnNum ∧
       (n.applyAdv apps (.chain caller op)).chain.statusOf r.V = .open cand.turnNum)) := by
  cases h : n.chain.apply apps caller op
  · rw [NetworkState.applyAdv_chain_none apps h]
    exact ⟨le_rfl, Or.inl rfl⟩
  rename_i s'
  rw [NetworkState.applyAdv_chain_some apps h]
  have hheld : ∀ ss ∈ op.proofStates,
      ({ n with chain := s', received := op.proofStates ++ n.received } : NetworkState E P).Holds
        ss :=
    fun ss hss => holds_of_mem_received (List.mem_append_left _ hss)
  dsimp only
  by_cases ht : Op.targets op r.V
  · rcases Op.latest_record_step h ht hlive with
        ⟨proof, cand, hop, hs, -, hmode, hnew⟩ | ⟨proof, cand, hop, hs, -, hlt, hnew⟩ |
        ⟨ss', hop, hcp, -⟩
    · subst hop
      rw [hE.app] at hs
      refine ⟨?_, Or.inr (Or.inl ⟨proof, cand, rfl, hs, hheld, hmode, hnew⟩)⟩
      rw [hnew, ChannelStatus.turnNumRecord_challenged]
      rcases hmode with ⟨-, hle⟩ | ⟨-, hlt⟩
      · exact hle
      · exact le_of_lt hlt
    · subst hop
      rw [hE.app] at hs
      refine ⟨?_, Or.inr (Or.inr ⟨proof, cand, rfl, hs, hheld, hlt, hnew⟩)⟩
      rw [hnew, ChannelStatus.turnNumRecord_open]
      exact le_of_lt hlt
    · subst hop
      exact (satpVirtual_conclude_fails hVs hE.toSatpEnds hcp hU).elim
  · have hsame := statusOf_apply_of_not_targets h ht
    exact ⟨le_of_eq (by rw [hsame]), Or.inl hsame⟩

/-- The frame every SATP round family carries: the round ends at `e`, less than `T.ε` after
    the step's own state (the clock only advances), and `P`'s own `r.V` setup states
    (`HoldsVirtualSetup`) stay as they are (no adversary move touches `sent`). Every step
    preserves both, whatever the guard and side condition. -/
theorem satpV_frame_step {apps : Apps E} {P : Participant} {T : Threat E P} {r : Route E}
    {alice bob : Participant} {Guard : NetworkState E P → Prop}
    {Cond : NetworkState E P → Op E → Prop} (e : Time) :
    T.StepInvariant apps Guard
      (fun n => e < n.chain.now + T.ε ∧ HoldsVirtualSetup n r alice bob true) Cond := by
  have hstep : ∀ {n : NetworkState E P} (m : AdvMove E),
      e < n.chain.now + T.ε ∧ HoldsVirtualSetup n r alice bob true →
      e < (n.applyAdv apps m).chain.now + T.ε ∧
        HoldsVirtualSetup (n.applyAdv apps m) r alice bob true :=
    fun m hI => ⟨lt_of_lt_of_le hI.1
      (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps _ m) T.ε),
      by unfold HoldsVirtualSetup; rw [NetworkState.applyAdv_sent]; exact hI.2⟩
  exact ⟨fun _ _ => hstep _, fun _ _ => hstep _, fun _ _ => hstep _, fun _ _ => hstep _⟩

/-- The step obligations of "`r.V` is live at the round's end `e`" (`SatpLive`), beside the
    frame (`satpV_frame_step`). A `challenge` on `r.V` registers a deadline after `e`
    (`r.V.IsTimed T.ε`: the new deadline is at least `T.ε` after the step's own clock), a
    `checkpoint` leaves `r.V` open, and every other successful call leaves `r.V`'s status
    unchanged (`satpV_record_step`). -/
theorem satpV_live_step {apps : Apps E} {P : Participant} {T : Threat E P}
    (hbounds : Bounds apps P T) {r : Route E} {alice bob : Participant}
    (hE : SatpVirtual apps T.ε r alice bob P) (e : Time) :
    T.StepInvariant apps (fun n => n.chain.now ≤ e)
      (fun n => (e < n.chain.now + T.ε ∧ HoldsVirtualSetup n r alice bob true) ∧
        SatpLive r n e) (fun _ _ => False) := by
  refine (satpV_frame_step e).and ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩
  · intro n ss _ _ hl
    exact hl
  · intro n dt _ _ hl
    unfold SatpLive at hl ⊢
    simp only [NetworkState.applyAdv, Adjudicator.tick_statusOf]
    exact hl
  · intro n caller op ⟨hg, ⟨hεb, hVs⟩⟩ hfeas hl
    rcases (satpV_record_step hE hVs (fun ss hss hsig => (hbounds.unforgeable _ _ _ hfeas ss
        hss).1 hsig) (hl.notFinal hg).1).2 with
        hsame | ⟨proof, cand, -, -, -, -, hnew⟩ | ⟨proof, cand, -, -, -, -, hnew⟩
    · unfold SatpLive at hl ⊢
      rw [hsame]
      exact hl
    · refine Or.inr ⟨cand.turnNum, _, hnew, lt_of_lt_of_le hεb (Nat.add_le_add_left
        (le_trans (by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε) hE.timed) _)⟩
    · exact Or.inl ⟨cand.turnNum, hnew⟩

/-- `r.V`'s status is challenged, at or above `cand0`'s turn, with a live deadline. Starting
    from this specific shape (not merely open-or-challenged) lets a `checkpoint` transition to
    `.open` only strictly past `cand0.turnNum` -- never weakly, since the checkpoint's own
    precondition (`turnNumRecord(before) < candidate.turnNum`) combined with
    `cand0.turnNum ≤ turnNumRecord(before)` already forces `cand0.turnNum < candidate.turnNum`. -/
def SatpChallengedAbove {P : Participant} (r : Route E) (net : NetworkState E P)
    (cand0 : State E) (now : Time) : Prop :=
  ∃ u ch, net.chain.statusOf r.V = .challenged u ch ∧ cand0.turnNum ≤ u ∧ now < ch.deadline

/-- Over a round with nothing of `P`'s own still pending, starting from `r.V` genuinely
    challenged at or above `cand0`'s turn, `r.V`'s record either strictly passes `cand0`'s
    turn, or `r.V` stays challenged at or above `cand0`'s turn with a live deadline. A
    successful `challenge` or `checkpoint` on `r.V` from the challenged shape is strictly
    above the record (`satpV_record_step`; the mode is `challenge` while the deadline is
    live), and the record never drops afterwards (the same lemma, one step at a time), so
    the invariant needs no look at the rest of the round. -/
theorem satp_late_round_keeps_challenged_above_nil {apps : Apps E} {P : Participant}
    {T : Threat E P} (hbounds : Bounds apps P T) {r : Route E} {alice bob : Participant}
    (hE : SatpVirtual apps T.ε r alice bob P) :
    ∀ {net net' : NetworkState E P} {t : Time}, Threat.TimedRun apps T t [] net net' →
      HoldsVirtualSetup net r alice bob true →
      ∀ {cand0 : State E}, SatpChallengedAbove r net cand0 net'.chain.now →
      (cand0.turnNum < (net'.chain.statusOf r.V).turnNumRecord ∨
       SatpChallengedAbove r net' cand0 net'.chain.now) := by
  intro net net' t ⟨hseq, hεbound⟩ hVs cand0 habove
  have hlive0 : SatpLive r net net'.chain.now := by
    obtain ⟨u, ch, hu, -, hdd⟩ := habove
    exact Or.inr ⟨u, ch, hu, hdd⟩
  have hres := hseq.nil_invariant
    ((satpV_live_step hbounds hE net'.chain.now).and
      (I2 := fun n => cand0.turnNum < (n.chain.statusOf r.V).turnNumRecord ∨
        SatpChallengedAbove r n cand0 net'.chain.now)
      ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩)
    ⟨⟨⟨hεbound, hVs⟩, hlive0⟩, Or.inr habove⟩
  · exact hres.2
  · intro n ss _ _ hI
    exact hI
  · intro n dt _ _ hI
    unfold SatpChallengedAbove at hI ⊢
    simp only [NetworkState.applyAdv, Adjudicator.tick_statusOf]
    exact hI
  · intro n caller op ⟨hg, ⟨_, hVsn⟩, hl⟩ hfeas hI
    obtain ⟨hmono, hstep⟩ := satpV_record_step hE hVsn (fun ss hss hsig =>
      (hbounds.unforgeable _ _ _ hfeas ss hss).1 hsig) (hl.notFinal hg).1
    rcases hI with hlt | ⟨u, ch, hu, hle, hdd⟩
    · exact Or.inl (lt_of_lt_of_le hlt hmono)
    · rcases hstep with hsame | ⟨proof, cand, -, -, -, hmode, hnew⟩ |
          ⟨proof, cand, -, -, -, hlt, hnew⟩
      · exact Or.inr ⟨u, ch, by rw [hsame]; exact hu, hle, hdd⟩
      · left
        have hm : n.chain.mode r.V = .challenge := by
          rw [Adjudicator.mode_eq, hu, ChannelStatus.mode_challenged,
            if_neg (not_le.mpr (lt_of_le_of_lt hg hdd))]
        rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt⟩
        · rw [hm] at hmo; cases hmo
        · rw [hnew, ChannelStatus.turnNumRecord_challenged]
          rw [hu, ChannelStatus.turnNumRecord_challenged] at hlt
          exact lt_of_le_of_lt hle hlt
      · left
        rw [hnew, ChannelStatus.turnNumRecord_open]
        rw [hu, ChannelStatus.turnNumRecord_challenged] at hlt
        exact lt_of_le_of_lt hle hlt

theorem validChallenge_channel {alice bob : Participant} {c : FixedPart} {s ch : SignedState E}
    (h : validChallenge c alice bob s ch = true) : ch.state.channel = c := by
  unfold validChallenge at h
  split at h
  · obtain ⟨⟨⟨⟨⟨hchan, hor⟩, hsig⟩, hav⟩, hbv⟩, hout⟩ := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    exact hchan.2
  · cases h

theorem validResponse_channel {alice bob : Participant} {c : FixedPart} {s ch re : SignedState E}
    (h : validResponse c alice bob s ch re = true) : re.state.channel = c := by
  unfold validResponse at h
  split at h
  · have h' := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    exact h'.1.1.1.1.1.1.1.1.2
  · cases h

/-- A supported candidate of `r.V` (`SatpCandidate`) is a state of `r.V`:
    `consensusRules.supports` (turn ≤ 1 or 4) and `validStart`/`validChallenge`/`validResponse`
    (turn 2/3) all check it directly. Purely structural: unlike `satpVirtual_supported`, needs
    no `HoldsVirtualSetup` or `P`-held witness. -/
theorem satpVirtual_channel {r : Route E} {alice bob : Participant}
    (hhead : r.V.participants.head? = some alice) (hlast : r.V.participants.getLast? = some bob)
    (c : SatpCandidate r) : c.cand.channel = r.V := by
  obtain ⟨proof, cand, hsupp⟩ := c
  dsimp only
  simp only [satpVirtualRules, hhead, hlast] at hsupp
  split_ifs at hsupp with ht1 ht4
  · match proof, hsupp with
    | [ssx], hcon =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
      rw [← hcon.1.1]; exact hcon.1.2
    | [], hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
    | _ :: _ :: _, hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
  · simp only [Bool.and_eq_true] at hsupp
    obtain ⟨hcon, -⟩ := hsupp
    match proof, hcon with
    | [ssx], hcon =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
      rw [← hcon.1.1]; exact hcon.1.2
    | [], hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
    | _ :: _ :: _, hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
  · match proof, hsupp with
    | [s], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvs, hceq⟩ := hsupp
      obtain ⟨-, hchan⟩ := satp_validStart_byAll hvs
      rw [← hceq]; exact hchan
    | [s, ch], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvc, hceq⟩ := hsupp
      rw [← hceq]; exact validChallenge_channel hvc
    | [s, ch, re], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvr, hceq⟩ := hsupp
      rw [← hceq]; exact validResponse_channel hvr
    | [], hsupp => (simp? [validateOutcomeChange] at hsupp says simp only [validateOutcomeChange, Bool.false_eq_true] at hsupp)
    | _ :: _ :: _ :: _ :: _, hsupp => (simp? [validateOutcomeChange] at hsupp says simp only [validateOutcomeChange, Bool.false_eq_true] at hsupp)


/-- A supported candidate of `r.V` (`SatpCandidate`) whose `P`-signed proof states `P` sent
    (`hU`), with `P`'s own signed states for `r.V` bounded by `HoldsVirtualSetup`: the
    candidate's turn is at most 3, and its outcome is a pair summing to `r.a0 + r.b0` (the SATP
    paper, line 705). Turn ≤ 1 keeps the ORIGINAL outcome exactly (`HoldsVirtualSetup`'s own
    bound on what `P` signs); turn 4 needs a final state that `P` signed, which
    `HoldsVirtualSetup` excludes; turn 2/3 preserve the funded total of the start state
    (`validChallenge_outcome`/`validResponse_outcome`), and that start state is itself `P`'s
    own (turn-1) signed state, so its outcome is ALSO the original one. -/
theorem satpVirtual_supported {P : Participant} {r : Route E} {alice bob : Participant}
    (hE : SatpEnds r alice bob P)
    {net : NetworkState E P} (hVs : HoldsVirtualSetup net r alice bob true)
    (c : SatpCandidate r)
    (hU : ∀ ss ∈ c.proof, P ∈ ss.signers → ∃ x ∈ net.sent, x.state = ss.state) :
    c.cand.turnNum ≤ 3 ∧
      ∃ a b, PairOutcome (r.dest alice) (r.dest bob) c.cand.outcome a b ∧ a + b = r.a0 + r.b0 := by
  obtain ⟨proof, cand, hsupp⟩ := c
  dsimp only at hU ⊢
  have hstart : ∀ s : SignedState E, s.ByAll → s.state.channel = r.V → s ∈ proof →
      s.state.outcome = originalOutcome (r.dest alice) (r.dest bob) r.a0 r.b0 := by
    intro s hall hchan hmem
    have hPsig : P ∈ s.signers := hall P (by rw [hchan]; exact hE.mem)
    obtain ⟨x, hx, hxs⟩ := hU s hmem hPsig
    obtain ⟨houtc, -, -⟩ := hVs.1 x hx (by rw [hxs]; exact hchan)
    rw [← hxs]; exact houtc
  simp only [satpVirtualRules, hE.head, hE.last] at hsupp
  split_ifs at hsupp with ht1 ht4
  · refine ⟨by omega, ?_⟩
    match proof, hsupp with
    | [ssx], hcon =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
      obtain ⟨⟨hst, hchan⟩, hall⟩ := hcon
      have houtc := hstart ssx hall hchan (List.mem_singleton_self _)
      rw [← hst, houtc]
      exact ⟨r.a0, r.b0, rfl, rfl⟩
    | [], hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
    | _ :: _ :: _, hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
  · exfalso
    simp only [Bool.and_eq_true] at hsupp
    obtain ⟨hcon, hisfin⟩ := hsupp
    match proof, hcon with
    | [ssx], hcon =>
      simp only [consensusRules, Bool.and_eq_true, decide_eq_true_eq] at hcon
      obtain ⟨⟨hst, hchan⟩, hall⟩ := hcon
      have hPsig : P ∈ ssx.signers := hall P (by rw [hchan]; exact hE.mem)
      obtain ⟨x, hx, hxs⟩ := hU ssx (List.mem_singleton_self _) hPsig
      obtain ⟨-, hfin, -⟩ := hVs.1 x hx (by rw [hxs]; exact hchan)
      rw [← hst, ← hxs, hfin] at hisfin
      exact absurd hisfin (by decide)
    | [], hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
    | _ :: _ :: _, hcon => (simp? [consensusRules] at hcon says simp only [consensusRules, Bool.false_eq_true] at hcon)
  · match proof, hsupp with
    | [s], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvs, hceq⟩ := hsupp
      obtain ⟨hall, hchan⟩ := satp_validStart_byAll hvs
      have hPsig : P ∈ s.signers := hall P (by rw [hchan]; exact hE.mem)
      obtain ⟨x, hx, hxs⟩ := hU s (List.mem_singleton_self _) hPsig
      obtain ⟨-, -, ht⟩ := hVs.1 x hx (by rw [hxs]; exact hchan)
      have houtc := hstart s hall hchan (List.mem_singleton_self _)
      refine ⟨?_, ?_⟩
      · rw [← hceq, ← hxs]
        rcases ht with h0 | ⟨-, h1⟩ <;> omega
      · rw [← hceq, houtc]
        exact ⟨r.a0, r.b0, rfl, rfl⟩
    | [s, ch], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvc, hceq⟩ := hsupp
      have hturn := validChallenge_turnNum hvc
      have hvsb : validStart r.V s = true := by
        unfold validChallenge at hvc
        split at hvc
        · obtain ⟨⟨⟨⟨⟨hchan, hor⟩, hsig⟩, hav⟩, hbv⟩, hout⟩ := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using hvc
          exact hchan.1.1.1
        · cases hvc
      obtain ⟨hall, hchan⟩ := satp_validStart_byAll hvsb
      have houtc := hstart s hall hchan (List.mem_cons_self)
      obtain ⟨da, db, a, b, hpd, hch, hab⟩ := validChallenge_outcome hvc
      rw [houtc] at hpd
      simp only [originalOutcome, Outcome.pairDests, Option.some.injEq, Prod.mk.injEq] at hpd
      obtain ⟨hda, hdb⟩ := hpd
      subst hda; subst hdb
      rw [← hceq]
      refine ⟨by omega, ?_⟩
      rw [hch]
      refine ⟨a, b, rfl, ?_⟩
      rw [hab, houtc]
      rfl
    | [s, ch, re], hsupp =>
      simp only [validateOutcomeChange, Bool.and_eq_true, decide_eq_true_eq] at hsupp
      obtain ⟨hvr, hceq⟩ := hsupp
      have hturn := validResponse_turnNum hvr
      have hvc : validChallenge r.V alice bob s ch = true := by
        unfold validResponse at hvr
        split at hvr
        · have h' := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hvr
          exact h'.1.1.1.1.1.1.1.1.1.1
        · cases hvr
      have hvsb : validStart r.V s = true := by
        unfold validChallenge at hvc
        split at hvc
        · obtain ⟨⟨⟨⟨⟨hchan, hor⟩, hsig⟩, hav⟩, hbv⟩, hout⟩ := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using hvc
          exact hchan.1.1.1
        · cases hvc
      obtain ⟨hall, hchan⟩ := satp_validStart_byAll hvsb
      have houtc := hstart s hall hchan (List.mem_cons_self)
      obtain ⟨da, db, a, b, hpd, hre, hab⟩ := validResponse_outcome hvr
      rw [houtc] at hpd
      simp only [originalOutcome, Outcome.pairDests, Option.some.injEq, Prod.mk.injEq] at hpd
      obtain ⟨hda, hdb⟩ := hpd
      subst hda; subst hdb
      rw [← hceq]
      refine ⟨by omega, ?_⟩
      rw [hre]
      refine ⟨a, b, rfl, ?_⟩
      rw [hab, houtc]
      rfl
    | [], hsupp => (simp? [validateOutcomeChange] at hsupp says simp only [validateOutcomeChange, Bool.false_eq_true] at hsupp)
    | _ :: _ :: _ :: _ :: _, hsupp => (simp? [validateOutcomeChange] at hsupp says simp only [validateOutcomeChange, Bool.false_eq_true] at hsupp)


/-- Over a round with nothing of `P`'s own pending, starting with `r.V` EXACTLY
    `.challenged T0 ch` (or already finalized with `ch.state.outcome`): `r.V` stays EXACTLY
    this, is finalized with `ch.state.outcome` (the deadline passed), or something escalated
    past `T0`. From the exact record `T0` with a live deadline, every successful
    `challenge`/`checkpoint` on `r.V` strictly beats `T0` (`satpV_record_step`: the mode is
    `challenge`). The escalated disjunct carries `SatpLive` at the round's end and the
    escalation witness; `satpV_live_step`, `NetworkState.Holds.mono` and the record's
    monotonicity preserve both one step at a time, so the invariant
    (`Threat.RoundSeq.nil_invariant`) needs no look at the rest of the round. -/
theorem satp_late_round_keeps_status_nil {apps : Apps E} {P : Participant} {T : Threat E P}
    (hbounds : Bounds apps P T) {r : Route E} {alice bob : Participant}
    (hE : SatpVirtual apps T.ε r alice bob P) :
    ∀ {net net' : NetworkState E P} {t : Time}, Threat.TimedRun apps T t [] net net' →
      HoldsVirtualSetup net r alice bob true →
      ∀ {T0 : Nat} {ch : Challenge E},
      (net.chain.finalizedWith r.V.address = some ch.state.outcome ∨
       net.chain.statusOf r.V = .challenged T0 ch) →
      (net'.chain.finalizedWith r.V.address = some ch.state.outcome ∨
       net'.chain.statusOf r.V = .challenged T0 ch ∨
       ∃ proof1 cand1, (∀ ss' ∈ proof1, net'.Holds ss') ∧
         (∀ ss' ∈ proof1, P ∈ ss'.signers → ∃ x ∈ net'.sent, x.state = ss'.state) ∧
         satpVirtualRules.supports r.V proof1 cand1 = true ∧ T0 < cand1.turnNum ∧
         cand1.turnNum ≤ (net'.chain.statusOf r.V).turnNumRecord ∧
         net'.chain.finalizedWith r.V.address = none) := by
  intro net net' t ⟨hseq, hεbound⟩ hVs T0 ch hbase
  have hlive := satpV_live_step hbounds hE net'.chain.now
  have hcd : T.ε ≤ r.V.challengeDuration :=
    le_trans (by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε) hE.timed
  -- A finalized `r.V` stays finalized through every adversary move.
  have hfin : ∀ {n : NetworkState E P} (m : AdvMove E), (∀ op, m ≠ .land op) →
      n.chain.finalizedWith r.V.address = some ch.state.outcome →
      (n.applyAdv apps m).chain.finalizedWith r.V.address = some ch.state.outcome := by
    intro n m hnoland hf
    cases m with
    | land op => exact absurd rfl (hnoland op)
    | deliver ss' => exact hf
    | tick dt =>
      have hf0 : (n.chain.statusOf r.V).finalizedWith n.chain.now = some ch.state.outcome := by
        (simpa? [FixedPart.address_eq] using hf says simpa only [FixedPart.address_eq, Adjudicator.finalizedWith_channel] using hf)
      have hf0' : (n.chain.statusOf r.V).finalizedWith (n.chain.now + dt) =
          some ch.state.outcome :=
        ChannelStatus.finalizedWith_mono hf0 (Nat.le_add_right _ dt)
      (simpa? [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.tick_statusOf,
        Adjudicator.tick_now] using hf0' says simpa only [NetworkState.applyAdv, FixedPart.address_eq, Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, Adjudicator.tick_now] using hf0')
    | chain caller op =>
      cases h : n.chain.apply apps caller op with
      | none => rw [NetworkState.applyAdv_chain_none apps h]; exact hf
      | some s' =>
        rw [NetworkState.applyAdv_chain_some apps h]
        exact Adjudicator.finalizedWith_apply h hf
  -- The escalation witness survives every adversary move that does not lower the record.
  have hWstep : ∀ {n : NetworkState E P} (m : AdvMove E),
      (n.chain.statusOf r.V).turnNumRecord ≤
        ((n.applyAdv apps m).chain.statusOf r.V).turnNumRecord →
      (∃ proof1 cand1, (∀ ss' ∈ proof1, n.Holds ss') ∧
        (∀ ss' ∈ proof1, P ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) ∧
        satpVirtualRules.supports r.V proof1 cand1 = true ∧ T0 < cand1.turnNum ∧
        cand1.turnNum ≤ (n.chain.statusOf r.V).turnNumRecord) →
      ∃ proof1 cand1, (∀ ss' ∈ proof1, (n.applyAdv apps m).Holds ss') ∧
        (∀ ss' ∈ proof1, P ∈ ss'.signers → ∃ x ∈ (n.applyAdv apps m).sent,
          x.state = ss'.state) ∧
        satpVirtualRules.supports r.V proof1 cand1 = true ∧ T0 < cand1.turnNum ∧
        cand1.turnNum ≤ ((n.applyAdv apps m).chain.statusOf r.V).turnNumRecord :=
    fun m hrec ⟨proof1, cand1, hH, hU, hs, hlt, hle⟩ =>
      ⟨proof1, cand1, fun ss' hss => NetworkState.Holds.mono
        (NetworkState.applyAdv_sent apps _ m).symm (NetworkState.applyAdv_received_subset apps _ m)
        (hH ss' hss), by rw [NetworkState.applyAdv_sent]; exact hU, hs, hlt, le_trans hle hrec⟩
  have hres := hseq.nil_invariant
    ((satpV_frame_step net'.chain.now).and
      (I2 := fun n => n.chain.finalizedWith r.V.address = some ch.state.outcome ∨
        n.chain.statusOf r.V = .challenged T0 ch ∨
        (SatpLive r n net'.chain.now ∧
          ∃ proof1 cand1, (∀ ss' ∈ proof1, n.Holds ss') ∧
            (∀ ss' ∈ proof1, P ∈ ss'.signers → ∃ x ∈ n.sent, x.state = ss'.state) ∧
            satpVirtualRules.supports r.V proof1 cand1 = true ∧ T0 < cand1.turnNum ∧
            cand1.turnNum ≤ (n.chain.statusOf r.V).turnNumRecord))
      ⟨fun _ h _ => (h : False).elim, ?_, ?_, ?_⟩)
    ⟨⟨hεbound, hVs⟩, hbase.elim Or.inl fun h => Or.inr (Or.inl h)⟩
  · rcases hres.2 with hf | hst | ⟨hl, proof1, cand1, hH, hU, hs, hlt, hle⟩
    · exact Or.inl hf
    · exact Or.inr (Or.inl hst)
    · exact Or.inr (Or.inr ⟨proof1, cand1, hH, hU, hs, hlt, hle, (hl.notFinal le_rfl).2⟩)
  · intro n ss ⟨hg, hεb, hVsn⟩ hfeas hI
    rcases hI with hf | hst | ⟨hl, hW⟩
    · exact Or.inl (hfin (.deliver ss) (fun _ h => by cases h) hf)
    · exact Or.inr (Or.inl hst)
    · exact Or.inr (Or.inr ⟨(hlive.deliver hg hfeas ⟨⟨hεb, hVsn⟩, hl⟩).2,
        hWstep (.deliver ss) le_rfl hW⟩)
  · intro n dt ⟨hg, hεb, hVsn⟩ hfeas hI
    have hrec : (n.chain.statusOf r.V).turnNumRecord =
        ((n.applyAdv apps (.tick dt)).chain.statusOf r.V).turnNumRecord := by
      simp only [NetworkState.applyAdv, Adjudicator.tick_statusOf]
    rcases hI with hf | hst | ⟨hl, hW⟩
    · exact Or.inl (hfin (.tick dt) (fun _ h => by cases h) hf)
    · refine Or.inr (Or.inl ?_)
      simp only [NetworkState.applyAdv]
      rw [Adjudicator.tick_statusOf]
      exact hst
    · exact Or.inr (Or.inr ⟨(hlive.tick hg hfeas ⟨⟨hεb, hVsn⟩, hl⟩).2,
        hWstep (.tick dt) (le_of_eq hrec) hW⟩)
  · intro n caller op ⟨hg, hεb, hVsn⟩ hfeas hI
    rcases hI with hf | hst | ⟨hl, hW⟩
    · exact Or.inl (hfin (.chain caller op) (fun _ h => by cases h) hf)
    · by_cases hexp : ch.deadline ≤ n.chain.now
      · refine Or.inl (hfin (.chain caller op) (fun _ h => by cases h) ?_)
        simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
          ChannelStatus.finalizedWith_challenged, if_pos hexp]
      · rw [not_le] at hexp
        have hfo : n.chain.finalOutcome r.V.address = none := by
          simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hst,
            ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hexp)]
        have hm : n.chain.mode r.V = .challenge := by
          rw [Adjudicator.mode_eq, hst, ChannelStatus.mode_challenged, if_neg (not_le.mpr hexp)]
        have hsent : ∀ ss' ∈ op.proofStates, P ∈ ss'.signers →
            ∃ x ∈ (n.applyAdv apps (.chain caller op)).sent, x.state = ss'.state := by
          rw [NetworkState.applyAdv_sent]
          exact fun ss' hss hsig => (hbounds.unforgeable n caller op hfeas ss' hss).1 hsig
        rcases (satpV_record_step hE hVsn (fun ss hss hsig => (hbounds.unforgeable _ _ _ hfeas
            ss hss).1 hsig) hfo).2 with
            hsame | ⟨proof, cand, rfl, hs, hH, hmode, hnew⟩ |
            ⟨proof, cand, rfl, hs, hH, hlt, hnew⟩
        · exact Or.inr (Or.inl (by rw [hsame]; exact hst))
        · have hlt2 : T0 < cand.turnNum := by
            rcases hmode with ⟨hmo, -⟩ | ⟨-, hlt⟩
            · rw [hm] at hmo; cases hmo
            · rwa [hst, ChannelStatus.turnNumRecord_challenged] at hlt
          refine Or.inr (Or.inr ⟨Or.inr ⟨cand.turnNum, _, hnew,
            lt_of_lt_of_le hεb (Nat.add_le_add_left hcd _)⟩, proof, cand, hH, hsent,
            hs, hlt2, ?_⟩)
          rw [hnew, ChannelStatus.turnNumRecord_challenged]
        · have hlt2 : T0 < cand.turnNum := by
            rwa [hst, ChannelStatus.turnNumRecord_challenged] at hlt
          refine Or.inr (Or.inr ⟨Or.inl ⟨cand.turnNum, hnew⟩, proof, cand, hH, hsent,
            hs, hlt2, ?_⟩)
          rw [hnew, ChannelStatus.turnNumRecord_open]
    · have hrec : (n.chain.statusOf r.V).turnNumRecord ≤
          ((n.applyAdv apps (.chain caller op)).chain.statusOf r.V).turnNumRecord :=
        (satpV_record_step hE hVsn (fun ss hss hsig => (hbounds.unforgeable _ _ _ hfeas ss
          hss).1 hsig) (hl.notFinal hg).1).1
      exact Or.inr (Or.inr ⟨(hlive.chain hg hfeas ⟨⟨hεb, hVsn⟩, hl⟩).2, hWstep _ hrec hW⟩)


/-- One `.wait w` move either finalizes `r.V` with `ch.state.outcome`, or something escalates
    past `T0` during the one round the adversary gets within the wait (`hseq2`, bounded by
    `T.ε` the same as any other move). No deadline MARGIN is required: `satp_late_round_keeps_
    status_nil`'s own restructured conclusion already folds "already finalizable" in, handling
    an unboundedly-long wait correctly (mirrors `wait_resolves_challenge`'s own handling of
    `latest_wait_keeps_status`'s finalized/still-live split). -/
theorem satp_wait_resolves_or_escalates {apps : Apps E} {P : Participant} {T : Threat E P}
    (hbounds : Bounds apps P T) {r : Route E} {alice bob : Participant}
    (hE : SatpVirtual apps T.ε r alice bob P) {net2 net3 : NetworkState E P} {t w : Time}
    {T0 : Nat} {ch : Challenge E} (hdw : ch.deadline ≤ net2.chain.now + w)
    (hVs : HoldsVirtualSetup net2 r alice bob true)
    (hseq2 : Threat.TimedRun apps T t [] net2 net3)
    (hst : SatpChallenged r net2 T0 ch) :
    (net3.chain.tick w).finalizedWith r.V.address = some ch.state.outcome ∨
    ∃ proof1 cand1, (∀ ss' ∈ proof1, net3.Holds ss') ∧
      (∀ ss' ∈ proof1, P ∈ ss'.signers → ∃ x ∈ net3.sent, x.state = ss'.state) ∧
      satpVirtualRules.supports r.V proof1 cand1 = true ∧ T0 < cand1.turnNum ∧
      cand1.turnNum ≤ (net3.chain.statusOf r.V).turnNumRecord ∧
      net3.chain.finalizedWith r.V.address = none := by
  obtain ⟨hseq2, hεbound⟩ := hseq2
  have hmono2 : net2.chain.now ≤ net3.chain.now := hseq2.now_le
  have hinv2 := satp_late_round_keeps_status_nil hbounds hE ⟨hseq2, hεbound⟩ hVs
    (Or.inr hst.status)
  rcases hinv2 with hf3 | hst3 | ⟨proof1, cand1, hH1, hU1, hs1, hlt1, hprog1, hfin1⟩
  · left
    simpa [Adjudicator.tick_statusOf, Adjudicator.tick_now, FixedPart.address_eq] using
      ChannelStatus.finalizedWith_mono (by simpa [FixedPart.address_eq] using hf3)
        (Nat.le_add_right _ w)
  · left
    have h1 : ch.deadline ≤ net3.chain.now + w := le_trans hdw (Nat.add_le_add_right hmono2 w)
    simp only [FixedPart.address_eq, Adjudicator.finalizedWith_channel,
      Adjudicator.tick_statusOf, hst3, Adjudicator.tick_now,
      ChannelStatus.finalizedWith_challenged, if_pos h1]
  · exact Or.inr ⟨proof1, cand1, hH1, hU1, hs1, hlt1, hprog1, hfin1⟩


theorem satp_land_keeps_status {apps : Apps E} {P : Participant} {T : Threat E P}
    (hbounds : Bounds apps P T) {r : Route E} {alice bob : Participant}
    (hE : SatpVirtual apps T.ε r alice bob P) (c0 : SatpCandidate r)
    {net net' : NetworkState E P} {t : Time}
    (hseq : Threat.TimedRun apps T t [Op.challenge r.V c0.proof c0.cand] net net') :
    HoldsVirtualSetup net r alice bob true → (∀ ss ∈ c0.proof, net.Holds ss) →
    SatpLive r net net'.chain.now →
    ((∃ ch, net'.chain.statusOf r.V = .challenged c0.cand.turnNum ch ∧ ch.state = c0.cand ∧
      net'.chain.now + T.ε ≤ ch.deadline) ∨
    (∃ proof1 cand1, (∀ ss' ∈ proof1, net'.Holds ss') ∧
      (∀ ss' ∈ proof1, P ∈ ss'.signers → ∃ x ∈ net'.sent, x.state = ss'.state) ∧
      satpVirtualRules.supports r.V proof1 cand1 = true ∧ c0.cand.turnNum < cand1.turnNum ∧
      cand1.turnNum ≤ (net'.chain.statusOf r.V).turnNumRecord ∧
      net'.chain.finalizedWith r.V.address = none) ∨
    ((c0.cand.turnNum < (net'.chain.statusOf r.V).turnNumRecord ∧
      SatpLive r net' net'.chain.now) ∨ SatpChallengedAbove r net' c0.cand net'.chain.now) ∨
    net'.chain.finalizedWith r.V.address = some c0.cand.outcome) := by
  obtain ⟨hseq, hεb⟩ := hseq; revert hεb
  have hchan : c0.cand.channel = r.V := satpVirtual_channel hE.head hE.last c0
  obtain ⟨proof0, cand0, hsupp0⟩ := c0
  dsimp only at hseq hchan ⊢
  generalize heq : ([Op.challenge r.V proof0 cand0] : List (Op E)) = pending at hseq
  induction hseq with
  | nil => intro _ _ _ _; cases heq
  | @land pending net1 net2 op l1 l2 hsplit hrest ih =>
    intro hεbound hVs hheld0 hlive0
    cases heq
    rcases l1 with _ | ⟨a, l1⟩
    · rcases l2 with _ | ⟨b, l2⟩
      · simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨hopeq, -⟩ := hsplit
        subst hopeq
        cases h : net1.chain.apply apps P (Op.challenge r.V proof0 cand0) with
        | none =>
          have hfail : ¬ (P ∈ r.V.participants ∧
              satpVirtualRules.supports r.V proof0 cand0 = true ∧ cand0.channel = r.V ∧
              ((net1.chain.mode r.V = .open ∧
                  (net1.chain.statusOf r.V).turnNumRecord ≤ cand0.turnNum) ∨
                (net1.chain.mode r.V = .challenge ∧
                  (net1.chain.statusOf r.V).turnNumRecord < cand0.turnNum))) := by
            intro hcon
            simp only [Adjudicator.apply, Adjudicator.challenge, hE.app, if_pos hcon] at h
            exact absurd h (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
          push_neg at hfail
          have hmd := (hfail hE.mem hsupp0 hchan)
          rcases hlive0 with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
          · -- `net1` is itself open: the land attempt's own precondition gives strict
            -- progress directly, regardless of what happens for the rest of the round.
            have hmo : net1.chain.mode r.V = .open := by
              rw [Adjudicator.mode_eq, hu, ChannelStatus.mode_open]
            have hstrict1 : cand0.turnNum < (net1.chain.statusOf r.V).turnNumRecord := hmd.1 hmo
            rw [NetworkState.applyAdv_land_none apps h] at hrest
            have hprog2 := Threat.RoundSeq.turnNumRecord_ge hbounds hE.toSatpEnds hVs hrest
            have hlive2 := (hrest.nil_invariant (satpV_live_step hbounds hE _)
              ⟨⟨hεbound, hVs⟩, Or.inl ⟨u, hu⟩⟩).2
            exact Or.inr (Or.inr (Or.inl (Or.inl ⟨lt_of_lt_of_le hstrict1 hprog2, hlive2⟩)))
          · -- `net1` is itself challenged: the land attempt's own precondition only gives a
            -- weak bound, but `net1`'s own shape is challenged, at or above `cand0`'s turn --
            -- `satp_late_round_keeps_challenged_above_nil` rules out ever weakly settling as
            -- open from here.
            have hnle : net1.chain.now ≤ net2.chain.now := by
              have := hrest.now_le
              rwa [NetworkState.applyAdv_land_none apps h] at this
            have hltdl : net1.chain.now < ch.deadline := lt_of_le_of_lt hnle hdd
            have hmo : net1.chain.mode r.V = .challenge := by
              rw [Adjudicator.mode_eq, hu, ChannelStatus.mode_challenged,
                if_neg (not_le.mpr hltdl)]
            have hweak1 : cand0.turnNum ≤ (net1.chain.statusOf r.V).turnNumRecord := hmd.2 hmo
            have hu0 : (net1.chain.statusOf r.V).turnNumRecord = u := by rw [hu]; rfl
            rw [NetworkState.applyAdv_land_none apps h] at hrest
            have hSCA1 : SatpChallengedAbove r net1 cand0 net2.chain.now :=
              ⟨u, ch, hu, hu0 ▸ hweak1, hdd⟩
            have hres2 := satp_late_round_keeps_challenged_above_nil hbounds hE ⟨hrest,
              hεbound⟩ hVs hSCA1
            rcases hres2 with hstrict2 | hSCA2
            · have hlive2 := (hrest.nil_invariant (satpV_live_step hbounds hE _)
                ⟨⟨hεbound, hVs⟩, Or.inr ⟨u, ch, hu, hdd⟩⟩).2
              exact Or.inr (Or.inr (Or.inl (Or.inl ⟨hstrict2, hlive2⟩)))
            · exact Or.inr (Or.inr (Or.inl (Or.inr hSCA2)))
        | some s' =>
          obtain ⟨⟨-, -, -, hmode⟩, hs'eq⟩ := Adjudicator.challenge_some h
          have hstatus1 : (net1.applyAdv apps
              (AdvMove.land (Op.challenge r.V proof0 cand0))).chain.statusOf r.V =
              .challenged cand0.turnNum ⟨cand0, net1.chain.now + r.V.challengeDuration⟩ := by
            rw [NetworkState.applyAdv_land_some apps h, hs'eq, Adjudicator.statusOf_setStatus,
              if_pos rfl]
          have hεbound' : net2.chain.now <
              (net1.applyAdv apps (AdvMove.land (Op.challenge r.V proof0 cand0))).chain.now +
                T.ε :=
            lt_of_lt_of_le hεbound
              (Nat.add_le_add_right
                (NetworkState.applyAdv_now_le apps net1
                  (.land (Op.challenge r.V proof0 cand0))) T.ε)
          have hVs' : HoldsVirtualSetup
              (net1.applyAdv apps (AdvMove.land (Op.challenge r.V proof0 cand0))) r alice bob
                true := by
            unfold HoldsVirtualSetup; rw [NetworkState.applyAdv_sent]; exact hVs
          have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
          have hge : T.ε ≤ r.V.challengeDuration := le_trans hself hE.timed
          have hnow_eq : (net1.applyAdv apps
              (AdvMove.land (Op.challenge r.V proof0 cand0))).chain.now = net1.chain.now := by
            rw [NetworkState.applyAdv_land_some apps h, hs'eq]; (simp? says simp only [Adjudicator.setStatus_now])
          have hεb : net2.chain.now < net1.chain.now + T.ε := by rwa [hnow_eq] at hεbound'
          have hdd1' : net2.chain.now < (⟨cand0, net1.chain.now +
              r.V.challengeDuration⟩ : Challenge E).deadline := by
            show net2.chain.now < net1.chain.now + r.V.challengeDuration
            exact lt_of_lt_of_le hεb (Nat.add_le_add_left hge net1.chain.now)
          have hinv2 := satp_late_round_keeps_status_nil hbounds hE ⟨hrest, hεbound'⟩ hVs'
            (Or.inr hstatus1)
          rcases hinv2 with hf2 | hst2 | ⟨proof1, cand1, hH1, hU1, hs1, hlt1, hprog1, hfin1⟩
          · exact Or.inr (Or.inr (Or.inr hf2))
          · refine Or.inl ⟨⟨cand0, net1.chain.now + r.V.challengeDuration⟩, hst2, rfl, ?_⟩
            show net2.chain.now + T.ε ≤ net1.chain.now + r.V.challengeDuration
            have hh1 : net2.chain.now + T.ε ≤ net1.chain.now + T.ε + T.ε :=
              Nat.add_le_add_right (le_of_lt hεb) T.ε
            have hh2 : net1.chain.now + T.ε + T.ε = net1.chain.now + 2 * T.ε := by
              rw [Nat.add_assoc, ← Nat.two_mul]
            rw [hh2] at hh1
            exact le_trans hh1 (Nat.add_le_add_left hE.timed net1.chain.now)
          · exact Or.inr (Or.inl ⟨proof1, cand1, hH1, hU1, hs1, hlt1, hprog1, hfin1⟩)
      · (simp? at hsplit says simp only [List.nil_append, List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at hsplit)
    · (simp? at hsplit says simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hsplit)
  | @tick pending net1 net2 dt hfeas hgate hrest ih =>
    intro hεbound hVs hheld0 hlive0
    have hεbound' : net2.chain.now < (net1.applyAdv apps (AdvMove.tick dt)).chain.now + T.ε :=
      lt_of_lt_of_le hεbound
        (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 (.tick dt)) T.ε)
    have hVs' : HoldsVirtualSetup (net1.applyAdv apps (AdvMove.tick dt)) r alice bob true := by
      unfold HoldsVirtualSetup; rw [NetworkState.applyAdv_sent]; exact hVs
    have hheld0' : ∀ ss ∈ proof0, (net1.applyAdv apps (AdvMove.tick dt)).Holds ss := by
      intro ss hss
      exact NetworkState.Holds.of_subset (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs))
        (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs)) (hheld0 ss hss)
    have hlive0' : SatpLive r (net1.applyAdv apps (AdvMove.tick dt)) net2.chain.now := by
      rcases hlive0 with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
      · refine Or.inl ⟨u, ?_⟩
        simp only [NetworkState.applyAdv]; rw [Adjudicator.tick_statusOf]; exact hu
      · refine Or.inr ⟨u, ch, ?_, hdd⟩
        simp only [NetworkState.applyAdv]; rw [Adjudicator.tick_statusOf]; exact hu
    exact ih heq hεbound' hVs' hheld0' hlive0'
  | @other pending net1 net2 m hfeas hnotick hnoland hrest ih =>
    intro hεbound hVs hheld0 hlive0
    have hεbound' : net2.chain.now < (net1.applyAdv apps m).chain.now + T.ε :=
      lt_of_lt_of_le hεbound (Nat.add_le_add_right (NetworkState.applyAdv_now_le apps net1 m) T.ε)
    have hVs' : HoldsVirtualSetup (net1.applyAdv apps m) r alice bob true := by
      unfold HoldsVirtualSetup; rw [NetworkState.applyAdv_sent]; exact hVs
    have hheld0' : ∀ ss ∈ proof0, (net1.applyAdv apps m).Holds ss := by
      intro ss hss
      cases m with
      | tick dt =>
        exact NetworkState.Holds.of_subset (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs))
          (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs)) (hheld0 ss hss)
      | deliver ss' =>
        exact NetworkState.Holds.of_subset (fun s hs => by (simpa? using hs says simpa only [NetworkState.applyAdv_deliver] using hs))
          (fun s hs => by simp only [NetworkState.applyAdv]; exact List.mem_cons_of_mem _ hs)
          (hheld0 ss hss)
      | land op => exact absurd rfl (hnoland op)
      | chain caller op =>
        cases h : net1.chain.apply apps caller op with
        | none =>
          exact NetworkState.Holds.of_subset (fun s hs => by
            rw [NetworkState.applyAdv_chain_none apps h]; exact hs)
            (fun s hs => by rw [NetworkState.applyAdv_chain_none apps h]; exact hs)
            (hheld0 ss hss)
        | some s' =>
          exact NetworkState.Holds.of_subset (fun s hs => by
            rw [NetworkState.applyAdv_chain_some apps h]; exact hs)
            (fun s hs => by
              rw [NetworkState.applyAdv_chain_some apps h]
              exact List.mem_append_right _ hs) (hheld0 ss hss)
    have hlive0' : SatpLive r (net1.applyAdv apps m) net2.chain.now := by
      have hfo1 : net1.chain.finalOutcome r.V.address = none := by
        rcases hlive0 with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
        · (simp? [hu] says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hu, ChannelStatus.finalOutcome_open])
        · have hltdl : net1.chain.now < ch.deadline :=
            lt_of_le_of_lt (le_trans (NetworkState.applyAdv_now_le apps net1 m) hrest.now_le) hdd
          simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hu,
            ChannelStatus.finalOutcome_challenged, if_neg (not_le.mpr hltdl)]
      cases m with
      | tick dt =>
        rcases hlive0 with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
        · exact Or.inl ⟨u, hu⟩
        · exact Or.inr ⟨u, ch, hu, hdd⟩
      | land op => exact absurd rfl (hnoland op)
      | deliver ss' =>
        rcases hlive0 with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
        · exact Or.inl ⟨u, hu⟩
        · exact Or.inr ⟨u, ch, hu, hdd⟩
      | chain caller op =>
        cases h : net1.chain.apply apps caller op with
        | none => rw [NetworkState.applyAdv_chain_none apps h]; exact hlive0
        | some s' =>
          have hcarry : s'.statusOf r.V = net1.chain.statusOf r.V →
              SatpLive r (net1.applyAdv apps (.chain caller op)) net2.chain.now := by
            intro hst'
            rw [NetworkState.applyAdv_chain_some apps h]
            rcases hlive0 with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
            · exact Or.inl ⟨u, by rw [hst']; exact hu⟩
            · exact Or.inr ⟨u, ch, by rw [hst']; exact hu, hdd⟩
          cases op with
          | deposit a e x =>
            obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
            exact hcarry (Adjudicator.statusOf_of_status hs r.V)
          | tick dt =>
            have hs' : net1.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
            subst hs'
            exact hcarry (Adjudicator.tick_statusOf _ _ _)
          | transfer a b =>
            by_cases hac : a = r.V
            · subst hac
              obtain ⟨o, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.transfer_some h
              rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
            · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
              exact hcarry (by
                rw [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
                  if_neg (Ne.symm hac)])
          | reclaim l v =>
            by_cases hlc : l = r.V
            · subst hlc
              obtain ⟨oL, -, -, -, -, hfo, -, -, -, -, -, -, -, -⟩ := Adjudicator.reclaim_some h
              rw [hfo1] at hfo; exact absurd hfo (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
            · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
              exact hcarry (by rw [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)])
          | challenge c' proof cand =>
            by_cases hcc : c' = r.V
            · subst hcc
              obtain ⟨⟨-, -, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
              have hnewstatus : (net1.applyAdv apps (.chain caller
                  (.challenge r.V proof cand))).chain.statusOf r.V = .challenged cand.turnNum
                    ⟨cand, net1.chain.now + r.V.challengeDuration⟩ := by
                rw [NetworkState.applyAdv_chain_some apps h]; (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])
              have hnow_eq : (net1.applyAdv apps (.chain caller
                  (.challenge r.V proof cand))).chain.now = net1.chain.now := by
                rw [NetworkState.applyAdv_chain_some apps h]; (simp? says simp only [Adjudicator.setStatus_now])
              have hself : T.ε ≤ 2 * T.ε := by rw [Nat.two_mul]; exact Nat.le_add_left T.ε T.ε
              have hge : T.ε ≤ r.V.challengeDuration := le_trans hself hE.timed
              have hεbound2 : net2.chain.now < net1.chain.now + T.ε := hnow_eq ▸ hεbound'
              have hdd2 : net2.chain.now < net1.chain.now + r.V.challengeDuration :=
                lt_of_lt_of_le hεbound2 (Nat.add_le_add_left hge net1.chain.now)
              exact Or.inr ⟨cand.turnNum, ⟨cand, net1.chain.now + r.V.challengeDuration⟩,
                hnewstatus, hdd2⟩
            · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
              exact hcarry (by rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)])
          | checkpoint c' proof cand =>
            by_cases hcc : c' = r.V
            · subst hcc
              obtain ⟨⟨-, -, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
              have hnewstatus : (net1.applyAdv apps (.chain caller
                  (.checkpoint r.V proof cand))).chain.statusOf r.V = .open cand.turnNum := by
                rw [NetworkState.applyAdv_chain_some apps h]; (simp? says simp only [Adjudicator.statusOf_setStatus, ↓reduceIte])
              exact Or.inl ⟨cand.turnNum, hnewstatus⟩
            · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
              exact hcarry (by rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)])
          | conclude c' ss' =>
            by_cases hcc : c' = r.V
            · subst hcc
              exfalso
              obtain ⟨⟨-, hconc⟩, -⟩ := Adjudicator.conclude_some h
              exact satpVirtual_conclude_fails hVs hE.toSatpEnds hconc
                (fun ss'' hmem hsig => (hbounds.unforgeable net1 caller (.conclude r.V ss')
                  hfeas ss'' hmem).1 hsig)
            · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
              exact hcarry (by rw [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)])
    exact ih heq hεbound' hVs' hheld0' hlive0'


/-- Whatever `r.V`'s on-chain status currently is (besides genesis `.open 0`), `P` holds the
    full proof that put it there: every element of a `(proof, cand)` pair satisfying
    `satpVirtualRules.supports`, matching the status's own turn/state. Lets `P` always resubmit
    whatever is on record, regardless of who submitted it originally (`D9`: a successful
    `challenge`/`checkpoint`'s proof states land in EVERY observer's `received`, including `P`'s,
    the instant it lands -- `P` observes the whole chain). -/
def NetVOrigin {P : Participant} (r : Route E) (net : NetworkState E P) : Prop :=
  (∀ u, net.chain.statusOf r.V = .open u → u ≠ 0 →
    ∃ proof cand, satpVirtualRules.supports r.V proof cand = true ∧ cand.turnNum = u ∧
      ∀ ss ∈ proof, net.Holds ss) ∧
  (∀ u ch, net.chain.statusOf r.V = .challenged u ch → ch.state.turnNum = u ∧
    ∃ proof, satpVirtualRules.supports r.V proof ch.state = true ∧ ∀ ss ∈ proof, net.Holds ss)


/-- `NetVOrigin` after one adversary `.chain caller op` step (`NetworkState.applyAdv`). A
    failed call leaves the network unchanged; a successful one gives
    `{net with chain := s', received := op.proofStates ++ net.received}`, the shared shape of
    `.land op` (definitionally the `.chain p op` step) and `.chain caller op`. Does not need
    `Bounds`/unforgeability at all: `D9` gives `P` the proof the instant it lands, regardless
    of who submitted it. -/
theorem NetVOrigin_apply_step {apps : Apps E} {P : Participant} {r : Route E}
    (hV : apps r.V.appDef = satpVirtualRules) {net : NetworkState E P} (hinv : NetVOrigin r net)
    (caller : Participant) (op : Op E) :
    NetVOrigin r (net.applyAdv apps (.chain caller op)) := by
  cases h : net.chain.apply apps caller op
  · rw [NetworkState.applyAdv_chain_none apps h]; exact hinv
  rename_i s'
  rw [NetworkState.applyAdv_chain_some apps h]
  have hmono : ∀ ss : SignedState E,
      net.Holds ss → ({ net with chain := s', received := op.proofStates ++ net.received } :
        NetworkState E P).Holds ss := by
    intro ss hss
    refine NetworkState.Holds.of_subset (net := net) (fun s hs => hs) ?_ hss
    intro s hs
    exact List.mem_append_right op.proofStates hs
  constructor
  · intro u hu hune
    cases op with
    | deposit a e x =>
      obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
      obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hinv.1 u (by
        (simpa? [Adjudicator.statusOf_of_status hs] using hu says simpa only [Adjudicator.statusOf_of_status hs] using hu)) hune
      exact ⟨proof, cand, hsupp, hcand, fun ss hss => hmono ss (hheld ss hss)⟩
    | tick dt =>
      have hs' : net.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
      subst hs'
      obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hinv.1 u (by
        (simpa? [Adjudicator.tick_statusOf] using hu says simpa only [Adjudicator.tick_statusOf] using hu)) hune
      exact ⟨proof, cand, hsupp, hcand, fun ss hss => hmono ss (hheld ss hss)⟩
    | transfer a b =>
      by_cases hac : a = r.V
      · subst hac
        obtain ⟨o, w1, w2, w3, w4, w5, w6, w7, hs, w9, w10, w11⟩ := Adjudicator.transfer_some h
        have hu3 : s'.statusOf r.V =
            (net.chain.setStatus r.V ((net.chain.statusOf r.V).withOutcome
              (Outcome.allocation (o.reduceOwed b w2)))).statusOf r.V :=
          congrArg (fun A => (A.lookup r.V).getD (ChannelStatus.open 0)) hs
        rw [hu, Adjudicator.statusOf_setStatus, if_pos rfl] at hu3
        unfold ChannelStatus.withOutcome at hu3
        split at hu3 <;> cases hu3
      · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
        obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hinv.1 u (by
          (simpa? [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hac)] using hu says simpa only [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac)] using hu)) hune
        exact ⟨proof, cand, hsupp, hcand, fun ss hss => hmono ss (hheld ss hss)⟩
    | reclaim l v =>
      by_cases hlc : l = r.V
      · subst hlc
        obtain ⟨oL, oV, x, left, right, hL, hVfo, hg, hl, hr, hxeq, hsr, hlk, hvk⟩ :=
          Adjudicator.reclaim_some h
        have hu3 : s'.statusOf r.V = (net.chain.setStatus r.V ((net.chain.statusOf r.V).withOutcome
            (Outcome.allocation (((oL.addTo left (oV.amountAt 0)).addTo right
              (oV.amountAt 1)).remove v.address)))).statusOf r.V :=
          congrArg (fun A => A.statusOf r.V) hsr
        rw [hu, Adjudicator.statusOf_setStatus, if_pos rfl] at hu3
        unfold ChannelStatus.withOutcome at hu3
        split at hu3 <;> cases hu3
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
        obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hinv.1 u (by
          (simpa? [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)] using hu says simpa only [hsr, FixedPart.address_eq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)] using hu)) hune
        exact ⟨proof, cand, hsupp, hcand, fun ss hss => hmono ss (hheld ss hss)⟩
    | challenge c' proof0 cand0 =>
      by_cases hcc : c' = r.V
      · subst hcc
        -- `challenge` never results in `.open`.
        obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hu
        cases hu
      · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hinv.1 u (by
          (simpa? [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hu says simpa only [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hu)) hune
        exact ⟨proof, cand, hsupp, hcand, fun ss hss => hmono ss (hheld ss hss)⟩
    | checkpoint c' proof0 cand0 =>
      by_cases hcc : c' = r.V
      · subst hcc
        obtain ⟨⟨-, hs0, -, -⟩, rfl⟩ := Adjudicator.checkpoint_some h
        rw [hV] at hs0
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hu
        cases hu
        exact ⟨proof0, cand0, hs0, rfl, fun ss hss =>
          holds_of_mem_received (List.mem_append_left net.received hss)⟩
      · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hinv.1 u (by
          (simpa? [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hu says simpa only [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hu)) hune
        exact ⟨proof, cand, hsupp, hcand, fun ss hss => hmono ss (hheld ss hss)⟩
    | conclude c' ss0 =>
      by_cases hcc : c' = r.V
      · subst hcc
        obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hu
        cases hu
      · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
        obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hinv.1 u (by
          (simpa? [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hu says simpa only [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hu)) hune
        exact ⟨proof, cand, hsupp, hcand, fun ss hss => hmono ss (hheld ss hss)⟩
  · intro u ch hst
    cases op with
    | deposit a e x =>
      obtain ⟨-, -, -, -, hs, -⟩ := Adjudicator.deposit_some h
      obtain ⟨hturn, proof, hsupp, hheld⟩ := hinv.2 u ch (by
        (simpa? [Adjudicator.statusOf_of_status hs] using hst says simpa only [Adjudicator.statusOf_of_status hs] using hst))
      exact ⟨hturn, proof, hsupp, fun ss hss => hmono ss (hheld ss hss)⟩
    | tick dt =>
      have hs' : net.chain.tick dt = s' := by (simpa? using h says simpa only [Adjudicator.apply_tick, Option.some.injEq] using h)
      subst hs'
      obtain ⟨hturn, proof, hsupp, hheld⟩ := hinv.2 u ch (by
        (simpa? [Adjudicator.tick_statusOf] using hst says simpa only [Adjudicator.tick_statusOf] using hst))
      exact ⟨hturn, proof, hsupp, fun ss hss => hmono ss (hheld ss hss)⟩
    | transfer a b =>
      by_cases hac : a = r.V
      · subst hac
        obtain ⟨o, w1, w2, w3, w4, w5, w6, w7, hs, w9, w10, w11⟩ := Adjudicator.transfer_some h
        have hst3 : s'.statusOf r.V =
            (net.chain.setStatus r.V ((net.chain.statusOf r.V).withOutcome
              (Outcome.allocation (o.reduceOwed b w2)))).statusOf r.V :=
          congrArg (fun A => (A.lookup r.V).getD (ChannelStatus.open 0)) hs
        rw [hst, Adjudicator.statusOf_setStatus, if_pos rfl] at hst3
        unfold ChannelStatus.withOutcome at hst3
        split at hst3 <;> cases hst3
      · obtain ⟨_, _, _, _, _, _, _, _, hs, _, _, _⟩ := Adjudicator.transfer_some h
        obtain ⟨hturn, proof, hsupp, hheld⟩ := hinv.2 u ch (by
          (simpa? [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus,
            if_neg (Ne.symm hac)] using hst says simpa only [Adjudicator.statusOf_of_status hs, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hac)] using hst))
        exact ⟨hturn, proof, hsupp, fun ss hss => hmono ss (hheld ss hss)⟩
    | reclaim l v =>
      by_cases hlc : l = r.V
      · subst hlc
        obtain ⟨oL, oV, x, left, right, hL, hVfo, hg, hl, hr, hxeq, hsr, hlk, hvk⟩ :=
          Adjudicator.reclaim_some h
        have hst3 : s'.statusOf r.V = (net.chain.setStatus r.V ((net.chain.statusOf r.V).withOutcome
            (Outcome.allocation (((oL.addTo left (oV.amountAt 0)).addTo right
              (oV.amountAt 1)).remove v.address)))).statusOf r.V :=
          congrArg (fun A => A.statusOf r.V) hsr
        rw [hst, Adjudicator.statusOf_setStatus, if_pos rfl] at hst3
        unfold ChannelStatus.withOutcome at hst3
        split at hst3 <;> cases hst3
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsr, _, _⟩ := Adjudicator.reclaim_some h
        obtain ⟨hturn, proof, hsupp, hheld⟩ := hinv.2 u ch (by
          (simpa? [hsr, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)] using hst says simpa only [hsr, FixedPart.address_eq, Adjudicator.statusOf_setStatus, if_neg (Ne.symm hlc)] using hst))
        exact ⟨hturn, proof, hsupp, fun ss hss => hmono ss (hheld ss hss)⟩
    | challenge c' proof0 cand0 =>
      by_cases hcc : c' = r.V
      · subst hcc
        obtain ⟨⟨-, hs0, -, -⟩, rfl⟩ := Adjudicator.challenge_some h
        rw [hV] at hs0
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
        cases hst
        exact ⟨rfl, proof0, hs0, fun ss hss =>
          holds_of_mem_received (List.mem_append_left net.received hss)⟩
      · obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        obtain ⟨hturn, proof, hsupp, hheld⟩ := hinv.2 u ch (by
          (simpa? [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hst says simpa only [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hst))
        exact ⟨hturn, proof, hsupp, fun ss hss => hmono ss (hheld ss hss)⟩
    | checkpoint c' proof0 cand0 =>
      by_cases hcc : c' = r.V
      · subst hcc
        -- `checkpoint` never results in `.challenged`.
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
        cases hst
      · obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        obtain ⟨hturn, proof, hsupp, hheld⟩ := hinv.2 u ch (by
          (simpa? [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hst says simpa only [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hst))
        exact ⟨hturn, proof, hsupp, fun ss hss => hmono ss (hheld ss hss)⟩
    | conclude c' ss0 =>
      by_cases hcc : c' = r.V
      · subst hcc
        obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
        cases hst
      · obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
        obtain ⟨hturn, proof, hsupp, hheld⟩ := hinv.2 u ch (by
          (simpa? [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hst says simpa only [Adjudicator.statusOf_setStatus, if_neg (Ne.symm hcc)] using hst))
        exact ⟨hturn, proof, hsupp, fun ss hss => hmono ss (hheld ss hss)⟩

/-- `NetVOrigin` holds for every network state reachable from genesis through `Nitro.participant`
    (honest moves, `P`'s own landed calls, adversary moves, landed deposits): genesis is
    `.open 0`, trivial; an honest move (`.react`/`.wait`) never touches `r.V`'s status
    (`NetworkState.applyHonest`); a landed call or adversary move is `NetVOrigin_apply_step`;
    a landed deposit never touches any channel's status (`Adjudicator.statusOf_of_status`). -/
theorem NetVOrigin_reachable {apps : Apps E} {P : Participant} {T : Threat E P} {r : Route E}
    (hV : apps r.V.appDef = satpVirtualRules) {net : NetworkState E P}
    (h : (Nitro.participant apps T).Reachable net) :
    NetVOrigin r net := by
  refine Machine.invariant (Nitro.participant apps T) (P := fun net => NetVOrigin r net) ?_ ?_
    net h
  · intro net hinit
    rw [hinit]
    constructor
    · intro u hu hune
      exfalso
      have : (Adjudicator.genesis (E := E)).statusOf r.V = .open 0 := by
        unfold Adjudicator.statusOf Adjudicator.genesis
        (simp? says simp only [List.lookup_nil, Option.getD_none])
      rw [this] at hu
      cases hu
      exact hune rfl
    · intro u ch hst
      exfalso
      have : (Adjudicator.genesis (E := E)).statusOf r.V = .open 0 := by
        unfold Adjudicator.statusOf Adjudicator.genesis
        (simp? says simp only [List.lookup_nil, Option.getD_none])
      rw [this] at hst
      cases hst
  · intro net net' hP hstep
    rcases hstep with ⟨m, -, rfl⟩ | ⟨op, -, rfl⟩ | ⟨m, -, -, rfl⟩ | ⟨a, e, x, rfl⟩
    · -- honest move
      cases m with
      | react rr =>
        constructor
        · intro u hu hune
          obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hP.1 u (by
            (simpa? [NetworkState.applyHonest] using hu says simpa only [NetworkState.applyHonest] using hu)) hune
          exact ⟨proof, cand, hsupp, hcand, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by
              simp only [NetworkState.applyHonest]; exact List.mem_append_right _ hs)
              (fun s hs => by (simpa? [NetworkState.applyHonest] using hs says simpa only [NetworkState.applyHonest] using hs)) (hheld ss hss)⟩
        · intro u ch hst
          obtain ⟨hturn, proof, hsupp, hheld⟩ := hP.2 u ch (by
            (simpa? [NetworkState.applyHonest] using hst says simpa only [NetworkState.applyHonest] using hst))
          exact ⟨hturn, proof, hsupp, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by
              simp only [NetworkState.applyHonest]; exact List.mem_append_right _ hs)
              (fun s hs => by (simpa? [NetworkState.applyHonest] using hs says simpa only [NetworkState.applyHonest] using hs)) (hheld ss hss)⟩
      | wait dt =>
        constructor
        · intro u hu hune
          obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hP.1 u (by
            simp only [NetworkState.applyHonest] at hu
            rwa [Adjudicator.tick_statusOf] at hu) hune
          exact ⟨proof, cand, hsupp, hcand, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by (simpa? [NetworkState.applyHonest] using hs says simpa only [NetworkState.applyHonest] using hs))
              (fun s hs => by (simpa? [NetworkState.applyHonest] using hs says simpa only [NetworkState.applyHonest] using hs)) (hheld ss hss)⟩
        · intro u ch hst
          obtain ⟨hturn, proof, hsupp, hheld⟩ := hP.2 u ch (by
            simp only [NetworkState.applyHonest] at hst
            rwa [Adjudicator.tick_statusOf] at hst)
          exact ⟨hturn, proof, hsupp, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by (simpa? [NetworkState.applyHonest] using hs says simpa only [NetworkState.applyHonest] using hs))
              (fun s hs => by (simpa? [NetworkState.applyHonest] using hs says simpa only [NetworkState.applyHonest] using hs)) (hheld ss hss)⟩
    · -- `.land op`: `P`'s own call, the `.chain P op` step
      exact NetVOrigin_apply_step hV hP P op
    · -- adversary move
      cases m with
      | chain caller op => exact NetVOrigin_apply_step hV hP caller op
      | deliver ss' =>
        constructor
        · intro u hu hune
          obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hP.1 u (by
            simp only [NetworkState.applyAdv] at hu; exact hu) hune
          exact ⟨proof, cand, hsupp, hcand, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by simp only [NetworkState.applyAdv]; exact hs)
              (fun s hs => by
                simp only [NetworkState.applyAdv]
                exact List.mem_cons_of_mem _ hs) (hheld ss hss)⟩
        · intro u ch hst
          obtain ⟨hturn, proof, hsupp, hheld⟩ := hP.2 u ch (by
            simp only [NetworkState.applyAdv] at hst; exact hst)
          exact ⟨hturn, proof, hsupp, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by simp only [NetworkState.applyAdv]; exact hs)
              (fun s hs => by
                simp only [NetworkState.applyAdv]
                exact List.mem_cons_of_mem _ hs) (hheld ss hss)⟩
      | tick dt =>
        constructor
        · intro u hu hune
          obtain ⟨proof, cand, hsupp, hcand, hheld⟩ := hP.1 u (by
            simp only [NetworkState.applyAdv] at hu
            rwa [Adjudicator.tick_statusOf] at hu) hune
          exact ⟨proof, cand, hsupp, hcand, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs))
              (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs)) (hheld ss hss)⟩
        · intro u ch hst
          obtain ⟨hturn, proof, hsupp, hheld⟩ := hP.2 u ch (by
            simp only [NetworkState.applyAdv] at hst
            rwa [Adjudicator.tick_statusOf] at hst)
          exact ⟨hturn, proof, hsupp, fun ss hss =>
            NetworkState.Holds.of_subset (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs))
              (fun s hs => by (simpa? [NetworkState.applyAdv] using hs says simpa only [NetworkState.applyAdv] using hs)) (hheld ss hss)⟩
      | land op => exact NetVOrigin_apply_step hV hP P op
    · -- landed deposit, the `.chain P (.deposit a e x)` step
      exact NetVOrigin_apply_step hV hP P (Op.deposit a e x)


/-- Reachability of `p`'s network as a round invariant: a landing of one of `p`'s own
    calls that `p` can make (`Op.HonestFeasible`, which stays true as `Holds` grows), and
    every adversary move the threat allows, are steps of `Nitro.participant`. -/
theorem Threat.reachable_step {apps : Apps E} {p : Participant} {T : Threat E p} :
    T.CondStepInvariant apps (fun _ => True) (Nitro.participant apps T).Reachable
      (fun n op => op.HonestFeasible n) :=
  ⟨⟨fun _ hop hR => Machine.Reachable.tail hR (Or.inr (Or.inl ⟨_, hop, rfl⟩)),
    fun _ hfeas hR => Machine.Reachable.tail hR
      (Or.inr (Or.inr (Or.inl ⟨_, hfeas, (fun _ h => by cases h), rfl⟩))),
    fun _ hfeas hR => Machine.Reachable.tail hR
      (Or.inr (Or.inr (Or.inl ⟨_, hfeas, (fun _ h => by cases h), rfl⟩))),
    fun _ hfeas hR => Machine.Reachable.tail hR
      (Or.inr (Or.inr (Or.inl ⟨_, hfeas, (fun _ h => by cases h), rfl⟩)))⟩,
    fun m hop => Op.HonestFeasible.applyAdv m hop⟩

/-- One round of a feasible honest move, from a reachable state, ends in a reachable state
    (`Threat.RoundSeq.condInvariant` on `Threat.reachable_step`). -/
theorem Threat.Round.reachable {apps : Apps E} {p : Participant} {T : Threat E p}
    {m : HonestMove E} {net net' : NetworkState E p} (h : T.Round apps m net net')
    (hfeas : m.Feasible apps net) (hR : (Nitro.participant apps T).Reachable net) :
    (Nitro.participant apps T).Reachable net' :=
  h.1.condInvariant ⟨(Threat.reachable_step (T := T)).toStepInvariant.anyGuard,
    (Threat.reachable_step (T := T)).condMono⟩ (match m, hfeas with
      | .react _, hf => hf.1
      | .wait _, _ => fun _ hop => absurd hop (List.not_mem_nil)) hR

theorem UnbeatableIn.and_reachable {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G : NetworkState E p → Prop} :
    ∀ {net : NetworkState E p}, UnbeatableIn apps T allowed G net →
    (Nitro.participant apps T).Reachable net →
    UnbeatableIn apps T allowed (fun n => G n ∧ (Nitro.participant apps T).Reachable n) net := by
  intro net hU
  induction hU with
  | done hG => intro hR; exact UnbeatableIn.done ⟨hG, hR⟩
  | move m hal hfeas _ ih =>
    intro hR
    refine UnbeatableIn.move m hal hfeas fun net' hround => ?_
    have hR1 : (Nitro.participant apps T).Reachable net' := hround.reachable hfeas hR
    exact ih net' hround (Machine.Reachable.tail hR1
      (Or.inl ⟨m, HonestMove.Feasible.round hround.1 hfeas, rfl⟩))


/-- Whatever `r.V` is challenged with, at any reachable state, the challenged state's own
    outcome is a valid pair summing to the pre-fund total. `NetVOrigin`'s challenged clause
    gives a supported `(proof, ch.state)` pair that `P` holds; every received state of a
    reachable participant is unforged (`Nitro.participant_received_unforged`), which lifts
    `Holds` to `Unforged`, giving `satpVirtual_supported`'s own `hU` shape. -/
theorem satpVirtual_challenged_outcome_pair {P : Participant} {r : Route E}
    {alice bob : Participant} {apps : Apps E} {T : Threat E P}
    (hE : SatpVirtual apps T.ε r alice bob P) (hbounds : Bounds apps P T)
    {net : NetworkState E P} (hnr : (Nitro.participant apps T).Reachable net)
    (hVs : HoldsVirtualSetup net r alice bob true)
    {u : Nat} {ch : Challenge E} (hst : SatpChallenged r net u ch) :
    ∃ a b, PairOutcome (r.dest alice) (r.dest bob) ch.state.outcome a b ∧ a + b = r.a0 + r.b0 := by
  obtain ⟨-, proof, hsupp, hHP⟩ := (NetVOrigin_reachable hE.app hnr).2 u ch hst.status
  have hU : ∀ ss ∈ proof, P ∈ ss.signers → ∃ x ∈ net.sent, x.state = ss.state := fun ss hss hsig =>
    ((hHP ss hss).unforged (Nitro.participant_received_unforged hbounds ⟨net, hnr⟩)).1 hsig
  exact (satpVirtual_supported hE.toSatpEnds hVs ⟨proof, ch.state, hsupp⟩ hU).2


/-- The goal of the virtual-channel finalization sub-game: `r.V` finalizes
    with a pair outcome that keeps the pre-fund total. -/
def SatpVGoal {P : Participant} (r : Route E) (alice bob : Participant)
    (net' : NetworkState E P) : Prop :=
  ∃ Ω a b, net'.Finalized r.V Ω ∧ PairOutcome (r.dest alice) (r.dest bob) Ω a b ∧
    a + b = r.a0 + r.b0

/-- A `.wait (ch.deadline - net2.chain.now)` move resolves `r.V`: it finalizes with a
    challenged state's own outcome (a valid pair, via `satpVirtual_challenged_outcome_pair`),
    or it escalates to a fresh, strictly-higher-turn witness, handed to `hescalate`. No
    deadline margin is required (see `satp_wait_resolves_or_escalates`'s own docstring): the
    wait's own duration can be unboundedly long, and `satp_late_round_keeps_status_nil`'s
    restructured conclusion already accounts for a deadline passing mid-round. -/
theorem satp_virtual_wait_step {apps : Apps E} {P : Participant} {T : Threat E P}
    (A : Assumptions apps P T) {r : Route E} {alice bob : Participant}
    (hE : SatpVirtual apps T.ε r alice bob P) {net2 : NetworkState E P} {T0 : Nat}
    {ch : Challenge E} (hnr2 : (Nitro.participant apps T).Reachable net2)
    (hVs : HoldsVirtualSetup net2 r alice bob true)
    (hst : SatpChallenged r net2 T0 ch)
    (hescalate : ∀ {net' : NetworkState E P} {proof1 : SupportProof E} {cand1 : State E},
      (Nitro.participant apps T).Reachable net' → HoldsVirtualSetup net' r alice bob true →
      (∀ ss' ∈ proof1, net'.Holds ss') →
      (∀ ss' ∈ proof1, P ∈ ss'.signers → ∃ x ∈ net'.sent, x.state = ss'.state) →
      satpVirtualRules.supports r.V proof1 cand1 = true → T0 < cand1.turnNum →
      cand1.turnNum ≤ (net'.chain.statusOf r.V).turnNumRecord →
      net'.chain.finalizedWith r.V.address = none →
      Unbeatable apps T (SatpVGoal r alice bob) net') :
    Unbeatable apps T (SatpVGoal r alice bob) net2 := by
  refine UnbeatableIn.move (.wait (ch.deadline - net2.chain.now)) trivial trivial
    (fun net3 hround => ?_)
  have hdw : ch.deadline ≤ net2.chain.now + (ch.deadline - net2.chain.now) := by
    by_cases hle : net2.chain.now ≤ ch.deadline
    · exact le_of_eq (Nat.add_sub_cancel' hle).symm
    · push_neg at hle
      rw [Nat.sub_eq_zero_of_le (le_of_lt hle), Nat.add_zero]
      exact le_of_lt hle
  have hres := satp_wait_resolves_or_escalates A.toBounds hE hdw hVs hround hst
  simp only [NetworkState.applyHonest]
  rcases hres with hfin | ⟨proof1, cand1, hH1, hU1, hs1, hlt1, hprog1, hfin1⟩
  · apply UnbeatableIn.done
    obtain ⟨a, b, hpo, hab⟩ := satpVirtual_challenged_outcome_pair hE A.toBounds hnr2 hVs hst
    exact ⟨ch.state.outcome, a, b, hfin, hpo, hab⟩
  · have hVs3 : HoldsVirtualSetup net3 r alice bob true := by
      unfold HoldsVirtualSetup; rw [hround.1.sent_eq]; exact hVs
    have hnr3 : (Nitro.participant apps T).Reachable net3 :=
      hround.reachable trivial hnr2
    rcases hcs : net3.chain.statusOf r.V with u | ⟨u, ch'⟩ | ⟨u, f, o⟩
    · -- `.open`: `finalizedWith` stays `none` through any tick.
      have hnr3' : (Nitro.participant apps T).Reachable
          (net3.applyHonest (.wait (ch.deadline - net2.chain.now))) :=
        Machine.Reachable.tail hnr3
          (Or.inl ⟨.wait (ch.deadline - net2.chain.now), trivial, rfl⟩)
      have hfin1' : (net3.applyHonest
          (.wait (ch.deadline - net2.chain.now))).chain.finalizedWith r.V.address = none := by
        simp only [NetworkState.applyHonest, FixedPart.address_eq,
          Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, hcs,
          ChannelStatus.finalizedWith_open]
      exact hescalate hnr3' hVs3 hH1 hU1 hs1 hlt1 hprog1 hfin1'
    · -- `.challenged u ch'`: either the tick stays short of `ch'.deadline` (escalate as
      -- before), or it reaches it (finalizes with `ch'.state.outcome`, a valid pair by
      -- `satpVirtual_challenged_outcome_pair`).
      by_cases hexp : ch'.deadline ≤
          net3.chain.now + (ch.deadline - net2.chain.now)
      · apply UnbeatableIn.done
        obtain ⟨a, b, hpo, hab⟩ := satpVirtual_challenged_outcome_pair hE A.toBounds
          hnr3 hVs3 ⟨hcs⟩
        refine ⟨ch'.state.outcome, a, b, ?_, hpo, hab⟩
        show (net3.applyHonest (.wait (ch.deadline - net2.chain.now))).chain.finalizedWith
          r.V.address = some ch'.state.outcome
        simp only [NetworkState.applyHonest, FixedPart.address_eq,
          Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, Adjudicator.tick_now,
          hcs, ChannelStatus.finalizedWith_challenged, if_pos hexp]
      · have hnr3' : (Nitro.participant apps T).Reachable
            (net3.applyHonest (.wait (ch.deadline - net2.chain.now))) :=
          Machine.Reachable.tail hnr3
            (Or.inl ⟨.wait (ch.deadline - net2.chain.now), trivial, rfl⟩)
        have hfin1' : (net3.applyHonest
            (.wait (ch.deadline - net2.chain.now))).chain.finalizedWith r.V.address = none := by
          simp only [NetworkState.applyHonest, FixedPart.address_eq,
            Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, Adjudicator.tick_now,
            hcs, ChannelStatus.finalizedWith_challenged, if_neg hexp]
        exact hescalate hnr3' hVs3 hH1 hU1 hs1 hlt1 hprog1 hfin1'
    · -- `.finalized`: contradicts `hfin1` directly.
      exfalso
      rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hcs,
        ChannelStatus.finalizedWith_finalized] at hfin1
      exact absurd hfin1 (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))

/-- A `.open 0` genesis shape also needs its own witness: `NetVOrigin`'s `open` clause is
    gated by `u ≠ 0`, since nothing ever challenges a brand-new channel to confirm it holds
    its own genesis state. `hzero` supplies that one case; every recursive call after the
    first escalation discharges it vacuously, since `turnNumRecord` only strictly increases
    from there (`satp_land_keeps_status`'s own `cand0.turnNum < cand1.turnNum` in its
    `escalates` branch, and the strict bound built into its `fails` branch's own `mode`
    case split). The proof is a strong induction on the progress measure
    `3 - turnNumRecord` (`satpVirtual_supported` bounds the record by 3). `NetVOrigin` and
    the unforgeability of every received state follow from reachability
    (`NetVOrigin_reachable`, `Nitro.participant_received_unforged`). -/
theorem satp_virtual_finalize_aux {apps : Apps E} {P : Participant} {T : Threat E P}
    (A : Assumptions apps P T) {r : Route E}
    {alice bob : Participant} (hE : SatpVirtual apps T.ε r alice bob P) :
    ∀ {net : NetworkState E P},
      (Nitro.participant apps T).Reachable net →
      HoldsVirtualSetup net r alice bob true →
      (net.chain.statusOf r.V = .open 0 →
        ∃ proof0 cand0, satpVirtualRules.supports r.V proof0 cand0 = true ∧
          cand0.turnNum = 0 ∧ ∀ ss ∈ proof0, net.Holds ss) →
      SatpLive r net net.chain.now →
      Unbeatable apps T (SatpVGoal r alice bob) net := by
  have hbounds := A.toBounds
  suffices h : ∀ n : Nat, ∀ {net : NetworkState E P},
      (Nitro.participant apps T).Reachable net →
      HoldsVirtualSetup net r alice bob true →
      (net.chain.statusOf r.V = .open 0 →
        ∃ proof0 cand0, satpVirtualRules.supports r.V proof0 cand0 = true ∧
          cand0.turnNum = 0 ∧ ∀ ss ∈ proof0, net.Holds ss) →
      SatpLive r net net.chain.now →
      n = 3 - (net.chain.statusOf r.V).turnNumRecord →
      Unbeatable apps T (SatpVGoal r alice bob) net from
    fun {_} hnr hVs hzero hlive => h _ hnr hVs hzero hlive rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- `hBound3`: any currently-on-chain witness has turn ≤ 3; packages a fresh `NetVOrigin`
    -- extraction into a bound on `turnNumRecord` itself, not just the extracted witness's
    -- own candidate.
    have hBound3 : ∀ {net'' : NetworkState E P},
        (Nitro.participant apps T).Reachable net'' → HoldsVirtualSetup net'' r alice bob true →
        SatpLive r net'' net''.chain.now →
        (net''.chain.statusOf r.V).turnNumRecord ≤ 3 := by
      intro net'' hnr'' hVs'' hlive''
      have hNo'' := NetVOrigin_reachable hE.app hnr''
      have hUnf'' : ∀ ss ∈ net''.received, net''.Unforged ss :=
        Nitro.participant_received_unforged hbounds ⟨net'', hnr''⟩
      rcases hcs : net''.chain.statusOf r.V with u | ⟨u, ch⟩ | ⟨u, f, o⟩
      · by_cases hu0 : u = 0
        · simp only [ChannelStatus.turnNumRecord, hu0]; omega
        · obtain ⟨proof0, cand0, hsupp0, hcand0, hHeld0⟩ := hNo''.1 u hcs hu0
          have hU0 : ∀ ss ∈ proof0, P ∈ ss.signers → ∃ x ∈ net''.sent, x.state = ss.state :=
            fun ss hss hsig => ((hHeld0 ss hss).unforged hUnf'').1 hsig
          have h3 : cand0.turnNum ≤ 3 :=
            (satpVirtual_supported hE.toSatpEnds hVs'' ⟨proof0, cand0, hsupp0⟩ hU0).1
          simp only [ChannelStatus.turnNumRecord]; omega
      · obtain ⟨hturn, proof0, hsupp0, hHeld0⟩ := hNo''.2 u ch hcs
        have hU0 : ∀ ss ∈ proof0, P ∈ ss.signers → ∃ x ∈ net''.sent, x.state = ss.state :=
          fun ss hss hsig => ((hHeld0 ss hss).unforged hUnf'').1 hsig
        have h3 : ch.state.turnNum ≤ 3 :=
          (satpVirtual_supported hE.toSatpEnds hVs'' ⟨proof0, ch.state, hsupp0⟩ hU0).1
        simp only [ChannelStatus.turnNumRecord]; omega
      · exfalso
        rcases hlive'' with ⟨u3, hu3⟩ | ⟨u3, ch3, hu3, -⟩ <;> rw [hcs] at hu3 <;> cases hu3
    -- `hChallenged`: from any reachable `net''` where `r.V` is challenged, within the measure,
    -- finish from there (`satp_virtual_wait_step`).
    have hChallenged : ∀ {net'' : NetworkState E P} {T0 : Nat} {ch : Challenge E},
        (Nitro.participant apps T).Reachable net'' → HoldsVirtualSetup net'' r alice bob true →
        3 - (net''.chain.statusOf r.V).turnNumRecord ≤ n →
        net''.chain.statusOf r.V = .challenged T0 ch →
        Unbeatable apps T (SatpVGoal r alice bob) net'' := by
      intro net'' T0 ch hnr'' hVs'' hle'' hst
      refine satp_virtual_wait_step A hE hnr'' hVs'' ⟨hst⟩ ?_
      intro net' proof1 cand1 hnr' hVs' hH1 hU1 hs1 hlt1 hprog1 hfin1
      have hlive' : SatpLive r net' net'.chain.now := by
        rcases hcs' : net'.chain.statusOf r.V with u' | ⟨u', ch'⟩ | ⟨u', f', o'⟩
        · exact Or.inl ⟨u', hcs'⟩
        · refine Or.inr ⟨u', ch', hcs', ?_⟩
          by_contra hge
          push_neg at hge
          rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hcs',
            ChannelStatus.finalizedWith_challenged, if_pos hge] at hfin1
          cases hfin1
        · exfalso
          rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hcs',
            ChannelStatus.finalizedWith_finalized] at hfin1
          exact absurd hfin1 (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
      have hzero' : net'.chain.statusOf r.V = .open 0 →
          ∃ proof0 cand0, satpVirtualRules.supports r.V proof0 cand0 = true ∧
            cand0.turnNum = 0 ∧ ∀ ss ∈ proof0, net'.Holds ss := by
        intro h0
        exfalso
        rw [h0] at hprog1
        simp only [ChannelStatus.turnNumRecord] at hprog1
        omega
      have hbound3' := hBound3 hnr' hVs' hlive'
      have hn0 : (net''.chain.statusOf r.V).turnNumRecord = T0 := by rw [hst]; rfl
      exact ih (3 - (net'.chain.statusOf r.V).turnNumRecord) (by omega) hnr' hVs' hzero'
        hlive' rfl
    intro net hnr hVs hzero hlive hn
    have hNo := NetVOrigin_reachable hE.app hnr
    have hUnf : ∀ ss ∈ net.received, net.Unforged ss :=
      Nitro.participant_received_unforged hbounds ⟨net, hnr⟩
    rcases hlive with ⟨u, hu⟩ | ⟨u, ch, hu, hdd⟩
    · -- OPEN u: get a matching witness, submit it.
      obtain ⟨proof0, cand0, hsupp0, hcand0, hHeld0⟩ :
          ∃ proof0 cand0, satpVirtualRules.supports r.V proof0 cand0 = true ∧
            cand0.turnNum = u ∧ ∀ ss ∈ proof0, net.Holds ss := by
        by_cases hu0 : u = 0
        · subst hu0; exact hzero hu
        · exact hNo.1 u hu hu0
      have hU0 : ∀ ss ∈ proof0, P ∈ ss.signers → ∃ x ∈ net.sent, x.state = ss.state :=
        fun ss hss hsig => ((hHeld0 ss hss).unforged hUnf).1 hsig
      have hfeasR : Reaction.Feasible net ⟨[Op.challenge r.V proof0 cand0], []⟩ := by
        intro op hop
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        subst hop
        (simpa? [Op.HonestFeasible, Op.proofStates] using hHeld0 says simpa only [Op.HonestFeasible, Op.proofStates] using hHeld0)
      have hfeasM : (HonestMove.react ⟨[Op.challenge r.V proof0 cand0], []⟩ : HonestMove E).Feasible
          apps net :=
        ⟨hfeasR, fun _ h => absurd h List.not_mem_nil⟩
      refine UnbeatableIn.move (.react ⟨[Op.challenge r.V proof0 cand0], []⟩) trivial hfeasM ?_
      intro net1 hround
      obtain ⟨hseq, hεbound⟩ := hround
      have hnet1 : net1.applyHonest (.react ⟨[Op.challenge r.V proof0 cand0], []⟩) = net1 := by
        (simp? [NetworkState.applyHonest] says simp only [NetworkState.applyHonest, List.map_nil, List.nil_append])
      rw [hnet1]
      have hres := satp_land_keeps_status hbounds hE ⟨proof0, cand0, hsupp0⟩ ⟨hseq,
        hεbound⟩ hVs hHeld0 (Or.inl ⟨u, hu⟩)
      dsimp only at hres
      have hnr1 : (Nitro.participant apps T).Reachable net1 :=
        Threat.Round.reachable ⟨hseq, hεbound⟩ hfeasM hnr
      have hVs1 : HoldsVirtualSetup net1 r alice bob true := by
        unfold HoldsVirtualSetup; rw [hseq.sent_eq]; exact hVs
      rcases hres with ⟨ch1, hst1, -, -⟩ |
          ⟨proof1, cand1, hH1, hU1, hs1, hlt1, hprog1, hfin1⟩ |
          ((⟨hstrict0, hlive0'⟩ | hSCA0) | hFin0)
      · -- lands: dispatch via `hChallenged`.
        have hn0 : (net.chain.statusOf r.V).turnNumRecord = u := by rw [hu]; rfl
        have hle1 : 3 - (net1.chain.statusOf r.V).turnNumRecord ≤ n := by
          rw [hst1]; simp only [ChannelStatus.turnNumRecord]; omega
        exact hChallenged hnr1 hVs1 hle1 hst1
      · -- escalates: recurse with the fresh `(proof1, cand1)`.
        have hlive1 : SatpLive r net1 net1.chain.now := by
          rcases hcs1 : net1.chain.statusOf r.V with u1 | ⟨u1, ch1⟩ | ⟨u1, f1, o1⟩
          · exact Or.inl ⟨u1, hcs1⟩
          · refine Or.inr ⟨u1, ch1, hcs1, ?_⟩
            by_contra hge
            push_neg at hge
            rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hcs1,
              ChannelStatus.finalizedWith_challenged, if_pos hge] at hfin1
            cases hfin1
          · exfalso
            rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hcs1,
              ChannelStatus.finalizedWith_finalized] at hfin1
            exact absurd hfin1 (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))
        have hzero1 : net1.chain.statusOf r.V = .open 0 →
            ∃ proof0' cand0', satpVirtualRules.supports r.V proof0' cand0' = true ∧
              cand0'.turnNum = 0 ∧ ∀ ss ∈ proof0', net1.Holds ss := by
          intro h0
          exfalso
          rw [h0] at hprog1
          simp only [ChannelStatus.turnNumRecord] at hprog1
          omega
        have hbound3_1 := hBound3 hnr1 hVs1 hlive1
        have hn0 : (net.chain.statusOf r.V).turnNumRecord = u := by rw [hu]; rfl
        exact ih (3 - (net1.chain.statusOf r.V).turnNumRecord) (by omega) hnr1 hVs1 hzero1
          hlive1 rfl
      · -- fails, strict: `net1`'s own progress is already strict past `cand0.turnNum`,
        -- regardless of its resulting shape -- recurse exactly like `escalates`.
        have hzero1 : net1.chain.statusOf r.V = .open 0 →
            ∃ proof0' cand0', satpVirtualRules.supports r.V proof0' cand0' = true ∧
              cand0'.turnNum = 0 ∧ ∀ ss ∈ proof0', net1.Holds ss := by
          intro h0
          exfalso
          rw [h0] at hstrict0
          simp only [ChannelStatus.turnNumRecord] at hstrict0
          omega
        have hbound3_1 := hBound3 hnr1 hVs1 hlive0'
        have hn0 : (net.chain.statusOf r.V).turnNumRecord = u := by rw [hu]; rfl
        exact ih (3 - (net1.chain.statusOf r.V).turnNumRecord) (by omega) hnr1 hVs1 hzero1
          hlive0' rfl
      · -- fails, stays challenged: dispatch `hChallenged` directly at `net1`, same measure
        -- (`SatpChallengedAbove`'s own `cand0.turnNum ≤ u'` gives `3 - turnNumRecord(net1) ≤
        -- n`, no decrease needed). No margin needed any more (gap 2's fix moved the deadline
        -- handling into `satp_late_round_keeps_status_nil` itself).
        obtain ⟨u', ch', hst1', hle1', -⟩ := hSCA0
        have hn0 : (net.chain.statusOf r.V).turnNumRecord = u := by rw [hu]; rfl
        have hn1 : (net1.chain.statusOf r.V).turnNumRecord = u' := by rw [hst1']; rfl
        have hle1 : 3 - (net1.chain.statusOf r.V).turnNumRecord ≤ n := by omega
        exact hChallenged hnr1 hVs1 hle1 hst1'
      · -- already finalized: `r.V` is already done with `cand0`'s own outcome -- `UnbeatableIn.
        -- done` directly, mirroring `satp_virtual_wait_step`'s own `hfin` handling.
        apply UnbeatableIn.done
        have hU0' : ∀ ss ∈ proof0, P ∈ ss.signers → ∃ x ∈ net1.sent, x.state = ss.state := by
          rw [hseq.sent_eq]; exact hU0
        obtain ⟨a, b, hpo, hab⟩ := (satpVirtual_supported hE.toSatpEnds hVs1 ⟨proof0, cand0, hsupp0⟩ hU0').2
        exact ⟨cand0.outcome, a, b, hFin0, hpo, hab⟩
    · -- CHALLENGED u ch: dispatch directly via `hChallenged`. No margin needed any more
      -- (gap 2's fix moved the deadline handling into `satp_late_round_keeps_status_nil`).
      exact hChallenged hnr hVs (le_of_eq hn.symm) hu


/-- SATP-15, SATP-20 (Protocol 3.3 step 3, SATP:484-485; SATP:550-553). After
    both ledgers and `V` are finalized, one reclaim on each ledger credits
    `Pi` with `a` in `L_{i-1}` and `b` in `L_i`: "implying Pi's balance
    increases by a + b = a0 + b0 across both Li and Li−1." go-nitro
    `compute_reclaim_effects` needs the peers' entries present and
    `a + b = a0 + b0`; both hold after Protocol 3.1 Round 2 (SATP:411-418). -/
theorem satp_reclaim_credits_intermediary (s : Adjudicator E) (r : Route E)
    (alice bob P Pprev Pnext : Participant)
    (Lm Lp : FixedPart) (om op : Allocation E) (a b : Coins)
    (hdist : r.dest P ≠ r.dest Pprev ∧ r.dest P ≠ r.dest Pnext ∧ r.dest Pprev ≠ r.dest Pnext)
    (hkLm : Lm.kind = .ledger) (hkLp : Lp.kind = .ledger) (hkV : r.V.kind = .virtual)
    (hV : s.finalizedWith r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]))
    (hLm : s.finalOutcome Lm.address = some (.allocation om))
    (hLp : s.finalOutcome Lp.address = some (.allocation op))
    (hgm : om.find r.V.address = some (r.guarantee Pprev P))
    (hgp : op.find r.V.address = some (r.guarantee P Pnext)) (hne : Lm ≠ Lp)
    (hem : om.find (.external (r.dest Pprev)) ≠ none ∧ om.find (.external (r.dest P)) ≠ none)
    (hep : op.find (.external (r.dest P)) ≠ none ∧ op.find (.external (r.dest Pnext)) ≠ none)
    (hab : a + b = r.a0 + r.b0) :
    ∃ s1 s2 om' op', s.reclaim Lm r.V = some s1 ∧ s1.reclaim Lp r.V = some s2 ∧
      s2.finalOutcome Lm.address = some (.allocation om') ∧
      s2.finalOutcome Lp.address = some (.allocation op') ∧
      om'.owed (.external (r.dest P)) = om.owed (.external (r.dest P)) + b ∧
      op'.owed (.external (r.dest P)) = op.owed (.external (r.dest P)) + a ∧
      om'.find r.V.address = none ∧ op'.find r.V.address = none := by
  obtain ⟨h1, h2, h3⟩ := hdist
  set dP : Address E := .external (r.dest P)
  set dPp : Address E := .external (r.dest Pprev)
  set dPn : Address E := .external (r.dest Pnext)
  set oV : Allocation E := [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]
  have hVa : oV.amountAt 0 = a := rfl
  have hVb : oV.amountAt 1 = b := rfl
  have hx : oV.amountAt 0 + oV.amountAt 1 = r.a0 + r.b0 := hab
  have hext : ∀ e : E, (Address.external e : Address E) ≠ r.V.address := by (simp? says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true, implies_true])
  -- `Lm ≠ V` and `Lp ≠ V`: a ledger channel is never a virtual one.
  have hmV : Lm ≠ r.V := by rintro rfl; rw [hkV] at hkLm; cases hkLm
  have hpV : Lp ≠ r.V := by rintro rfl; rw [hkV] at hkLp; cases hkLp
  let om' := ((om.addTo dPp (oV.amountAt 0)).addTo dP (oV.amountAt 1)).remove r.V.address
  let op' := ((op.addTo dP (oV.amountAt 0)).addTo dPn (oV.amountAt 1)).remove r.V.address
  have hr1 := reclaim_can_happen s Lm r.V om oV (r.a0 + r.b0) dPp dP hkLm hkV hLm hV hgm
    (by rw [Allocation.find_remove, if_neg (hext _)]; exact hem.1)
    (by rw [Allocation.find_remove, if_neg (hext _)]; exact hem.2) hx
  set s1 := s.setStatus Lm ((s.statusOf Lm).withOutcome (.allocation om'))
  have hV1 : s1.finalizedWith r.V.address = some (.allocation oV) := by
    simpa [s1, Ne.symm hmV] using hV
  have hLp1 : s1.finalOutcome Lp.address = some (.allocation op) := by
    simpa [s1, Ne.symm hne] using hLp
  have hr2 := reclaim_can_happen s1 Lp r.V op oV (r.a0 + r.b0) dP dPn hkLp hkV hLp1 hV1 hgp
    (by rw [Allocation.find_remove, if_neg (hext _)]; exact hep.1)
    (by rw [Allocation.find_remove, if_neg (hext _)]; exact hep.2) hx
  refine ⟨s1, _, om', op', hr1, hr2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · (simp? [s1, hne] says simp only [Adjudicator.statusOf_setStatus, FixedPart.address_eq, Adjudicator.finalOutcome_channel, hne, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_withOutcome, s1])
  · (simp? says simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, Adjudicator.statusOf_setStatus, ↓reduceIte, Adjudicator.setStatus_now, ChannelStatus.finalOutcome_withOutcome, Option.some.injEq, Outcome.allocation.injEq]); rfl
  · rw [Allocation.owed_remove_of_ne _ (hext _), Allocation.owed_addTo_self _ ?_,
      Allocation.owed_addTo_of_ne _ _ (by (simpa? [dP, dPp] using h1 says simpa only [ne_eq, Address.external.injEq, dP, dPp] using h1)), hVb]
    rw [Allocation.find_addTo_of_ne _ _ (by (simpa? [dP, dPp] using h1 says simpa only [ne_eq, Address.external.injEq, dP, dPp] using h1))]; exact hem.2
  · rw [Allocation.owed_remove_of_ne _ (hext _), Allocation.owed_addTo_of_ne _ _
      (by (simpa? [dP, dPn] using h2 says simpa only [ne_eq, Address.external.injEq, dPn] using h2)), Allocation.owed_addTo_self _ hep.1, hVa]
  · rw [Allocation.find_remove, if_pos rfl]
  · rw [Allocation.find_remove, if_pos rfl]

omit [DecidableEq E] in
/-- A status that is not `.finalized` with a payout already applied has the
    same stored outcome as its outcome of finalization. -/
theorem ChannelStatus.finalOutcome_eq_finalizedWith (st : ChannelStatus E) (now : Time)
    (h : ∀ t f o, st = .finalized t f o → f = o) : st.finalOutcome now = st.finalizedWith now := by
  cases st with
  | «open» t => rfl
  | challenged t ch => rfl
  | finalized t f o => (simp? [h t f o rfl] says simp only [h t f o rfl, finalOutcome_finalized, finalizedWith_finalized])

/-- One on-chain step keeps a finalized ledger channel `L` finalized with an
    allocation that has no entry for `V`. The owed amount of `.external d` in
    `L`'s stored outcome does not fall, except when the step is a `transfer`
    out of `L`. Such a transfer moves coins from `L` to the destination in
    lockstep, so the owed amount plus the balance of `.external d` does not
    fall. `transfer` cannot target `V`: it needs an `.alloc` entry for its
    target (`Adjudicator.transfer_some`). `reclaim` only raises entries that
    are already present (`Allocation.owed_addTo_ge`). `challenge`,
    `checkpoint` and `conclude` need `L` not finalized. Used by
    `ledger_credit_step`. -/
theorem ledger_claim_step {apps : Apps E} {caller : Participant} {op : Op E} {s s' : Adjudicator E}
    (h : s.apply apps caller op = some s') (L : FixedPart) (V : Address E) (d : E)
    (o : Allocation E) (ho : s.finalOutcome L.address = some (.allocation o))
    (hoV : o.find V = none) :
    ∃ o', s'.finalOutcome L.address = some (.allocation o') ∧ o'.find V = none ∧
      (o.owed (.external d) ≤ o'.owed (.external d) ∨ ∃ b, op = .transfer L b) ∧
      o.owed (.external d) + s.balances.get (.external d) ≤
        o'.owed (.external d) + s'.balances.get (.external d) := by
  have hbal : s.balances.get (.external d) ≤ s'.balances.get (.external d) :=
    paid_out_monotone apps s s' (Step.mk caller op s s' h) d
  suffices hs : ∃ o', s'.finalOutcome L.address = some (.allocation o') ∧ o'.find V = none ∧
      (o.owed (.external d) ≤ o'.owed (.external d) ∨ ∃ b, op = .transfer L b ∧
        o.owed (.external d) + s.balances.get (.external d) ≤
          o'.owed (.external d) + s'.balances.get (.external d)) by
    obtain ⟨o', ho', hoV', hle | ⟨b, hb, hsum⟩⟩ := hs
    · exact ⟨o', ho', hoV', Or.inl hle, Nat.add_le_add hle hbal⟩
    · exact ⟨o', ho', hoV', Or.inr ⟨b, hb⟩, hsum⟩
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at ho ⊢
  have hmode : (s.statusOf L).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, ho]; rfl
  have keep : s'.statusOf L = s.statusOf L → s.now ≤ s'.now →
      ∃ o', (s'.statusOf L).finalOutcome s'.now = some (.allocation o') ∧ o'.find V = none ∧
        (o.owed (.external d) ≤ o'.owed (.external d) ∨ ∃ b, op = .transfer L b ∧
          o.owed (.external d) + s.balances.get (.external d) ≤
            o'.owed (.external d) + s'.balances.get (.external d)) := by
    intro hst hn
    exact ⟨o, by rw [hst]; exact ChannelStatus.finalOutcome_mono ho hn, hoV, Or.inl (le_refl _)⟩
  have hn := Adjudicator.apply_now_le h
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hstatus, -⟩ := Adjudicator.deposit_some h
    exact keep (Adjudicator.statusOf_of_status hstatus L) hn
  | tick dt =>
    simp only [Adjudicator.apply_tick, Option.some.injEq] at h
    subst h
    exact keep (Adjudicator.tick_statusOf s dt L) hn
  | transfer a b =>
    obtain ⟨o1, amt, x, hfo, hfind, hx, hbal', -, hstatus, hnow, -, -⟩ := Adjudicator.transfer_some h
    by_cases hac : L = a
    · subst hac
      rw [Adjudicator.statusOf_of_status hstatus, Adjudicator.statusOf_setStatus, if_pos rfl,
        ChannelStatus.finalOutcome_withOutcome]
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
        Option.some.injEq, Outcome.allocation.injEq] at hfo
      subst hfo
      have hbne : b ≠ V := fun hbV => by rw [hbV, hoV] at hfind; cases hfind
      refine ⟨o.reduceOwed b x, rfl, ?_, Or.inr ⟨b, rfl, ?_⟩⟩
      · rw [Allocation.find_reduceOwed, if_neg (Ne.symm hbne)]; exact hoV
      · have hxle : x ≤ o.owed b := hx ▸ paidTo_first_entry_only _ o b
        have haddr : (Address.external d : Address E) ≠ L.address := by (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])
        rw [hbal', Allocation.owed_reduceOwed, Balances.get_sub, if_neg haddr, Balances.get_add]
        by_cases hbd : (Address.external d : Address E) = b
        · rw [if_pos hbd, if_pos hbd, hbd]; unfold Coins at *; omega
        · rw [if_neg hbd, if_neg hbd]
    · exact keep (by rw [Adjudicator.statusOf_of_status hstatus, Adjudicator.statusOf_setStatus,
        if_neg hac]) hn
  | reclaim l v =>
    obtain ⟨oL, oV, x, left, right, hfo, -, hgfind, hleftfind, hrightfind, -, hs', -, -⟩ :=
      Adjudicator.reclaim_some h
    subst hs'
    by_cases hlc : L = l
    · subst hlc
      rw [Adjudicator.statusOf_setStatus, Adjudicator.setStatus_now, if_pos rfl,
        ChannelStatus.finalOutcome_withOutcome]
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, ho,
        Option.some.injEq, Outcome.allocation.injEq] at hfo
      subst hfo
      have hvV : v.address ≠ V := fun hveq => by rw [hveq, hoV] at hgfind; cases hgfind
      have hleftV : left ≠ V := by
        intro hleq
        rw [hleq, Allocation.find_remove, if_neg (Ne.symm hvV), hoV] at hleftfind
        exact hleftfind rfl
      have hrightV : right ≠ V := by
        intro hreq
        rw [hreq, Allocation.find_remove, if_neg (Ne.symm hvV), hoV] at hrightfind
        exact hrightfind rfl
      refine ⟨((o.addTo left (oV.amountAt 0)).addTo right (oV.amountAt 1)).remove v.address, rfl,
        ?_, Or.inl ?_⟩
      · rw [Allocation.find_remove, if_neg (Ne.symm hvV),
          Allocation.find_addTo_of_ne _ _ (Ne.symm hrightV),
          Allocation.find_addTo_of_ne _ _ (Ne.symm hleftV)]
        exact hoV
      · have hdne : (Address.external d : Address E) ≠ v.address := by (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])
        rw [Allocation.owed_remove_of_ne _ hdne]
        exact le_trans (Allocation.owed_addTo_ge o left _ _)
          (Allocation.owed_addTo_ge _ right _ _)
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hlc]) hn
  | challenge c proof cand =>
    obtain ⟨⟨-, -, -, hmd⟩, hs'⟩ := Adjudicator.challenge_some h
    subst hs'
    by_cases hcc : L = c
    · exfalso
      subst hcc
      rw [Adjudicator.mode_eq] at hmd
      rcases hmd with ⟨hmo, -⟩ | ⟨hmo, -⟩ <;> rw [hmode] at hmo <;> cases hmo
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc]) hn
  | checkpoint c proof cand =>
    obtain ⟨⟨hopen, -, -, -⟩, hs'⟩ := Adjudicator.checkpoint_some h
    subst hs'
    by_cases hcc : L = c
    · exfalso
      subst hcc
      exact hopen hmode
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc]) hn
  | conclude c ss =>
    obtain ⟨⟨hopen, -⟩, hs'⟩ := Adjudicator.conclude_some h
    subst hs'
    by_cases hcc : L = c
    · exfalso
      subst hcc
      exact hopen hmode
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc]) hn

/-- A step that finalizes `L` for the first time stores the outcome of
    finalization unchanged: the new status is `.challenged` (a deadline
    passes, or a challenge with a zero duration) or `.finalized` by
    `conclude` with equal fields. `transfer` and `reclaim` need `L` already
    finalized. Used by `ledger_credit_step`. -/
theorem finalOutcome_of_fresh_finalizedWith {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') (L : FixedPart)
    {f : Outcome E} (hnone : s.finalizedWith L.address = none)
    (hf : s'.finalizedWith L.address = some f) : s'.finalOutcome L.address = some f := by
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
    Adjudicator.finalizedWith_channel] at hnone hf ⊢
  have hnotfin : ∀ t f o, s.statusOf L = .finalized t f o → f = o := by
    intro t f o hst; rw [hst] at hnone; cases hnone
  have hfo : (s.statusOf L).finalOutcome s.now = none := by
    cases hst : s.statusOf L with
    | «open» t => rfl
    | challenged t ch => rw [hst] at hnone; exact hnone
    | finalized t f o => rw [hst] at hnone; cases hnone
  suffices hs : ∀ t f o, s'.statusOf L = .finalized t f o → f = o by
    rw [ChannelStatus.finalOutcome_eq_finalizedWith _ _ hs]; exact hf
  have same : s'.statusOf L = s.statusOf L → ∀ t f o, s'.statusOf L = .finalized t f o → f = o := by
    intro hst; rw [hst]; exact hnotfin
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hstatus, -⟩ := Adjudicator.deposit_some h
    exact same (Adjudicator.statusOf_of_status hstatus L)
  | tick dt =>
    simp only [Adjudicator.apply_tick, Option.some.injEq] at h
    subst h
    exact same (Adjudicator.tick_statusOf s dt L)
  | transfer a b =>
    obtain ⟨o1, _amt, _x, hfo1, _, _, _, _, hstatus, _, _, _⟩ := Adjudicator.transfer_some h
    by_cases hac : L = a
    · subst hac
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hfo] at hfo1
      cases hfo1
    · exact same (by rw [Adjudicator.statusOf_of_status hstatus, Adjudicator.statusOf_setStatus,
        if_neg hac])
  | reclaim l v =>
    obtain ⟨oL, _oV, _x, _l, _r, hfo1, _, _, _, _, _, hs', _, _⟩ := Adjudicator.reclaim_some h
    by_cases hlc : L = l
    · subst hlc
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel, hfo] at hfo1
      cases hfo1
    · exact same (by rw [hs', Adjudicator.statusOf_setStatus, if_neg hlc])
  | challenge c proof cand =>
    obtain ⟨-, hs'⟩ := Adjudicator.challenge_some h
    subst hs'
    by_cases hcc : L = c
    · intro t f o hst
      rw [Adjudicator.statusOf_setStatus, if_pos hcc] at hst
      cases hst
    · exact same (by rw [Adjudicator.statusOf_setStatus, if_neg hcc])
  | checkpoint c proof cand =>
    obtain ⟨-, hs'⟩ := Adjudicator.checkpoint_some h
    subst hs'
    by_cases hcc : L = c
    · intro t f o hst
      rw [Adjudicator.statusOf_setStatus, if_pos hcc] at hst
      cases hst
    · exact same (by rw [Adjudicator.statusOf_setStatus, if_neg hcc])
  | conclude c ss =>
    obtain ⟨-, hs'⟩ := Adjudicator.conclude_some h
    subst hs'
    by_cases hcc : L = c
    · intro t f o hst
      rw [Adjudicator.statusOf_setStatus, if_pos hcc] at hst
      cases hst
      rfl
    · exact same (by rw [Adjudicator.statusOf_setStatus, if_neg hcc])

/-- What a ledger channel `L` owes `a`, counted toward `IntermediaryRecovered`:
    once `L` finalized with its latest allocation `oL`, the owed amount in
    the stored outcome (a payout lowers it, `ledger_claim_step`); before
    that, the owed amount in `oL` itself. -/
def ledgerCredit (s : Adjudicator E) (L : FixedPart) (oL : Allocation E) (a : Address E) : Coins :=
  if s.finalizedWith L.address = some (.allocation oL) then
    ((s.finalOutcome L.address).map (fun Ω => Ω.entries.owed a)).getD 0
  else oL.owed a

/-- One on-chain step and the credit of one ledger channel `L` whose latest
    allocation `oL` has no entry for `V`. If `L` was finalized with `oL`, the
    step keeps a stored outcome with no entry for `V` (`ledger_claim_step`).
    If the step finalizes `L` with `oL`, the stored outcome is `oL`
    (`finalOutcome_of_fresh_finalizedWith`), so the credit does not change.
    The credit falls only under a `transfer` out of `L`, and then the
    balance of `.external d` rises by at least the same amount. Used by
    `LedgerPairInv.step`. -/
theorem ledger_credit_step {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') (L : FixedPart) (V : Address E)
    (d : E) (oL : Allocation E) (hoLV : oL.find V = none)
    (hinv : s.finalizedWith L.address = some (.allocation oL) →
      ∃ o, s.finalOutcome L.address = some (.allocation o) ∧ o.find V = none) :
    (s'.finalizedWith L.address = some (.allocation oL) →
      ∃ o, s'.finalOutcome L.address = some (.allocation o) ∧ o.find V = none) ∧
    (ledgerCredit s L oL (.external d) ≤ ledgerCredit s' L oL (.external d) ∨
      ∃ b, op = .transfer L b) ∧
    ledgerCredit s L oL (.external d) + s.balances.get (.external d) ≤
      ledgerCredit s' L oL (.external d) + s'.balances.get (.external d) := by
  have hbal : s.balances.get (.external d) ≤ s'.balances.get (.external d) :=
    paid_out_monotone apps s s' (Step.mk caller op s s' h) d
  by_cases hf : s.finalizedWith L.address = some (.allocation oL)
  · obtain ⟨o, ho, hoV⟩ := hinv hf
    have hf' := Adjudicator.finalizedWith_apply h hf
    obtain ⟨o', ho', hoV', hle, hsum⟩ := ledger_claim_step h L V d o ho hoV
    have hc : ledgerCredit s L oL (.external d) = o.owed (.external d) := by
      unfold ledgerCredit; rw [if_pos hf, ho]; rfl
    have hc' : ledgerCredit s' L oL (.external d) = o'.owed (.external d) := by
      unfold ledgerCredit; rw [if_pos hf', ho']; rfl
    rw [hc, hc']
    exact ⟨fun _ => ⟨o', ho', hoV'⟩, hle, hsum⟩
  · have hc : ledgerCredit s L oL (.external d) = oL.owed (.external d) := by
      unfold ledgerCredit; rw [if_neg hf]
    by_cases hf' : s'.finalizedWith L.address = some (.allocation oL)
    · have hnone : s.finalizedWith L.address = none := by
        cases hfs : s.finalizedWith L.address with
        | none => rfl
        | some Ω =>
          have := Adjudicator.finalizedWith_apply h hfs
          rw [hf'] at this
          exact absurd (hfs.trans (congrArg some (Option.some.inj this).symm)) hf
      have ho' := finalOutcome_of_fresh_finalizedWith h L hnone hf'
      have hc' : ledgerCredit s' L oL (.external d) = oL.owed (.external d) := by
        unfold ledgerCredit; rw [if_pos hf', ho']; rfl
      rw [hc, hc']
      exact ⟨fun _ => ⟨oL, ho', hoLV⟩, Or.inl (le_refl _), Nat.add_le_add_left hbal _⟩
    · have hc' : ledgerCredit s' L oL (.external d) = oL.owed (.external d) := by
        unfold ledgerCredit; rw [if_neg hf']
      rw [hc, hc']
      exact ⟨fun h' => absurd h' hf', Or.inl (le_refl _), Nat.add_le_add_left hbal _⟩

/-- The chain invariant of `satp_intermediary_before_round2`'s strategy, for
    the two ledgers `Lm`, `Lp` with latest allocations `om`, `op`: each ledger
    finalized with its latest allocation stores an allocation with no entry
    for `V`, and `total` is at most the two credits (`ledgerCredit`) plus the
    balance of `.external d`. -/
def LedgerPairInv (Lm Lp : FixedPart) (om op : Allocation E) (V : Address E) (d : E)
    (total : Coins) (s : Adjudicator E) : Prop :=
  (s.finalizedWith Lm.address = some (.allocation om) →
    ∃ o, s.finalOutcome Lm.address = some (.allocation o) ∧ o.find V = none) ∧
  (s.finalizedWith Lp.address = some (.allocation op) →
    ∃ o, s.finalOutcome Lp.address = some (.allocation o) ∧ o.find V = none) ∧
  total ≤ ledgerCredit s Lm om (.external d) + ledgerCredit s Lp op (.external d) +
    s.balances.get (.external d)

/-- Every on-chain step keeps `LedgerPairInv` (`ledger_credit_step` once per
    ledger). One step is a `transfer` out of at most one of the two distinct
    ledgers, so at most one credit falls, and the balance of `.external d`
    covers that fall. -/
theorem LedgerPairInv.step {apps : Apps E} {Lm Lp : FixedPart} {om op : Allocation E}
    {V : Address E} {d : E} {total : Coins} (hne : Lm ≠ Lp) (hmV : om.find V = none)
    (hpV : op.find V = none) {caller : Participant} {o : Op E} {s s' : Adjudicator E}
    (hI : LedgerPairInv Lm Lp om op V d total s) (h : s.apply apps caller o = some s') :
    LedgerPairInv Lm Lp om op V d total s' := by
  obtain ⟨hIm, hIp, htot⟩ := hI
  obtain ⟨hAm, hBm, hCm⟩ := ledger_credit_step h Lm V d om hmV hIm
  obtain ⟨hAp, hBp, hCp⟩ := ledger_credit_step h Lp V d op hpV hIp
  have hbal : s.balances.get (.external d) ≤ s'.balances.get (.external d) :=
    paid_out_monotone apps s s' (Step.mk caller o s s' h) d
  refine ⟨hAm, hAp, ?_⟩
  rcases hBm with hm | ⟨b, hb⟩
  · rcases hBp with hp | ⟨b', hb'⟩
    · unfold Coins at *; omega
    · unfold Coins at *; omega
  · rcases hBp with hp | ⟨b', hb'⟩
    · unfold Coins at *; omega
    · rw [hb] at hb'
      exact absurd (Op.transfer.inj hb').1 hne

/-- A chain predicate that every successful on-chain step keeps holds after
    any adversary move (`NetworkState.applyAdv`): `.chain` and `.land` are one
    step or none, `.tick` is the step `Op.tick`, `.deliver` leaves the chain
    alone. -/
theorem NetworkState.applyAdv_chainInv (apps : Apps E) {p : Participant}
    {I : Adjudicator E → Prop}
    (hstep : ∀ (caller : Participant) (o : Op E) (s s' : Adjudicator E),
      I s → s.apply apps caller o = some s' → I s')
    (net : NetworkState E p) (m : AdvMove E) (hI : I net.chain) :
    I (net.applyAdv apps m).chain := by
  cases m with
  | chain caller o =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps caller o with
    | none => exact hI
    | some s' => exact hstep caller o _ s' hI h
  | deliver ss => exact hI
  | tick dt => exact hstep p (.tick dt) _ _ hI rfl
  | land o =>
    simp only [NetworkState.applyAdv]
    cases h : net.chain.apply apps p o with
    | none => exact hI
    | some s' => exact hstep p o _ s' hI h

/-- A chain predicate that every successful on-chain step keeps holds over
    a whole round's adversary play (`NetworkState.applyAdv_chainInv`, by
    induction). -/
theorem Threat.RoundSeq.chainInv {apps : Apps E} {p : Participant} {T : Threat E p} {t : Time}
    {pending : List (Op E)} {net net' : NetworkState E p} {I : Adjudicator E → Prop}
    (hstep : ∀ (caller : Participant) (o : Op E) (s s' : Adjudicator E),
      I s → s.apply apps caller o = some s' → I s')
    (h : Threat.RoundSeq apps T t pending net net') (hI : I net.chain) : I net'.chain := by
  induction h with
  | nil => exact hI
  | land _ _ ih => exact ih (NetworkState.applyAdv_chainInv apps hstep _ _ hI)
  | tick _ _ _ ih => exact ih (NetworkState.applyAdv_chainInv apps hstep _ _ hI)
  | other _ _ _ _ ih => exact ih (NetworkState.applyAdv_chainInv apps hstep _ _ hI)

/-- An unbeatable strategy for `G` also reaches `G` together with any chain
    predicate `I` that holds at the start and that every successful on-chain
    step keeps: each round keeps `I` (`Threat.RoundSeq.chainInv`), a
    reaction's own `applyHonest` leaves the chain alone, and `wait` is the
    step `Op.tick`. -/
theorem UnbeatableIn.and_chainInv {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G : NetworkState E p → Prop} {I : Adjudicator E → Prop}
    (hstep : ∀ (caller : Participant) (o : Op E) (s s' : Adjudicator E),
      I s → s.apply apps caller o = some s' → I s')
    {net : NetworkState E p} (hU : UnbeatableIn apps T allowed G net) (hI : I net.chain) :
    UnbeatableIn apps T allowed (fun n => G n ∧ I n.chain) net := by
  induction hU with
  | done hG => exact UnbeatableIn.done ⟨hG, hI⟩
  | move m hal hfeas _ ih =>
    refine UnbeatableIn.move m hal hfeas fun net' hround => ih net' hround ?_
    have hI' := hround.1.chainInv hstep hI
    cases m with
    | react r => exact hI'
    | wait dt => exact hstep p (.tick dt) _ _ hI' rfl

/-- SATP-20 (Theorem 3.2, Case 1-2, SATP:522-537). An intermediary that has not
    signed any ledger update with a guarantee for `V` keeps its ledger
    balances: "Without Pi's signature on such an update, the consensus app
    guarantees there is no risk to Pi's balances".

    **Argument under the explicit-time game: the hypotheses suffice,
    unchanged.** `hpend` gives one `T.ε` bound
    per channel (`net.DeadlineAfter Lm T.ε`, `net.DeadlineAfter Lp T.ε`
    separately), not `2 * T.ε` on either. `P`'s strategy issues ONE
    reaction (`Reaction.calls`, `Strategy.lean`) carrying both channels'
    calls — the checkpoint or challenge Protocol 3.1 names for `Lm` and
    for `Lp` — at the same time `t = net.chain.now`. Both calls get the
    SAME deadline `t + T.ε` (`Threat.RoundSeq.land`, one entry per call in
    `Reaction.calls`); the round that lands them (`Threat.RoundSeq`'s
    `land`/`tick`/`other` steps) cannot close until BOTH have landed, and
    cannot let the clock pass `t + T.ε` while either is still pending
    (`Threat.RoundSeq.tick`'s gate, Lamport's enabling condition,
    `Strategy.lean`'s header). So both calls are guaranteed to land before
    `t + T.ε`, exactly the bound `hpend` already grants each channel
    separately — no `2 * T.ε` margin is needed. The adversary may still
    front-run between the two (`Threat.RoundSeq.land`'s unconstrained
    position among the round's other moves, Nitro:540-542): it can act on
    `Lp` after `Lm` lands, or vice versa, but it cannot delay either
    landing past its OWN channel's `T.ε` bound to do so. This is the exact
    fix that "Time bounds per
    pending action" names: the earlier per-move game forced two
    sequential rounds for two calls, so the second call's deadline was
    measured from the SECOND round's own start, up to `2 * T.ε` after the
    first; the explicit-time game measures both calls' deadlines from the
    ONE reaction that issues them.

    The proof: `latest_state_finalizable_two` issues the one reaction and
    finalizes `Lm` with `om` and `Lp` with `op`. Payouts after that lower
    an owed amount only by a `transfer`, which raises the balance of
    `P`'s destination by the same amount. `LedgerPairInv` holds at every
    chain step (`LedgerPairInv.step`), so `UnbeatableIn.and_chainInv`
    carries it to the goal. -/
theorem satp_intermediary_before_round2 (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (hr : r.WellFormed apps) (i : Nat) (hi : 1 ≤ i)
    (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Lm Lp : TimedChannel T.ε) (hLm : r.ledgers[i - 1]? = some (Lm : FixedPart))
    (hLp : r.ledgers[i]? = some (Lp : FixedPart))
    (om op : Allocation E) (balm balp : Coins)
    (hom : r.LedgerBeforeRound2 om P balm) (hop : r.LedgerBeforeRound2 op P balp)
    (net : Nitro.ReachableParticipant apps T)
    (hHm : HoldsLatestLedger net.state (Lm : FixedPart) om)
    (hHp : HoldsLatestLedger net.state (Lp : FixedPart) op)
    (hpend : net.state.DeadlineAfter (Lm : FixedPart) T.ε ∧ net.state.DeadlineAfter (Lp : FixedPart) T.ε)
    (hchain : net.state.chain.finalizedWith (Lm : FixedPart).address = none ∧
      net.state.chain.finalizedWith (Lp : FixedPart).address = none) :
    Unbeatable apps T (IntermediaryRecovered r (Lm : FixedPart) (Lp : FixedPart) balm balp
      (net.state.chain.balances.get (.external (r.dest P)))) net.state := by
  obtain_reach ⟨net, hnr⟩ := net
  obtain ⟨Lm, hdurLm⟩ := Lm
  obtain ⟨Lp, hdurLp⟩ := Lp
  have hdur : 2 * T.ε ≤ Lm.challengeDuration ∧ 2 * T.ε ≤ Lp.challengeDuration := ⟨hdurLm, hdurLp⟩
  -- The route facts: both ledgers run the consensus app, `P` is a participant
  -- of each, and the two ledgers are distinct (their left peers differ).
  obtain ⟨-, -, hnodup, -, hled, -, -, -⟩ := hr
  obtain ⟨Pm, Qm, hPm, hQm, hLmp, ⟨-, hcm⟩⟩ := hled (i - 1) Lm hLm
  obtain ⟨Pp, Qp, hPp, -, hLpp, ⟨-, hcp⟩⟩ := hled i Lp hLp
  rw [Nat.sub_add_cancel hi, hP, Option.some.injEq] at hQm
  rw [hP, Option.some.injEq] at hPp
  subst hQm hPp
  have hPLm : P ∈ Lm.participants := by rw [hLmp]; (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
  have hPLp : P ∈ Lp.participants := by rw [hLpp]; (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])
  have hne : Lm ≠ Lp := by
    intro heq
    rw [heq, hLpp, List.cons.injEq] at hLmp
    rw [hLmp.1] at hP
    have hlt : i - 1 < r.peers.length := by omega
    have := (List.getElem?_inj hlt hnodup).1 (hPm.trans hP.symm)
    omega
  -- The latest supported states of both ledgers.
  obtain ⟨ssm, hhm, hallm, hchm, houtm, -, hsentm, hstm⟩ := hHm
  obtain ⟨ssp, hhp, hallp, hchp, houtp, -, hsentp, hstp⟩ := hHp
  have hst1 : (∃ t, net.chain.statusOf Lm = .open t ∧ t ≤ ssm.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf Lm = .challenged t ch ∧
        (t < ssm.state.turnNum ∨ ch.state = ssm.state) ∧ net.chain.now + T.ε ≤ ch.deadline) := by
    rcases hstm with ho | ⟨t, ch, hstt, hlt⟩
    · exact Or.inl ho
    · exact Or.inr ⟨t, ch, hstt, hlt, hpend.1 t ch hstt⟩
  have hst2 : (∃ t, net.chain.statusOf Lp = .open t ∧ t ≤ ssp.state.turnNum) ∨
      (∃ t ch, net.chain.statusOf Lp = .challenged t ch ∧
        (t < ssp.state.turnNum ∨ ch.state = ssp.state) ∧ net.chain.now + T.ε ≤ ch.deadline) := by
    rcases hstp with ho | ⟨t, ch, hstt, hlt⟩
    · exact Or.inl ho
    · exact Or.inr ⟨t, ch, hstt, hlt, hpend.2 t ch hstt⟩
  -- One reaction challenges both ledgers; both finalize with the latest states.
  have hU := latest_state_finalizable_two (allowed := fun _ => True) apps T A net hnr Lm Lp ssm
    ssp hne ⟨⟨hcm, hPLm⟩, hdur.1⟩ ⟨⟨hcp, hPLp⟩, hdur.2⟩
    hhm hhp hallm hallp hchm hchp (fun t ht hc => (hsentm t ht hc).1)
    (fun t ht hc => (hsentp t ht hc).1)
    (fun t ht hc hfin => by rw [(hsentm t ht hc).2] at hfin; cases hfin)
    (fun t ht hc hfin => by rw [(hsentp t ht hc).2] at hfin; cases hfin)
    hst1 hst2 trivial (fun _ => trivial)
  rw [houtm, houtp] at hU
  -- Every chain step keeps the credit invariant, from the start to the goal.
  have hI0 : LedgerPairInv Lm Lp om op r.V.address (r.dest P)
      (balm + balp + net.chain.balances.get (.external (r.dest P))) net.chain := by
    have hcm0 : ledgerCredit net.chain Lm om (.external (r.dest P)) = balm := by
      unfold ledgerCredit; rw [if_neg (by rw [hchain.1]; (simp? says simp only [reduceCtorEq, not_false_eq_true]))]; exact hom.1
    have hcp0 : ledgerCredit net.chain Lp op (.external (r.dest P)) = balp := by
      unfold ledgerCredit; rw [if_neg (by rw [hchain.2]; (simp? says simp only [reduceCtorEq, not_false_eq_true]))]; exact hop.1
    refine ⟨fun h => ?_, fun h => ?_, by rw [hcm0, hcp0]⟩
    · rw [hchain.1] at h; cases h
    · rw [hchain.2] at h; cases h
  have hU2 := UnbeatableIn.and_chainInv
    (fun _ _ _ _ hI h => LedgerPairInv.step hne hom.2 hop.2 hI h) hU hI0
  refine UnbeatableIn.imp (fun {n} hn => ?_) hU2
  obtain ⟨⟨hfm, hfp⟩, hIm, hIp, htot⟩ := hn
  obtain ⟨om', hom', hom'V⟩ := hIm hfm
  obtain ⟨op', hop', hop'V⟩ := hIp hfp
  have hcm : ledgerCredit n.chain Lm om (.external (r.dest P)) = om'.owed (.external (r.dest P)) := by
    unfold ledgerCredit; rw [if_pos (show n.chain.finalizedWith Lm.address = _ from hfm), hom']; rfl
  have hcp : ledgerCredit n.chain Lp op (.external (r.dest P)) = op'.owed (.external (r.dest P)) := by
    unfold ledgerCredit; rw [if_pos (show n.chain.finalizedWith Lp.address = _ from hfp), hop']; rfl
  rw [hcm, hcp] at htot
  exact ⟨om', op', hom', hop', hom'V, hop'V, htot⟩

/-- `addTo` keeps every entry that is present. -/
theorem Allocation.find_addTo_ne_none {o : Allocation E} {d' : Address E} (d : Address E)
    (x : Coins) (h : o.find d' ≠ none) : (o.addTo d x).find d' ≠ none := by
  by_cases hd : d' = d
  · subst hd
    rw [Allocation.find_addTo_self]
    simpa only [ne_eq, Option.map_eq_none_iff] using h
  · rwa [Allocation.find_addTo_of_ne _ _ hd]

/-- `reduceOwed` keeps every entry that is present. -/
theorem Allocation.find_reduceOwed_ne_none {o : Allocation E} {d' : Address E} (d : Address E)
    (x : Coins) (h : o.find d' ≠ none) : (o.reduceOwed d x).find d' ≠ none := by
  rw [Allocation.find_reduceOwed]
  split
  · rename_i hd
    subst hd
    simpa only [ne_eq, Option.map_eq_none_iff] using h
  · exact h

/-- The ledger allocation `o` still carries the Round 2 guarantee of `r.V` for the ledger
    between `P` and `Q` (SATP:411-418), every guarantee of `o` names external peers
    (`HonestSend.guaranteesExternal`), and both peers still have entries, as `reclaim` needs
    (go-nitro MultiAssetHolder.sol:363-364). -/
structure Route.GuaranteeHeld (r : Route E) (P Q : Participant) (o : Allocation E) : Prop where
  /-- The guarantee `G(a0 + b0, [P, Q])` for `r.V`. -/
  find : o.find r.V.address = some (r.guarantee P Q)
  /-- Every guarantee names external peers. -/
  external : o.GuaranteesExternal
  /-- `P` has an entry. -/
  left : o.find (.external (r.dest P)) ≠ none
  /-- `Q` has an entry. -/
  right : o.find (.external (r.dest Q)) ≠ none

/-- One on-chain step and a finalized ledger channel `L` whose stored allocation `o` holds
    the Round 2 guarantee of `r.V` (`Route.GuaranteeHeld`). Either the new stored allocation
    still holds it, with the accounting of `ledger_claim_step`, or the step reclaimed it:
    then `r.V` finalized with amounts that sum to `a0 + b0`, and the peers' entries rose by
    those amounts (`Adjudicator.reclaim_some`). A reclaim for another virtual channel cannot
    touch the guarantee of `r.V`: its targets are external (`Allocation.GuaranteesExternal`),
    and `r.V.address` is a channel address. A transfer cannot pay `r.V`: its entry is a
    guarantee, and `transfer` pays only an `.alloc` entry. Used by `ledger_held_step`. -/
theorem ledger_guarantee_step {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') {r : Route E}
    (L : FixedPart) {P Q : Participant} (d : E) (o : Allocation E)
    (ho : s.finalOutcome L.address = some (.allocation o)) (hG : r.GuaranteeHeld P Q o) :
    ∃ o', s'.finalOutcome L.address = some (.allocation o') ∧
      ((r.GuaranteeHeld P Q o' ∧
          (o.owed (.external d) ≤ o'.owed (.external d) ∨ ∃ b, op = .transfer L b) ∧
          o.owed (.external d) + s.balances.get (.external d) ≤
            o'.owed (.external d) + s'.balances.get (.external d)) ∨
        (o'.find r.V.address = none ∧ ∃ oV, s.finalizedWith r.V.address = some (.allocation oV) ∧
          oV.amountAt 0 + oV.amountAt 1 = r.a0 + r.b0 ∧
          o'.owed (.external d) = ((o.addTo (.external (r.dest P)) (oV.amountAt 0)).addTo
            (.external (r.dest Q)) (oV.amountAt 1)).owed (.external d))) := by
  obtain ⟨hg, hGE, hPf, hQf⟩ := hG
  -- `reduceOwed`, `addTo` and `remove` keep `Allocation.GuaranteesExternal`: they turn one
  -- entry into an `.alloc` entry or drop entries.
  have geRed : ∀ (b : Address E) (x : Coins) (o1 : Allocation E), o1.GuaranteesExternal →
      (o1.reduceOwed b x).GuaranteesExternal := by
    intro b x o1
    induction o1 with
    | nil => intro _ e he; (simp? [Allocation.reduceOwed] at he says simp only [Allocation.reduceOwed, List.not_mem_nil] at he)
    | cons e0 rest ih =>
      intro h1 e he y ps hit
      unfold Allocation.reduceOwed at he
      split at he
      · rcases List.mem_cons.mp he with rfl | hmem
        · (simp? at hit says simp only [reduceCtorEq] at hit)
        · exact h1 e (List.mem_cons_of_mem _ hmem) y ps hit
      · rcases List.mem_cons.mp he with rfl | hmem
        · exact h1 e List.mem_cons_self y ps hit
        · exact ih (fun e' he' => h1 e' (List.mem_cons_of_mem _ he')) e hmem y ps hit
  have geAdd : ∀ (b : Address E) (x : Coins) (o1 : Allocation E), o1.GuaranteesExternal →
      (o1.addTo b x).GuaranteesExternal := by
    intro b x o1
    induction o1 with
    | nil => intro _ e he; (simp? [Allocation.addTo] at he says simp only [Allocation.addTo, List.not_mem_nil] at he)
    | cons e0 rest ih =>
      intro h1 e he y ps hit
      unfold Allocation.addTo at he
      split at he
      · rcases List.mem_cons.mp he with rfl | hmem
        · (simp? at hit says simp only [reduceCtorEq] at hit)
        · exact h1 e (List.mem_cons_of_mem _ hmem) y ps hit
      · rcases List.mem_cons.mp he with rfl | hmem
        · exact h1 e List.mem_cons_self y ps hit
        · exact ih (fun e' he' => h1 e' (List.mem_cons_of_mem _ he')) e hmem y ps hit
  have geRem : ∀ (b : Address E) (o1 : Allocation E), o1.GuaranteesExternal →
      (o1.remove b).GuaranteesExternal :=
    fun _ _ h1 e he => h1 e (List.mem_filter.mp he).1
  have hbal : s.balances.get (.external d) ≤ s'.balances.get (.external d) :=
    paid_out_monotone apps s s' (Step.mk caller op s s' h) d
  have ho2 := ho
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at ho2
  have hmode : (s.statusOf L).mode s.now = .finalized := by
    rw [ChannelStatus.mode_eq_finalized_iff, ho2]; rfl
  have hVext : ∀ a : Address E, a.isExternal = true → a ≠ r.V.address := by
    intro a ha heq; subst heq; (simp? [FixedPart.address_eq] at ha says simp only [FixedPart.address_eq, Address.isExternal_channel, Bool.false_eq_true] at ha)
  have keep : s'.statusOf L = s.statusOf L → s.now ≤ s'.now →
      ∃ o', s'.finalOutcome L.address = some (.allocation o') ∧
      ((r.GuaranteeHeld P Q o' ∧
          (o.owed (.external d) ≤ o'.owed (.external d) ∨ ∃ b, op = .transfer L b) ∧
          o.owed (.external d) + s.balances.get (.external d) ≤
            o'.owed (.external d) + s'.balances.get (.external d)) ∨
        (o'.find r.V.address = none ∧ ∃ oV, s.finalizedWith r.V.address = some (.allocation oV) ∧
          oV.amountAt 0 + oV.amountAt 1 = r.a0 + r.b0 ∧
          o'.owed (.external d) = ((o.addTo (.external (r.dest P)) (oV.amountAt 0)).addTo
            (.external (r.dest Q)) (oV.amountAt 1)).owed (.external d))) := by
    intro hst hn
    refine ⟨o, ?_, Or.inl ⟨⟨hg, hGE, hPf, hQf⟩, Or.inl le_rfl, Nat.add_le_add_left hbal _⟩⟩
    simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel]
    rw [hst]
    exact ChannelStatus.finalOutcome_mono ho2 hn
  have hn := Adjudicator.apply_now_le h
  cases op with
  | deposit a e x =>
    obtain ⟨-, -, -, -, hstatus, -⟩ := Adjudicator.deposit_some h
    exact keep (Adjudicator.statusOf_of_status hstatus L) hn
  | tick dt =>
    simp only [Adjudicator.apply_tick, Option.some.injEq] at h
    subst h
    exact keep (Adjudicator.tick_statusOf s dt L) hn
  | transfer a b =>
    obtain ⟨o1, amt, x, hfo, hfind, hx, hbal', -, hstatus, hnow, -, -⟩ :=
      Adjudicator.transfer_some h
    by_cases hac : L = a
    · subst hac
      rw [ho, Option.some.injEq, Outcome.allocation.injEq] at hfo
      subst hfo
      have hbV : r.V.address ≠ b := by
        intro heq
        rw [← heq, hg] at hfind
        (simp? [Route.guarantee] at hfind says simp only [Route.guarantee, FixedPart.address_eq, Option.some.injEq, Entry.mk.injEq, reduceCtorEq, and_false] at hfind)
      refine ⟨o.reduceOwed b x, ?_, Or.inl ⟨⟨?_, geRed b x o hGE,
        Allocation.find_reduceOwed_ne_none b x hPf, Allocation.find_reduceOwed_ne_none b x hQf⟩,
        Or.inr ⟨b, rfl⟩, ?_⟩⟩
      · simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel]
        rw [Adjudicator.statusOf_of_status hstatus, Adjudicator.statusOf_setStatus, if_pos rfl,
          ChannelStatus.finalOutcome_withOutcome]
      · rw [Allocation.find_reduceOwed, if_neg hbV]; exact hg
      · have hxle : x ≤ o.owed b := hx ▸ paidTo_first_entry_only _ o b
        have haddr : (Address.external d : Address E) ≠ L.address := by (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])
        rw [hbal', Allocation.owed_reduceOwed, Balances.get_sub, if_neg haddr, Balances.get_add]
        by_cases hbd : (Address.external d : Address E) = b
        · rw [if_pos hbd, if_pos hbd, hbd]; unfold Coins at *; omega
        · rw [if_neg hbd, if_neg hbd]
    · exact keep (by rw [Adjudicator.statusOf_of_status hstatus, Adjudicator.statusOf_setStatus,
        if_neg hac]) hn
  | reclaim l v =>
    obtain ⟨oL, oV, y, lft, rgt, hfo, hfoV, hgfind, -, -, hxeq, hs', -, -⟩ :=
      Adjudicator.reclaim_some h
    subst hs'
    by_cases hlc : L = l
    · subst hlc
      rw [ho, Option.some.injEq, Outcome.allocation.injEq] at hfo
      subst hfo
      have hfo' : (s.setStatus L ((s.statusOf L).withOutcome (.allocation
          (((o.addTo lft (oV.amountAt 0)).addTo rgt (oV.amountAt 1)).remove v.address)))).finalOutcome
          L.address = some (.allocation
            (((o.addTo lft (oV.amountAt 0)).addTo rgt (oV.amountAt 1)).remove v.address)) := by
        simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
          Adjudicator.statusOf_setStatus, ↓reduceIte, ChannelStatus.finalOutcome_withOutcome]
      have hdv : (Address.external d : Address E) ≠ v.address := by (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])
      by_cases hvV : (v.address : Address E) = r.V.address
      · rw [hvV, hg] at hgfind
        simp only [Route.guarantee, Option.some.injEq, Entry.mk.injEq, Item.guarantee.injEq,
          List.cons.injEq, and_true, true_and] at hgfind
        obtain ⟨hy, hl, hr⟩ := hgfind
        subst hy hl hr
        refine ⟨_, hfo', Or.inr ⟨?_, oV, hvV ▸ hfoV, hxeq, ?_⟩⟩
        · rw [Allocation.find_remove, if_pos hvV.symm]
        · rw [Allocation.owed_remove_of_ne _ hdv]
      · have hmem := List.mem_of_find?_eq_some hgfind
        have hlx : lft.isExternal = true := hGE _ hmem y [lft, rgt] rfl lft (by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]))
        have hrx : rgt.isExternal = true := hGE _ hmem y [lft, rgt] rfl rgt (by (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]))
        have hPv : (Address.external (r.dest P) : Address E) ≠ v.address := by
          (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])
        have hQv : (Address.external (r.dest Q) : Address E) ≠ v.address := by
          (simp? [FixedPart.address_eq] says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true])
        refine ⟨_, hfo', Or.inl ⟨⟨?_, geRem _ _ (geAdd _ _ _ (geAdd _ _ _ hGE)), ?_, ?_⟩,
          Or.inl ?_, ?_⟩⟩
        · rw [Allocation.find_remove, if_neg (Ne.symm hvV),
            Allocation.find_addTo_of_ne _ _ (Ne.symm (hVext rgt hrx)),
            Allocation.find_addTo_of_ne _ _ (Ne.symm (hVext lft hlx))]
          exact hg
        · rw [Allocation.find_remove, if_neg hPv]
          exact Allocation.find_addTo_ne_none _ _ (Allocation.find_addTo_ne_none _ _ hPf)
        · rw [Allocation.find_remove, if_neg hQv]
          exact Allocation.find_addTo_ne_none _ _ (Allocation.find_addTo_ne_none _ _ hQf)
        · rw [Allocation.owed_remove_of_ne _ hdv]
          exact le_trans (Allocation.owed_addTo_ge o lft _ _) (Allocation.owed_addTo_ge _ rgt _ _)
        · rw [Allocation.owed_remove_of_ne _ hdv]
          exact Nat.add_le_add (le_trans (Allocation.owed_addTo_ge o lft _ _)
            (Allocation.owed_addTo_ge _ rgt _ _)) hbal
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hlc]) hn
  | challenge c proof cand =>
    obtain ⟨⟨-, -, -, hmd⟩, hs'⟩ := Adjudicator.challenge_some h
    subst hs'
    by_cases hcc : L = c
    · exfalso
      subst hcc
      rw [Adjudicator.mode_eq] at hmd
      rcases hmd with ⟨hmo, -⟩ | ⟨hmo, -⟩ <;> rw [hmode] at hmo <;> cases hmo
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc]) hn
  | checkpoint c proof cand =>
    obtain ⟨⟨hopen, -, -, -⟩, hs'⟩ := Adjudicator.checkpoint_some h
    subst hs'
    by_cases hcc : L = c
    · exfalso
      subst hcc
      exact hopen hmode
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc]) hn
  | conclude c ss =>
    obtain ⟨⟨hopen, -⟩, hs'⟩ := Adjudicator.conclude_some h
    subst hs'
    by_cases hcc : L = c
    · exfalso
      subst hcc
      exact hopen hmode
    · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc]) hn

/-- The allocation of `L` that counts toward `IntermediaryRecovered`: once `L` finalized with
    its latest allocation `oL`, the stored outcome (a payout or a reclaim changes it); before
    that, `oL` itself. `ledgerCredit` reads the owed amount of this allocation. -/
def ledgerCur (s : Adjudicator E) (L : FixedPart) (oL : Allocation E) : Allocation E :=
  if s.finalizedWith L.address = some (.allocation oL) then
    ((s.finalOutcome L.address).map Outcome.entries).getD []
  else oL

/-- `ledgerCur` once `L` finalized with `oL`: the stored allocation. -/
theorem ledgerCur_of_fin {s : Adjudicator E} {L : FixedPart} {oL o : Allocation E}
    (hf : s.finalizedWith L.address = some (.allocation oL))
    (ho : s.finalOutcome L.address = some (.allocation o)) : ledgerCur s L oL = o := by
  unfold ledgerCur; rw [if_pos hf, ho]; rfl

/-- `ledgerCur` before `L` finalized with `oL`: `oL`. -/
theorem ledgerCur_of_not_fin {s : Adjudicator E} {L : FixedPart} {oL : Allocation E}
    (hf : s.finalizedWith L.address ≠ some (.allocation oL)) : ledgerCur s L oL = oL := by
  unfold ledgerCur; rw [if_neg hf]

/-- Once `L` finalized with its latest allocation `oL`, its stored allocation still holds the
    Round 2 guarantee of `r.V` (`Route.GuaranteeHeld`), or has no entry for `r.V`. -/
structure Route.LedgerHeldInv (r : Route E) (P Q : Participant) (L : FixedPart)
    (oL : Allocation E) (s : Adjudicator E) : Prop where
  /-- The stored allocation of a finalized `L`. -/
  held : s.finalizedWith L.address = some (.allocation oL) →
    ∃ o, s.finalOutcome L.address = some (.allocation o) ∧
      (r.GuaranteeHeld P Q o ∨ o.find r.V.address = none)

/-- The share `sh` that a reclaim of the guarantee of `r.V` in `L` still owes to one peer: `sh`
    while the current allocation of `L` (`ledgerCur`) holds the guarantee, zero after. -/
def ledgerPend (r : Route E) (P Q : Participant) (s : Adjudicator E) (L : FixedPart)
    (oL : Allocation E) (sh : Coins) : Coins :=
  if (ledgerCur s L oL).find r.V.address = some (r.guarantee P Q) then sh else 0

/-- One on-chain step and one ledger `L` of `Route.IntermediaryInv`: the step keeps
    `Route.LedgerHeldInv`; it keeps the entry of `r.V` in `ledgerCur`, unless `r.V` was already
    finalized (a reclaim); and the owed amount of `.external d` plus the pending share `sh`
    (`ledgerPend`) falls only under a transfer out of `L`, which the balance of `.external d`
    covers. `hpos` places `d` as the left (`k = 0`) or right (`k = 1`) peer of the guarantee,
    and `hsh` makes `sh` the share that a reclaim pays at that index. -/
theorem ledger_held_step {apps : Apps E} {caller : Participant} {op : Op E}
    {s s' : Adjudicator E} (h : s.apply apps caller op = some s') {r : Route E}
    (L : FixedPart) {P Q : Participant} (d : E) {oL : Allocation E}
    (hoL : r.GuaranteeHeld P Q oL) (hinv : r.LedgerHeldInv P Q L oL s) (k : Nat) (sh : Coins)
    (hpos : (d = r.dest P ∧ d ≠ r.dest Q ∧ k = 0) ∨ (d = r.dest Q ∧ d ≠ r.dest P ∧ k = 1))
    (hsh : ∀ oV, s.finalizedWith r.V.address = some (.allocation oV) →
      oV.amountAt 0 + oV.amountAt 1 = r.a0 + r.b0 → oV.amountAt k = sh) :
    r.LedgerHeldInv P Q L oL s' ∧
    ((ledgerCur s' L oL).find r.V.address = (ledgerCur s L oL).find r.V.address ∨
      ∃ oV, s.finalizedWith r.V.address = some (.allocation oV)) ∧
    ((ledgerCur s L oL).owed (.external d) + ledgerPend r P Q s L oL sh ≤
        (ledgerCur s' L oL).owed (.external d) + ledgerPend r P Q s' L oL sh ∨
      ∃ b, op = .transfer L b) ∧
    (ledgerCur s L oL).owed (.external d) + ledgerPend r P Q s L oL sh +
        s.balances.get (.external d) ≤
      (ledgerCur s' L oL).owed (.external d) + ledgerPend r P Q s' L oL sh +
        s'.balances.get (.external d) := by
  have hbal : s.balances.get (.external d) ≤ s'.balances.get (.external d) :=
    paid_out_monotone apps s s' (Step.mk caller op s s' h) d
  have hpend : ∀ {s1 : Adjudicator E} {o : Allocation E}, ledgerCur s1 L oL = o →
      ledgerPend r P Q s1 L oL sh = if o.find r.V.address = some (r.guarantee P Q) then sh else 0 := by
    intro s1 o h1; unfold ledgerPend; rw [h1]
  by_cases hf : s.finalizedWith L.address = some (.allocation oL)
  · obtain ⟨o, ho, hdisj⟩ := hinv.held hf
    have hf' := Adjudicator.finalizedWith_apply h hf
    have hc := ledgerCur_of_fin hf ho
    rcases hdisj with hG | hnone
    · obtain ⟨o', ho', hcase⟩ := ledger_guarantee_step h L d o ho hG
      have hc' := ledgerCur_of_fin hf' ho'
      rw [hpend hc, hpend hc', hc, hc', if_pos hG.find]
      rcases hcase with ⟨hG', hle, hsum⟩ | ⟨hnone', oV, hfV, hx, howed⟩
      · rw [if_pos hG'.find]
        refine ⟨⟨fun _ => ⟨o', ho', Or.inl hG'⟩⟩, Or.inl (by rw [hG.find, hG'.find]), ?_, ?_⟩
        · rcases hle with hle | hb
          · exact Or.inl (Nat.add_le_add_right hle _)
          · exact Or.inr hb
        · unfold Coins at *; omega
      · have hn' : ¬ (o'.find r.V.address = some (r.guarantee P Q)) := by rw [hnone']; (simp? says simp only [reduceCtorEq, not_false_eq_true])
        rw [if_neg hn']
        have hk := hsh oV hfV hx
        have hcred : o'.owed (.external d) = o.owed (.external d) + sh := by
          rw [howed]
          rcases hpos with ⟨rfl, hdQ, rfl⟩ | ⟨rfl, hdP, rfl⟩
          · rw [Allocation.owed_addTo_of_ne _ _ (by (simpa? using hdQ says simpa only [ne_eq, Address.external.injEq] using hdQ)),
              Allocation.owed_addTo_self _ hG.left, hk]
          · rw [Allocation.owed_addTo_self _ (Allocation.find_addTo_ne_none _ _ hG.right),
              Allocation.owed_addTo_of_ne _ _ (by (simpa? using hdP says simpa only [ne_eq, Address.external.injEq] using hdP)), hk]
        refine ⟨⟨fun _ => ⟨o', ho', Or.inr hnone'⟩⟩, Or.inr ⟨oV, hfV⟩, ?_, ?_⟩
        · exact Or.inl (by rw [hcred, Nat.add_zero])
        · rw [hcred, Nat.add_zero]; exact Nat.add_le_add_left hbal _
    · obtain ⟨o', ho', hoV', hle, hsum⟩ := ledger_claim_step h L r.V.address d o ho hnone
      have hc' := ledgerCur_of_fin hf' ho'
      have hn1 : ¬ (o.find r.V.address = some (r.guarantee P Q)) := by rw [hnone]; (simp? says simp only [reduceCtorEq, not_false_eq_true])
      have hn2 : ¬ (o'.find r.V.address = some (r.guarantee P Q)) := by rw [hoV']; (simp? says simp only [reduceCtorEq, not_false_eq_true])
      rw [hpend hc, hpend hc', hc, hc', if_neg hn1, if_neg hn2]
      refine ⟨⟨fun _ => ⟨o', ho', Or.inr hoV'⟩⟩, Or.inl (by rw [hnone, hoV']), ?_, ?_⟩
      · rcases hle with hle | hb
        · exact Or.inl (Nat.add_le_add_right hle _)
        · exact Or.inr hb
      · simpa only [Nat.add_zero] using hsum
  · have hc := ledgerCur_of_not_fin hf
    by_cases hf' : s'.finalizedWith L.address = some (.allocation oL)
    · have hnone : s.finalizedWith L.address = none := by
        cases hfs : s.finalizedWith L.address with
        | none => rfl
        | some Ω =>
          have := Adjudicator.finalizedWith_apply h hfs
          rw [hf'] at this
          exact absurd (hfs.trans (congrArg some (Option.some.inj this).symm)) hf
      have ho' := finalOutcome_of_fresh_finalizedWith h L hnone hf'
      have hc' := ledgerCur_of_fin hf' ho'
      rw [hpend hc, hpend hc', hc, hc']
      exact ⟨⟨fun _ => ⟨oL, ho', Or.inl hoL⟩⟩, Or.inl rfl, Or.inl le_rfl,
        Nat.add_le_add_left hbal _⟩
    · have hc' := ledgerCur_of_not_fin hf'
      rw [hpend hc, hpend hc', hc, hc']
      exact ⟨⟨fun h' => absurd h' hf'⟩, Or.inl rfl, Or.inl le_rfl, Nat.add_le_add_left hbal _⟩

/-- The share of `r.V`'s final outcome at index `k` (`Allocation.amountAt`, the index `reclaim`
    reads): the finalized amount when `r.V` finalized with amounts that sum to `a0 + b0`
    (`reclaim`'s amount check, go-nitro MultiAssetHolder.sol:365), `dflt` otherwise. -/
def satpShare (r : Route E) (s : Adjudicator E) (k : Nat) (dflt : Coins) : Coins :=
  match s.finalizedWith r.V.address with
  | some Ω =>
    if Ω.entries.amountAt 0 + Ω.entries.amountAt 1 = r.a0 + r.b0 then Ω.entries.amountAt k
    else dflt
  | none => dflt

/-- The route facts of the intermediary `P` that `satp_theorem_3_2`'s chain invariant reads:
    the left ledger `Lm` (latest allocation `om`, guarantee `G(a0 + b0, [Pprev, P])`) and the
    right ledger `Lp` (latest allocation `op`, guarantee `G(a0 + b0, [P, Pnext])`) are two
    distinct ledger channels, the three peers have distinct destinations, and `r.V` is
    virtual (`Route.WellFormed`, `Route.Round2Ledger`, `HonestSend.guaranteesExternal`). -/
structure Route.Intermediary (r : Route E) (Pprev P Pnext : Participant) (Lm Lp : FixedPart)
    (om op : Allocation E) : Prop where
  /-- The two ledgers differ. -/
  ne : Lm ≠ Lp
  /-- `P` and `Pprev` have distinct destinations. -/
  destPrev : r.dest P ≠ r.dest Pprev
  /-- `P` and `Pnext` have distinct destinations. -/
  destNext : r.dest P ≠ r.dest Pnext
  /-- `om` holds the guarantee of the left ledger. -/
  heldm : r.GuaranteeHeld Pprev P om
  /-- `op` holds the guarantee of the right ledger. -/
  heldp : r.GuaranteeHeld P Pnext op
  /-- `Lm` is a ledger channel. -/
  kindm : Lm.kind = .ledger
  /-- `Lp` is a ledger channel. -/
  kindp : Lp.kind = .ledger
  /-- `r.V` is a virtual channel. -/
  kindV : r.V.kind = .virtual

/-- The chain invariant of `satp_theorem_3_2`'s strategy (`Route.Intermediary`): each ledger
    finalized with its latest allocation keeps the guarantee or drops it
    (`Route.LedgerHeldInv`); while `r.V` is not finalized, both guarantees are still there; and
    `total` is at most `P`'s owed amounts, the shares the remaining guarantees still owe `P`
    (`ledgerPend`, `satpShare`: `b` in `Lm`, `a` in `Lp`, SATP:550-553), and the balance of
    `P`'s destination. -/
structure Route.IntermediaryInv (r : Route E) (Pprev P Pnext : Participant) (Lm Lp : FixedPart)
    (om op : Allocation E) (total : Coins) (s : Adjudicator E) : Prop where
  /-- The left ledger keeps or drops its guarantee. -/
  heldm : r.LedgerHeldInv Pprev P Lm om s
  /-- The right ledger keeps or drops its guarantee. -/
  heldp : r.LedgerHeldInv P Pnext Lp op s
  /-- Both guarantees stay while `r.V` is not finalized. -/
  present : s.finalizedWith r.V.address = none →
    (ledgerCur s Lm om).find r.V.address = some (r.guarantee Pprev P) ∧
    (ledgerCur s Lp op).find r.V.address = some (r.guarantee P Pnext)
  /-- `P`'s credit. -/
  credit : total ≤ (ledgerCur s Lm om).owed (.external (r.dest P)) +
      ledgerPend r Pprev P s Lm om (satpShare r s 1 r.b0) +
    ((ledgerCur s Lp op).owed (.external (r.dest P)) +
      ledgerPend r P Pnext s Lp op (satpShare r s 0 r.a0)) +
    s.balances.get (.external (r.dest P))

/-- Every on-chain step keeps `Route.IntermediaryInv` (`ledger_held_step` once per ledger). At
    most one of the two distinct ledgers pays out in one step, and the balance of `P`'s
    destination covers that payout. The step that finalizes `r.V` exchanges the default shares
    `b0`, `a0` for the finalized shares, which have the same sum when `reclaim` can use
    them; both guarantees are still there at that step, as no reclaim of `r.V` can run before
    `r.V` is finalized. -/
theorem Route.IntermediaryInv.step {apps : Apps E} {r : Route E} {Pprev P Pnext : Participant}
    {Lm Lp : FixedPart} {om op : Allocation E} {total : Coins}
    (w : r.Intermediary Pprev P Pnext Lm Lp om op) {caller : Participant} {o : Op E}
    {s s' : Adjudicator E} (hI : r.IntermediaryInv Pprev P Pnext Lm Lp om op total s)
    (h : s.apply apps caller o = some s') :
    r.IntermediaryInv Pprev P Pnext Lm Lp om op total s' := by
  obtain ⟨hIm, hIp, hpres, htot⟩ := hI
  have hspec : ∀ {k : Nat} {dflt : Coins} (oV : Allocation E),
      s.finalizedWith r.V.address = some (.allocation oV) →
      oV.amountAt 0 + oV.amountAt 1 = r.a0 + r.b0 → oV.amountAt k = satpShare r s k dflt := by
    intro k dflt oV hf hx
    unfold satpShare
    simp only [hf, Outcome.entries, hx, ↓reduceIte]
  have hAm : r.LedgerHeldInv Pprev P Lm om s' :=
      (ledger_held_step h Lm (r.dest P) w.heldm hIm 1 (satpShare r s 1 r.b0)
        (Or.inr ⟨rfl, w.destPrev, rfl⟩) hspec).1
  have hAp : r.LedgerHeldInv P Pnext Lp op s' :=
      (ledger_held_step h Lp (r.dest P) w.heldp hIp 0 (satpShare r s 0 r.a0)
        (Or.inl ⟨rfl, w.destNext, rfl⟩) hspec).1
  have hmid : total ≤ (ledgerCur s' Lm om).owed (.external (r.dest P)) +
      ledgerPend r Pprev P s' Lm om (satpShare r s 1 r.b0) +
      ((ledgerCur s' Lp op).owed (.external (r.dest P)) +
        ledgerPend r P Pnext s' Lp op (satpShare r s 0 r.a0)) +
      s'.balances.get (.external (r.dest P)) := by
    obtain ⟨_, hFm, hBm, hCm⟩ := ledger_held_step h Lm (r.dest P) w.heldm hIm 1
      (satpShare r s 1 r.b0) (Or.inr ⟨rfl, w.destPrev, rfl⟩) hspec
    obtain ⟨_, hFp, hBp, hCp⟩ := ledger_held_step h Lp (r.dest P) w.heldp hIp 0
      (satpShare r s 0 r.a0) (Or.inl ⟨rfl, w.destNext, rfl⟩) hspec
    rcases hBm with hm | ⟨b, hb⟩
    · rcases hBp with hp | ⟨b', hb'⟩
      · unfold Coins at *; omega
      · unfold Coins at *; omega
    · rcases hBp with hp | ⟨b', hb'⟩
      · unfold Coins at *; omega
      · rw [hb] at hb'
        exact absurd (Op.transfer.inj hb').1 w.ne
  have hVnone : s'.finalizedWith r.V.address = none → s.finalizedWith r.V.address = none := by
    intro h'
    cases hfs : s.finalizedWith r.V.address with
    | none => rfl
    | some Ω => rw [Adjudicator.finalizedWith_apply h hfs] at h'; cases h'
  have hkeep : s.finalizedWith r.V.address = none →
      (ledgerCur s' Lm om).find r.V.address = some (r.guarantee Pprev P) ∧
      (ledgerCur s' Lp op).find r.V.address = some (r.guarantee P Pnext) := by
    obtain ⟨_, hFm, hBm, hCm⟩ := ledger_held_step h Lm (r.dest P) w.heldm hIm 1
      (satpShare r s 1 r.b0) (Or.inr ⟨rfl, w.destPrev, rfl⟩) hspec
    obtain ⟨_, hFp, hBp, hCp⟩ := ledger_held_step h Lp (r.dest P) w.heldp hIp 0
      (satpShare r s 0 r.a0) (Or.inl ⟨rfl, w.destNext, rfl⟩) hspec
    intro hs
    obtain ⟨hpm, hpp⟩ := hpres hs
    refine ⟨?_, ?_⟩
    · rcases hFm with heq | ⟨oV, hoV⟩
      · rw [heq]; exact hpm
      · rw [hs] at hoV; cases hoV
    · rcases hFp with heq | ⟨oV, hoV⟩
      · rw [heq]; exact hpp
      · rw [hs] at hoV; cases hoV
  have hshare : ledgerPend r Pprev P s' Lm om (satpShare r s 1 r.b0) +
      ledgerPend r P Pnext s' Lp op (satpShare r s 0 r.a0) ≤
      ledgerPend r Pprev P s' Lm om (satpShare r s' 1 r.b0) +
      ledgerPend r P Pnext s' Lp op (satpShare r s' 0 r.a0) := by
    cases hfs : s.finalizedWith r.V.address with
    | some Ω =>
      have hfs' := Adjudicator.finalizedWith_apply h hfs
      have e1 : satpShare r s' 1 r.b0 = satpShare r s 1 r.b0 := by unfold satpShare; rw [hfs, hfs']
      have e0 : satpShare r s' 0 r.a0 = satpShare r s 0 r.a0 := by unfold satpShare; rw [hfs, hfs']
      rw [e1, e0]
    | none =>
      have e1 : satpShare r s 1 r.b0 = r.b0 := by unfold satpShare; rw [hfs]
      have e0 : satpShare r s 0 r.a0 = r.a0 := by unfold satpShare; rw [hfs]
      obtain ⟨hpm', hpp'⟩ := hkeep hfs
      unfold ledgerPend
      rw [hpm', hpp', if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl, e1, e0]
      unfold satpShare
      cases hfs' : s'.finalizedWith r.V.address with
      | none => exact le_rfl
      | some Ω =>
        dsimp only
        split
        · rename_i hx; unfold Coins at *; omega
        · exact le_rfl
  refine ⟨hAm, hAp, fun h' => hkeep (hVnone h'), ?_⟩
  unfold Coins at *; omega

/-- An unbeatable strategy also reaches its goal with `Route.IntermediaryInv`, when that holds
    at the start (`UnbeatableIn.and_chainInv`, `Route.IntermediaryInv.step`). -/
theorem UnbeatableIn.and_intermediaryInv {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G : NetworkState E p → Prop} {r : Route E}
    {Pprev P Pnext : Participant} {Lm Lp : FixedPart} {om op : Allocation E} {total : Coins}
    (w : r.Intermediary Pprev P Pnext Lm Lp om op) {net : NetworkState E p}
    (hU : UnbeatableIn apps T allowed G net)
    (hI : r.IntermediaryInv Pprev P Pnext Lm Lp om op total net.chain) :
    UnbeatableIn apps T allowed
      (fun n => G n ∧ r.IntermediaryInv Pprev P Pnext Lm Lp om op total n.chain) net :=
  UnbeatableIn.and_chainInv (fun _ _ _ _ hI h => hI.step w h) hU hI

/-- An unbeatable strategy also reaches its goal with `c` still finalized with `Ω`, when `c`
    is finalized with `Ω` at the start: the outcome of finalization never changes
    (`Adjudicator.finalizedWith_apply`). -/
theorem UnbeatableIn.and_finalized {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G : NetworkState E p → Prop} {net : NetworkState E p}
    {c : FixedPart} {Ω : Outcome E} (hU : UnbeatableIn apps T allowed G net)
    (hf : net.chain.finalizedWith c.address = some Ω) :
    UnbeatableIn apps T allowed (fun n => G n ∧ n.chain.finalizedWith c.address = some Ω) net :=
  UnbeatableIn.and_chainInv (fun _ _ _ _ hI h => Adjudicator.finalizedWith_apply h hI) hU hf

/-- The stored allocation of `L` has no entry for `r.V`. -/
structure Route.LedgerCleared (r : Route E) (L : FixedPart) (s : Adjudicator E) : Prop where
  /-- The stored allocation. -/
  cleared : ∃ o, s.finalOutcome L.address = some (.allocation o) ∧ o.find r.V.address = none

/-- Once cleared, `L` stays cleared (`ledger_claim_step`). -/
theorem Route.LedgerCleared.step {apps : Apps E} {r : Route E} {L : FixedPart} (d : E)
    {caller : Participant} {op : Op E} {s s' : Adjudicator E} (hI : r.LedgerCleared L s)
    (h : s.apply apps caller op = some s') : r.LedgerCleared L s' := by
  obtain ⟨o, ho, hoV⟩ := hI.cleared
  obtain ⟨o', ho', hoV', -, -⟩ := ledger_claim_step h L r.V.address d o ho hoV
  exact ⟨o', ho', hoV'⟩

/-- The chain at the start of `satp_theorem_3_2`'s reclaim round: `Route.IntermediaryInv`,
    both ledgers finalized with their latest allocations, and `r.V` finalized with a pair
    outcome that keeps the pre-fund total. -/
structure Route.IntermediaryReady (r : Route E) (alice bob Pprev P Pnext : Participant)
    (Lm Lp : FixedPart) (om op : Allocation E) (total : Coins) (s : Adjudicator E) : Prop where
  /-- The chain invariant. -/
  inv : r.IntermediaryInv Pprev P Pnext Lm Lp om op total s
  /-- `Lm` finalized with `om`. -/
  finm : s.finalizedWith Lm.address = some (.allocation om)
  /-- `Lp` finalized with `op`. -/
  finp : s.finalizedWith Lp.address = some (.allocation op)
  /-- `r.V` finalized with a pair outcome. -/
  finV : ∃ a b, s.finalizedWith r.V.address = some (.allocation
    [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]) ∧ a + b = r.a0 + r.b0

/-- The round of `P`'s reaction `[reclaim Lm r.V, reclaim Lp r.V]` (Protocol 3.3 step 3) ends
    in `IntermediaryRecovered`. Each landing clears its ledger: the reclaim succeeds when the
    guarantee is there (`reclaim_can_happen`), and fails, changing nothing, when it is gone.
    A cleared ledger stays cleared (`Route.LedgerCleared.step`), and every step keeps
    `Route.IntermediaryReady`; the adversary lands the two calls in either order
    (`Threat.RoundSeq.peel_two`). With both guarantees gone, `Route.IntermediaryInv`'s credit
    is the goal's bound. -/
theorem satp_reclaim_round {apps : Apps E} {r : Route E} {alice bob Pprev P Pnext : Participant}
    {T : Threat E P} {t : Time} {Lm Lp : FixedPart}
    {om op : Allocation E} {balm balp base : Coins}
    (w : r.Intermediary Pprev P Pnext Lm Lp om op) {n0 n3 : NetworkState E P}
    (hseq : T.RoundSeq apps t [Op.reclaim Lm r.V, Op.reclaim Lp r.V] n0 n3)
    (hR : r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) n0.chain) :
    IntermediaryRecovered r Lm Lp balm balp base n3 := by
  have hstep : ∀ (caller : Participant) (o : Op E) (s s' : Adjudicator E),
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) s →
      s.apply apps caller o = some s' →
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) s' := by
    intro caller o s s' hs h
    obtain ⟨a, b, hV, hab⟩ := hs.finV
    exact ⟨hs.inv.step w h, Adjudicator.finalizedWith_apply h hs.finm,
      Adjudicator.finalizedWith_apply h hs.finp, a, b, Adjudicator.finalizedWith_apply h hV, hab⟩
  -- A landing of `reclaim L r.V` clears `L`.
  have clears : ∀ {Q1 Q2 : Participant} {L : FixedPart} {oL : Allocation E}
      (n : NetworkState E P), L.kind = .ledger →
      n.chain.finalizedWith L.address = some (.allocation oL) →
      r.LedgerHeldInv Q1 Q2 L oL n.chain →
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) n.chain →
      r.LedgerCleared L (n.applyAdv apps (.land (Op.reclaim L r.V))).chain := by
    intro Q1 Q2 L oL n hkL hfL hinv hn
    obtain ⟨a, b, hfV, hab⟩ := hn.finV
    have hx : Allocation.amountAt [alloc (.external (r.dest alice)) a,
        alloc (.external (r.dest bob)) b] 0 + Allocation.amountAt
          [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b] 1 =
        r.a0 + r.b0 := hab
    obtain ⟨o, ho, hG | hnone⟩ := hinv.held hfL
    · have hext : ∀ e : E, (Address.external e : Address E) ≠ r.V.address := by (simp? says simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true, implies_true])
      have hrc : n.chain.apply apps P (.reclaim L r.V) = some
          (n.chain.setStatus L ((n.chain.statusOf L).withOutcome (.allocation
            (((o.addTo (.external (r.dest Q1)) (Allocation.amountAt
              [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b] 0)).addTo
              (.external (r.dest Q2)) (Allocation.amountAt
              [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b] 1)).remove
              r.V.address)))) :=
        reclaim_can_happen n.chain L r.V o _ (r.a0 + r.b0) _ _ hkL w.kindV ho hfV
        hG.find (by rw [Allocation.find_remove, if_neg (hext _)]; exact hG.left)
        (by rw [Allocation.find_remove, if_neg (hext _)]; exact hG.right) hx
      rw [NetworkState.applyAdv_land_some apps (p := P) hrc]
      refine ⟨⟨((o.addTo (.external (r.dest Q1)) (Allocation.amountAt
          [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b] 0)).addTo
          (.external (r.dest Q2)) (Allocation.amountAt
          [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b] 1)).remove
          r.V.address, ?_, by rw [Allocation.find_remove, if_pos rfl]⟩⟩
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
        Adjudicator.statusOf_setStatus, ↓reduceIte, ChannelStatus.finalOutcome_withOutcome]
    · have hrc : n.chain.apply apps P (.reclaim L r.V) = none := by
        show n.chain.reclaim L r.V = none
        unfold Adjudicator.reclaim
        simp only [if_pos (⟨hkL, w.kindV⟩ : L.kind = .ledger ∧ r.V.kind = .virtual), ho, hfV,
          hnone]
      rw [NetworkState.applyAdv_land_none apps hrc]
      exact ⟨o, ho, hnone⟩
  have clearm : ∀ n : NetworkState E P,
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) n.chain →
      r.LedgerCleared Lm (n.applyAdv apps (.land (Op.reclaim Lm r.V))).chain :=
    fun n hn => clears n w.kindm hn.finm hn.inv.heldm hn
  have clearp : ∀ n : NetworkState E P,
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) n.chain →
      r.LedgerCleared Lp (n.applyAdv apps (.land (Op.reclaim Lp r.V))).chain :=
    fun n hn => clears n w.kindp hn.finp hn.inv.heldp hn
  -- One pending reclaim, landed after any adversary play, with a cleared ledger kept.
  have one : ∀ {L L' : FixedPart} {m0 m2 : NetworkState E P},
      (∀ n : NetworkState E P,
        r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) n.chain →
        r.LedgerCleared L (n.applyAdv apps (.land (Op.reclaim L r.V))).chain) →
      T.RoundSeq apps t [Op.reclaim L r.V] m0 m2 →
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) m0.chain →
      r.LedgerCleared L' m0.chain →
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) m2.chain ∧
        r.LedgerCleared L' m2.chain ∧ r.LedgerCleared L m2.chain := by
    intro L L' m0 m2 hland hs hI hC
    obtain ⟨m1, hA, hB⟩ := Threat.RoundSeq.peel_one _ _ _ hs
    have hI1 := hA.chainInv (I := fun s =>
      r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) s ∧
        r.LedgerCleared L' s)
      (fun caller o s s' hs h => ⟨hstep caller o s s' hs.1 h, hs.2.step (r.dest P) h⟩) ⟨hI, hC⟩
    have hland1 := hland m1 hI1.1
    obtain ⟨⟨hI2, hC2⟩, hL2⟩ := hB.chainInv (I := fun s =>
      (r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) s ∧
        r.LedgerCleared L' s) ∧ r.LedgerCleared L s)
      (fun caller o s s' hs h => ⟨⟨hstep caller o s s' hs.1.1 h, hs.1.2.step (r.dest P) h⟩,
        hs.2.step (r.dest P) h⟩)
      ⟨NetworkState.applyAdv_chainInv apps (I := fun s =>
        r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base) s ∧
          r.LedgerCleared L' s)
        (fun caller o s s' hs h => ⟨hstep caller o s s' hs.1 h, hs.2.step (r.dest P) h⟩)
        m1 _ hI1, hland1⟩
    exact ⟨hI2, hC2, hL2⟩
  have hfin : r.IntermediaryReady alice bob Pprev P Pnext Lm Lp om op (balm + balp + base)
      n3.chain ∧ r.LedgerCleared Lm n3.chain ∧ r.LedgerCleared Lp n3.chain := by
    rcases Threat.RoundSeq.peel_two _ _ _ _ hseq with ⟨n1, hA, hB⟩ | ⟨n1, hA, hB⟩
    · have hI1 := hA.chainInv hstep hR
      obtain ⟨hI3, hCm, hCp⟩ := one clearp hB
        (NetworkState.applyAdv_chainInv apps hstep n1 _ hI1) (clearm n1 hI1)
      exact ⟨hI3, hCm, hCp⟩
    · have hI1 := hA.chainInv hstep hR
      obtain ⟨hI3, hCp, hCm⟩ := one clearm hB
        (NetworkState.applyAdv_chainInv apps hstep n1 _ hI1) (clearp n1 hI1)
      exact ⟨hI3, hCm, hCp⟩
  obtain ⟨hI3, ⟨om', hom', hom'V⟩, ⟨op', hop', hop'V⟩⟩ := hfin
  have htot := hI3.inv.credit
  unfold ledgerPend at htot
  rw [ledgerCur_of_fin hI3.finm hom', ledgerCur_of_fin hI3.finp hop', hom'V, hop'V,
    if_neg (by (simp? says simp only [reduceCtorEq, not_false_eq_true])), if_neg (by (simp? says simp only [reduceCtorEq, not_false_eq_true]))] at htot
  exact ⟨om', op', hom', hop', hom'V, hop'V, by simpa only [Nat.add_zero] using htot⟩

/-- `r.V`'s status is not the `.finalized` constructor. A virtual channel takes no `transfer`
    and no `reclaim` of its own, so only a `conclude` writes that constructor. -/
def SatpNotFinalized {P : Participant} (r : Route E) (net : NetworkState E P) : Prop :=
  ∀ u f o, net.chain.statusOf r.V ≠ .finalized u f o

/-- `P`'s facts on `r.V` that `satp_theorem_3_2`'s ledger phase keeps: `P`'s setup states
    (`HoldsVirtualSetup`), `r.V` not `.finalized` (`SatpNotFinalized`), and the held
    all-signed pre-fund state of `r.V` (`NetworkState.HoldsPrefund`). -/
structure SatpSetup {P : Participant} (r : Route E) (alice bob : Participant)
    (net : NetworkState E P) : Prop where
  /-- `P`'s setup states on `r.V`. -/
  virtualSetup : HoldsVirtualSetup net r alice bob true
  /-- `r.V` is not `.finalized`. -/
  notFinalized : SatpNotFinalized r net
  /-- `P` holds the pre-fund state of `r.V`. -/
  prefund : net.HoldsPrefund r.V

/-- A strategy whose moves send nothing and whose calls do not target `r.V` keeps `SatpSetup`:
    the instance of `UnbeatableIn.and_condInvariant` that carries `satp_theorem_3_2`'s ledger
    phase. `HoldsVirtualSetup` and `HoldsPrefund` read only `sent` and `received`, which no
    adversary move shrinks. One successful call keeps `r.V` off `.finalized`: a `conclude` of
    `r.V` needs a final state that `P` signed, and every `P`-signed proof state of an adversary
    call is one `P` sent (`Bounds.unforgeable`), while `P` sent no final state of `r.V`
    (`satpVirtual_conclude_fails`); a `challenge` or `checkpoint` of `r.V` writes
    `.challenged` or `.open`; `transfer` and `reclaim` need a ledger channel; every other call,
    and `P`'s own calls, leave the status of `r.V` alone (`statusOf_apply_of_not_targets`). -/
theorem UnbeatableIn.and_satpSetup {apps : Apps E} {P : Participant} {T : Threat E P}
    (hbounds : Bounds apps P T) {r : Route E} (hr : r.WellFormed apps)
    {alice bob : Participant} (hE : SatpEnds r alice bob P) {G : NetworkState E P → Prop}
    {net : NetworkState E P}
    (hU : UnbeatableIn apps T (fun m => (∀ op ∈ m.calls, ¬ Op.targets op r.V) ∧ m.NoSend) G net)
    (hI : SatpSetup r alice bob net) :
    UnbeatableIn apps T (fun m => (∀ op ∈ m.calls, ¬ Op.targets op r.V) ∧ m.NoSend)
      (fun n => G n ∧ SatpSetup r alice bob n) net := by
  have hkV : r.V.kind = .virtual := hr.2.2.2.2.2.2.1
  have notFin : ∀ {n : NetworkState E P} {caller : Participant} {op : Op E}
      {s' : Adjudicator E}, HoldsVirtualSetup n r alice bob true →
      (∀ ss ∈ op.proofStates, P ∈ ss.signers → ∃ x ∈ n.sent, x.state = ss.state) →
      n.chain.apply apps caller op = some s' → SatpNotFinalized r n →
      ∀ u f o, s'.statusOf r.V ≠ .finalized u f o := by
    intro n caller op s' hVs hU h hnf
    by_cases ht : Op.targets op r.V
    · cases op with
      | deposit a e x => exact ht.elim
      | tick dt => exact ht.elim
      | transfer a b =>
        simp only [Op.targets] at ht
        subst ht
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hk, -⟩ := Adjudicator.transfer_some h
        rw [hkV] at hk; cases hk
      | reclaim l v =>
        simp only [Op.targets] at ht
        subst ht
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := Adjudicator.reclaim_some h
        rw [hkV] at hk; cases hk
      | challenge c proof cand =>
        simp only [Op.targets] at ht
        subst ht
        obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        intro u f o hst
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
        cases hst
      | checkpoint c proof cand =>
        simp only [Op.targets] at ht
        subst ht
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        intro u f o hst
        rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
        cases hst
      | conclude c ss =>
        simp only [Op.targets] at ht
        subst ht
        obtain ⟨⟨-, hcp⟩, -⟩ := Adjudicator.conclude_some h
        exact (satpVirtual_conclude_fails hVs hE hcp hU).elim
    · rw [statusOf_apply_of_not_targets h ht]
      exact hnf
  have frame : ∀ {n : NetworkState E P} (m : AdvMove E),
      HoldsVirtualSetup n r alice bob true → n.HoldsPrefund r.V →
      HoldsVirtualSetup (n.applyAdv apps m) r alice bob true ∧
        (n.applyAdv apps m).HoldsPrefund r.V := by
    intro n m hVs hpre
    refine ⟨by unfold HoldsVirtualSetup; rw [NetworkState.applyAdv_sent]; exact hVs, ?_⟩
    refine (NetworkState.held_mono (apps := apps) fun ss hH => hH.of_subset (fun s hs => ?_)
      (NetworkState.applyAdv_received_subset apps n m)).1 _ hpre
    rw [NetworkState.applyAdv_sent]; exact hs
  have hstep : T.CondStepInvariant apps (fun _ => True) (fun n => SatpSetup r alice bob n)
      (fun _ op => ¬ Op.targets op r.V) := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, fun _ hc => hc⟩
    · intro n op _ hc ⟨hVs, hnf, hpre⟩
      obtain ⟨hVs', hpre'⟩ := frame (.land op) hVs hpre
      refine ⟨hVs', ?_, hpre'⟩
      intro u f o
      rw [NetworkState.applyAdv_land_chain]
      cases h : n.chain.apply apps P op with
      | none => exact hnf u f o
      | some s' =>
        simp only [Option.getD_some]
        rw [statusOf_apply_of_not_targets h hc]
        exact hnf u f o
    · intro n ss _ _ ⟨hVs, hnf, hpre⟩
      obtain ⟨hVs', hpre'⟩ := frame (.deliver ss) hVs hpre
      exact ⟨hVs', hnf, hpre'⟩
    · intro n dt _ _ ⟨hVs, hnf, hpre⟩
      obtain ⟨hVs', hpre'⟩ := frame (.tick dt) hVs hpre
      refine ⟨hVs', ?_, hpre'⟩
      simp only [SatpNotFinalized, NetworkState.applyAdv, Adjudicator.tick_statusOf]
      exact hnf
    · intro n caller op _ hfeas ⟨hVs, hnf, hpre⟩
      obtain ⟨hVs', hpre'⟩ := frame (.chain caller op) hVs hpre
      refine ⟨hVs', ?_, hpre'⟩
      intro u f o
      rw [NetworkState.applyAdv_chain_chain]
      cases h : n.chain.apply apps caller op with
      | none => exact hnf u f o
      | some s' =>
        simp only [Option.getD_some]
        exact notFin hVs
          (fun ss hss hsig => (hbounds.unforgeable n caller op hfeas ss hss).1 hsig) h hnf u f o
  refine UnbeatableIn.and_condInvariant hstep (fun hal _ op hop => hal.1 op hop) ?_ hU hI
  intro n m hal hI'
  cases m with
  | react rr =>
    obtain ⟨calls, sends⟩ := rr
    have hm : sends = [] := hal.2
    subst hm
    have hn : n.applyHonest (.react ⟨calls, []⟩) = n := by (simp? [NetworkState.applyHonest] says simp only [NetworkState.applyHonest, List.map_nil, List.nil_append])
    rw [hn]; exact hI'
  | wait dt => exact ⟨hI'.virtualSetup, hI'.notFinalized, hI'.prefund⟩

/-- SATP-20 (Theorem 3.2, SATP:503-507). "Let d(V, Pi) be the amount debited to
    V from Pi's balances, across Li and Li−1 in Protocol 3.1. Let c(V, Pi) be
    the amount credited to Pi's balance from guarantees targeting V across Li
    and Li−1 in both Protocol 3.2 and 3.3. For all V, for all i = 1, ..., n,
    if Pi follows Protocols 3.1-3.3, then c(Pi) = d(Pi)." An intermediary
    that completed Round 2 (SATP:411-418) and holds the latest ledger states
    has an unbeatable strategy (Protocol 3.3, SATP:480-485) to finalize both
    ledgers with no guarantee for `V` and its pre-protocol balances
    restored. `Pi`'s own signatures on `V` are the setup states
    (`HoldsVirtualSetup`); the game rule `Bounds.unforgeable` bounds the
    rest. `P` signs a ledger state that funds `V` only when it holds the
    all-signed pre-fund state of `V` (SATP:409,
    "Proceed when s0 is committed"; Definition 3.1, SATP:394-399), and every
    guarantee `P` signs names external peers (SATP:411-418). Both are rules
    of the honest signer (`HonestSend.fundsCommitted`,
    `HonestSend.guaranteesExternal`), which
    `Nitro.participant_sent_honest` and `Nitro.participant_holds_honest` give. -/
theorem satp_theorem_3_2 (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (i : Nat) (hi : 1 ≤ i) (hin : i + 1 < r.peers.length) (hP : r.peers[i]? = some P)
    (Pprev Pnext : Participant) (hprev : r.peers[i - 1]? = some Pprev)
    (hnext : r.peers[i + 1]? = some Pnext)
    (Lm Lp : TimedChannel T.ε) (hLm : r.ledgers[i - 1]? = some (Lm : FixedPart))
    (hLp : r.ledgers[i]? = some (Lp : FixedPart))
    (hdurV : r.V.IsTimed T.ε)
    (om : r.Round2Ledger Pprev P P r.b0) (op : r.Round2Ledger P Pnext P r.a0)
    (net : Nitro.ReachableParticipant apps T)
    (hHm : HoldsLatestLedger net.state (Lm : FixedPart) om.outcome)
    (hHp : HoldsLatestLedger net.state (Lp : FixedPart) op.outcome)
    (hVs : HoldsVirtualSetup net.state r alice bob true)
    (hpend : net.state.DeadlineAfter (Lm : FixedPart) T.ε ∧ net.state.DeadlineAfter (Lp : FixedPart) T.ε ∧
      net.state.DeadlineAfter r.V T.ε)
    (hchain : net.state.chain.finalizedWith (Lm : FixedPart).address = none ∧
      net.state.chain.finalizedWith (Lp : FixedPart).address = none ∧
      net.state.chain.finalizedWith r.V.address = none) :
    Unbeatable apps T (IntermediaryRecovered r (Lm : FixedPart) (Lp : FixedPart) om.bal op.bal
      (net.state.chain.balances.get (.external (r.dest P)))) net.state := by
  have hbounds := A.toBounds
  have hr0 := hr
  obtain ⟨Lm, hdurLm⟩ := Lm
  obtain ⟨Lp, hdurLp⟩ := Lp
  have hchm0 : net.state.chain.finalizedWith Lm.address = none := hchain.1
  have hchp0 : net.state.chain.finalizedWith Lp.address = none := hchain.2.1
  -- The route facts.
  obtain ⟨-, -, hnodup, hdnodup, hled, hVp, hkV, hLV⟩ := hr
  obtain ⟨Pm, Qm, hPm, hQm, hLmp, hkLm, hcm⟩ := hled (i - 1) Lm hLm
  obtain ⟨Pp, Qp, hPp, hQp, hLpp, hkLp, hcp⟩ := hled i Lp hLp
  rw [Nat.sub_add_cancel hi, hP, Option.some.injEq] at hQm
  rw [hP, Option.some.injEq] at hPp
  rw [hprev, Option.some.injEq] at hPm
  rw [hnext, Option.some.injEq] at hQp
  subst hQm hPp hPm hQp
  have hPLm : P ∈ Lm.participants := by rw [hLmp]; (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
  have hPLp : P ∈ Lp.participants := by rw [hLpp]; (simp? says simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])
  have hlt : i - 1 < r.peers.length := by omega
  have hne : Lm ≠ Lp := by
    intro heq
    rw [heq, hLpp, List.cons.injEq] at hLmp
    rw [hLmp.1] at hP
    have := (List.getElem?_inj hlt hnodup).1 (hprev.trans hP.symm)
    omega
  have hidx : ∀ {j k : Nat} {X Y : Participant}, j < r.peers.length → r.peers[j]? = some X →
      r.peers[k]? = some Y → r.dest X = r.dest Y → j = k := by
    intro j k X Y hj hX hY hXY
    have hj' : j < (r.peers.map r.dest).length := by rw [List.length_map]; exact hj
    apply (List.getElem?_inj hj' hdnodup).1
    rw [List.getElem?_map, List.getElem?_map, hX, hY, Option.map_some, Option.map_some, hXY]
  have hdm : r.dest P ≠ r.dest Pprev := fun h => by
    have := hidx (by omega) hP hprev h; omega
  have hdp : r.dest P ≠ r.dest Pnext := fun h => by
    have := hidx (by omega) hP hnext h; omega
  have hE : SatpVirtual apps T.ε r alice bob P :=
    ⟨⟨by rw [hVp]; exact halice, by rw [hVp]; exact hbob, by rw [hVp]; exact List.mem_of_getElem? hP⟩,
      hV, hdurV⟩
  -- The latest ledger states, and what `P`'s honest signing gives about them.
  obtain ⟨ssm, hhm, hallm, hchm, houtm, -, hsentm, hstm⟩ := hHm
  obtain ⟨ssp, hhp, hallp, hchp, houtp, -, hsentp, hstp⟩ := hHp
  have hhonm := Nitro.participant_holds_honest hbounds net hhm (hallm P (by rw [hchm]; exact hPLm))
  have hhonp := Nitro.participant_holds_honest hbounds net hhp (hallp P (by rw [hchp]; exact hPLp))
  have hgm : r.GuaranteeHeld Pprev P om.outcome := by
    have hext := hhonm.guaranteesExternal
    rw [houtm] at hext
    exact ⟨om.afterRound2.2.2.2, hext, om.afterRound2.2.1, om.afterRound2.2.2.1⟩
  have hgp : r.GuaranteeHeld P Pnext op.outcome := by
    have hext := hhonp.guaranteesExternal
    rw [houtp] at hext
    exact ⟨op.afterRound2.2.2.2, hext, op.afterRound2.2.1, op.afterRound2.2.2.1⟩
  have w : r.Intermediary Pprev P Pnext Lm Lp om.outcome op.outcome :=
    ⟨hne, hdm, hdp, hgm, hgp, hkLm, hkLp, hkV⟩
  have hpre : net.state.HoldsPrefund r.V := by
    refine hhonm.fundsCommitted r.V hkV ?_
    rw [houtm]
    show om.outcome.find r.V.address ≠ none
    rw [hgm.find]
    (simp? says simp only [ne_eq, reduceCtorEq, not_false_eq_true])
  have hst1 : (∃ t, net.state.chain.statusOf Lm = .open t ∧ t ≤ ssm.state.turnNum) ∨
      (∃ t ch, net.state.chain.statusOf Lm = .challenged t ch ∧
        (t < ssm.state.turnNum ∨ ch.state = ssm.state) ∧
        net.state.chain.now + T.ε ≤ ch.deadline) := by
    rcases hstm with ho | ⟨t, ch, hstt, hlt⟩
    · exact Or.inl ho
    · exact Or.inr ⟨t, ch, hstt, hlt, hpend.1 t ch hstt⟩
  have hst2 : (∃ t, net.state.chain.statusOf Lp = .open t ∧ t ≤ ssp.state.turnNum) ∨
      (∃ t ch, net.state.chain.statusOf Lp = .challenged t ch ∧
        (t < ssp.state.turnNum ∨ ch.state = ssp.state) ∧
        net.state.chain.now + T.ε ≤ ch.deadline) := by
    rcases hstp with ho | ⟨t, ch, hstt, hlt⟩
    · exact Or.inl ho
    · exact Or.inr ⟨t, ch, hstt, hlt, hpend.2.1 t ch hstt⟩
  -- Phase 1 (Protocol 3.3 step 1): one reaction challenges both ledgers, and both finalize
  -- with the latest states. The strategy sends nothing and does not target `r.V`.
  have hLmV : Lm ≠ r.V := hLV (i - 1) Lm hLm
  have hLpV : Lp ≠ r.V := hLV i Lp hLp
  have hU1 := latest_state_finalizable_two
    (allowed := fun m => (∀ op ∈ m.calls, ¬ Op.targets op r.V) ∧ m.NoSend) apps T A net.state
    net.reachable Lm Lp ssm ssp hne ⟨⟨hcm, hPLm⟩, hdurLm⟩ ⟨⟨hcp, hPLp⟩, hdurLp⟩ hhm hhp hallm hallp hchm hchp
    (fun t ht hc => (hsentm t ht hc).1) (fun t ht hc => (hsentp t ht hc).1)
    (fun t ht hc hfin => by rw [(hsentm t ht hc).2] at hfin; cases hfin)
    (fun t ht hc hfin => by rw [(hsentp t ht hc).2] at hfin; cases hfin)
    hst1 hst2
    ⟨fun op hop => by
      simp only [HonestMove.calls, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl
      · exact hLmV
      · exact hLpV, rfl⟩
    (fun _ => ⟨fun _ h => absurd h List.not_mem_nil, trivial⟩)
  rw [houtm, houtp] at hU1
  have hNF0 : SatpNotFinalized r net.state := by
    intro u f o hst
    have h0 := hchain.2.2
    rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
      ChannelStatus.finalizedWith_finalized] at h0
    cases h0
  have hU2 := UnbeatableIn.and_satpSetup hbounds hr0 hE.toSatpEnds
    (UnbeatableIn.and_reachable hU1 net.reachable) ⟨hVs, hNF0, hpre⟩
  -- The chain invariant, from the start to the goal.
  have hJ0 : r.IntermediaryInv Pprev P Pnext Lm Lp om.outcome op.outcome
      (om.bal + op.bal + net.state.chain.balances.get (.external (r.dest P))) net.state.chain := by
    have hcm0 := ledgerCur_of_not_fin (s := net.state.chain) (L := Lm) (oL := om.outcome)
      (by rw [hchm0]; (simp? says simp only [ne_eq, reduceCtorEq, not_false_eq_true]))
    have hcp0 := ledgerCur_of_not_fin (s := net.state.chain) (L := Lp) (oL := op.outcome)
      (by rw [hchp0]; (simp? says simp only [ne_eq, reduceCtorEq, not_false_eq_true]))
    have hsm : satpShare r net.state.chain 1 r.b0 = r.b0 := by unfold satpShare; rw [hchain.2.2]
    have hsp : satpShare r net.state.chain 0 r.a0 = r.a0 := by unfold satpShare; rw [hchain.2.2]
    refine ⟨⟨fun h => ?_⟩, ⟨fun h => ?_⟩, fun _ => ?_, ?_⟩
    · rw [hchm0] at h; cases h
    · rw [hchp0] at h; cases h
    · rw [hcm0, hcp0]; exact ⟨hgm.find, hgp.find⟩
    unfold ledgerPend
    rw [hcm0, hcp0, if_pos hgm.find, if_pos hgp.find, hsm, hsp, ← om.afterRound2.1,
      ← op.afterRound2.1]
  have hU3 := UnbeatableIn.and_intermediaryInv w hU2 hJ0
  refine UnbeatableIn.bind (UnbeatableIn.mono (fun _ _ => trivial) hU3) (fun {net1} hn1 => ?_)
  obtain ⟨⟨⟨⟨hfm, hfp⟩, hnr1⟩, hVs1, hNF1, hpre1⟩, hJ1⟩ := hn1
  -- Phase 2 (Protocol 3.3 step 2): `r.V` finalizes with a pair outcome.
  have hV2 : Unbeatable apps T (SatpVGoal r alice bob) net1 := by
    obtain ⟨ss0, hH0, hall0, hch0, ht0⟩ := hpre1
    have hsupp0 : satpVirtualRules.supports r.V [ss0] ss0.state = true := by
      simp only [satpVirtualRules, hE.head, hE.last, ht0, Nat.zero_le, ↓reduceIte,
        consensusRules, hch0, decide_true, Bool.true_and, decide_eq_true_eq]
      exact hall0
    have hzero : net1.chain.statusOf r.V = .open 0 →
        ∃ proof0 cand0, satpVirtualRules.supports r.V proof0 cand0 = true ∧
          cand0.turnNum = 0 ∧ ∀ ss ∈ proof0, net1.Holds ss := fun _ =>
      ⟨[ss0], ss0.state, hsupp0, ht0, fun ss hss => by
        rw [List.mem_singleton] at hss; subst hss; exact hH0⟩
    rcases hcs : net1.chain.statusOf r.V with u | ⟨u, ch⟩ | ⟨u, f, o⟩
    · exact satp_virtual_finalize_aux A hE hnr1 hVs1 hzero (Or.inl ⟨u, hcs⟩)
    · by_cases hlt : net1.chain.now < ch.deadline
      · exact satp_virtual_finalize_aux A hE hnr1 hVs1 hzero (Or.inr ⟨u, ch, hcs, hlt⟩)
      · obtain ⟨a, b, hpo, hab⟩ :=
          satpVirtual_challenged_outcome_pair hE hbounds hnr1 hVs1 ⟨hcs⟩
        refine UnbeatableIn.done ⟨ch.state.outcome, a, b, ?_, hpo, hab⟩
        show net1.chain.finalizedWith r.V.address = some ch.state.outcome
        rw [FixedPart.address_eq, Adjudicator.finalizedWith_channel, hcs,
          ChannelStatus.finalizedWith_challenged, if_pos (Nat.le_of_not_lt hlt)]
    · exact absurd hcs (hNF1 u f o)
  have hV3 := UnbeatableIn.and_intermediaryInv w
    ((hV2.and_finalized hfm).and_finalized hfp) hJ1
  refine UnbeatableIn.bind hV3 (fun {net2} hn2 => ?_)
  obtain ⟨⟨⟨⟨Ω, a, b, hΩ, hpo, hab⟩, hfm2⟩, hfp2⟩, hJ2⟩ := hn2
  subst hpo
  -- Phase 3 (Protocol 3.3 step 3): one reaction reclaims both guarantees.
  have hfeas : (HonestMove.react ⟨[Op.reclaim Lm r.V, Op.reclaim Lp r.V], []⟩ :
      HonestMove E).Feasible apps net2 :=
    ⟨fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> exact fun ss hss => by (simp? [Op.proofStates] at hss says simp only [Op.proofStates, List.not_mem_nil] at hss),
     fun _ h => absurd h List.not_mem_nil⟩
  refine UnbeatableIn.move _ trivial hfeas (fun net3 hround => ?_)
  have happ : net3.applyHonest (.react ⟨[Op.reclaim Lm r.V, Op.reclaim Lp r.V], []⟩) = net3 := by
    (simp? [NetworkState.applyHonest] says simp only [NetworkState.applyHonest, List.map_nil, List.nil_append])
  rw [happ]
  exact UnbeatableIn.done (satp_reclaim_round w hround.1 ⟨hJ2, hfm2, hfp2, a, b, hΩ, hab⟩)

/-- On a reachable chain, the virtual channel `r.V` has one outcome: its outcome of
    finalization is its stored outcome (`ChannelStatus.finalOutcome_eq_finalizedWith`).
    Genesis has every channel open. Only `transfer` and `reclaim` rewrite a stored outcome
    (`ChannelStatus.withOutcome`), and both need a ledger channel (`Adjudicator.transfer_some`,
    `Adjudicator.reclaim_some`), while `r.V` is virtual (`Route.WellFormed`). `conclude` stores
    one outcome twice (`Adjudicator.conclude_some`). -/
theorem Route.V_finalOutcome_eq {apps : Apps E} {r : Route E} (hr : r.WellFormed apps)
    {s : Adjudicator E} (hs : Reachable apps s) :
    s.finalOutcome r.V.address = s.finalizedWith r.V.address := by
  have hk : r.V.kind = .virtual := hr.2.2.2.2.2.2.1
  have hsame : ∀ t f o, s.statusOf r.V = .finalized t f o → f = o := by
    induction hs with
    | refl =>
      intro t f o hst
      simp only [Adjudicator.statusOf, Adjudicator.genesis, List.lookup_nil, Option.getD_none,
        reduceCtorEq] at hst
    | @tail s s' _ hstep ih =>
      obtain ⟨caller, op, _, _, h⟩ := hstep
      have keep : s'.statusOf r.V = s.statusOf r.V →
          ∀ t f o, s'.statusOf r.V = .finalized t f o → f = o :=
        fun hst => by rw [hst]; exact ih
      cases op with
      | deposit a e x =>
        obtain ⟨-, -, -, -, hst, -⟩ := Adjudicator.deposit_some h
        exact keep (Adjudicator.statusOf_of_status hst r.V)
      | tick dt =>
        simp only [Adjudicator.apply_tick, Option.some.injEq] at h
        subst h
        exact keep (Adjudicator.tick_statusOf s dt r.V)
      | transfer a b =>
        obtain ⟨_, _, _, _, _, _, _, _, hst, _, hak, _⟩ := Adjudicator.transfer_some h
        have hca : r.V ≠ a := by rintro rfl; rw [hk] at hak; cases hak
        exact keep (by
          rw [Adjudicator.statusOf_of_status hst, Adjudicator.statusOf_setStatus, if_neg hca])
      | reclaim l v =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hst, hlk, _⟩ := Adjudicator.reclaim_some h
        subst hst
        have hcl : r.V ≠ l := by rintro rfl; rw [hk] at hlk; cases hlk
        exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcl])
      | challenge c proof cand =>
        obtain ⟨-, rfl⟩ := Adjudicator.challenge_some h
        by_cases hcc : r.V = c
        · subst hcc
          intro t f o hst
          rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
          cases hst
        · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc])
      | checkpoint c proof cand =>
        obtain ⟨-, rfl⟩ := Adjudicator.checkpoint_some h
        by_cases hcc : r.V = c
        · subst hcc
          intro t f o hst
          rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
          cases hst
        · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc])
      | conclude c ss =>
        obtain ⟨-, rfl⟩ := Adjudicator.conclude_some h
        by_cases hcc : r.V = c
        · subst hcc
          intro t f o hst
          rw [Adjudicator.statusOf_setStatus, if_pos rfl] at hst
          cases hst
          rfl
        · exact keep (by rw [Adjudicator.statusOf_setStatus, if_neg hcc])
  simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
    Adjudicator.finalizedWith_channel]
  exact ChannelStatus.finalOutcome_eq_finalizedWith _ _ hsame

/-- The route facts of the end user `P` that `satp_end_user_recovers`'s chain invariant reads:
    the ledger `L` (latest allocation `oL`) holds the guarantee `G(a0 + b0, [P, Q])` of `r.V`
    (`Route.GuaranteeHeld`), `P` and its peer `Q` have distinct destinations, `L` is a ledger
    channel, and `r.V` is virtual (`Route.WellFormed`, `Route.Round2Ledger`,
    `HonestSend.guaranteesExternal`). -/
structure Route.EndUser (r : Route E) (P Q : Participant) (L : FixedPart) (oL : Allocation E) :
    Prop where
  /-- `oL` holds the guarantee of `r.V`. -/
  held : r.GuaranteeHeld P Q oL
  /-- `P` and `Q` have distinct destinations. -/
  dest : r.dest P ≠ r.dest Q
  /-- `L` is a ledger channel. -/
  kindL : L.kind = .ledger
  /-- `r.V` is a virtual channel. -/
  kindV : r.V.kind = .virtual

/-- The chain invariant of `satp_end_user_recovers`'s strategy (`Route.EndUser`): `L` keeps or
    drops its guarantee (`Route.LedgerHeldInv`), `r.V` stays finalized with `oV`, and `total`
    is at most `P`'s owed amount, the share `oV.amountAt 0` that the guarantee still owes `P`
    (`ledgerPend`), and the balance of `P`'s destination. -/
structure Route.EndUserInv (r : Route E) (P Q : Participant) (L : FixedPart)
    (oL oV : Allocation E) (total : Coins) (s : Adjudicator E) : Prop where
  /-- `L` keeps or drops its guarantee. -/
  held : r.LedgerHeldInv P Q L oL s
  /-- `r.V` is finalized with `oV`. -/
  finV : s.finalizedWith r.V.address = some (.allocation oV)
  /-- `P`'s credit. -/
  credit : total ≤ (ledgerCur s L oL).owed (.external (r.dest P)) +
      ledgerPend r P Q s L oL (oV.amountAt 0) + s.balances.get (.external (r.dest P))

/-- Every on-chain step keeps `Route.EndUserInv` (`ledger_held_step` with `P` as the left
    peer, index 0). The outcome of finalization of `r.V` never changes
    (`Adjudicator.finalizedWith_apply`), so a reclaim pays `P` the share `oV.amountAt 0`. -/
theorem Route.EndUserInv.step {apps : Apps E} {r : Route E} {P Q : Participant}
    {L : FixedPart} {oL oV : Allocation E} {total : Coins} (w : r.EndUser P Q L oL)
    {caller : Participant} {o : Op E} {s s' : Adjudicator E}
    (hI : r.EndUserInv P Q L oL oV total s) (h : s.apply apps caller o = some s') :
    r.EndUserInv P Q L oL oV total s' := by
  obtain ⟨hA, -, -, hC⟩ := ledger_held_step h L (r.dest P) w.held hI.held 0 (oV.amountAt 0)
    (Or.inl ⟨rfl, w.dest, rfl⟩) (fun oV' hf _ => by
      rw [hI.finV, Option.some.injEq, Outcome.allocation.injEq] at hf
      rw [hf])
  exact ⟨hA, Adjudicator.finalizedWith_apply h hI.finV, le_trans hI.credit hC⟩

/-- An unbeatable strategy also reaches its goal with `Route.EndUserInv`, when that holds at
    the start (`UnbeatableIn.and_chainInv`, `Route.EndUserInv.step`). -/
theorem UnbeatableIn.and_endUserInv {apps : Apps E} {p : Participant} {T : Threat E p}
    {allowed : HonestMove E → Prop} {G : NetworkState E p → Prop} {r : Route E}
    {P Q : Participant} {L : FixedPart} {oL oV : Allocation E} {total : Coins}
    (w : r.EndUser P Q L oL) {net : NetworkState E p} (hU : UnbeatableIn apps T allowed G net)
    (hI : r.EndUserInv P Q L oL oV total net.chain) :
    UnbeatableIn apps T allowed (fun n => G n ∧ r.EndUserInv P Q L oL oV total n.chain) net :=
  UnbeatableIn.and_chainInv (fun _ _ _ _ hI h => hI.step w h) hU hI

/-- The chain at the start of `satp_end_user_recovers`'s reclaim round: `Route.EndUserInv`, and
    `L` finalized with its latest allocation. -/
structure Route.EndUserReady (r : Route E) (P Q : Participant) (L : FixedPart)
    (oL oV : Allocation E) (total : Coins) (s : Adjudicator E) : Prop where
  /-- The chain invariant. -/
  inv : r.EndUserInv P Q L oL oV total s
  /-- `L` finalized with `oL`. -/
  finL : s.finalizedWith L.address = some (.allocation oL)

/-- The round of `P`'s call `reclaim L r.V` (Protocol 3.3 step 3) clears `L`. The landing
    succeeds when the guarantee is there (`reclaim_can_happen`), and fails, changing nothing,
    when it is gone. A cleared ledger stays cleared (`Route.LedgerCleared.step`), and every
    step keeps `Route.EndUserReady`. With the guarantee gone, the credit of
    `Route.EndUserInv` is the bound of `EndUserRecovered`. -/
theorem satp_end_user_reclaim_round {apps : Apps E} {r : Route E} {P Q : Participant}
    {T : Threat E P} {t : Time} {L : FixedPart} {oL oV : Allocation E} {total : Coins}
    (w : r.EndUser P Q L oL) (hx : oV.amountAt 0 + oV.amountAt 1 = r.a0 + r.b0)
    {n0 n2 : NetworkState E P} (hseq : T.RoundSeq apps t [Op.reclaim L r.V] n0 n2)
    (hR : r.EndUserReady P Q L oL oV total n0.chain) :
    ∃ o, n2.chain.finalOutcome L.address = some (.allocation o) ∧ o.find r.V.address = none ∧
      total ≤ o.owed (.external (r.dest P)) + n2.chain.balances.get (.external (r.dest P)) := by
  have hstep : ∀ (caller : Participant) (o : Op E) (s s' : Adjudicator E),
      r.EndUserReady P Q L oL oV total s → s.apply apps caller o = some s' →
      r.EndUserReady P Q L oL oV total s' :=
    fun _ _ _ _ hs h => ⟨hs.inv.step w h, Adjudicator.finalizedWith_apply h hs.finL⟩
  have hstepC : ∀ (caller : Participant) (o : Op E) (s s' : Adjudicator E),
      r.EndUserReady P Q L oL oV total s ∧ r.LedgerCleared L s →
      s.apply apps caller o = some s' →
      r.EndUserReady P Q L oL oV total s' ∧ r.LedgerCleared L s' :=
    fun caller o s s' hs h => ⟨hstep caller o s s' hs.1 h, hs.2.step (r.dest P) h⟩
  obtain ⟨n1, hA, hB⟩ := Threat.RoundSeq.peel_one _ _ _ hseq
  have hR1 := hA.chainInv hstep hR
  -- The landing of `reclaim L r.V` clears `L`.
  have hC1 : r.LedgerCleared L (n1.applyAdv apps (.land (Op.reclaim L r.V))).chain := by
    obtain ⟨o, ho, hG | hnone⟩ := hR1.inv.held.held hR1.finL
    · have hext : ∀ e : E, (Address.external e : Address E) ≠ r.V.address := by
        simp only [FixedPart.address_eq, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
      have hrc : n1.chain.apply apps P (.reclaim L r.V) = some _ :=
        reclaim_can_happen n1.chain L r.V o oV (r.a0 + r.b0) _ _ w.kindL w.kindV ho
        hR1.inv.finV hG.find (by rw [Allocation.find_remove, if_neg (hext _)]; exact hG.left)
        (by rw [Allocation.find_remove, if_neg (hext _)]; exact hG.right) hx
      rw [NetworkState.applyAdv_land_some apps (p := P) hrc]
      refine ⟨⟨((o.addTo (.external (r.dest P)) (oV.amountAt 0)).addTo (.external (r.dest Q))
        (oV.amountAt 1)).remove r.V.address, ?_, by rw [Allocation.find_remove, if_pos rfl]⟩⟩
      simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel,
        Adjudicator.statusOf_setStatus, ↓reduceIte, ChannelStatus.finalOutcome_withOutcome]
    · have hrc : n1.chain.apply apps P (.reclaim L r.V) = none := by
        show n1.chain.reclaim L r.V = none
        unfold Adjudicator.reclaim
        simp only [if_pos (⟨w.kindL, w.kindV⟩ : L.kind = .ledger ∧ r.V.kind = .virtual), ho,
          hR1.inv.finV, hnone]
      rw [NetworkState.applyAdv_land_none apps hrc]
      exact ⟨o, ho, hnone⟩
  obtain ⟨hR2, hC2⟩ := hB.chainInv hstepC
    ⟨NetworkState.applyAdv_chainInv apps hstep n1 _ hR1, hC1⟩
  obtain ⟨o', ho', ho'V⟩ := hC2.cleared
  have htot := hR2.inv.credit
  unfold ledgerPend at htot
  rw [ledgerCur_of_fin hR2.finL ho', ho'V,
    if_neg (by simp only [reduceCtorEq, not_false_eq_true])] at htot
  exact ⟨o', ho', ho'V, by simpa only [Nat.add_zero] using htot⟩

/-- SATP-20 (SATP:500-501): "We omit the analogous statement that can be stated
    for the end-users Alice and Bob." The analogue for Alice (`P0`, ledger
    `L0`): if `V` finalizes with `{A : A(a), B : A(b)}` and `a + b = a0 + b0`
    (go-nitro `reclaim` needs it, MultiAssetHolder.sol:365), Alice can
    finalize `L0` with no guarantee for `V` and her entry raised by `a` from
    its Round 2 level, so she is owed her pre-protocol balance minus `a0`
    plus `a`.
    Every guarantee Alice signed in `o` names external peers, as SATP Protocol 3.1 Round 2 has her sign `G(a0 + b0, [P_i, P_{i+1}]` (SATP:411-418); signing otherwise is an own-violation of IR. This is a rule of the honest signer (`HonestSend.guaranteesExternal`), which `Nitro.participant_holds_honest` gives for `o`. -/
theorem satp_end_user_recovers (apps : Apps E) {P : Participant} (T : Threat E P)
    (A : Assumptions apps P T) (r : Route E) (alice bob : Participant) (hr : r.WellFormed apps)
    (hV : apps r.V.appDef = satpVirtualRules)
    (halice : r.peers.head? = some alice) (hbob : r.peers.getLast? = some bob)
    (hPA : P = alice) (P1 : Participant) (hP1 : r.peers[1]? = some P1)
    (L0 : TimedChannel T.ε) (hL0 : r.ledgers[0]? = some (L0 : FixedPart))
    (hdurV : r.V.IsTimed T.ε)
    (o : r.Round2Ledger P P1 P r.a0)
    (net : Nitro.ReachableParticipant apps T)
    (hH : HoldsLatestLedger net.state (L0 : FixedPart) o.outcome)
    (hVs : HoldsVirtualSetup net.state r alice bob true)
    (a b : Coins) (hab : a + b = r.a0 + r.b0)
    (hfin : net.state.chain.finalOutcome r.V.address =
      some (.allocation [alloc (.external (r.dest alice)) a, alloc (.external (r.dest bob)) b]))
    (hpend : net.state.DeadlineAfter (L0 : FixedPart) T.ε)
    (hchain : net.state.chain.finalizedWith (L0 : FixedPart).address = none) :
    Unbeatable apps T (EndUserRecovered r (L0 : FixedPart) o.bal a
      (net.state.chain.balances.get (.external (r.dest P)))) net.state := by
  have hbounds := A.toBounds
  subst hPA
  have hnr := net.reachable
  obtain ⟨L0, hdur0⟩ := L0
  -- The route facts.
  have hr0 := hr
  obtain ⟨-, -, -, hdnodup, hled, -, hkV, -⟩ := hr
  obtain ⟨Pa, Qa, hPa, hQa, hLp, hkL, hcL⟩ := hled 0 L0 hL0
  have h0 : r.peers[0]? = some P := by rw [← List.head?_eq_getElem?]; exact halice
  rw [h0, Option.some.injEq] at hPa
  rw [hP1, Option.some.injEq] at hQa
  subst hPa hQa
  have hPL : P ∈ L0.participants := by
    rw [hLp]; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]
  have hd : r.dest P ≠ r.dest P1 := by
    intro hPQ
    have hlen : 0 < (r.peers.map r.dest).length := by
      rw [List.length_map]
      exact List.length_pos_of_ne_nil (by
        rintro hnil
        simp only [hnil, List.length_nil, lt_self_iff_false, not_false_eq_true, getElem?_neg,
          reduceCtorEq] at h0)
    have h01 : (0 : Nat) = 1 := (List.getElem?_inj hlen hdnodup).1 (by
      rw [List.getElem?_map, List.getElem?_map, h0, hP1, Option.map_some, Option.map_some, hPQ])
    cases h01
  -- The latest ledger state, and what `P`'s honest signing gives about it.
  obtain ⟨ss, hh, hall, hch, hout, -, hsent, hst⟩ := hH
  have hhon := Nitro.participant_holds_honest hbounds net hh (hall P (by rw [hch]; exact hPL))
  have hg : r.GuaranteeHeld P P1 o.outcome := by
    have hext := hhon.guaranteesExternal
    rw [hout] at hext
    exact ⟨o.afterRound2.2.2.2, hext, o.afterRound2.2.1, o.afterRound2.2.2.1⟩
  have w : r.EndUser P P1 L0 o.outcome := ⟨hg, hd, hkL, hkV⟩
  -- Phase 1 (Protocol 3.3 step 1): `P` challenges `L0` with its latest state.
  have hU1 := latest_state_finalizable apps T A net ⟨L0, hdur0⟩ ss hcL hPL hh hall hch
    (fun t ht hc => (hsent t ht hc).1)
    (fun t ht hc hfin => by rw [(hsent t ht hc).2] at hfin; cases hfin)
    (by
      rcases hst with ho | ⟨t, ch, hstt, hlt⟩
      · exact Or.inr (Or.inl ho)
      · exact Or.inr (Or.inr ⟨t, ch, hstt, hlt, hpend t ch hstt⟩))
  rw [hout] at hU1
  -- `r.V` is virtual, so its outcome of finalization is its stored outcome.
  set oV : Allocation E := [alloc (.external (r.dest P)) a, alloc (.external (r.dest bob)) b]
  have hfV : net.state.chain.finalizedWith r.V.address = some (.allocation oV) := by
    rw [← Route.V_finalOutcome_eq hr0 (Nitro.participant_chain_reachable hnr)]
    exact hfin
  -- The chain invariant, from the start to the goal.
  have hJ0 : r.EndUserInv P P1 L0 o.outcome oV
      (o.outcome.owed (.external (r.dest P)) + oV.amountAt 0 +
        net.state.chain.balances.get (.external (r.dest P))) net.state.chain := by
    have hc0 := ledgerCur_of_not_fin (s := net.state.chain) (L := L0) (oL := o.outcome)
      (by rw [hchain]; simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    refine ⟨⟨fun h => ?_⟩, hfV, ?_⟩
    · rw [hchain] at h; cases h
    unfold ledgerPend
    rw [hc0, if_pos hg.find]
  refine UnbeatableIn.bind (UnbeatableIn.and_endUserInv w hU1 hJ0) (fun {net1} hn1 => ?_)
  obtain ⟨hfL1, hJ1⟩ := hn1
  -- Phase 2 (Protocol 3.3 step 3): `P` reclaims the guarantee of `r.V` in `L0`.
  refine UnbeatableIn.move (.chain (.reclaim L0 r.V)) trivial
    (by simp only [HonestMove.Feasible_chain, Op.HonestFeasible, Op.proofStates, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]) (fun net2 hround => ?_)
  rw [NetworkState.applyHonest_chain]
  apply UnbeatableIn.done
  obtain ⟨o', ho', ho'V, htot⟩ := satp_end_user_reclaim_round w
    (show oV.amountAt 0 + oV.amountAt 1 = r.a0 + r.b0 from hab) hround.1 ⟨hJ1, hfL1⟩
  refine ⟨o', ho', ho'V, ?_⟩
  -- `o.bal = owed + a0` (`Route.LedgerAfterRound2`), and `oV.amountAt 0 = a`.
  rw [← o.afterRound2.1]
  have key : ∀ x y z w v u : Nat, x + y + z ≤ w + v → x + u + y + z ≤ w + u + v := by
    intro x y z w v u h
    rw [Nat.add_right_comm x u y, Nat.add_right_comm (x + y) u z, Nat.add_right_comm w u v]
    exact Nat.add_le_add_right h u
  exact key _ _ _ _ _ _ htot

/-! ### The funding point (`funding_point_universally_finalizable`)

The strategy of `p`: challenge an open `c` with a held support proof (first
the funding window, later the proof that the last checkpoint published, D9),
and wait for a running challenge to end. Every supported candidate of `c`
has the outcome `Ω` (`funding_candidate`), and so does every conclusion
proof (`funding_conclusion`): each one carries a signature of `p`, and every
state of `c` that `p` signed has the outcome `Ω` (`FundingSent`, from
`HonestSend.noConflict` and `State.signSlot_setup`). The rank `fundingRank` falls at each change of
the status of `c`. -/

/-- The setup facts of a ForceMove channel `c` at the funding point: the app
    of `c` is `forceMoveRules vt`, and the game library keeps the outcome and
    accepts the setup transitions. -/
structure ForceMoveSetup (apps : Apps E) (vt : State E → State E → Bool) (c : FixedPart) :
    Prop where
  rules : apps c.appDef = forceMoveRules vt
  keeps : SetupPhaseKeepsOutcome vt c
  accepted : SetupPhaseAccepted vt c

/-- What `p`, a participant of `c`, signed for `c`, at the funding point and later in its
    strategy: every state is below the funding point and has the outcome `Ω`. The final
    theorem derives it from `AtFundingPoint` and the signing rule
    `HonestSend.noConflict` (`State.signSlot_setup`). -/
structure FundingSent (p : Participant) (c : FixedPart) (Ω : Outcome E)
    (sent : List (SignedState E)) : Prop where
  mem : p ∈ c.participants
  below : ∀ s ∈ sent, s.state.channel = c → s.state.turnNum < c.n
  outcome : ∀ s ∈ sent, s.state.channel = c → s.state.outcome = Ω

/-- Every candidate of a `forceMoveRules` support proof of `c`, whose
    signatures of `p` are on states `p` sent, has the outcome `Ω` and a turn
    below `2 * c.n`. The proof carries a state at a turn of `p`
    (`forceMove_mover_pos`); `p` sent it, so its turn is below `c.n` and its
    outcome is `Ω`. From there to the candidate, a step into a final state
    keeps the outcome (`forceMove_conclude_keeps_outcome`), and any other step
    is a setup step that the game library keeps (`SetupPhaseKeepsOutcome`),
    because its turn stays below `2 * c.n`. -/
theorem funding_candidate {apps : Apps E} {vt : State E → State E → Bool} {c : FixedPart}
    {Ω : Outcome E} {p : Participant} {sent : List (SignedState E)}
    (G : ForceMoveSetup apps vt c) (hF : FundingSent p c Ω sent)
    {proof : SupportProof E} {cand : State E} (h : (forceMoveRules vt).supports c proof cand = true)
    (hU : ∀ ss ∈ proof, p ∈ ss.signers → ∃ s ∈ sent, s.state = ss.state) :
    cand.outcome = Ω ∧ cand.turnNum < 2 * c.n := by
  obtain ⟨i0, hi0, m0, h0, hchan, -, hsig⟩ := forceMove_mover_pos h hF.mem
  obtain ⟨s, hs, hseq⟩ := hU m0 (List.mem_of_getElem? h0) hsig
  have hsc : s.state.channel = c := by rw [hseq]; exact hchan
  have hb : m0.state.turnNum < c.n := by rw [← hseq]; exact hF.below s hs hsc
  have hΩ : m0.state.outcome = Ω := by rw [← hseq]; exact hF.outcome s hs hsc
  have hlen : proof.length = c.n := (forceMove_supports_valid_run vt c proof cand h).1
  have hfwd : ∀ k, i0 + k < proof.length → ∃ mk : SignedState E, proof[i0 + k]? = some mk ∧
      mk.state.outcome = Ω := by
    intro k
    induction k with
    | zero => intro _; exact ⟨m0, by (simpa? using h0 says simpa only [add_zero] using h0), hΩ⟩
    | succ k ih =>
      intro hlt
      obtain ⟨mk, hmk, hout⟩ := ih (by omega)
      obtain ⟨mk', hmk', hturn⟩ := forceMove_fwd_turnNum h h0 k (by omega)
      obtain rfl : mk = mk' := Option.some.inj (hmk.symm.trans hmk')
      obtain ⟨mk1, hmk1⟩ : ∃ mk1, proof[(i0 + k) + 1]? = some mk1 :=
        ⟨proof[(i0 + k) + 1], List.getElem?_eq_getElem hlt⟩
      have hstep := (forceMove_supports_valid_run vt c proof cand h).2.1 (i0 + k) mk mk1 hmk hmk1
      have hfin := forceMove_conclude_keeps_outcome vt c proof cand h (i0 + k) mk mk1 hmk hmk1
      have hchank : mk.state.channel = c :=
        forceMove_supports_all_channel h mk (List.mem_of_getElem? hmk)
      refine ⟨mk1, hmk1, ?_⟩
      rw [← hout]
      cases hf : mk1.state.isFinal
      · exact G.keeps mk.state mk1.state (hstep.2.2.2 hf) hchank (by omega)
      · exact hfin.1 hf
  obtain ⟨mlast, hlast, rfl⟩ := (forceMove_supports_valid_run vt c proof cand h).2.2
  have hidx : i0 + (proof.length - 1 - i0) = proof.length - 1 := by omega
  obtain ⟨mk, hmk, hout⟩ := hfwd (proof.length - 1 - i0) (by omega)
  obtain ⟨mk', hmk', hturn⟩ := forceMove_fwd_turnNum h h0 (proof.length - 1 - i0) (by omega)
  rw [hidx, ← List.getLast?_eq_getElem?, hlast] at hmk hmk'
  obtain rfl : mlast = mk := Option.some.inj hmk
  obtain rfl : mlast = mk' := Option.some.inj hmk'
  exact ⟨hout, by omega⟩

omit [DecidableEq E] in
/-- Every conclusion proof of `c`, whose signature of `p` is on a state `p`
    sent, has the outcome `Ω`: `p` signs it, and every state of `c` that `p`
    sent has the outcome `Ω`. -/
theorem funding_conclusion {c : FixedPart} {Ω : Outcome E} {p : Participant}
    {sent : List (SignedState E)} (hF : FundingSent p c Ω sent)
    {ss : SignedState E} (hcp : ConclusionProof c ss)
    (hU : p ∈ ss.signers → ∃ s ∈ sent, s.state = ss.state) : ss.state.outcome = Ω := by
  obtain ⟨hchan, -, hall⟩ := hcp
  obtain ⟨s, hs, hseq⟩ := hU (hall p (by rw [hchan]; exact hF.mem))
  rw [← hseq]
  exact hF.outcome s hs (by rw [hseq]; exact hchan)

/-- The statuses of `c` from which no outcome but `Ω` finalizes: the turn
    record is below `2 * c.n`, and a challenge or a finalization carries `Ω`. -/
def FundingSafe (c : FixedPart) (Ω : Outcome E) : ChannelStatus E → Prop
  | .open t => t < 2 * c.n
  | .challenged t ch => t < 2 * c.n ∧ ch.state.outcome = Ω
  | .finalized _ f _ => f = Ω

/-- The progress rank of the strategy of `p`: it falls at each change of the
    status of `c` (`funding_status_step`). A challenge ranks below an open
    status at the same record; a finalization ranks lowest. -/
def fundingRank (c : FixedPart) : ChannelStatus E → Nat
  | .open t => 2 * (2 * c.n - t) + 2
  | .challenged t _ => 2 * (2 * c.n - t) + 1
  | .finalized .. => 0

/-- One step of the status of `c` under an operation `op`: the new status is
    safe, it is the old one or has a lower rank or the rank `0`, and a new
    open status comes from a support proof that `op` publishes. -/
structure FundingStep (apps : Apps E) (c : FixedPart) (Ω : Outcome E) (op : Op E)
    (st st' : ChannelStatus E) : Prop where
  safe : FundingSafe c Ω st'
  rank : st' = st ∨ fundingRank c st' < fundingRank c st ∨ fundingRank c st' = 0
  witness : ∀ t, st' = .open t → st' ≠ st → ∃ cand,
    (apps c.appDef).supports c op.proofStates cand = true ∧ cand.channel = c ∧ t ≤ cand.turnNum

/-- A successful operation whose signatures of `p` are on states `p` sent
    is a `FundingStep` of the status of `c`. A payout (`transfer`, `reclaim`)
    of `c` needs `c` finalized and keeps the outcome of finalization; a
    challenge or a checkpoint raises the record to a candidate with the
    outcome `Ω` (`funding_candidate`); a conclusion has the outcome `Ω`
    (`funding_conclusion`). -/
theorem funding_status_step {apps : Apps E} {vt : State E → State E → Bool} {c : FixedPart}
    {Ω : Outcome E} {p : Participant} {sent : List (SignedState E)}
    (G : ForceMoveSetup apps vt c) (hF : FundingSent p c Ω sent)
    {s s' : Adjudicator E} {caller : Participant} {op : Op E} (h : s.apply apps caller op = some s')
    (hU : ∀ ss ∈ op.proofStates, p ∈ ss.signers → ∃ x ∈ sent, x.state = ss.state)
    (hS : FundingSafe c Ω (s.statusOf c)) :
    FundingStep apps c Ω op (s.statusOf c) (s'.statusOf c) := by
  have hpay : ∀ {x : Outcome E} (o : Outcome E), (s.statusOf c).finalOutcome s.now = some x →
      FundingStep apps c Ω op (s.statusOf c) ((s.statusOf c).withOutcome o) := by
    intro x o hf
    cases hst : s.statusOf c with
    | «open» r => rw [hst] at hf; (simp? [ChannelStatus.finalOutcome] at hf says simp only [ChannelStatus.finalOutcome, reduceCtorEq] at hf)
    | challenged r ch =>
      rw [hst] at hS
      exact ⟨hS.2, Or.inr (Or.inr rfl), fun _ h' => by cases h'⟩
    | finalized r f o' =>
      rw [hst] at hS
      exact ⟨hS, Or.inr (Or.inr rfl), fun _ h' => by cases h'⟩
  by_cases ht : Op.targets op c
  swap
  · rw [statusOf_apply_of_not_targets h ht]
    exact ⟨hS, Or.inl rfl, fun _ _ hne => absurd rfl hne⟩
  cases op with
  | deposit a e x => (simp? [Op.targets] at ht says simp only [Op.targets] at ht)
  | tick dt => (simp? [Op.targets] at ht says simp only [Op.targets] at ht)
  | transfer a b =>
    simp only [Op.targets] at ht; subst a
    obtain ⟨o, amt, x, hf, -, -, -, -, hst, -⟩ := Adjudicator.transfer_some h
    rw [Adjudicator.statusOf_of_status hst]
    simp only [Adjudicator.statusOf_setStatus, if_true]
    simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hf
    exact hpay _ hf
  | reclaim l v =>
    simp only [Op.targets] at ht; subst l
    obtain ⟨oL, -, -, -, -, hL, -, -, -, -, -, rfl, -, -⟩ := Adjudicator.reclaim_some h
    simp only [Adjudicator.statusOf_setStatus, if_true]
    simp only [FixedPart.address_eq, Adjudicator.finalOutcome_channel] at hL
    exact hpay _ hL
  | challenge c' proof cand =>
    simp only [Op.targets] at ht; subst c'
    obtain ⟨⟨-, hsup, -, hmode⟩, rfl⟩ := Adjudicator.challenge_some h
    simp only [Adjudicator.statusOf_setStatus, if_true]
    rw [G.rules] at hsup
    obtain ⟨hΩ, hturn⟩ := funding_candidate G hF hsup hU
    refine ⟨⟨hturn, hΩ⟩, Or.inr (Or.inl ?_), fun _ h' => by cases h'⟩
    rw [Adjudicator.mode_eq] at hmode
    cases hst : s.statusOf c with
    | «open» r =>
      rw [hst] at hmode
      rcases hmode with ⟨-, hr⟩ | ⟨hm, -⟩
      · simp only [ChannelStatus.turnNumRecord_open] at hr
        simp only [fundingRank]
        omega
      · cases hm
    | challenged r ch' =>
      rw [hst] at hmode
      rcases hmode with ⟨hm, -⟩ | ⟨-, hr⟩
      · simp only [ChannelStatus.mode] at hm
        split at hm <;> cases hm
      · simp only [ChannelStatus.turnNumRecord_challenged] at hr
        simp only [fundingRank]
        omega
    | finalized r f o =>
      rw [hst] at hmode
      rcases hmode with ⟨hm, -⟩ | ⟨hm, -⟩ <;> cases hm
  | checkpoint c' proof cand =>
    simp only [Op.targets] at ht; subst c'
    obtain ⟨⟨hopen, hsup, hcc, hlt⟩, rfl⟩ := Adjudicator.checkpoint_some h
    simp only [Adjudicator.statusOf_setStatus, if_true]
    have hsup' := hsup
    rw [G.rules] at hsup'
    obtain ⟨-, hturn⟩ := funding_candidate G hF hsup' hU
    refine ⟨hturn, Or.inr (Or.inl ?_), fun t h' _ => ?_⟩
    · cases hst : s.statusOf c with
      | «open» r =>
        rw [hst] at hlt
        simp only [ChannelStatus.turnNumRecord_open] at hlt
        simp only [fundingRank]
        omega
      | challenged r ch =>
        rw [hst] at hlt
        simp only [ChannelStatus.turnNumRecord_challenged] at hlt
        simp only [fundingRank]
        omega
      | finalized r f o => rw [hst] at hopen; exact absurd rfl hopen
    · cases h'
      exact ⟨cand, hsup, hcc, le_refl _⟩
  | conclude c' ss =>
    simp only [Op.targets] at ht; subst c'
    obtain ⟨⟨-, hcp⟩, rfl⟩ := Adjudicator.conclude_some h
    simp only [Adjudicator.statusOf_setStatus, if_true]
    exact ⟨funding_conclusion hF hcp (hU ss (List.mem_singleton_self ss)), Or.inr (Or.inr rfl),
      fun _ h' => by cases h'⟩

/-- The invariant of the strategy of `p` at the funding point: the network is
    reachable, `p` signs nothing new, the status of `c` is safe, and `p`
    holds a support proof for every open record of `c`, to challenge with. -/
structure FundingInv (apps : Apps E) {p : Participant} (T : Threat E p) (c : FixedPart)
    (Ω : Outcome E) (sent : List (SignedState E)) (net : NetworkState E p) : Prop where
  reach : (Nitro.participant apps T).Reachable net
  sent_eq : net.sent = sent
  safe : FundingSafe c Ω (net.chain.statusOf c)
  witness : ∀ t, net.chain.statusOf c = .open t → ∃ proof cand, (∀ ss ∈ proof, net.Holds ss) ∧
    (apps c.appDef).supports c proof cand = true ∧ cand.channel = c ∧ t ≤ cand.turnNum

/-- The progress bound of one round: the rank stays below `K`, or the status
    stays `S`. `K` is positive and `S` ranks at most `K`. -/
structure FundingBound (c : FixedPart) (K : Nat) (S : ChannelStatus E) : Prop where
  pos : 0 < K
  le : fundingRank c S ≤ K

omit [DecidableEq E] in
/-- The rank stays below `K`, or the status stays `S`, over a step that keeps
    the status, lowers the rank, or gives the rank `0`. -/
theorem FundingBound.step {c : FixedPart} {K : Nat} {S st st' : ChannelStatus E}
    (hB : FundingBound c K S) (hprev : fundingRank c st < K ∨ st = S)
    (hstep : st' = st ∨ fundingRank c st' < fundingRank c st ∨ fundingRank c st' = 0) :
    fundingRank c st' < K ∨ st' = S := by
  rcases hstep with rfl | hlt | h0
  · exact hprev
  · rcases hprev with h | rfl
    · exact Or.inl (lt_trans hlt h)
    · exact Or.inl (lt_of_lt_of_le hlt hB.le)
  · exact Or.inl (by rw [h0]; exact hB.pos)

/-- An adversary move that keeps the status of `c` keeps `FundingInv`. -/
theorem FundingInv.of_adv {apps : Apps E} {p : Participant} {T : Threat E p} {c : FixedPart}
    {Ω : Outcome E} {sent : List (SignedState E)} {n : NetworkState E p}
    (hI : FundingInv apps T c Ω sent n) (m : AdvMove E)
    (hreach : (Nitro.participant apps T).Reachable (n.applyAdv apps m))
    (hst : (n.applyAdv apps m).chain.statusOf c = n.chain.statusOf c) :
    FundingInv apps T c Ω sent (n.applyAdv apps m) := by
  refine ⟨hreach, by rw [NetworkState.applyAdv_sent]; exact hI.sent_eq,
    by rw [hst]; exact hI.safe, fun t ht => ?_⟩
  obtain ⟨proof, cand, hH, hsup, hcc, hle⟩ := hI.witness t (hst ▸ ht)
  exact ⟨proof, cand, fun ss hss => NetworkState.Holds.mono (NetworkState.applyAdv_sent apps n m).symm
    (NetworkState.applyAdv_received_subset apps n m) (hH ss hss), hsup, hcc, hle⟩

/-- An on-chain call whose proof states are unforged keeps `FundingInv`, and
    keeps the status of `c`, lowers its rank, or gives the rank `0`. -/
theorem FundingInv.chain {apps : Apps E} {vt : State E → State E → Bool} {c : FixedPart}
    {Ω : Outcome E} {p : Participant} {T : Threat E p} {sent : List (SignedState E)}
    (G : ForceMoveSetup apps vt c) (hF : FundingSent p c Ω sent)
    {n : NetworkState E p} (hI : FundingInv apps T c Ω sent n) {caller : Participant} {op : Op E}
    (hreach : (Nitro.participant apps T).Reachable (n.applyAdv apps (.chain caller op)))
    (hU : ∀ ss ∈ op.proofStates, n.Unforged ss) :
    FundingInv apps T c Ω sent (n.applyAdv apps (.chain caller op)) ∧
      ((n.applyAdv apps (.chain caller op)).chain.statusOf c = n.chain.statusOf c ∨
        fundingRank c ((n.applyAdv apps (.chain caller op)).chain.statusOf c) <
          fundingRank c (n.chain.statusOf c) ∨
        fundingRank c ((n.applyAdv apps (.chain caller op)).chain.statusOf c) = 0) := by
  cases hap : n.chain.apply apps caller op with
  | none =>
    rw [NetworkState.applyAdv_chain_none apps hap] at hreach ⊢
    exact ⟨hI, Or.inl rfl⟩
  | some s' =>
    rw [NetworkState.applyAdv_chain_some apps hap] at hreach ⊢
    have hU' : ∀ ss ∈ op.proofStates, p ∈ ss.signers → ∃ x ∈ sent, x.state = ss.state := by
      intro ss hss hps
      rw [← hI.sent_eq]
      exact (hU ss hss).1 hps
    have hst := funding_status_step G hF hap hU' hI.safe
    refine ⟨⟨hreach, hI.sent_eq, hst.safe, fun t ht => ?_⟩, hst.rank⟩
    by_cases hch : s'.statusOf c = n.chain.statusOf c
    · obtain ⟨proof, cand, hH, hsup, hcc, hle⟩ := hI.witness t (hch ▸ ht)
      exact ⟨proof, cand, fun ss hss => NetworkState.Holds.of_subset (net := n) (fun x hx => hx)
        (fun r hr => List.mem_append_right _ hr) (hH ss hss), hsup, hcc, hle⟩
    · obtain ⟨cand, hsup, hcc, hle⟩ := hst.witness t ht hch
      exact ⟨op.proofStates, cand, fun ss hss => holds_of_mem_received (List.mem_append_left _ hss),
        hsup, hcc, hle⟩

/-- `FundingInv` with the progress bound (`FundingBound.step`), as a step
    invariant of a sub-round of pure adversary play
    (`Threat.RoundSeq.nil_invariant`). -/
theorem funding_nil_step {apps : Apps E} {vt : State E → State E → Bool} {c : FixedPart}
    {Ω : Outcome E} {p : Participant} {T : Threat E p} {sent : List (SignedState E)}
    (A : Assumptions apps p T) (G : ForceMoveSetup apps vt c)
    (hF : FundingSent p c Ω sent) {Guard : NetworkState E p → Prop} {K : Nat}
    {S : ChannelStatus E} (hB : FundingBound c K S) :
    T.StepInvariant apps Guard
      (fun n => FundingInv apps T c Ω sent n ∧
        (fundingRank c (n.chain.statusOf c) < K ∨ n.chain.statusOf c = S))
      (fun _ _ => False) where
  land := fun _ h _ => h.elim
  deliver := fun {_ ss} _ hfeas hI =>
    ⟨hI.1.of_adv (.deliver ss) ((Threat.reachable_step (T := T)).deliver trivial hfeas hI.1.reach) rfl,
      hI.2⟩
  tick := fun {n dt} _ hfeas hI =>
    ⟨hI.1.of_adv (.tick dt) ((Threat.reachable_step (T := T)).tick trivial hfeas hI.1.reach)
      (Adjudicator.tick_statusOf n.chain dt c), hI.2⟩
  chain := fun {n caller op} _ hfeas hI => by
    obtain ⟨hI', hstep⟩ := hI.1.chain G hF
      ((Threat.reachable_step (T := T)).chain trivial hfeas hI.1.reach)
      (A.unforgeable n caller op hfeas)
    exact ⟨hI', hB.step hI.2 hstep⟩

/-- **The strategy of `p` at the funding point.** From a state with
    `FundingInv`, `p` finalizes `c` with `Ω`: it challenges an open `c` with
    its held support proof, and waits for a running challenge to end. Each
    round lowers `fundingRank` or ends at the goal. Strong induction on the
    rank. -/
theorem funding_strategy {apps : Apps E} {vt : State E → State E → Bool} {c : FixedPart}
    {Ω : Outcome E} {p : Participant} {T : Threat E p} {sent : List (SignedState E)}
    (A : Assumptions apps p T) (G : ForceMoveSetup apps vt c) (hF : FundingSent p c Ω sent) :
    ∀ μ (n : NetworkState E p), FundingInv apps T c Ω sent n →
      fundingRank c (n.chain.statusOf c) ≤ μ →
      UnbeatableIn apps T (fun _ => True) (fun n => n.Finalized c Ω) n := by
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
  intro n hI hμ
  cases hst : n.chain.statusOf c with
  | finalized t f o =>
    have hf : f = Ω := by have h := hI.safe; rw [hst] at h; exact h
    apply UnbeatableIn.done
    simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
      ChannelStatus.finalizedWith_finalized, hf]
  | challenged t ch =>
    have hsafe : t < 2 * c.n ∧ ch.state.outcome = Ω := by have h := hI.safe; rw [hst] at h; exact h
    rw [hst] at hμ
    by_cases hexp : ch.deadline ≤ n.chain.now
    · apply UnbeatableIn.done
      simp only [NetworkState.Finalized, FixedPart.address_eq, Adjudicator.finalizedWith_channel, hst,
        ChannelStatus.finalizedWith_challenged, if_pos hexp, hsafe.2]
    · refine UnbeatableIn.move (.wait (ch.deadline - n.chain.now)) trivial trivial
        fun n1 hround => ?_
      have hK : 0 < fundingRank c (ChannelStatus.challenged t ch) := Nat.succ_pos _
      obtain ⟨hI1, hprog⟩ := Threat.RoundSeq.nil_invariant hround.1
        (funding_nil_step A G hF ⟨hK, le_refl _⟩) ⟨hI, Or.inr hst⟩
      have hI2 : FundingInv apps T c Ω sent (n1.applyHonest (.wait (ch.deadline - n.chain.now))) :=
        ⟨Machine.Reachable.tail hI1.reach (Or.inl ⟨.wait (ch.deadline - n.chain.now), trivial, rfl⟩), hI1.sent_eq, hI1.safe,
          hI1.witness⟩
      rcases hprog with hlt | heq
      · exact ih _ (lt_of_lt_of_le hlt hμ) _ hI2 (le_refl _)
      · apply UnbeatableIn.done
        have hnow : n.chain.now ≤ n1.chain.now := hround.1.now_le
        have hge : ch.deadline ≤ n1.chain.now + (ch.deadline - n.chain.now) :=
          (Nat.add_sub_cancel' (le_of_lt (not_le.mp hexp))).symm.le.trans (Nat.add_le_add_right hnow _)
        simp only [NetworkState.applyHonest, NetworkState.Finalized, FixedPart.address_eq,
          Adjudicator.finalizedWith_channel, Adjudicator.tick_statusOf, heq, Adjudicator.tick_now,
          ChannelStatus.finalizedWith_challenged, if_pos hge, hsafe.2]
  | «open» t =>
    rw [hst] at hμ
    obtain ⟨proof, cand, hH, hsup, hcc, hle⟩ := hI.witness t hst
    have hfeas : (Op.challenge c proof cand).HonestFeasible n := hH
    refine UnbeatableIn.move (.chain (.challenge c proof cand)) trivial
      ((HonestMove.Feasible_chain _ _ _).2 hfeas) fun n1 hround => ?_
    rw [NetworkState.applyHonest_chain]
    obtain ⟨na, hseqA, hseqB⟩ := Threat.Round.single hround
    have hK : 0 < fundingRank c (ChannelStatus.open t : ChannelStatus E) := Nat.succ_pos _
    obtain ⟨hIa, hproga⟩ := Threat.RoundSeq.nil_invariant hseqA
      (funding_nil_step A G hF ⟨hK, le_refl _⟩) ⟨hI, Or.inr hst⟩
    have hfeasA : (Op.challenge c proof cand).HonestFeasible na := Op.HonestFeasible.round hseqA hfeas
    have hland : na.applyAdv apps (.land (.challenge c proof cand)) =
        na.applyAdv apps (.chain p (.challenge c proof cand)) := rfl
    have hreachL := (Threat.reachable_step (T := T)).land trivial hfeasA hIa.reach
    rw [hland] at hreachL hseqB
    have hUL : ∀ ss ∈ (Op.challenge c proof cand).proofStates, na.Unforged ss := fun ss hss =>
      (hfeasA ss hss).unforged (Nitro.participant_received_unforged A.toBounds ⟨na, hIa.reach⟩)
    obtain ⟨hIL, hstepL⟩ := hIa.chain G hF hreachL hUL
    have hprogL : fundingRank c ((na.applyAdv apps (.chain p (.challenge c proof cand))).chain.statusOf c) <
        fundingRank c (ChannelStatus.open t : ChannelStatus E) := by
      rcases hproga with hlt | hopen
      · rcases hstepL with heq | hlt' | h0
        · rw [heq]; exact hlt
        · exact lt_trans hlt' hlt
        · rw [h0]; exact hK
      · have hmode : (na.chain.statusOf c).mode na.chain.now = .open ∧
            (na.chain.statusOf c).turnNumRecord ≤ cand.turnNum := by
          rw [hopen]; exact ⟨rfl, hle⟩
        have happ : na.chain.apply apps p (.challenge c proof cand) = some (na.chain.setStatus c
            (.challenged cand.turnNum ⟨cand, na.chain.now + c.challengeDuration⟩)) := by
          simp only [Adjudicator.apply, Adjudicator.challenge]
          rw [if_pos ⟨hF.mem, hsup, hcc, Or.inl ⟨by rw [Adjudicator.mode_eq]; exact hmode.1, hmode.2⟩⟩]
        have hsafeL := hIL.safe
        rw [NetworkState.applyAdv_chain_some apps happ] at hsafeL ⊢
        simp only [Adjudicator.statusOf_setStatus, if_true] at hsafeL ⊢
        have hturn := hsafeL.1
        simp only [fundingRank]
        omega
    obtain ⟨hIB, hprogB⟩ := Threat.RoundSeq.nil_invariant hseqB
      (funding_nil_step A G hF (S := .finalized 0 Ω Ω) ⟨hK, Nat.zero_le _⟩)
      ⟨hIL, Or.inl hprogL⟩
    have hlt : fundingRank c (n1.chain.statusOf c) < fundingRank c (ChannelStatus.open t : ChannelStatus E) := by
      rcases hprogB with h | h
      · exact h
      · rw [h]; exact hK
    exact ih _ (lt_of_lt_of_le hlt hμ) n1 hIB (le_refl _)

/-- Nitro-23, ForceMove-B06, ForceMove-A06, ForceMove-A07. Nitro:635-636, Nitro:639-640: at the funding
    point, "After the first n states have been broadcast", the outcome is
    universally finalizable. ForceMove:862-871: the prefund states are "exactly what
    they need to launch a challenge on-chain to recover their funds". The
    setup phase keeps the outcome (ForceMove:1092-1125, ForceMove:1150-1184),
    and the game library accepts its transitions. An honest participant signs
    every setup state of `c` with the setup outcome:
    `HonestSend.noConflict` (`State.signSlot_setup`), which `Nitro.participant_sent_honest` gives for
    every view. The strategy is `funding_strategy`. Design decision 2026-11-01: no
    timing premise; every candidate and conclusion proof carries Ω
    (`HonestSend.noConflict`). -/
theorem funding_point_universally_finalizable (apps : Apps E) (Ts : Threats E apps) (v : Views E)
    (n : Nitro.ReachableNetwork apps Ts)
    (hvn : v = n.state.views) (c : FixedPart) (Ω : Outcome E) (vt : State E → State E → Bool)
    (hc : apps c.appDef = forceMoveRules vt) (hsetup : SetupPhaseKeepsOutcome vt c)
    (hvt : SetupPhaseAccepted vt c)
    (hn : 0 < c.n) (h : AtFundingPoint v c Ω)
    (hchain : ∀ p, (v p).chain.mode c = .open ∧ (v p).chain.statusOf c = .open 0) :
    ∀ p ∈ c.participants, Finalizable apps (Ts.T p) c Ω (v p) := by
  intro p hp
  have G : ForceMoveSetup apps vt c := ⟨hc, hsetup, hvt⟩
  have hreach : (Nitro.participant apps (Ts.T p)).Reachable (v p) := by
    subst hvn; exact Nitro.network_views_participant_reachable n p
  have hhon := Nitro.participant_sent_honest ⟨_, hreach⟩
  have hunf := Nitro.participant_received_unforged (Ts.ok p).toBounds ⟨_, hreach⟩
  obtain ⟨hfund, hbelow⟩ := h
  have hsentk : ∀ k, k < c.n → c.participants[k]? = some p →
      ∃ s ∈ (v p).sent, s.state.channel = c ∧ s.state.turnNum = k ∧ s.state.outcome = Ω := by
    intro k hk hkp
    obtain ⟨ss, hH, hc', ht, hΩ, -, hbm⟩ := hfund p hp k hk
    have hmv : ss.state.mover = some p := by
      unfold State.mover
      rw [hc', ht, Nat.mod_eq_of_lt hk]
      exact hkp
    obtain ⟨s, hs, hseq⟩ := (hH.unforged hunf).1 (hbm.signer_of_mover hmv)
    exact ⟨s, hs, by rw [hseq]; exact hc', by rw [hseq]; exact ht, by rw [hseq]; exact hΩ⟩
  have hF : FundingSent p c Ω (v p).sent := by
    refine ⟨hp, hbelow p hp, fun s hs hsc => ?_⟩
    obtain ⟨k, hkp⟩ := List.mem_iff_getElem?.mp hp
    have hk : k < c.n := (List.getElem?_eq_some_iff.mp hkp).1
    obtain ⟨s', hs', hc', ht', hΩ'⟩ := hsentk k hk hkp
    have heq := (hhon s hs).outcome_eq s' hs' (by rw [hc', hsc]) (State.signSlot_setup
      ⟨by rw [hc', ht']; exact hk, by rw [hsc]; exact hbelow p hp s hs hsc⟩)
    rw [← heq, hΩ']
  -- The funding window: the `c.n` setup states that `p` holds form a
  -- `forceMoveRules` support proof (`SetupPhaseAccepted` accepts each step).
  have hwindow : ∃ proof cand, (∀ ss ∈ proof, (v p).Holds ss) ∧
      (apps c.appDef).supports c proof cand = true ∧ cand.channel = c := by
    choose f hf using fun k : Fin c.n => hfund p hp k.1 k.2
    have hget : ∀ i (hi : i < c.n), (List.ofFn f)[i]? = some (f ⟨i, hi⟩) := fun i hi => by
      (simp? [hi] says simp only [List.length_ofFn, hi, getElem?_pos, List.getElem_ofFn])
    refine ⟨List.ofFn f, (f ⟨c.n - 1, by omega⟩).state, fun ss hss => ?_, ?_, (hf _).2.1⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hss
      exact (hf i).1
    · rw [G.rules]
      simp only [forceMoveRules, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨List.length_ofFn, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [List.head?_eq_getElem?, hget 0 hn]
        exact (SignedState.byMover_iff _).2 (hf _).2.2.2.2.2
      · apply validRun_of_getElem?
        intro i m1 m2 h1 h2
        have hi1 : i + 1 < c.n := by
          by_contra hge
          rw [List.getElem?_eq_none (by simp only [List.length_ofFn]; omega)] at h2
          cases h2
        rw [hget i (by omega)] at h1
        rw [hget (i + 1) hi1] at h2
        obtain rfl := Option.some.inj h1
        obtain rfl := Option.some.inj h2
        obtain ⟨-, hc1, ht1, hΩ1, hf1, -⟩ := hf ⟨i, by omega⟩
        obtain ⟨-, hc2, ht2, hΩ2, hf2, hbm2⟩ := hf ⟨i + 1, hi1⟩
        have hvt' := G.accepted _ _ hc1 hc2 (by rw [ht1, ht2]) (by rw [ht2]; exact hi1)
          (by rw [hΩ1, hΩ2]) hf2
        simp only [validMove, hc1, hc2, ht1, ht2, hf1, hf2, hvt', (SignedState.byMover_iff _).2 hbm2,
          decide_true, Bool.not_false, Bool.true_or, Bool.false_or, Bool.and_self]
      · rw [List.all_eq_true]
        intro m hm
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hm
        exact decide_eq_true (hf i).2.1
      · rw [List.getLast?_eq_getElem?, List.length_ofFn, hget _ (by omega)]
        rfl
  have hI0 : FundingInv apps (Ts.T p) c Ω (v p).sent (v p) := by
    refine ⟨hreach, rfl, ?_, fun t ht => ?_⟩
    · rw [(hchain p).2]
      show 0 < 2 * c.n
      omega
    · rw [(hchain p).2] at ht
      cases ht
      obtain ⟨proof, cand, hH, hsup, hcc⟩ := hwindow
      exact ⟨proof, cand, hH, hsup, hcc, Nat.zero_le _⟩
  exact funding_strategy (Ts.ok p) G hF _ _ hI0 (le_refl _)

end ArmadaLean.Nitro
